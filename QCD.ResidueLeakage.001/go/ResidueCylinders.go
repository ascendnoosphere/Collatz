// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere
package main

import (
	"encoding/json"
	"fmt"
	"math/big"
	"math/bits"
	"os"
	"path/filepath"
	"runtime"
	"sync"
)

const (
	MaxBits    = 4096
	MaxModulus = uint64(1 << 20)
	MaxSeeds   = uint64(1 << 20)
	WordCount  = MaxBits/bits.UintSize + 2
)

// Parameters retain the positive-divisor raw convention; the offset may also be zero.
type Parameters struct {
	Q uint64 `json:"q"`
	C uint64 `json:"c"`
	D uint64 `json:"d"`
}

// Workspace owns independent reusable limbs for the block and raw-clock computations.
type Workspace struct {
	words                    [16][WordCount]big.Word
	Q, C, D, Seed            big.Int
	State, Multiplier        big.Int
	Quotient, Remainder      big.Int
	Product, PowerProduct    big.Int
	RawState, RawQuotient    big.Int
	RawRemainder, RawProduct big.Int
	SavedEndpoint, SavedUnit big.Int
	Ticks, Divisions         uint64
}

// Record is a finite exhaustive certificate, not a decision of infinite division survival.
type Record struct {
	Parameters       Parameters `json:"parameters"`
	Period           uint64     `json:"period"`
	Depth            uint64     `json:"depth"`
	Modulus          uint64     `json:"source_modulus"`
	Classes          uint64     `json:"legal_classes"`
	Expected         uint64     `json:"expected_classes"`
	RawClocksChecked uint64     `json:"raw_clocks_checked"`
	LiftsChecked     uint64     `json:"lift_digits_checked"`
	StrictShortfall  bool       `json:"strict_shortfall"`
}

// Report separates finite evidence from the infinite theorem proved in Lean and TeX.
type Report struct {
	Scope   string   `json:"scope"`
	Records []Record `json:"records"`
}

// Initialize gives every big integer disjoint capacity before entering a hot loop.
func (w *Workspace) Initialize() {
	values := [...]*big.Int{
		&w.Q, &w.C, &w.D, &w.Seed, &w.State, &w.Multiplier,
		&w.Quotient, &w.Remainder, &w.Product, &w.PowerProduct,
		&w.RawState, &w.RawQuotient, &w.RawRemainder, &w.RawProduct,
		&w.SavedEndpoint, &w.SavedUnit,
	}
	for i, value := range values {
		value.SetBits(w.words[i][:])
		value.SetUint64(0)
	}
}

// GCD certifies the unit condition required by the residue permutation.
func GCD(a, b uint64) uint64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// AccessPeriod finds the first positive zero return using at most D residue steps.
func AccessPeriod(p Parameters) (uint64, error) {
	if p.Q < 2 || p.D < 2 || p.D > MaxModulus || GCD(p.Q, p.D) != 1 {
		return 0, fmt.Errorf("inadmissible positive unit parameters: %+v", p)
	}
	// Reducing both coefficients first bounds the intermediate below 2^41.
	q, c, r := p.Q%p.D, p.C%p.D, uint64(0)
	for m := uint64(1); m <= p.D; m++ {
		r = (q*r + c) % p.D
		if r == 0 {
			return m, nil
		}
	}
	return 0, fmt.Errorf("unit residue map failed to return within D steps")
}

// CheckBudget proves that the retained limb capacity covers all requested affine events.
func CheckBudget(p Parameters, m, h uint64, seed *big.Int) error {
	if p.Q < 2 || p.D < 2 || p.D > MaxModulus ||
		seed == nil || seed.Sign() < 0 || m == 0 || m > p.D || h > MaxBits {
		return fmt.Errorf("invalid nonnegative seed or block budget")
	}
	// At most m*h affine events occur. The sum is bounded by q^k*(seed+c+1).
	bound := uint64(seed.BitLen()) + uint64(bits.Len64(p.C)) + 16
	bound += m * h * uint64(bits.Len64(p.Q)+1)
	if bound > MaxBits {
		return fmt.Errorf("limb budget exceeded: %d > %d", bound, MaxBits)
	}
	return nil
}

// Block advances to the first division; failure is complete only for the verified period.
func (w *Workspace) Block(m uint64) bool {
	for k := uint64(0); k < m; k++ {
		w.Quotient.QuoRem(&w.State, &w.D, &w.Remainder)
		if w.Remainder.Sign() == 0 {
			w.State.Set(&w.Quotient)
			w.Ticks++
			w.Divisions++
			return true
		}
		// Separate destinations prevent multiplication aliases from allocating limbs.
		w.Product.Mul(&w.State, &w.Q)
		w.State.Add(&w.Product, &w.C)
		w.PowerProduct.Mul(&w.Multiplier, &w.Q)
		w.Multiplier.Set(&w.PowerProduct)
		w.Ticks++
	}
	return false
}

// Run checks period and capacity before computing a legal h-division prefix.
func (w *Workspace) Run(p Parameters, m, h uint64, seed *big.Int) (bool, error) {
	period, err := AccessPeriod(p)
	if err != nil {
		return false, err
	}
	if m != period {
		return false, fmt.Errorf("incorrect least positive period: %d != %d", m, period)
	}
	if err := CheckBudget(p, m, h, seed); err != nil {
		return false, err
	}
	// Snapshot before parameters change, even if the seed aliases a parameter buffer.
	w.State.Set(seed)
	w.Q.SetUint64(p.Q)
	w.C.SetUint64(p.C)
	w.D.SetUint64(p.D)
	w.Multiplier.SetUint64(1)
	w.Ticks, w.Divisions = 0, 0
	for j := uint64(0); j < h; j++ {
		if !w.Block(m) {
			return false, nil
		}
	}
	return true, nil
}

// RawClock independently executes division-first raw steps with no block search.
func (w *Workspace) RawClock(p Parameters, seed *big.Int, ticks uint64) (uint64, error) {
	if err := CheckBudget(p, 1, ticks, seed); err != nil {
		return 0, err
	}
	w.RawState.Set(seed)
	w.Q.SetUint64(p.Q)
	w.C.SetUint64(p.C)
	w.D.SetUint64(p.D)
	divisions := uint64(0)
	for j := uint64(0); j < ticks; j++ {
		w.RawQuotient.QuoRem(&w.RawState, &w.D, &w.RawRemainder)
		if w.RawRemainder.Sign() == 0 {
			w.RawState.Set(&w.RawQuotient)
			divisions++
		} else {
			w.RawProduct.Mul(&w.RawState, &w.Q)
			w.RawState.Add(&w.RawProduct, &w.C)
		}
	}
	return divisions, nil
}

// Power bounds enumeration and rejects overflow rather than wrapping a source modulus.
func Power(base, exponent, limit uint64) (uint64, error) {
	if base == 0 && exponent > 0 {
		return 0, nil
	}
	if limit < 1 {
		return 0, fmt.Errorf("enumeration budget excludes the zeroth power")
	}
	if base == 1 || exponent == 0 {
		return 1, nil
	}
	x := uint64(1)
	for j := uint64(0); j < exponent; j++ {
		if base != 0 && x > limit/base {
			return 0, fmt.Errorf("enumeration budget exceeded for %d^%d", base, exponent)
		}
		x *= base
	}
	return x, nil
}

// Census compares all legal prefixes and every high-digit lift with independent raw clocks.
func Census(p Parameters, h uint64, w, v *Workspace) (Record, error) {
	m, err := AccessPeriod(p)
	if err != nil {
		return Record{}, err
	}
	L, err := Power(p.D, h, MaxSeeds)
	if err != nil {
		return Record{}, err
	}
	// The extra source digit is part of the census, so budget the complete next level.
	if _, err := Power(p.D, h+1, MaxSeeds); err != nil {
		return Record{}, err
	}
	expected, err := Power(m, h, MaxSeeds)
	if err != nil {
		return Record{}, err
	}
	record := Record{
		Parameters: p, Period: m, Depth: h, Modulus: L,
		Expected: expected, StrictShortfall: m < p.D,
	}
	for r := uint64(0); r < L; r++ {
		w.Seed.SetUint64(r)
		ok, err := w.Run(p, m, h, &w.Seed)
		if err != nil {
			return Record{}, err
		}
		if !ok {
			// A complete block search reaches h divisions within m*h raw events if legal.
			count, err := w.RawClock(p, &w.Seed, m*h)
			if err != nil || count >= h {
				return Record{}, fmt.Errorf("false parent rejection for r=%d: %v", r, err)
			}
			record.RawClocksChecked++
			continue
		}
		record.Classes++
		rawCount, rawErr := w.RawClock(p, &w.Seed, w.Ticks)
		if rawErr != nil || w.Divisions != h || rawCount != h ||
			w.RawState.Cmp(&w.State) != 0 {
			return Record{}, fmt.Errorf("raw endpoint/count mismatch for r=%d", r)
		}
		record.RawClocksChecked++
		w.SavedEndpoint.Set(&w.State)
		w.SavedUnit.Set(&w.Multiplier)
		children := uint64(0)
		for t := uint64(0); t < p.D; t++ {
			// The child shares this exact parent's low h digits and its saved unit.
			v.Seed.SetUint64(r + L*t)
			prefix, err := v.Run(p, m, h, &v.Seed)
			if err != nil || !prefix {
				return Record{}, fmt.Errorf("lost parent prefix for r=%d t=%d: %v", r, t, err)
			}
			w.Product.SetUint64(t)
			w.PowerProduct.Mul(&w.SavedUnit, &w.Product)
			w.Product.Add(&w.SavedEndpoint, &w.PowerProduct)
			if v.State.Cmp(&w.Product) != 0 || v.Multiplier.Cmp(&w.SavedUnit) != 0 {
				return Record{}, fmt.Errorf("endpoint lifting mismatch for r=%d t=%d", r, t)
			}
			// Re-running h+1 also checks the guard on the lifted actual endpoint.
			child, err := v.Run(p, m, h+1, &v.Seed)
			if err != nil {
				return Record{}, err
			}
			if child {
				children++
				rawCount, rawErr := v.RawClock(p, &v.Seed, v.Ticks)
				if rawErr != nil || rawCount != h+1 || v.RawState.Cmp(&v.State) != 0 {
					return Record{}, fmt.Errorf("child raw-clock mismatch for r=%d t=%d", r, t)
				}
			} else {
				count, err := v.RawClock(p, &v.Seed, m*(h+1))
				if err != nil || count >= h+1 {
					return Record{}, fmt.Errorf("false child rejection for r=%d t=%d", r, t)
				}
			}
			record.RawClocksChecked++
			record.LiftsChecked++
		}
		if children != m {
			return Record{}, fmt.Errorf("child count mismatch: %d != %d", children, m)
		}
	}
	if record.Classes != expected {
		return Record{}, fmt.Errorf("class count mismatch: %d != %d", record.Classes, expected)
	}
	return record, nil
}

// Models lists a deterministic parameter family containing strict and critical cases.
func Models() []Parameters {
	models := make([]Parameters, 0, 224)
	for q := uint64(2); q <= 8; q++ {
		for d := uint64(2); d <= 9; d++ {
			if GCD(q, d) != 1 {
				continue
			}
			for c := uint64(0); c <= 3; c++ {
				models = append(models, Parameters{Q: q, C: c, D: d})
			}
		}
	}
	return models
}

// Execute assigns disjoint record chunks and one pair of working buffers to each goroutine.
func Execute(models []Parameters, depths uint64) ([]Record, error) {
	if depths > 16 || (depths != 0 && uint64(len(models)) > MaxSeeds/depths) {
		return nil, fmt.Errorf("record budget exceeded")
	}
	records := make([]Record, len(models)*int(depths))
	workers := min(runtime.GOMAXPROCS(0), 4, max(len(models), 1))
	errors := make([]error, workers)
	var group sync.WaitGroup
	for worker := 0; worker < workers; worker++ {
		start, end := len(models)*worker/workers, len(models)*(worker+1)/workers
		group.Add(1)
		go func(worker, start, end int) {
			defer group.Done()
			var w, v Workspace
			w.Initialize()
			v.Initialize()
			for i := start; i < end; i++ {
				for h := uint64(0); h < depths; h++ {
					row, err := Census(models[i], h, &w, &v)
					if err != nil {
						errors[worker] = err
						return
					}
					records[i*int(depths)+int(h)] = row
				}
			}
		}(worker, start, end)
	}
	group.Wait()
	for _, err := range errors {
		if err != nil {
			return nil, err
		}
	}
	return records, nil
}

// WriteReport publishes only the completed finite certificate, with stable record order.
func WriteReport(path string, rows []Record) error {
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	file, err := os.CreateTemp(filepath.Dir(path), ".ResidueCylinders-*.json")
	if err != nil {
		return err
	}
	name := file.Name()
	defer os.Remove(name)
	encoder := json.NewEncoder(file)
	encoder.SetIndent("", "  ")
	report := Report{
		Scope:   "Finite legal cylinders and full raw clocks; no infinite predicate is computed.",
		Records: rows,
	}
	if err := encoder.Encode(report); err != nil {
		file.Close()
		return err
	}
	if err := file.Close(); err != nil {
		return err
	}
	return os.Rename(name, path)
}

// main regenerates the finite evidence from the repository root without source execution.
func main() {
	models := Models()
	rows, err := Execute(models, 5)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if err := WriteReport("QCD.ResidueLeakage.001/other/ResidueCylinders.json", rows); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	var raw, lifts, classes, strict uint64
	for _, row := range rows {
		raw += row.RawClocksChecked
		lifts += row.LiftsChecked
		classes += row.Classes
		if row.StrictShortfall {
			strict++
		}
	}
	fmt.Printf("models=%d records=%d legal-classes=%d raw-clocks=%d lifts=%d strict-rows=%d\n",
		len(models), len(rows), classes, raw, lifts, strict)
}

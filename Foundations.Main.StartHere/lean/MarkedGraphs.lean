import Mathlib.CategoryTheory.Category.Basic

/-!
The category of labelled graphs and of two-stage marked transition systems.

Marks are graph morphisms, not automatically inclusions. Consequently these
objects impose no hidden determinism, target invariance, order or measure.
Arithmetic and dynamical recovery require their separate hypotheses.
-/

set_option autoImplicit false

universe u

namespace GeneralizedCollatz

/-- A labelled graph remembers edge identity as well as both endpoints and its label. -/
structure LabelledGraph where
  Vertex : Type u
  Edge : Type u
  Alphabet : Type u
  Source : Edge → Vertex
  Target : Edge → Vertex
  Label : Edge → Alphabet

/-- A graph morphism consists of three maps satisfying all incidence and label squares. -/
@[ext]
structure GraphMorphism (x y : LabelledGraph.{u}) where
  VertexMap : x.Vertex → y.Vertex
  EdgeMap : x.Edge → y.Edge
  AlphabetMap : x.Alphabet → y.Alphabet
  SourceSquare : ∀ e, VertexMap (x.Source e) = y.Source (EdgeMap e)
  TargetSquare : ∀ e, VertexMap (x.Target e) = y.Target (EdgeMap e)
  LabelSquare : ∀ e, AlphabetMap (x.Label e) = y.Label (EdgeMap e)

/-- The identity preserves the actual edges rather than replacing them by endpoint pairs. -/
def GraphIdentity (x : LabelledGraph.{u}) : GraphMorphism x x where
  VertexMap := id
  EdgeMap := id
  AlphabetMap := id
  SourceSquare := fun _ => rfl
  TargetSquare := fun _ => rfl
  LabelSquare := fun _ => rfl

/-- Execute graph morphisms in chronological order and compose every commuting square. -/
def GraphThen {x y z : LabelledGraph.{u}} (f : GraphMorphism x y)
    (g : GraphMorphism y z) : GraphMorphism x z where
  VertexMap := fun v => g.VertexMap (f.VertexMap v)
  EdgeMap := fun e => g.EdgeMap (f.EdgeMap e)
  AlphabetMap := fun a => g.AlphabetMap (f.AlphabetMap a)
  SourceSquare := fun e => by rw [f.SourceSquare, g.SourceSquare]
  TargetSquare := fun e => by rw [f.TargetSquare, g.TargetSquare]
  LabelSquare := fun e => by rw [f.LabelSquare, g.LabelSquare]

/-- Chronological graph composition is associative with the same three component maps. -/
theorem GraphThenAssociative {w x y z : LabelledGraph.{u}}
    (f : GraphMorphism w x) (g : GraphMorphism x y) (h : GraphMorphism y z) :
    GraphThen (GraphThen f g) h = GraphThen f (GraphThen g h) := by
  rfl

/-- Identity at the source is a left identity for all graph-morphism data. -/
theorem GraphIdentityThen {x y : LabelledGraph.{u}} (f : GraphMorphism x y) :
    GraphThen (GraphIdentity x) f = f := by
  rfl

/-- Identity at the target is a right identity for all graph-morphism data. -/
theorem GraphThenIdentity {x y : LabelledGraph.{u}} (f : GraphMorphism x y) :
    GraphThen f (GraphIdentity y) = f := by
  rfl

/-- Labelled graphs form an actual category, with no arithmetic restrictions silently attached. -/
instance GraphCategory : CategoryTheory.Category LabelledGraph.{u} where
  Hom := GraphMorphism
  id := GraphIdentity
  comp := GraphThen
  id_comp := GraphIdentityThen
  comp_id := GraphThenIdentity
  assoc := GraphThenAssociative

/-- A marked system is two composable graph maps, retaining the target and live graphs. -/
structure MarkedSystem where
  TargetGraph : LabelledGraph.{u}
  LiveGraph : LabelledGraph.{u}
  AmbientGraph : LabelledGraph.{u}
  TargetMark : GraphMorphism TargetGraph LiveGraph
  LiveMark : GraphMorphism LiveGraph AmbientGraph

/-- Marked morphisms preserve both marking maps as well as the three graph structures. -/
@[ext]
structure MarkedMorphism (x y : MarkedSystem.{u}) where
  TargetMap : GraphMorphism x.TargetGraph y.TargetGraph
  LiveMap : GraphMorphism x.LiveGraph y.LiveGraph
  AmbientMap : GraphMorphism x.AmbientGraph y.AmbientGraph
  TargetSquare : GraphThen x.TargetMark LiveMap = GraphThen TargetMap y.TargetMark
  LiveSquare : GraphThen x.LiveMark AmbientMap = GraphThen LiveMap y.LiveMark

/-- Identity on each marked stage satisfies both naturality squares. -/
def MarkedIdentity (x : MarkedSystem.{u}) : MarkedMorphism x x where
  TargetMap := GraphIdentity x.TargetGraph
  LiveMap := GraphIdentity x.LiveGraph
  AmbientMap := GraphIdentity x.AmbientGraph
  TargetSquare := rfl
  LiveSquare := rfl

/-- Componentwise marked composition retains one compatible pair of naturality squares. -/
def MarkedThen {x y z : MarkedSystem.{u}} (f : MarkedMorphism x y)
    (g : MarkedMorphism y z) : MarkedMorphism x z where
  TargetMap := GraphThen f.TargetMap g.TargetMap
  LiveMap := GraphThen f.LiveMap g.LiveMap
  AmbientMap := GraphThen f.AmbientMap g.AmbientMap
  TargetSquare := by
    calc
      GraphThen x.TargetMark (GraphThen f.LiveMap g.LiveMap) =
          GraphThen (GraphThen x.TargetMark f.LiveMap) g.LiveMap := by rfl
      _ = GraphThen (GraphThen f.TargetMap y.TargetMark) g.LiveMap := by
        rw [f.TargetSquare]
      _ = GraphThen f.TargetMap (GraphThen y.TargetMark g.LiveMap) := by rfl
      _ = GraphThen f.TargetMap (GraphThen g.TargetMap z.TargetMark) := by
        rw [g.TargetSquare]
      _ = GraphThen (GraphThen f.TargetMap g.TargetMap) z.TargetMark := by rfl
  LiveSquare := by
    calc
      GraphThen x.LiveMark (GraphThen f.AmbientMap g.AmbientMap) =
          GraphThen (GraphThen x.LiveMark f.AmbientMap) g.AmbientMap := by rfl
      _ = GraphThen (GraphThen f.LiveMap y.LiveMark) g.AmbientMap := by
        rw [f.LiveSquare]
      _ = GraphThen f.LiveMap (GraphThen y.LiveMark g.AmbientMap) := by rfl
      _ = GraphThen f.LiveMap (GraphThen g.LiveMap z.LiveMark) := by
        rw [g.LiveSquare]
      _ = GraphThen (GraphThen f.LiveMap g.LiveMap) z.LiveMark := by rfl

/-- Marked composition is associative at all three stages simultaneously. -/
theorem MarkedThenAssociative {w x y z : MarkedSystem.{u}}
    (f : MarkedMorphism w x) (g : MarkedMorphism x y) (h : MarkedMorphism y z) :
    MarkedThen (MarkedThen f g) h = MarkedThen f (MarkedThen g h) := by
  rfl

/-- The identity marked morphism is a left identity, including both marking squares. -/
theorem MarkedIdentityThen {x y : MarkedSystem.{u}} (f : MarkedMorphism x y) :
    MarkedThen (MarkedIdentity x) f = f := by
  rfl

/-- The identity marked morphism is a right identity without assuming injective marks. -/
theorem MarkedThenIdentity {x y : MarkedSystem.{u}} (f : MarkedMorphism x y) :
    MarkedThen f (MarkedIdentity y) = f := by
  rfl

/-- The two-stage systems and square-preserving morphisms form the declared category. -/
instance MarkedCategory : CategoryTheory.Category MarkedSystem.{u} where
  Hom := MarkedMorphism
  id := MarkedIdentity
  comp := MarkedThen
  id_comp := MarkedIdentityThen
  comp_id := MarkedThenIdentity
  assoc := MarkedThenAssociative

end GeneralizedCollatz

import Mathlib.Tactic

/- This section defines a product between subsets of X×X (for X some set) as well as an operation for taking inverses
  and the diagonal set as a neutral element. These will be needed in order to define coarse spaces.
-/

section set_operations
  def SetInv {X : Type*} (sub : Set (X × X)) : Set (X × X) := {⟨x_2, x_1⟩| (⟨x_1,x_2⟩∈ sub)}

  def SetDiag (X : Type*) : Set (X×X) := {⟨x,x⟩| x : X }

  def SetProd {X : Type*} (sub₁ : Set (X × X))  (sub₂ : Set (X × X)) : Set (X × X) := by
    rintro e
    have indicator : (X × X) → Prop := by
      rintro ⟨x₁, x₂⟩
      exact ∃ x₃: X, sub₁ ⟨x₁,x₃ ⟩ ∧ ∃ x₄, sub₂ ⟨x₄, x₂⟩
    exact indicator e

end set_operations

/- Now we define the class CoarseSpace analogously to a Topology. A coarse space consists of a set X and a coarse structure
ε ⊆ P(X×X) ("controlled sets"), where ε is closed under union, inverse and product as well as contains the diagonal.-/

class CoarseSpace (X : Type*) where
  IsControlled : Set (X × X) → Prop
  IsControlled_union : ∀ s t : Set (X × X), IsControlled s → IsControlled t → IsControlled (s ∪ t)
  IsControlled_diag : IsControlled (SetDiag X)
  IsControlled_inv : ∀ s : Set (X×X), IsControlled s → IsControlled (SetInv s)
  IsControlled_prod : ∀ s t : Set (X × X), IsControlled s → IsControlled t → IsControlled (SetProd s t)


/-We subsequently define coarse maps, which are needed in order to formulate the end goal. In order to
do that, one first needs proper and bornologous maps, and before that, we need a notion of boundedness.-/

section coarse_maps
  def IsBounded {X : Type*} [h: CoarseSpace X] (B : Set X) : Prop := @CoarseSpace.IsControlled X h {⟨a,b⟩|(a∈ B) (b∈ B)}
  def IsProper (X: Type*) [CoarseSpace X] (f: X→ X) : Prop := ∀ {B: Set X} (h: IsBounded B)
end coarse_maps

#check @CoarseSpace.IsControlled
/- In the following, we want to establish that every MetricSpace is coarse by showing that an arbitrary
MetricSpace is an instance of a CoarseSpace. This holds, if we define s ⊆ X×X controlled ↔ diam(s) := sup{d(x,y)| (x,y) ∈ S} < ∞.
We start with a section for auxiliary lemmas and definitions.
-/

section lemmas_defs_for_metric_coarse
-- Coordinate projections π₁, π₂ for elements x ∈ s ⊆ X×X

def π₁ {X : Type*} {s : Set (X×X)} (x:X× X) (h : x∈ s) : X := by
  let ⟨ x₁, x₂⟩ := x
  exact x₁

def π₂ {X : Type*} {s : Set (X×X)} (x:X× X) (h : x∈ s) : X := by
  let ⟨ x₁, x₂⟩ := x
  exact x₂

-- The dist_set of s ⊆ X×X is defined as {d(x,y)| (x,y) ∈ S} ⊆ ℝ

@[simp]
def dist_set {X : Type*} [MetricSpace X] (s : Set (X×X)) : Set ℝ := { dist (π₁ x h) (π₂ x h) | (x:X×X) (h:x∈ s) }

-- Lemma for showing that the dist_set of a nonempty set is nonempty and vice versa (very useful for later)

@[simp]
lemma nonempty_set_distset {X : Type*} [MetricSpace X] (s : Set (X×X)) : s.Nonempty ↔ (dist_set s).Nonempty := by
  constructor
  intro non_s
  have xh : ∃ x : X× X, x ∈ s := by
    exact non_s
  let ⟨x,h⟩:= xh
  unfold dist_set
  use dist (π₁ x h) (π₂ x h)
  tauto
  --
  intro non_ds
  have rh : ∃ r : ℝ, r ∈ (dist_set s) := by
    exact non_ds
  let ⟨r,h⟩:= rh
  simp at h
  let ⟨h₁,h₂,h₃,h₄⟩:= h
  use (⟨h₁,h₂⟩)


-- Definition for the conditions of the existence of diam(s)

def exists_diam {X : Type*} [MetricSpace X] (s : Set (X×X)) : Prop := (dist_set s).Nonempty ∧ BddAbove (dist_set s)

end lemmas_defs_for_metric_coarse

-- Proof that every nonempty MetricSpace is a CoarseSpace
-- we need the @ to make the implicit argument explicit
#check @Set.univ

class NonemptyMetricSpace (X: Type*) where
  Nonemptiness : (@Set.univ X).Nonempty
  Metricness : MetricSpace X

#check @NonemptyMetricSpace

instance {X : Type*} [NonemptyMetricSpace X] : MetricSpace X := by
  apply NonemptyMetricSpace.Metricness

instance {X : Type*} [NonemptyMetricSpace X] :  CoarseSpace X where
  IsControlled := exists_diam
  IsControlled_union := by
    -- show that the union is nonempty
    -- have {X: Type*} [MetricSpace X] (s t: Set (X×X)): (dist_set s).Nonempty ∧ (dist_set t).Nonempty → (dist_set (s∪t)).Nonempty := by
    rintro s t ⟨non_s, bd_s⟩ ⟨non_t, bd_t⟩
    constructor
    rw [<- nonempty_set_distset]
    rw [<- nonempty_set_distset] at non_s
    rw [<- nonempty_set_distset] at non_t
    have xh :∃ x : X×X, x∈ s := by
      exact non_s
    let ⟨x,h⟩:= xh
    use x
    tauto
    -- show that union is bounded above
    unfold BddAbove
    unfold upperBounds
    have xsh : ∃ x: ℝ, ∀{a: ℝ}, a ∈ dist_set s → a ≤ x := by
      exact bd_s
    have ytg : ∃ y: ℝ, ∀{a: ℝ}, a ∈ dist_set t → a ≤ y := by
      exact bd_t
    let ⟨x,h⟩:= xsh
    let ⟨y,g⟩:= ytg
    /- Idea for proceeding: take s₁=(s_11, s_12) ∈ s∪t (by non_s, non_t),
    set R:= max{x,y}, and show that R is upper bound -/
    let R :=  max x y
    -- should not need that (but for some reason, forall_upper_bd_st does not compile without it)
    have x_sth : ∃ x₁ : X×X, x₁∈ s∪ t := by
      rw[<- nonempty_set_distset] at non_s
      have x2h: ∃ x₂: X×X, x₂∈ s := by
        exact non_s
      let ⟨x₂,h₂⟩:= x2h
      use x₂
      tauto
    let ⟨x₁,h₁⟩:= x_sth
    let ⟨x_11, x_12⟩:= x₁
    --
    have forall_upper_bd_st : ∀x_11 x_12 : X, (x_3 : (x_11, x_12)∈ s ∪ t) → dist x_11 x_12 ≤ R := by
      intro x_11 x_12 h
      cases h
      have taut_1 : dist x_11 x_12 ∈ dist_set s := by
        simp
        tauto
      have upper_1 : dist x_11 x_12 ≤ x := by
        apply h
        exact taut_1
      have taut_11 : x ≤ R := by
        unfold R
        exact le_max_left x y
      trans x
      exact upper_1
      exact taut_11
      --
      have taut_2 : dist x_11 x_12 ∈ dist_set t := by
        simp
        tauto
      have upper_2 : dist x_11 x_12 ≤ y := by
        apply g
        exact taut_2
      have taut_22 : y ≤ R := by
        unfold R
        exact le_max_right x y
      trans y
      exact upper_2
      exact taut_22
    use R
    let ⟨x_st, h_st⟩ := x_sth
    have upper_bd_st : dist (π₁ x_st h_st) (π₂ x_st h_st) ≤ R := by
      apply forall_upper_bd_st
      tauto
    simp
    -- we want to show that the goal is equivalent to forall_upper_bd_st
    convert forall_upper_bd_st
    constructor
    intro h_3 x_31 x_32 h_x3
    apply forall_upper_bd_st
    exact h_x3
    --
    intro g_3 a_3 x_31 x_32 h_x3 f_x3
    have taut_3 : (x_31, x_32) ∈ s∪ t := by
      exact h_x3
    rw[<- f_x3]
    apply forall_upper_bd_st
    apply taut_3

  IsControlled_diag := by
    constructor
    unfold SetDiag
    rw[<- nonempty_set_distset]
    have x: X := by
      sorry
    use ⟨x,x⟩
    tauto
    sorry

  IsControlled_inv := by
    rintro s ⟨non_s, bd_s⟩
    constructor
    rw[<- nonempty_set_distset]
    rw[<- nonempty_set_distset] at non_s
    have x_hs : ∃ x: X×X, x ∈ s := by
      exact non_s
    let ⟨x,hs⟩ := x_hs
    let ⟨x_1, x_2⟩ := x
    use ⟨x_2,x_1⟩
    unfold SetInv
    simp
    exact hs
    --
    have distset_eq : dist_set s = dist_set (SetInv s) := by
      have h :  ∀ (x_1 x_2 : X), dist x_1 x_2 = dist x_2 x_1 := by
        exact dist_comm
      unfold dist_set
      unfold SetInv
      simp
      ext
      constructor
      intro ⟨a,b,h_ab,h_dist⟩
      simp
      use b
      use a
      use h_ab
      rw[h]
      exact h_dist
      --
      intro ⟨a,b,h_ab,h_dist⟩
      simp
      use b
      use a
      use h_ab
      rw[h]
      exact h_dist
    rw[<-distset_eq]
    exact bd_s

  IsControlled_prod := sorry

  #print NonemptyMetricSpace.Nonemptiness
  #check (Set.univ).Nonempty

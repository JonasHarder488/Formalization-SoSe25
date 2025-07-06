import Mathlib.Tactic

/- This section defines a product between subsets of X×X (for X some set) as well as an operation for taking inverses
  and the diagonal set as a neutral element. These will be needed in order to define coarse spaces.
-/

section set_operations
  def SetInv {X : Type*} (sub : Set (X × X)) : Set (X × X) := {⟨x_2, x_1⟩| (⟨x_1,x_2⟩∈ sub)}

  def SetDiag (X : Type*) : Set (X×X) := {⟨x,x⟩| x : X }

  def SetProd {X : Type*} (sub₁ : Set (X × X))  (sub₂ : Set (X × X)) : Set (X × X) := {⟨x_1, x_3⟩ | ∃ (x_2 : X), (⟨x_1, x_2⟩∈ sub₁)∧  (⟨x_2,x_3⟩ ∈ sub₂)}

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
  def IsProper {X: Type*} {Y: Type*} [CoarseSpace X] [CoarseSpace Y] (f: X→ Y) : Prop := ∀ {B: Set Y}, (IsBounded B) →  (IsBounded (Set.preimage f B))
  def IsBornological {X: Type*} {Y: Type*} [CoarseSpace X] [CoarseSpace Y] (f: X→ Y): Prop := ∀ {E : Set (X×X)}, (CoarseSpace.IsControlled E) → (CoarseSpace.IsControlled (Set.image (Prod.map f f) E))
  def IsCoarse {X : Type*} {Y: Type*}[CoarseSpace X] [CoarseSpace Y] (f: X→Y) : Prop := IsProper f ∧ IsBornological f

  /-Another notion needed is that of closeness of maps-/

  def IsClose {X: Type*} {Y:Type*} [CoarseSpace Y] (f: X→ Y) (g: X→ Y) : Prop := CoarseSpace.IsControlled ({⟨f x , g x⟩| x : X})

  /- Now, we can define coarse equvialence (our endgoal is to show that ℝ and ℤ are coarsely equivalent)-/

  def IsCoarselyEquivalent (X: Type*) (Y: Type*) [CoarseSpace X] [CoarseSpace Y] : Prop := ∃ (f : X→Y) (g: Y→ X), (IsCoarse f) ∧ (IsCoarse g) ∧ (IsClose (f ∘ g) id ) ∧ (IsClose (g∘ f) id)
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
lemma non_non_empty_is_empty {X:Type*} (s : Set X): ¬ s.Nonempty → s = ∅ := by
  have excluded_middle_s : s = ∅ ∨ s.Nonempty := by
    have almost_ex_mid: IsEmpty s ∨ Nonempty s := by
      exact @isEmpty_or_nonempty s
    unfold Nonempty at almost_ex_mid
    have taut_1 : IsEmpty s ↔ s = ∅ := by
      simp
    have taut_2 : s.Nonempty ↔ Nonempty s := by
      simp
      tauto
    rw [taut_1] at almost_ex_mid
    rw [<-taut_2] at almost_ex_mid
    exact almost_ex_mid
  convert excluded_middle_s
  tauto

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

lemma empty_set_distset {X : Type*} [MetricSpace X] (s: Set (X× X)) : s = ∅ → (dist_set s) = ∅ := by
  aesop

-- Definition for the conditions of the existence of diam(s)

-- Wrong one: def exists_diam {X : Type*} [MetricSpace X] (s : Set (X×X)) : Prop := (dist_set s).Nonempty ∧ BddAbove (dist_set s)
def ex_diam {X : Type*} [MetricSpace X] (s : Set (X×X)) : Prop :=  BddAbove (dist_set s)

end lemmas_defs_for_metric_coarse

instance {X : Type*} [MetricSpace X] :  CoarseSpace X where
  IsControlled := ex_diam
  IsControlled_union:= by
    rintro s t bd_s bd_t
    by_cases empt_union : (s∪t).Nonempty
    swap

    ----- case (s∪t) empty
    rw[nonempty_set_distset] at empt_union
    unfold ex_diam
    have s_t_empty : dist_set (s∪ t) = ∅ := by
      apply non_non_empty_is_empty
      exact empt_union
    rw[s_t_empty]
    exact bddAbove_empty

    ----- case (s∪t) not empty
    unfold ex_diam
    unfold BddAbove
    unfold upperBounds
    have ⟨sbound,h_sbound⟩ : ∃ y: ℝ, ∀{a: ℝ}, a ∈ dist_set s → a ≤ y := by
      exact bd_s
    have ⟨tbound,h_tbound⟩ : ∃ y: ℝ, ∀{a: ℝ}, a ∈ dist_set t → a ≤ y := by
      exact bd_t

    -- union_bound is maximum of bounds for s and t and we have to show that it is a bound for s ∪ t
    let union_bound :=  max sbound tbound
    -- take an arbitrary element in s∪t
    have ⟨x_union, h_x_union⟩ : ∃ x : X× X, x∈ s∪ t := by
      exact empt_union

    -- now we show that union_bound is indeed an upper bound for elements in the union (forall_upper_bd_st)
    have forall_upper_bd_st : ∀x_11 x_12 : X, ((x_11, x_12)∈ s ∪ t) → dist x_11 x_12 ≤ union_bound := by
      intro x_11 x_12 h_pair_in_union
      -- distinguish the cases (x_11, x_22) ∈ s or (x_11, x_22) ∈ t
      cases h_pair_in_union
      ----- case (x_11, x_22) ∈ s
      have taut_1 : dist x_11 x_12 ∈ dist_set s := by
        simp
        tauto
      have upper_1 : dist x_11 x_12 ≤ sbound := by
        apply h_sbound
        exact taut_1
      have taut_11 : sbound ≤ union_bound := by
        unfold union_bound
        exact le_max_left sbound tbound
      trans sbound
      exact upper_1
      exact taut_11
      ----- case (x_11, x_22) ∈ t (completely analogous)
      have taut_2 : dist x_11 x_12 ∈ dist_set t := by
        simp
        tauto
      have upper_2 : dist x_11 x_12 ≤ tbound := by
        apply h_tbound
        exact taut_2
      have taut_22 : tbound ≤ union_bound := by
        unfold union_bound
        exact le_max_right sbound tbound
      trans tbound
      exact upper_2
      exact taut_22
    -- now we need to convince lean that the upper theorem is sufficient --> for that we take the arbitrary element x_union from above
    use union_bound
    have upper_bd_st : dist (π₁ x_union h_x_union) (π₂ x_union h_x_union) ≤ union_bound := by
      apply forall_upper_bd_st
      tauto
    simp
    -- we want to show that the goal is equivalent to forall_upper_bd_st (that is for some mysterious)
    convert forall_upper_bd_st
    constructor
    ----- first direction
    -- (naming scheme collapsed)
    intro h_3 x_31 x_32 h_x3
    apply forall_upper_bd_st
    exact h_x3
    ----- second direction
    intro g_3 a_3 x_31 x_32 h_x3 f_x3
    have taut_3 : (x_31, x_32) ∈ s∪ t := by
      exact h_x3
    rw[<- f_x3]
    apply forall_upper_bd_st
    apply taut_3

  IsControlled_diag := by
    -- distinguish the cases that X is empty or not
    by_cases empt_X : (@Set.univ X).Nonempty
    ----- case X nonempty
    have ⟨x, h_x_X⟩ : ∃ x : X, x ∈ Set.univ := by
      exact empt_X
    unfold ex_diam
    have explicit_dist_set : ∀ a : ℝ, a∈ dist_set (SetDiag X) → a = 0  := by
      intro a h_dist_a
      unfold SetDiag at h_dist_a
      unfold dist_set at h_dist_a
      simp at h_dist_a
      have dist_zero : ∀ x : X, (h: ⟨x,x⟩ ∈ @Set.univ (X× X)) → dist (π₁ ⟨x,x⟩ h) (π₂ ⟨x,x⟩ h) = 0 := by
        have taut_proj : ∀ x : X, (h: ⟨x,x⟩ ∈ @Set.univ (X× X)) → π₁ ⟨x,x⟩ h = π₂ ⟨x,x⟩ h := by
          unfold π₁
          unfold π₂
          tauto
        simp[taut_proj]
      let ⟨x,h_dist_x⟩ := h_dist_a
      rw[<- h_dist_x]
      apply dist_zero
      tauto
    use 0
    unfold upperBounds
    simp
    intro a x_1 x_2 h_x h_dist
    have taut_dist_elem : a ∈ dist_set (SetDiag X) := by
      unfold dist_set
      use ⟨x_1, x_2⟩
      use h_x
    have almost_result : a = 0 := by
      apply explicit_dist_set
      exact taut_dist_elem
    apply le_of_eq
    exact almost_result

    ----- case X = ∅
    have X_is_empty : @Set.univ X = ∅ := by
      apply non_non_empty_is_empty at empt_X
      exact empt_X
    have diagX_is_empty : SetDiag X = ∅ := by
      unfold SetDiag
      have taut_no_elem : ¬ (∃ x : X, x ∈ @Set.univ X) := by
        simp
        rw[<-Set.univ_eq_empty_iff]
        exact X_is_empty
      ext x
      constructor
      intro h_x
      aesop
      aesop
    unfold ex_diam
    rw[diagX_is_empty]
    rw[empty_set_distset]
    swap
    tauto
    exact bddAbove_empty

  IsControlled_inv := by
    intro s bd_s
    -- it is sufficient to show that the dist_set is invariant under taking inverses
    have distset_eq : dist_set s = dist_set (SetInv s) := by
      unfold dist_set
      unfold SetInv
      simp
      -- show both inclusions with ext
      ext
      constructor
      ----- first inclusion
      intro ⟨x_1,x_2,h_x_s,h_dist⟩
      simp
      use x_2
      use x_1
      use h_x_s
      -- using symmetry of the metric
      rw[dist_comm]
      exact h_dist
      ----- second inclusion (completely analogous)
      intro ⟨x_1,x_2,h_x_s,h_dist⟩
      simp
      use x_2
      use x_1
      use h_x_s
      rw[dist_comm]
      exact h_dist
    unfold ex_diam
    rw[<- distset_eq]
    exact bd_s

  IsControlled_prod := by
    rintro s t bd_s bd_t
    unfold SetProd
    unfold ex_diam at bd_s bd_t
    unfold BddAbove at bd_s bd_t
    have ⟨upper_bd_s, hs⟩ := bd_s
    have ⟨upper_bd_t, ht⟩:= bd_t
    -- prod_dist shows that for all elements in s ∘ t the distance is bounded
    have prod_dist : ∀ x_1 x_4 : X, (∃ x_2 : X, (⟨x_1,x_2⟩∈ s)∧ (⟨x_2,x_4⟩∈ t))  → dist x_1 x_4 ≤ upper_bd_s + upper_bd_t := by
      intro x_1 x_4 ⟨x_2, ⟨h_1,h_2⟩⟩
      have taut_1 : dist x_1 x_2 ≤ upper_bd_s := by
        have taut_11 : ∀ y_1 y_2 : X, ⟨y_1,y_2⟩∈ s → dist y_1 y_2 ≤ upper_bd_s := by
          intro y_1 y_2 h_y
          unfold upperBounds at hs
          unfold dist_set at hs
          apply hs
          use ⟨y_1,y_2⟩
          use h_y
          tauto
        apply taut_11
        exact h_1
      have taut_2 : dist x_2 x_4 ≤ upper_bd_t := by
        have taut_21 : ∀ y_1 y_2 : X, ⟨y_1,y_2⟩∈ t → dist y_1 y_2 ≤ upper_bd_t := by
          intro y_1 y_2 h_y
          unfold upperBounds at ht
          unfold dist_set at ht
          apply ht
          use ⟨y_1,y_2⟩
          use h_y
          tauto
        apply taut_21
        exact h_2
      have triangle: dist x_1 x_4 ≤ dist x_1 x_2 + dist x_2 x_4  := by
        apply dist_triangle
      apply le_trans
      apply triangle
      linarith
    unfold ex_diam
    unfold dist_set
    use upper_bd_s + upper_bd_t
    unfold upperBounds
    simp
    intro a x_1 x_2 x_3 h_x h_dist
    have h_x_prod : ⟨x_1, x_2⟩ ∈ SetProd s t := by
      unfold SetProd
      simp
      use x_3
    have applied_prod_dist : dist (π₁ ⟨x_1, x_2⟩ h_x_prod) (π₂ ⟨x_1, x_2⟩ h_x_prod)  ≤ upper_bd_s + upper_bd_t := by
      apply prod_dist
      use x_3
      exact h_x
    rw[<-h_dist]
    exact applied_prod_dist

theorem main_thm : IsCoarselyEquivalent ℝ ℤ := by
  sorry

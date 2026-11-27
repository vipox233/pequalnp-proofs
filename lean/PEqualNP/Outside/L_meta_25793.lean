import Mathlib
import PEqualNP.Defs

-- The whole argument (wire sets, the trace counting and the bound 13 < size) is adapted from the
-- merged proof of L-meta-12400 by Astendann; only the final restatement is new.

namespace PEqualNP.Outside.L_meta_25793

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev S := Finset (Fin 8)

def gateSet (Sl : List S) (g : Gate) : S :=
  Finset.univ.filter (fun p => g.op.eval (g.inputs.map fun i => decide (p ∈ Sl.getD i ∅)) = true)

def setsFrom (gs : List Gate) (Sl : List S) : List S :=
  gs.foldl (fun Sl g => Sl ++ [gateSet Sl g]) Sl

def init : List S := List.ofFn (fun q : Fin 8 => ({q} : S))

theorem setsFrom_cons (g : Gate) (gs : List Gate) (Sl : List S) :
    setsFrom (g :: gs) Sl = setsFrom gs (Sl ++ [gateSet Sl g]) := rfl

theorem getD_map_mem (p : Fin 8) (Sl : List S) (i : ℕ) :
    (Sl.map (fun A => decide (p ∈ A))).getD i false = decide (p ∈ Sl.getD i ∅) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases Sl[i]? <;> simp

theorem wires_eq (p : Fin 8) (gs : List Gate) : ∀ (Sl : List S),
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (Sl.map (fun A => decide (p ∈ A))) = (setsFrom gs Sl).map (fun A => decide (p ∈ A)) := by
  induction gs with
  | nil => intro Sl; rfl
  | cons g gs ih =>
    intro Sl
    have e : g.op.eval (g.inputs.map fun i => (Sl.map (fun A => decide (p ∈ A))).getD i false)
        = decide (p ∈ gateSet Sl g) := by
      have e1 : (fun i => (Sl.map (fun A => decide (p ∈ A))).getD i false)
          = (fun i => decide (p ∈ Sl.getD i ∅)) := funext (getD_map_mem p Sl)
      rw [e1]
      simp [gateSet]
    rw [setsFrom_cons, ← ih]
    simp only [List.foldl_cons, List.map_append, List.map_cons, List.map_nil, e]

theorem getD_mem (Sl : List S) (i : ℕ) : Sl.getD i ∅ ∈ Sl ∨ Sl.getD i ∅ = ∅ := by
  by_cases h : i < Sl.length
  · left
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · right
    exact List.getD_eq_default _ _ (Nat.le_of_not_gt h)

theorem gateSet_cases (Sl : List S) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) :
    gateSet Sl g = Finset.univ ∨ ∃ A B, (A ∈ Sl ∨ A = ∅) ∧ (B ∈ Sl ∨ B = ∅) ∧
      (gateSet Sl g = A ∪ B ∨ gateSet Sl g = A ∩ B) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · rcases hop with rfl | rfl
    · left
      ext p
      simp [gateSet, GateOp.eval]
    · right
      exact ⟨∅, ∅, Or.inr rfl, Or.inr rfl, Or.inl (by ext p; simp [gateSet, GateOp.eval])⟩
  · right
    refine ⟨Sl.getD i ∅, Sl.getD i ∅, getD_mem Sl i, getD_mem Sl i, Or.inl ?_⟩
    rcases hop with rfl | rfl
    · ext p
      simp [gateSet, GateOp.eval]
    · ext p
      simp [gateSet, GateOp.eval]
  · right
    refine ⟨Sl.getD i ∅, Sl.getD j ∅, getD_mem Sl i, getD_mem Sl j, ?_⟩
    rcases hop with rfl | rfl
    · right
      ext p
      simp [gateSet, GateOp.eval]
    · left
      ext p
      simp [gateSet, GateOp.eval]
  · exfalso
    simp only [List.length_cons] at hlen
    omega

theorem mem_setsFrom (gs : List Gate) : ∀ (Sl : List S) (A : S), A ∈ Sl → A ∈ setsFrom gs Sl := by
  induction gs with
  | nil => intro Sl A h; exact h
  | cons g gs ih =>
    intro Sl A h
    rw [setsFrom_cons]
    exact ih _ A (List.mem_append_left _ h)

theorem setsFrom_split (gs : List Gate) : ∀ (Sl : List S),
    ∃ rest, setsFrom gs Sl = Sl ++ rest ∧ rest.length = gs.length := by
  induction gs with
  | nil => intro Sl; exact ⟨[], by simp [setsFrom], rfl⟩
  | cons g gs ih =>
    intro Sl
    obtain ⟨rest, h1, h2⟩ := ih (Sl ++ [gateSet Sl g])
    exact ⟨gateSet Sl g :: rest, by rw [setsFrom_cons, h1]; simp, by simp [h2]⟩

theorem ind (Q : S → Prop) (Wf : List S) (h0 : Q ∅) (h1 : Q Finset.univ)
    (hc : ∀ A B, (A ∈ Wf ∨ A = ∅) → (B ∈ Wf ∨ B = ∅) → Q A → Q B →
      (A ∪ B ∈ Wf → Q (A ∪ B)) ∧ (A ∩ B ∈ Wf → Q (A ∩ B)))
    (gs : List Gate) :
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∀ Sl : List S, (∀ A ∈ Sl, Q A) → (∀ A ∈ setsFrom gs Sl, A ∈ Wf) →
      ∀ A ∈ setsFrom gs Sl, Q A := by
  induction gs with
  | nil => intro _ Sl hS _ A hA; exact hS A hA
  | cons g gs ih =>
    intro hg Sl hS hW
    rw [setsFrom_cons] at hW ⊢
    have hgg := hg g (by simp)
    have inW : ∀ A, A ∈ Sl ∨ A = ∅ → A ∈ Wf ∨ A = ∅ := by
      intro A hA
      rcases hA with hA | hA
      · exact Or.inl (hW A (mem_setsFrom gs _ A (List.mem_append_left _ hA)))
      · exact Or.inr hA
    have qS : ∀ A, A ∈ Sl ∨ A = ∅ → Q A := by
      intro A hA
      rcases hA with hA | hA
      · exact hS A hA
      · rw [hA]; exact h0
    have gW : gateSet Sl g ∈ Wf :=
      hW _ (mem_setsFrom gs _ _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
    have qG : Q (gateSet Sl g) := by
      rcases gateSet_cases Sl g hgg.1 hgg.2 with h | ⟨A, B, hA, hB, h | h⟩
      · rw [h]; exact h1
      · rw [h] at gW ⊢
        exact (hc A B (inW A hA) (inW B hB) (qS A hA) (qS B hB)).1 gW
      · rw [h] at gW ⊢
        exact (hc A B (inW A hA) (inW B hB) (qS A hA) (qS B hB)).2 gW
    refine ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) (Sl ++ [gateSet Sl g]) ?_ hW
    intro A hA
    rcases List.mem_append.mp hA with hA | hA
    · exact hS A hA
    · rw [List.mem_singleton.mp hA]; exact qG

def Tr (W : Finset S) (X : S) : Finset S := W.image (fun A => A ∩ X)

def N (W : Finset S) (X : S) : Finset S := (Tr W X).filter (fun T => 2 ≤ T.card)

def Ef (W : Finset S) (V : S) (p : Fin 8) : Finset S :=
  (Tr W (insert p V)).filter
    (fun T => p ∉ T ∧ T.Nonempty ∧ insert p T ∈ Tr W (insert p V))

def R (W : Finset S) (V : S) (p : Fin 8) (T0 : S) (t : S) : Prop :=
  t = {p} ∨ (T0 ∈ Ef W V p ∧ insert p T0 ⊆ t) ∨ t = insert p V

theorem R_union (W : Finset S) (V : S) (p : Fin 8) (T0 : S) (hE : Ef W V p ⊆ {T0})
    (A B : S) (hB : B ∈ W) (hAB : A ∪ B ∈ W)
    (qB : p ∈ B → R W V p T0 (B ∩ insert p V))
    (rA : R W V p T0 (A ∩ insert p V)) :
    R W V p T0 ((A ∪ B) ∩ insert p V) := by
  rw [Finset.union_inter_distrib_right]
  have sub_a : A ∩ insert p V ⊆ insert p V := Finset.inter_subset_right
  have sub_b : B ∩ insert p V ⊆ insert p V := Finset.inter_subset_right
  rcases rA with h | h | h
  · by_cases hpB : p ∈ B
    · rcases qB hpB with h' | h' | h'
      · left
        rw [h, h']
        exact Finset.union_self _
      · right; left
        exact ⟨h'.1, h'.2.trans Finset.subset_union_right⟩
      · right; right
        rw [h']
        exact Finset.union_eq_right.mpr sub_a
    · by_cases hbe : B ∩ insert p V = ∅
      · left
        rw [h, hbe, Finset.union_empty]
      · right; left
        have pb : p ∉ B ∩ insert p V := fun hh => hpB (Finset.mem_inter.mp hh).1
        have key : insert p (B ∩ insert p V) = (A ∪ B) ∩ insert p V := by
          rw [Finset.union_inter_distrib_right, h, Finset.insert_eq]
        have bE : B ∩ insert p V ∈ Ef W V p := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨B, hB, rfl⟩, pb,
            Finset.nonempty_iff_ne_empty.mpr hbe, ?_⟩
          rw [key]
          exact Finset.mem_image.mpr ⟨A ∪ B, hAB, rfl⟩
        have e0 : B ∩ insert p V = T0 := Finset.mem_singleton.mp (hE bE)
        rw [e0] at bE
        refine ⟨bE, ?_⟩
        rw [h, e0, Finset.insert_eq]
  · right; left
    exact ⟨h.1, h.2.trans Finset.subset_union_left⟩
  · right; right
    rw [h]
    exact Finset.union_eq_left.mpr sub_b

theorem R_inter (W : Finset S) (V : S) (p : Fin 8) (T0 : S)
    (A B : S) (hpA : p ∈ A) (hpB : p ∈ B)
    (rA : R W V p T0 (A ∩ insert p V)) (rB : R W V p T0 (B ∩ insert p V)) :
    R W V p T0 ((A ∩ B) ∩ insert p V) := by
  rw [Finset.inter_inter_distrib_right]
  have pa : p ∈ A ∩ insert p V := Finset.mem_inter.mpr ⟨hpA, Finset.mem_insert_self p V⟩
  have pb : p ∈ B ∩ insert p V := Finset.mem_inter.mpr ⟨hpB, Finset.mem_insert_self p V⟩
  have sub_a : A ∩ insert p V ⊆ insert p V := Finset.inter_subset_right
  have sub_b : B ∩ insert p V ⊆ insert p V := Finset.inter_subset_right
  rcases rA with h | h | h
  · left
    rw [h]
    exact Finset.singleton_inter_of_mem pb
  · rcases rB with h' | h' | h'
    · left
      rw [h']
      exact Finset.inter_singleton_of_mem pa
    · right; left
      exact ⟨h.1, Finset.subset_inter h.2 h'.2⟩
    · right; left
      refine ⟨h.1, Finset.subset_inter h.2 ?_⟩
      rw [h']
      exact h.2.trans sub_a
  · rcases rB with h' | h' | h'
    · left
      rw [h']
      exact Finset.inter_singleton_of_mem pa
    · right; left
      refine ⟨h'.1, Finset.subset_inter ?_ h'.2⟩
      rw [h]
      exact h'.2.trans sub_b
    · right; right
      rw [h, h', Finset.inter_self]

theorem two_extras (W : Finset S)
    (IND : ∀ Q : S → Prop, Q ∅ → (∀ x, Q {x}) → Q Finset.univ →
      (∀ A ∈ W, ∀ B ∈ W, Q A → Q B → (A ∪ B ∈ W → Q (A ∪ B)) ∧ (A ∩ B ∈ W → Q (A ∩ B))) →
      ∀ A ∈ W, Q A)
    (V : S) (p : Fin 8) (hp : p ∉ V)
    (hsep : ∀ q ∈ V, ∃ F ∈ W, p ∈ F ∧ q ∉ F ∧ (F ∩ V).Nonempty) (hV : V.Nonempty) (T0 : S) :
    ¬ (Ef W V p ⊆ {T0}) := by
  intro hE
  have key : ∀ A ∈ W, p ∈ A → R W V p T0 (A ∩ insert p V) := by
    apply IND (fun A => p ∈ A → R W V p T0 (A ∩ insert p V))
    · intro h
      simp at h
    · intro x h
      have hx : p = x := Finset.mem_singleton.mp h
      subst hx
      exact Or.inl (Finset.singleton_inter_of_mem (Finset.mem_insert_self _ _))
    · intro _
      exact Or.inr (Or.inr (Finset.univ_inter _))
    · intro A hA B hB qA qB
      refine ⟨fun hAB hp' => ?_, fun _ hp' => ?_⟩
      · rcases Finset.mem_union.mp hp' with hpA | hpB
        · exact R_union W V p T0 hE A B hB hAB qB (qA hpA)
        · have h3 := R_union W V p T0 hE B A hA (by rw [Finset.union_comm B A]; exact hAB) qA (qB hpB)
          rw [Finset.union_comm B A] at h3
          exact h3
      · have h4 := Finset.mem_inter.mp hp'
        exact R_inter W V p T0 A B h4.1 h4.2 (qA h4.1) (qB h4.2)
  have hq : ∃ q, q ∈ V ∧ (T0 ∈ Ef W V p → q ∈ T0) := by
    by_cases hT : T0 ∈ Ef W V p
    · obtain ⟨hTr, hpT, ⟨q, hq⟩, _⟩ := Finset.mem_filter.mp hT
      obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hTr
      have hqX : q ∈ insert p V := (Finset.mem_inter.mp hq).2
      rcases Finset.mem_insert.mp hqX with rfl | hqV
      · exact absurd hq hpT
      · exact ⟨q, hqV, fun _ => hq⟩
    · obtain ⟨q, hqV⟩ := hV
      exact ⟨q, hqV, fun h => absurd h hT⟩
  obtain ⟨q, hqV, hqT⟩ := hq
  obtain ⟨F, hF, hpF, hqF, ⟨v, hv⟩⟩ := hsep q hqV
  have hv' := Finset.mem_inter.mp hv
  rcases key F hF hpF with h | h | h
  · have hvX : v ∈ F ∩ insert p V :=
      Finset.mem_inter.mpr ⟨hv'.1, Finset.mem_insert_of_mem hv'.2⟩
    rw [h] at hvX
    have hvp : v = p := Finset.mem_singleton.mp hvX
    rw [hvp] at hv'
    exact hp hv'.2
  · have hqI : q ∈ F ∩ insert p V := h.2 (Finset.mem_insert_of_mem (hqT h.1))
    exact hqF (Finset.mem_inter.mp hqI).1
  · have hqX : q ∈ F ∩ insert p V := by
      rw [h]
      exact Finset.mem_insert_of_mem hqV
    exact hqF (Finset.mem_inter.mp hqX).1

def phi (W : Finset S) (V : S) (p : Fin 8) (T : S) : S :=
  if T ∈ Tr W (insert p V) then T else insert p T

theorem phi_erase (W : Finset S) (V : S) (p : Fin 8) (T : S) (hT : p ∉ T) :
    (phi W V p T).erase p = T := by
  unfold phi
  split_ifs
  · exact Finset.erase_eq_self.mpr hT
  · exact Finset.erase_insert hT

theorem trace_cases (A V : S) (p : Fin 8) :
    A ∩ insert p V = A ∩ V ∨ A ∩ insert p V = insert p (A ∩ V) := by
  by_cases h : p ∈ A
  · right
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hx' | hx'⟩
      · exact Or.inl hx'
      · exact Or.inr ⟨hx, hx'⟩
    · rintro (hx | ⟨hx, hx'⟩)
      · rw [hx]; exact ⟨h, Or.inl rfl⟩
      · exact ⟨hx, Or.inr hx'⟩
  · left
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hx' | hx'⟩
      · rw [hx'] at hx; exact absurd hx h
      · exact ⟨hx, hx'⟩
    · rintro ⟨hx, hx'⟩
      exact ⟨hx, Or.inr hx'⟩

theorem card_step (W : Finset S) (V : S) (p : Fin 8) (hp : p ∉ V) :
    (N W V).card + (Ef W V p).card ≤ (N W (insert p V)).card := by
  have notin : ∀ T ∈ N W V, p ∉ T := by
    intro T hT hpT
    obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hT).1
    exact hp (Finset.mem_inter.mp hpT).2
  have phi_mem : ∀ T ∈ N W V, phi W V p T ∈ N W (insert p V) := by
    intro T hT
    have hc := (Finset.mem_filter.mp hT).2
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hT).1
    have hAX : A ∩ insert p V ∈ Tr W (insert p V) := Finset.mem_image.mpr ⟨A, hA, rfl⟩
    unfold phi
    split_ifs with h
    · exact Finset.mem_filter.mpr ⟨h, hc⟩
    · rcases trace_cases A V p with e | e
      · rw [e] at hAX
        exact absurd hAX h
      · rw [e] at hAX
        exact Finset.mem_filter.mpr ⟨hAX,
          hc.trans (Finset.card_le_card (Finset.subset_insert _ _))⟩
  have ins_mem : ∀ T ∈ Ef W V p, insert p T ∈ N W (insert p V) := by
    intro T hT
    obtain ⟨_, hpT, hne, hins⟩ := Finset.mem_filter.mp hT
    refine Finset.mem_filter.mpr ⟨hins, ?_⟩
    rw [Finset.card_insert_eq_ite]
    simp only [hpT, ite_false]
    have := Finset.card_pos.mpr hne
    omega
  have inj1 : Set.InjOn (phi W V p) (N W V : Set S) := by
    intro T1 h1 T2 h2 e
    rw [← phi_erase W V p T1 (notin T1 h1), ← phi_erase W V p T2 (notin T2 h2), e]
  have inj2 : Set.InjOn (fun T : S => insert p T) (Ef W V p : Set S) := by
    intro T1 h1 T2 h2 e
    have e' : insert p T1 = insert p T2 := e
    have n1 := (Finset.mem_filter.mp h1).2.1
    have n2 := (Finset.mem_filter.mp h2).2.1
    rw [← Finset.erase_insert n1, ← Finset.erase_insert n2, e']
  have disj : Disjoint ((N W V).image (phi W V p)) ((Ef W V p).image (fun T : S => insert p T)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨T', hT', e⟩ := Finset.mem_image.mp hx2
    have e' : insert p T' = phi W V p T := e
    have n' := (Finset.mem_filter.mp hT').2.1
    have hTT : T' = T := by
      rw [← Finset.erase_insert n', e', phi_erase W V p T (notin T hT)]
    have hTr : T ∈ Tr W (insert p V) := hTT ▸ (Finset.mem_filter.mp hT').1
    have hphi : phi W V p T = T := by
      unfold phi
      simp only [hTr, ite_true]
    rw [hphi, hTT] at e'
    have : p ∈ T := by
      rw [← e']
      exact Finset.mem_insert_self _ _
    exact notin T hT this
  calc (N W V).card + (Ef W V p).card
      = ((N W V).image (phi W V p)).card + ((Ef W V p).image (fun T : S => insert p T)).card := by
        rw [Finset.card_image_of_injOn inj1, Finset.card_image_of_injOn inj2]
    _ = ((N W V).image (phi W V p) ∪ (Ef W V p).image (fun T : S => insert p T)).card :=
        (Finset.card_union_of_disjoint disj).symm
    _ ≤ (N W (insert p V)).card := by
        apply Finset.card_le_card
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hx
          exact phi_mem T hT
        · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hx
          exact ins_mem T hT

theorem step (W : Finset S)
    (IND : ∀ Q : S → Prop, Q ∅ → (∀ x, Q {x}) → Q Finset.univ →
      (∀ A ∈ W, ∀ B ∈ W, Q A → Q B → (A ∪ B ∈ W → Q (A ∪ B)) ∧ (A ∩ B ∈ W → Q (A ∩ B))) →
      ∀ A ∈ W, Q A)
    (V : S) (p : Fin 8) (hp : p ∉ V)
    (hsep : ∀ q ∈ V, ∃ F ∈ W, p ∈ F ∧ q ∉ F ∧ (F ∩ V).Nonempty) (hV : V.Nonempty) :
    (N W V).card + 2 ≤ (N W (insert p V)).card := by
  have h2 : 2 ≤ (Ef W V p).card := by
    by_contra hlt
    have h1 : (Ef W V p).card ≤ 1 := by omega
    obtain ⟨T0, hT0⟩ := Finset.card_le_one_iff_subset_singleton.mp h1
    exact two_extras W IND V p hp hsep hV T0 hT0
  have h3 := card_step W V p hp
  omega

def Fc (b : Fin 3) (c : Bool) : S :=
  Finset.univ.filter (fun p : Fin 8 => Nat.testBit p.val b.val = c)

def V4 : S := {0, 3, 5, 6}

theorem Fc_ne : ∀ (b : Fin 3) (c : Bool), Fc b c ≠ ∅ := by decide +kernel

theorem base_card :
    (Finset.univ.image (fun bc : Fin 3 × Bool => Fc bc.1 bc.2 ∩ V4)).card = 6 := by decide +kernel

theorem base_two : ∀ bc : Fin 3 × Bool, 2 ≤ (Fc bc.1 bc.2 ∩ V4).card := by decide +kernel

theorem sep7 : ∀ q ∈ V4, ∃ bc : Fin 3 × Bool,
    (7 : Fin 8) ∈ Fc bc.1 bc.2 ∧ q ∉ Fc bc.1 bc.2 ∧ (Fc bc.1 bc.2 ∩ V4).Nonempty := by
  decide +kernel

theorem sep4 : ∀ q ∈ insert (7 : Fin 8) V4, ∃ bc : Fin 3 × Bool,
    (4 : Fin 8) ∈ Fc bc.1 bc.2 ∧ q ∉ Fc bc.1 bc.2 ∧
      (Fc bc.1 bc.2 ∩ insert (7 : Fin 8) V4).Nonempty := by
  decide +kernel

theorem sep2 : ∀ q ∈ insert (4 : Fin 8) (insert (7 : Fin 8) V4), ∃ bc : Fin 3 × Bool,
    (2 : Fin 8) ∈ Fc bc.1 bc.2 ∧ q ∉ Fc bc.1 bc.2 ∧
      (Fc bc.1 bc.2 ∩ insert (4 : Fin 8) (insert (7 : Fin 8) V4)).Nonempty := by
  decide +kernel

theorem sep1 : ∀ q ∈ insert (2 : Fin 8) (insert (4 : Fin 8) (insert (7 : Fin 8) V4)),
    ∃ bc : Fin 3 × Bool,
    (1 : Fin 8) ∈ Fc bc.1 bc.2 ∧ q ∉ Fc bc.1 bc.2 ∧
      (Fc bc.1 bc.2 ∩ insert (2 : Fin 8) (insert (4 : Fin 8) (insert (7 : Fin 8) V4))).Nonempty := by
  decide +kernel

theorem top : insert (1 : Fin 8) (insert (2 : Fin 8) (insert (4 : Fin 8) (insert (7 : Fin 8) V4)))
    = Finset.univ := by decide +kernel

theorem notin7 : (7 : Fin 8) ∉ V4 := by decide +kernel

theorem notin4 : (4 : Fin 8) ∉ insert (7 : Fin 8) V4 := by decide +kernel

theorem notin2 : (2 : Fin 8) ∉ insert (4 : Fin 8) (insert (7 : Fin 8) V4) := by decide +kernel

theorem notin1 : (1 : Fin 8) ∉ insert (2 : Fin 8) (insert (4 : Fin 8) (insert (7 : Fin 8) V4)) := by
  decide +kernel

theorem base6 (W : Finset S) (hF : ∀ b c, Fc b c ∈ W) : 6 ≤ (N W V4).card := by
  have hsub : (Finset.univ.image (fun bc : Fin 3 × Bool => Fc bc.1 bc.2 ∩ V4)) ⊆ N W V4 := by
    intro T hT
    obtain ⟨bc, _, rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨Fc bc.1 bc.2, hF bc.1 bc.2, rfl⟩, base_two bc⟩
  have h := Finset.card_le_card hsub
  rw [base_card] at h
  exact h

theorem sep (W : Finset S) (hF : ∀ b c, Fc b c ∈ W) (p : Fin 8) (V : S)
    (h : ∀ q ∈ V, ∃ bc : Fin 3 × Bool,
      p ∈ Fc bc.1 bc.2 ∧ q ∉ Fc bc.1 bc.2 ∧ (Fc bc.1 bc.2 ∩ V).Nonempty) :
    ∀ q ∈ V, ∃ F ∈ W, p ∈ F ∧ q ∉ F ∧ (F ∩ V).Nonempty := by
  intro q hq
  obtain ⟨bc, h1⟩ := h q hq
  exact ⟨Fc bc.1 bc.2, hF bc.1 bc.2, h1⟩

theorem bound (W : Finset S) (hF : ∀ b c, Fc b c ∈ W)
    (IND : ∀ Q : S → Prop, Q ∅ → (∀ x, Q {x}) → Q Finset.univ →
      (∀ A ∈ W, ∀ B ∈ W, Q A → Q B → (A ∪ B ∈ W → Q (A ∪ B)) ∧ (A ∩ B ∈ W → Q (A ∩ B))) →
      ∀ A ∈ W, Q A) :
    14 ≤ (N W Finset.univ).card := by
  have b6 := base6 W hF
  have s1 := step W IND V4 7 notin7 (sep W hF 7 V4 sep7) ⟨0, by decide +kernel⟩
  have s2 := step W IND (insert 7 V4) 4 notin4 (sep W hF 4 _ sep4) ⟨7, Finset.mem_insert_self _ _⟩
  have s3 := step W IND (insert 4 (insert 7 V4)) 2 notin2 (sep W hF 2 _ sep2)
    ⟨4, Finset.mem_insert_self _ _⟩
  have s4 := step W IND (insert 2 (insert 4 (insert 7 V4))) 1 notin1 (sep W hF 1 _ sep1)
    ⟨2, Finset.mem_insert_self _ _⟩
  rw [top] at s4
  omega

theorem main (C : Circuit) (hmono : Monotone2 C)
    (hw : ∀ b : Fin 3, ∀ c : Bool, ∃ w : ℕ, ∀ p : Fin 8,
      (C.wires (List.ofFn (fun q : Fin 8 => decide (q = p)))).getD w false
        = (Nat.testBit p.val b.val == c)) :
    14 ≤ C.gates.length := by
  have hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have h := hmono g hg
    exact ⟨by simpa using h.1, h.2⟩
  have hval : ∀ (p : Fin 8) (w : ℕ),
      (C.wires (List.ofFn (fun q : Fin 8 => decide (q = p)))).getD w false
        = decide (p ∈ (setsFrom C.gates init).getD w ∅) := by
    intro p w
    have hinit : List.ofFn (fun q : Fin 8 => decide (q = p))
        = init.map (fun A => decide (p ∈ A)) := by
      unfold init
      rw [List.map_ofFn]
      congr 1
      funext q
      simp [eq_comm]
    unfold Circuit.wires
    rw [hinit, wires_eq, getD_map_mem]
  obtain ⟨rest, hsplit, hlen⟩ := setsFrom_split C.gates init
  have hFW : ∀ b c, Fc b c ∈ (setsFrom C.gates init).toFinset ∪ {∅} := by
    intro b c
    obtain ⟨w, hw'⟩ := hw b c
    have hset : (setsFrom C.gates init).getD w ∅ = Fc b c := by
      ext p
      have h := hw' p
      rw [hval] at h
      simp only [Fc, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hp
        have h2 : (Nat.testBit p.val b.val == c) = true := by
          rw [← h]
          exact decide_eq_true hp
        exact beq_iff_eq.mp h2
      · intro hp
        have h2 : decide (p ∈ (setsFrom C.gates init).getD w ∅) = true := by
          rw [h]
          exact beq_iff_eq.mpr hp
        exact of_decide_eq_true h2
    rcases getD_mem (setsFrom C.gates init) w with h | h
    · rw [hset] at h
      exact Finset.mem_union_left _ (List.mem_toFinset.mpr h)
    · rw [hset] at h
      exact absurd h (Fc_ne b c)
  have memW : ∀ A : S, (A ∈ setsFrom C.gates init ∨ A = ∅) →
      A ∈ (setsFrom C.gates init).toFinset ∪ {∅} := by
    intro A hA
    rcases hA with hA | hA
    · exact Finset.mem_union_left _ (List.mem_toFinset.mpr hA)
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hA)
  have IND : ∀ Q : S → Prop, Q ∅ → (∀ x, Q {x}) → Q Finset.univ →
      (∀ A ∈ (setsFrom C.gates init).toFinset ∪ {∅}, ∀ B ∈ (setsFrom C.gates init).toFinset ∪ {∅},
        Q A → Q B →
        (A ∪ B ∈ (setsFrom C.gates init).toFinset ∪ {∅} → Q (A ∪ B)) ∧
        (A ∩ B ∈ (setsFrom C.gates init).toFinset ∪ {∅} → Q (A ∩ B))) →
      ∀ A ∈ (setsFrom C.gates init).toFinset ∪ {∅}, Q A := by
    intro Q h0 hs h1 hc A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · refine ind Q (setsFrom C.gates init) h0 h1 ?_ C.gates hgates init ?_ (fun A hA => hA) A
        (List.mem_toFinset.mp hA)
      · intro A B hA' hB' qA qB
        have h5 := hc A (memW A hA') B (memW B hB') qA qB
        exact ⟨fun h => h5.1 (memW _ (Or.inl h)), fun h => h5.2 (memW _ (Or.inl h))⟩
      · intro A hA'
        unfold init at hA'
        obtain ⟨q, rfl⟩ := (List.mem_ofFn' _ _).mp hA'
        exact hs q
    · rw [Finset.mem_singleton.mp hA]
      exact h0
  have h14 := bound _ hFW IND
  have hsub : N ((setsFrom C.gates init).toFinset ∪ {∅}) Finset.univ ⊆ rest.toFinset := by
    intro T hT
    obtain ⟨hTr, hc⟩ := Finset.mem_filter.mp hT
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hTr
    rw [Finset.inter_univ] at hc ⊢
    rcases Finset.mem_union.mp hA with hA | hA
    · have hA' := List.mem_toFinset.mp hA
      rw [hsplit] at hA'
      rcases List.mem_append.mp hA' with hA' | hA'
      · unfold init at hA'
        obtain ⟨q, rfl⟩ := (List.mem_ofFn' _ _).mp hA'
        simp at hc
      · exact List.mem_toFinset.mpr hA'
    · rw [Finset.mem_singleton.mp hA] at hc
      simp at hc
  have h6 := Finset.card_le_card hsub
  have h7 := List.toFinset_card_le rest
  omega

end PEqualNP.Outside.L_meta_25793

theorem PEqualNP.Outside.L_meta_25793 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ v : Fin 3, (∃ w : ℕ, ∀ p : Fin 8, (C.wires (List.ofFn (fun q : Fin 8 => decide (q = p)))).getD w false = Nat.testBit p.val v.val) ∧ (∃ w : ℕ, ∀ p : Fin 8, (C.wires (List.ofFn (fun q : Fin 8 => decide (q = p)))).getD w false = !(Nat.testBit p.val v.val))) → 14 ≤ C.size := by
  intro C hmono hw
  have hw' : ∀ b : Fin 3, ∀ c : Bool, ∃ w : ℕ, ∀ p : Fin 8,
      (C.wires (List.ofFn (fun q : Fin 8 => decide (q = p)))).getD w false =
        (Nat.testBit p.val b.val == c) := by
    intro b c
    cases c
    · obtain ⟨w, hw2⟩ := (hw b).2
      exact ⟨w, fun p => by rw [hw2 p]; cases Nat.testBit p.val b.val <;> rfl⟩
    · obtain ⟨w, hw2⟩ := (hw b).1
      exact ⟨w, fun p => by rw [hw2 p]; cases Nat.testBit p.val b.val <;> rfl⟩
  have h := PEqualNP.Outside.L_meta_25793.main C hmono hw'
  have hs : C.size = C.gates.length := rfl
  omega

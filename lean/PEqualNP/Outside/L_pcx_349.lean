import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_349_aux

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem functional_eq_sum {m : ℕ} (φ : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (R : Finset (Fin m)) (v : Fin m → ZMod 2) (hv : ∀ i, i ∉ R → v i = 0) :
    φ v = ∑ i ∈ R.filter (fun i => φ (fun j => if i = j then 1 else 0) = 1), v i := by
  rw [LinearMap.pi_apply_eq_sum_univ φ v, Finset.sum_filter]
  have hsub : ∑ i ∈ R, v i • φ (fun j => if i = j then 1 else 0)
      = ∑ i, v i • φ (fun j => if i = j then 1 else 0) :=
    Finset.sum_subset (Finset.subset_univ R) (fun i _ hi => by rw [hv i hi, zero_smul])
  rw [← hsub]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rcases zmod2_cases (φ fun j => if i = j then 1 else 0) with h | h <;> rw [h] <;> simp

theorem exists_oddDep {n m : ℕ} (row : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (rhs : Fin m → ZMod 2) (R : Finset (Fin m))
    (h : ∀ x : Fin n → ZMod 2, ∃ i ∈ R, row i x ≠ rhs i) :
    ∃ P : Finset (Fin m), P ⊆ R ∧ P.sum row = 0 ∧ P.sum rhs = 1 := by
  classical
  let A : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
    LinearMap.pi (fun i => if i ∈ R then row i else 0)
  let b : Fin m → ZMod 2 := fun i => if i ∈ R then rhs i else 0
  have hb : b ∉ LinearMap.range A := by
    rintro ⟨x, hx⟩
    obtain ⟨i, hi, hne⟩ := h x
    apply hne
    have := congrFun hx i
    simpa [A, b, hi] using this
  obtain ⟨φ, hφb, hφ⟩ := Submodule.exists_le_ker_of_notMem hb
  refine ⟨R.filter (fun i => φ (fun j => if i = j then 1 else 0) = 1),
    Finset.filter_subset _ _, ?_, ?_⟩
  · refine LinearMap.ext (fun x => ?_)
    have hx : φ (A x) = 0 := LinearMap.mem_ker.mp (hφ (LinearMap.mem_range_self A x))
    rw [functional_eq_sum φ R (A x) (fun i hi => by simp [A, hi])] at hx
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    refine Eq.trans (Finset.sum_congr rfl (fun i hi => ?_)) hx
    have hiR : i ∈ R := (Finset.mem_filter.mp hi).1
    simp [A, hiR]
  · have hb1 : φ b = 1 := (zmod2_cases (φ b)).resolve_left hφb
    rw [functional_eq_sum φ R b (fun i hi => by simp [b, hi])] at hb1
    refine Eq.trans (Finset.sum_congr rfl (fun i hi => ?_)) hb1
    have hiR : i ∈ R := (Finset.mem_filter.mp hi).1
    simp [b, hiR]

theorem fiber_card {k t : ℕ} (A : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2))
    (u0 : Fin k → ZMod 2) :
    2 ^ Module.finrank (ZMod 2) (LinearMap.range A) *
      (Finset.univ.filter (fun u : Fin k → ZMod 2 => A u = A u0)).card
      = Fintype.card (Fin k → ZMod 2) := by
  classical
  have hker : (Finset.univ.filter (fun u : Fin k → ZMod 2 => A u = A u0)).card
      = Fintype.card (LinearMap.ker A) := by
    rw [← Fintype.card_subtype]
    refine Fintype.card_congr
      ⟨fun u => ⟨u.1 - u0, by simp [LinearMap.mem_ker, map_sub, u.2]⟩,
        fun v => ⟨v.1 + u0, by simp [map_add, LinearMap.mem_ker.mp v.2]⟩,
        fun u => Subtype.ext (by simp), fun v => Subtype.ext (by simp)⟩
  rw [hker, Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker A),
    Module.card_eq_pow_finrank (K := ZMod 2) (V := Fin k → ZMod 2), ZMod.card, ← pow_add,
    LinearMap.finrank_range_add_finrank_ker]

theorem double_count {k t m : ℕ} (M : Fin m → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2))
    (B : Finset (Fin m × (Fin t → ZMod 2))) :
    ∑ u : Fin k → ZMod 2, ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i, M i u) ∈ B),
        2 ^ Module.finrank (ZMod 2) (LinearMap.range (M i))
      = ∑ b ∈ B, (if ∃ u : Fin k → ZMod 2, b.2 = M b.1 u then
          Fintype.card (Fin k → ZMod 2) else 0) := by
  classical
  have step : ∀ u : Fin k → ZMod 2,
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i, M i u) ∈ B),
          (2 : ℕ) ^ Module.finrank (ZMod 2) (LinearMap.range (M i))
        = ∑ b ∈ B, if b.2 = M b.1 u then
            (2 : ℕ) ^ Module.finrank (ZMod 2) (LinearMap.range (M b.1)) else 0 := by
    intro u
    rw [← Finset.sum_filter]
    refine Finset.sum_nbij' (fun i => (i, M i u)) (fun b => b.1) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2, rfl⟩
    · intro b hb
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← (Finset.mem_filter.mp hb).2]
      exact (Finset.mem_filter.mp hb).1
    · intro i _
      rfl
    · intro b hb
      exact Prod.ext rfl (Finset.mem_filter.mp hb).2.symm
    · intro i _
      rfl
  rw [Finset.sum_congr rfl (fun u _ => step u), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  by_cases hex : ∃ u : Fin k → ZMod 2, b.2 = M b.1 u
  · obtain ⟨u0, h0⟩ := hex
    rw [ite_eq_left ⟨u0, h0⟩, mul_comm]
    have hf : Finset.univ.filter (fun u : Fin k → ZMod 2 => b.2 = M b.1 u)
        = Finset.univ.filter (fun u : Fin k → ZMod 2 => M b.1 u = M b.1 u0) := by
      refine Finset.filter_congr (fun u _ => ?_)
      rw [h0]
      exact eq_comm
    rw [hf]
    exact fiber_card (M b.1) u0
  · rw [ite_eq_right hex]
    have hf : Finset.univ.filter (fun u : Fin k → ZMod 2 => b.2 = M b.1 u) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun u _ hu => hex ⟨u, hu⟩)
    rw [hf]
    simp

theorem sup_invariant {k : ℕ} {α ι : Type} (F : (Fin k → ZMod 2) → α) (I : Finset ι)
    (K : ι → Submodule (ZMod 2) (Fin k → ZMod 2))
    (h : ∀ i ∈ I, ∀ v ∈ K i, ∀ u, F (u + v) = F u) :
    ∀ v ∈ I.sup K, ∀ u, F (u + v) = F u := by
  let S : Submodule (ZMod 2) (Fin k → ZMod 2) :=
    { carrier := {v | ∀ u, F (u + v) = F u}, add_mem' := by
        intro a b ha hb
        have ha' : ∀ u, F (u + a) = F u := ha
        have hb' : ∀ u, F (u + b) = F u := hb
        change ∀ u, F (u + (a + b)) = F u
        intro u
        rw [← add_assoc, hb' (u + a), ha' u]
      , zero_mem' := by
        change ∀ u, F (u + 0) = F u
        intro u
        rw [add_zero]
      , smul_mem' := by
        intro c v hv
        have hv' : ∀ u, F (u + v) = F u := hv
        change ∀ u, F (u + c • v) = F u
        intro u
        rcases zmod2_cases c with rfl | rfl
        · rw [zero_smul, add_zero]
        · rw [one_smul]
          exact hv' u }
  have hle : I.sup K ≤ S := Finset.sup_le (fun i hi v hv => h i hi v hv)
  exact fun v hv => hle hv


def Shape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧ (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

abbrev Vec (n : ℕ) : Type := Fin n → ZMod 2

def Queries (V : Type) [AddCommGroup V] [Module (ZMod 2) V] : Set (V → Bool) :=
  {f | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}

def Cert {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
    (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) : Prop :=
  Shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
    (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → ok x (out p)

theorem exists_leaf {V : Type} (N J : Finset (List Bool)) (q : List Bool → V → Bool)
    (hs : Shape N J) (z : V) :
    ∃ p ∈ N \ J, ∀ j : Fin p.length, q (p.take j.val) z = p.get j := by
  classical
  obtain ⟨h0, hJN, -, hch⟩ := hs
  let C := N.filter (fun p => ∀ j : Fin p.length, q (p.take j.val) z = p.get j)
  have hC : C.Nonempty := ⟨[], by simp [C, h0]⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image C List.length hC
  have hp2 := Finset.mem_filter.mp hp
  refine ⟨p, Finset.mem_sdiff.mpr ⟨hp2.1, fun hpJ => ?_⟩, hp2.2⟩
  have hmem : p ++ [q p z] ∈ N := by
    cases hb : q p z
    · exact (hch p hpJ).1
    · exact (hch p hpJ).2
  have hc : p ++ [q p z] ∈ C := by
    refine Finset.mem_filter.mpr ⟨hmem, fun j => ?_⟩
    have hj : j.val < p.length + 1 := by simpa using j.isLt
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · rw [List.take_append_of_le_length (le_of_lt h)]
      have h1 := hp2.2 ⟨j.val, h⟩
      rw [List.get_eq_getElem] at h1 ⊢
      rw [List.getElem_append_left h]
      exact h1
    · have h2 : (p ++ [q p z]).take j.val = p := by rw [h]; simp
      rw [h2, List.get_eq_getElem]
      simp [h]
  have h3 := hmax _ hc
  simp at h3

section Main
variable {n k t m : ℕ} (row : Fin m → Vec n →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
  (M : Fin m → Vec k →ₗ[ZMod 2] Vec t)

def OddDep (P : Finset (Fin m)) : Prop := P.sum row = 0 ∧ P.sum rhs = 1

noncomputable def wt (i : Fin m) : ℕ := 2 ^ Module.finrank (ZMod 2) (LinearMap.range (M i))

def Answer (z : Vec n × Vec k) (a : Fin m × Vec t) : Prop :=
  row a.1 z.1 ≠ rhs a.1 ∧ a.2 = M a.1 z.2

def Rset (B : Finset (Fin m × Vec t)) (u : Vec k) : Finset (Fin m) :=
  Finset.univ.filter (fun i => (i, M i u) ∈ B)

def Realizable (W : ℕ) (B : Finset (Fin m × Vec t)) : Prop :=
  ∃ (N J : Finset (List Bool)) (q : List Bool → (Vec n × Vec k) → Bool)
    (out : List Bool → Fin m × Vec t),
    Cert (Queries (Vec n × Vec k)) (Answer row rhs M) N J q out ∧
    (N \ J).card = W ∧ (N \ J).image out = B

theorem wt_pos (i : Fin m) : 0 < wt M i := by unfold wt; positivity

theorem cert_oddDep (N J : Finset (List Bool)) (q : List Bool → (Vec n × Vec k) → Bool)
    (out : List Bool → Fin m × Vec t)
    (hc : Cert (Queries (Vec n × Vec k)) (Answer row rhs M) N J q out) (u : Vec k) :
    ∃ P : Finset (Fin m), P ⊆ Rset M ((N \ J).image out) u ∧ OddDep row rhs P := by
  refine exists_oddDep row rhs (Rset M ((N \ J).image out) u) (fun x => ?_)
  obtain ⟨p, hp, hcons⟩ := exists_leaf N J q hc.1 (x, u)
  have ha := hc.2.2 p hp (x, u) hcons
  refine ⟨(out p).1, ?_, ha.1⟩
  simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : ((out p).1, M (out p).1 u) = out p := Prod.ext rfl ha.2.symm
  rw [h1]; exact Finset.mem_image_of_mem out hp

theorem card_lower (W : ℕ) (B : Finset (Fin m × Vec t))
    (h : ∀ u, W ≤ ∑ i ∈ Rset M B u, wt M i) : W ≤ B.card := by
  have hdc : ∑ u : Vec k, ∑ i ∈ Rset M B u, wt M i = ∑ b ∈ B,
      (if ∃ u : Vec k, b.2 = M b.1 u then Fintype.card (Vec k) else 0) := double_count M B
  have h1 : ∑ _u : Vec k, W ≤ ∑ u : Vec k, ∑ i ∈ Rset M B u, wt M i :=
    Finset.sum_le_sum (fun u _ => h u)
  have h2 : ∑ b ∈ B, (if ∃ u : Vec k, b.2 = M b.1 u then Fintype.card (Vec k) else 0)
      ≤ ∑ _b ∈ B, Fintype.card (Vec k) :=
    Finset.sum_le_sum (fun b _ => by split_ifs <;> simp)
  have hsumW : ∑ _u : Vec k, W = Fintype.card (Vec k) * W := by simp [Finset.card_univ]
  have hsumc : ∑ _b ∈ B, Fintype.card (Vec k) = Fintype.card (Vec k) * B.card := by
    simp [mul_comm]
  have hpos : 0 < Fintype.card (Vec k) := Fintype.card_pos
  have h3 : Fintype.card (Vec k) * W ≤ Fintype.card (Vec k) * B.card := by
    rw [← hsumW, ← hsumc]; exact le_trans h1 (hdc ▸ h2)
  exact Nat.le_of_mul_le_mul_left h3 hpos

variable (S T : Finset (Fin m))

def hidden : Submodule (ZMod 2) (Vec k) :=
  ((S \ T) ∪ (T \ S)).sup (fun i => LinearMap.ker (M i))

def cg (g : (Vec k ⧸ hidden M S T) → Bool) (u : Vec k) : Finset (Fin m) :=
  if g (Submodule.Quotient.mk u) then S else T

open Classical in
noncomputable def Bg (g : (Vec k ⧸ hidden M S T) → Bool) : Finset (Fin m × Vec t) :=
  Finset.univ.filter (fun b => ∃ u : Vec k, b.2 = M b.1 u ∧ b.1 ∈ cg M S T g u)

def Best2 : Prop :=
  ∀ P, (OddDep row rhs P ∧ ∀ T2, OddDep row rhs T2 → P.sum (wt M) ≤ T2.sum (wt M)) ↔
    P = S ∨ P = T

theorem best_S (hb : Best2 row rhs M S T) :
    OddDep row rhs S ∧ ∀ T2, OddDep row rhs T2 → ∑ i ∈ S, wt M i ≤ ∑ i ∈ T2, wt M i :=
  (hb S).2 (Or.inl rfl)

theorem best_T (hb : Best2 row rhs M S T) :
    OddDep row rhs T ∧ ∀ T2, OddDep row rhs T2 → ∑ i ∈ T, wt M i ≤ ∑ i ∈ T2, wt M i :=
  (hb T).2 (Or.inr rfl)

theorem wS_eq_wT (hb : Best2 row rhs M S T) : ∑ i ∈ S, wt M i = ∑ i ∈ T, wt M i :=
  le_antisymm ((best_S row rhs M S T hb).2 T (best_T row rhs M S T hb).1)
    ((best_T row rhs M S T hb).2 S (best_S row rhs M S T hb).1)

theorem sdiff_nonempty_of_wt {A B : Finset (Fin m)} (hne : A ≠ B)
    (hw : ∑ i ∈ A, wt M i = ∑ i ∈ B, wt M i) : (A \ B).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h
  have hss : A ⊂ B := lt_of_le_of_ne h hne
  obtain ⟨i, hiB, hiA⟩ := Finset.exists_of_ssubset hss
  have h1 : ∑ j ∈ A, wt M j < ∑ j ∈ B, wt M j :=
    Finset.sum_lt_sum_of_subset h hiB hiA (wt_pos M i) (fun j _ _ => Nat.zero_le _)
  omega

theorem classify (hb : Best2 row rhs M S T) (B : Finset (Fin m × Vec t))
    (hB : Realizable row rhs M (∑ i ∈ S, wt M i) B) :
    (∀ u, Rset M B u = S ∨ Rset M B u = T) ∧ ∀ b ∈ B, ∃ u : Vec k, b.2 = M b.1 u := by
  classical
  obtain ⟨N, J, q, out, hc, hcard, him⟩ := hB
  have hBc : B.card ≤ ∑ i ∈ S, wt M i := by
    rw [← him, ← hcard]; exact Finset.card_image_le
  have hP : ∀ u, ∃ P : Finset (Fin m), P ⊆ Rset M B u ∧ OddDep row rhs P := by
    intro u
    have h0 := cert_oddDep row rhs M N J q out hc u
    rwa [him] at h0
  have hge : ∀ u, ∑ i ∈ S, wt M i ≤ ∑ i ∈ Rset M B u, wt M i := by
    intro u
    obtain ⟨P, hPs, hPo⟩ := hP u
    exact le_trans ((best_S row rhs M S T hb).2 P hPo) (Finset.sum_le_sum_of_subset hPs)
  have hdc : ∑ u : Vec k, ∑ i ∈ Rset M B u, wt M i = ∑ b ∈ B,
      (if ∃ u : Vec k, b.2 = M b.1 u then Fintype.card (Vec k) else 0) := double_count M B
  have hle2 : ∀ b ∈ B, (if ∃ u : Vec k, b.2 = M b.1 u then Fintype.card (Vec k) else 0)
      ≤ Fintype.card (Vec k) := by
    intro b _; split_ifs <;> simp
  have hsumc : ∑ _b ∈ B, Fintype.card (Vec k) = Fintype.card (Vec k) * B.card := by
    simp [mul_comm]
  have hsumW : ∑ _u : Vec k, ∑ i ∈ S, wt M i = Fintype.card (Vec k) * ∑ i ∈ S, wt M i := by
    simp [Finset.card_univ]
  have h1 : ∑ _u : Vec k, ∑ i ∈ S, wt M i ≤ ∑ u : Vec k, ∑ i ∈ Rset M B u, wt M i :=
    Finset.sum_le_sum (fun u _ => hge u)
  have h2 : ∑ b ∈ B, (if ∃ u : Vec k, b.2 = M b.1 u then Fintype.card (Vec k) else 0)
      ≤ ∑ _b ∈ B, Fintype.card (Vec k) := Finset.sum_le_sum hle2
  have h3 : Fintype.card (Vec k) * B.card ≤ Fintype.card (Vec k) * ∑ i ∈ S, wt M i :=
    Nat.mul_le_mul_left _ hBc
  have e1 : ∑ _u : Vec k, ∑ i ∈ S, wt M i = ∑ u : Vec k, ∑ i ∈ Rset M B u, wt M i := by
    apply le_antisymm h1
    rw [hdc, hsumW]; exact le_trans h2 (hsumc ▸ h3)
  have e2 : ∑ b ∈ B, (if ∃ u : Vec k, b.2 = M b.1 u then Fintype.card (Vec k) else 0)
      = ∑ _b ∈ B, Fintype.card (Vec k) := by
    apply le_antisymm h2
    rw [← hdc, hsumc]; exact le_trans h3 (hsumW ▸ h1)
  have t1 := (Finset.sum_eq_sum_iff_of_le (fun u _ => hge u)).mp e1
  have t2 := (Finset.sum_eq_sum_iff_of_le hle2).mp e2
  constructor
  · intro u
    obtain ⟨P, hPs, hPo⟩ := hP u
    have hu : ∑ i ∈ S, wt M i = ∑ i ∈ Rset M B u, wt M i := t1 u (Finset.mem_univ u)
    have hPW : ∑ i ∈ S, wt M i ≤ ∑ i ∈ P, wt M i := (best_S row rhs M S T hb).2 P hPo
    have hPeq : P = Rset M B u := by
      by_contra hne
      have hss : P ⊂ Rset M B u := lt_of_le_of_ne hPs hne
      obtain ⟨i, hi1, hi2⟩ := Finset.exists_of_ssubset hss
      have h4 : ∑ j ∈ P, wt M j < ∑ j ∈ Rset M B u, wt M j :=
        Finset.sum_lt_sum_of_subset hPs hi1 hi2 (wt_pos M i) (fun j _ _ => Nat.zero_le _)
      omega
    rw [← hPeq]
    refine (hb P).1 ⟨hPo, fun T2 hT2 => ?_⟩
    have h5 : ∑ i ∈ S, wt M i ≤ ∑ i ∈ T2, wt M i := (best_S row rhs M S T hb).2 T2 hT2
    have h6 : ∑ i ∈ P, wt M i = ∑ i ∈ S, wt M i := by rw [hPeq]; exact hu.symm
    exact h6 ▸ h5
  · intro b hbB
    have h7 := t2 b hbB
    by_contra hne
    rw [if_neg hne] at h7
    have hpos : 0 < Fintype.card (Vec k) := Fintype.card_pos
    omega

theorem Rset_invariant (B : Finset (Fin m × Vec t))
    (hcl : ∀ u, Rset M B u = S ∨ Rset M B u = T) :
    ∀ v ∈ hidden M S T, ∀ u, Rset M B (u + v) = Rset M B u := by
  refine sup_invariant (fun u => Rset M B u) ((S \ T) ∪ (T \ S))
    (fun i => LinearMap.ker (M i)) ?_
  intro i hi v hv u
  have hMv : M i (u + v) = M i u := by rw [map_add, LinearMap.mem_ker.mp hv, add_zero]
  have hiff : i ∈ Rset M B (u + v) ↔ i ∈ Rset M B u := by
    simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hMv]
  simp only [Finset.mem_union, Finset.mem_sdiff] at hi
  rcases hcl (u + v) with h1 | h1 <;> rcases hcl u with h2 | h2
  · show Rset M B (u + v) = Rset M B u
    rw [h1, h2]
  · exfalso; rw [h1, h2] at hiff; tauto
  · exfalso; rw [h1, h2] at hiff; tauto
  · show Rset M B (u + v) = Rset M B u
    rw [h1, h2]

theorem cg_cases (g : (Vec k ⧸ hidden M S T) → Bool) (u : Vec k) :
    cg M S T g u = S ∨ cg M S T g u = T := by
  unfold cg; split_ifs <;> simp

theorem ker_le_hidden {i : Fin m} (hi : i ∈ (S \ T) ∪ (T \ S)) :
    LinearMap.ker (M i) ≤ hidden M S T :=
  Finset.le_sup (f := fun i => LinearMap.ker (M i)) hi

theorem Rset_Bg (g : (Vec k ⧸ hidden M S T) → Bool) (u : Vec k) :
    Rset M (Bg M S T g) u = cg M S T g u := by
  classical
  ext i
  simp only [Rset, Bg, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u2, hu2, hi⟩
    have hu3 : M i u = M i u2 := hu2
    have hi2 : i ∈ cg M S T g u2 := hi
    by_cases hmk : (Submodule.Quotient.mk u : Vec k ⧸ hidden M S T) = Submodule.Quotient.mk u2
    · have h1 : cg M S T g u = cg M S T g u2 := by unfold cg; rw [hmk]
      rw [h1]; exact hi2
    · have hnd : i ∉ (S \ T) ∪ (T \ S) := by
        intro hd
        apply hmk
        rw [Submodule.Quotient.eq]
        apply ker_le_hidden M S T hd
        rw [LinearMap.mem_ker, map_sub, hu3, sub_self]
      simp only [Finset.mem_union, Finset.mem_sdiff, not_or, not_and, not_not] at hnd
      rcases cg_cases M S T g u2 with h | h <;> rcases cg_cases M S T g u with h2 | h2 <;>
        rw [h] at hi2 <;> rw [h2] <;> tauto
  · intro hi; exact ⟨u, rfl, hi⟩

theorem Bg_of_realizable (hST : S ≠ T) (hb : Best2 row rhs M S T)
    (B : Finset (Fin m × Vec t)) (hB : Realizable row rhs M (∑ i ∈ S, wt M i) B) :
    ∃ g, B = Bg M S T g := by
  classical
  obtain ⟨hcl, hrange⟩ := classify row rhs M S T hb B hB
  have hinv := Rset_invariant M S T B hcl
  refine ⟨fun q => decide (Rset M B (Quotient.out q) = S), ?_⟩
  have hcg : ∀ u, cg M S T (fun q => decide (Rset M B (Quotient.out q) = S)) u
      = Rset M B u := by
    intro u
    have hmem : u - Quotient.out (Submodule.Quotient.mk u : Vec k ⧸ hidden M S T)
        ∈ hidden M S T := by
      rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_out]
    have hR : Rset M B (Quotient.out (Submodule.Quotient.mk u : Vec k ⧸ hidden M S T))
        = Rset M B u := by
      have h1 := hinv _ hmem (Quotient.out (Submodule.Quotient.mk u : Vec k ⧸ hidden M S T))
      rw [← h1]; congr 1; abel
    unfold cg
    simp only [decide_eq_true_eq]
    rw [hR]
    rcases hcl u with h | h
    · rw [if_pos h, h]
    · rw [if_neg (by rw [h]; exact fun e => hST e.symm), h]
  ext b
  constructor
  · intro hbB
    obtain ⟨u, hu⟩ := hrange b hbB
    simp only [Bg, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨u, hu, ?_⟩
    rw [hcg]
    simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hu]; exact hbB
  · intro hbg
    simp only [Bg, Finset.mem_filter, Finset.mem_univ, true_and] at hbg
    obtain ⟨u, hu, hi⟩ := hbg
    rw [hcg] at hi
    simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [← hu] at hi; exact hi

theorem card_Bg (hb : Best2 row rhs M S T) (g : (Vec k ⧸ hidden M S T) → Bool) :
    (Bg M S T g).card = ∑ i ∈ S, wt M i := by
  have hdc : ∑ u : Vec k, ∑ i ∈ Rset M (Bg M S T g) u, wt M i = ∑ b ∈ Bg M S T g,
      (if ∃ u : Vec k, b.2 = M b.1 u then Fintype.card (Vec k) else 0) :=
    double_count M (Bg M S T g)
  have hl : ∑ u : Vec k, ∑ i ∈ Rset M (Bg M S T g) u, wt M i
      = ∑ _u : Vec k, ∑ i ∈ S, wt M i := by
    apply Finset.sum_congr rfl
    intro u _
    rw [Rset_Bg]
    rcases cg_cases M S T g u with h | h <;> rw [h]
    exact (wS_eq_wT row rhs M S T hb).symm
  have hr : ∑ b ∈ Bg M S T g, (if ∃ u : Vec k, b.2 = M b.1 u then Fintype.card (Vec k) else 0)
      = ∑ _b ∈ Bg M S T g, Fintype.card (Vec k) := by
    apply Finset.sum_congr rfl
    intro b hbm
    simp only [Bg, Finset.mem_filter, Finset.mem_univ, true_and] at hbm
    obtain ⟨u, hu, _⟩ := hbm
    rw [if_pos ⟨u, hu⟩]
  have hsumc : ∑ _b ∈ Bg M S T g, Fintype.card (Vec k)
      = Fintype.card (Vec k) * (Bg M S T g).card := by simp [mul_comm]
  have hsumW : ∑ _u : Vec k, ∑ i ∈ S, wt M i = Fintype.card (Vec k) * ∑ i ∈ S, wt M i := by
    simp [Finset.card_univ]
  have hpos : 0 < Fintype.card (Vec k) := Fintype.card_pos
  have h1 : Fintype.card (Vec k) * (Bg M S T g).card
      = Fintype.card (Vec k) * ∑ i ∈ S, wt M i := by
    rw [← hsumc, ← hsumW, ← hl, ← hr, hdc]
  exact Nat.eq_of_mul_eq_mul_left hpos h1

end Main

section Trees

def Cons {V : Type} (q : List Bool → V → Bool) (p : List Bool) (x : V) : Prop :=
  ∀ (j : Fin p.length), q (List.take (↑j) p) x = p.get j

def Has {V O : Type} [AddCommGroup V] [Module (ZMod 2) V] (ok : V → O → Prop)
    (Z : V → Prop) (h c : ℕ) : Prop :=
  ∃ (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O),
    Shape N J ∧ (∀ p ∈ J, q p ∈ Queries V) ∧
    (∀ p ∈ N \ J, ∀ x, Z x → Cons q p x → ok x (out p)) ∧
    (∀ p ∈ N \ J, p.length ≤ h) ∧ (N \ J).card ≤ c

def bw_nn (N0 N1 : Finset (List Bool)) : Finset (List Bool) :=
  insert [] (N0.image (List.cons false) ∪ N1.image (List.cons true))

theorem bw_nn_nil (N0 N1 : Finset (List Bool)) : [] ∈ bw_nn N0 N1 := by simp [bw_nn]

theorem bw_nn_false (N0 N1 : Finset (List Bool)) (r : List Bool) :
    (false :: r) ∈ bw_nn N0 N1 ↔ r ∈ N0 := by simp [bw_nn]

theorem bw_nn_true (N0 N1 : Finset (List Bool)) (r : List Bool) :
    (true :: r) ∈ bw_nn N0 N1 ↔ r ∈ N1 := by simp [bw_nn]

theorem bw_nn_shape (N0 J0 N1 J1 : Finset (List Bool)) (h0 : Shape N0 J0) (h1 : Shape N1 J1) :
    Shape (bw_nn N0 N1) (bw_nn J0 J1) := by
  refine ⟨bw_nn_nil _ _, ?_, ?_, ?_⟩
  · intro p hp
    rcases p with _ | ⟨c, r⟩
    · exact bw_nn_nil _ _
    · cases c
      · rw [bw_nn_false] at hp ⊢
        exact h0.2.1 hp
      · rw [bw_nn_true] at hp ⊢
        exact h1.2.1 hp
  · intro p b hp
    rcases p with _ | ⟨c, r⟩
    · exact bw_nn_nil _ _
    · cases c
      · rw [List.cons_append, bw_nn_false] at hp
        rw [bw_nn_false]
        exact h0.2.2.1 r b hp
      · rw [List.cons_append, bw_nn_true] at hp
        rw [bw_nn_true]
        exact h1.2.2.1 r b hp
  · intro p hp
    rcases p with _ | ⟨c, r⟩
    · exact ⟨(bw_nn_false _ _ _).2 h0.1, (bw_nn_true _ _ _).2 h1.1⟩
    · cases c
      · rw [bw_nn_false] at hp
        rw [List.cons_append, List.cons_append, bw_nn_false, bw_nn_false]
        exact h0.2.2.2 r hp
      · rw [bw_nn_true] at hp
        rw [List.cons_append, List.cons_append, bw_nn_true, bw_nn_true]
        exact h1.2.2.2 r hp

theorem bw_nn_leaves (N0 J0 N1 J1 : Finset (List Bool)) :
    bw_nn N0 N1 \ bw_nn J0 J1 =
      (N0 \ J0).image (List.cons false) ∪ (N1 \ J1).image (List.cons true) := by
  ext p
  rcases p with _ | ⟨c, r⟩
  · simp [bw_nn]
  · cases c <;> simp [bw_nn]

def bw_nq {V : Type} (f : V → Bool) (q0 q1 : List Bool → V → Bool) : List Bool → V → Bool
  | [] => f
  | false :: r => q0 r
  | true :: r => q1 r

def bw_nout {O : Type} (o0 o1 : List Bool → O) : List Bool → O
  | [] => o0 []
  | false :: r => o0 r
  | true :: r => o1 r

theorem bw_cons {V : Type} (q : List Bool → V → Bool) (c : Bool) (p : List Bool) (x : V) :
    Cons q (c :: p) x ↔ q [] x = c ∧ Cons (fun r => q (c :: r)) p x := by
  unfold Cons
  constructor
  · intro h
    refine ⟨by simpa using h ⟨0, by simp⟩, fun j => ?_⟩
    have := h ⟨j.1 + 1, by simp⟩
    simpa using this
  · rintro ⟨h0, h1⟩ ⟨j, hj⟩
    rcases j with _ | j
    · simpa using h0
    · have := h1 ⟨j, by simpa using hj⟩
      simpa using this


variable {V O : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem has_mono (ok : V → O → Prop) (Z Z' : V → Prop) (h h' c c' : ℕ)
    (hZ : ∀ x, Z' x → Z x) (hh : h ≤ h') (hc : c ≤ c') (H : Has ok Z h c) :
    Has ok Z' h' c' := by
  obtain ⟨N, J, q, out, s, a, k0, d, e⟩ := H
  exact ⟨N, J, q, out, s, a, fun p hp x hz => k0 p hp x (hZ x hz),
    fun p hp => (d p hp).trans hh, e.trans hc⟩

theorem has_leaf (ok : V → O → Prop) (Z : V → Prop) (a : O)
    (ha : ∀ x, Z x → ok x a) : Has ok Z 0 1 := by
  refine ⟨{[]}, ∅, fun _ _ => false, fun _ => a, ⟨by simp, by simp, ?_, by simp⟩, by simp,
    ?_, ?_, by simp⟩
  · intro p b hp
    simp at hp
  · intro p _ x hz _
    exact ha x hz
  · intro p hp
    simp at hp
    simp [hp]

theorem has_node (ok : V → O → Prop) (Z : V → Prop)
    (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2) (h c0 c1 : ℕ)
    (H0 : Has ok (fun x => Z x ∧ l x ≠ b) h c0)
    (H1 : Has ok (fun x => Z x ∧ l x = b) h c1) :
    Has ok Z (h + 1) (c0 + c1) := by
  obtain ⟨N0, J0, q0, o0, s0, a0, k0, d0, e0⟩ := H0
  obtain ⟨N1, J1, q1, o1, s1, a1, k1, d1, e1⟩ := H1
  refine ⟨bw_nn N0 N1, bw_nn J0 J1, bw_nq (fun x => decide (l x = b)) q0 q1, bw_nout o0 o1,
    bw_nn_shape _ _ _ _ s0 s1, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases p with _ | ⟨c, r⟩
    · exact ⟨l, b, rfl⟩
    · cases c
      · exact a0 r ((bw_nn_false _ _ _).1 hp)
      · exact a1 r ((bw_nn_true _ _ _).1 hp)
  · intro p hp x hz hc
    rw [bw_nn_leaves] at hp
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨hf, hc'⟩ := (bw_cons _ _ _ _).1 hc
      exact k0 r hr x ⟨hz, by simpa [bw_nq] using hf⟩ hc'
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨hf, hc'⟩ := (bw_cons _ _ _ _).1 hc
      exact k1 r hr x ⟨hz, by simpa [bw_nq] using hf⟩ hc'
  · intro p hp
    rw [bw_nn_leaves] at hp
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hp
      simpa using d0 r hr
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hp
      simpa using d1 r hr
  · rw [bw_nn_leaves]
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add (Finset.card_image_le.trans e0) (Finset.card_image_le.trans e1))

theorem bw_z2_a : ∀ a b : ZMod 2, a ≠ b + 1 → a - b = 0 := by decide

theorem bw_z2_b : ∀ a b w : ZMod 2, a = b + 1 → w ≠ 0 → a - (b + w) = 0 := by decide

theorem bw_z2_c : ∀ a b : ZMod 2, a = b + 1 ↔ a + b = 1 := by decide

theorem bw_z2_d : ∀ u v : ZMod 2, u + v = 1 → v ≠ 1 → u = 1 := by decide

theorem bw_z2_e : ∀ a b : ZMod 2, a + b = 1 → a ≠ b := by decide


theorem has_read (ok : V → O → Prop) {t : ℕ} (F : V →ₗ[ZMod 2] (Fin t → ZMod 2))
    (mk : (Fin t → ZMod 2) → O) :
    ∀ (d : ℕ) (D : Submodule (ZMod 2) (Fin t → ZMod 2)) (y0 : Fin t → ZMod 2) (Z : V → Prop),
      Module.finrank (ZMod 2) D ≤ d → (∀ x, Z x → F x - y0 ∈ D) →
      (∀ x, Z x → ok x (mk (F x))) → Has ok Z d (2 ^ d) := by
  intro d
  induction d with
  | zero =>
    intro D y0 Z hd hZ hok
    have hD : D = ⊥ := Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hd)
    subst hD
    refine has_leaf ok Z (mk y0) (fun x hx => ?_)
    have h1 : F x - y0 = 0 := by simpa using hZ x hx
    have h2 : F x = y0 := sub_eq_zero.1 h1
    rw [← h2]
    exact hok x hx
  | succ d ih =>
    intro D y0 Z hd hZ hok
    by_cases hD : D = ⊥
    · subst hD
      refine has_mono ok Z Z 0 (d + 1) 1 (2 ^ (d + 1)) (fun _ hx => hx) (Nat.zero_le _)
        Nat.one_le_two_pow (has_leaf ok Z (mk y0) (fun x hx => ?_))
      have h1 : F x - y0 = 0 := by simpa using hZ x hx
      have h2 : F x = y0 := sub_eq_zero.1 h1
      rw [← h2]
      exact hok x hx
    · obtain ⟨v, hvD, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
      obtain ⟨c, hc⟩ : ∃ c, v c ≠ 0 := by
        by_contra hcon
        exact hv0 (funext fun c => by_contra fun hc => hcon ⟨c, hc⟩)
      have hlt : Module.finrank (ZMod 2)
          ↥(D ⊓ LinearMap.ker (LinearMap.proj c : (Fin t → ZMod 2) →ₗ[ZMod 2] ZMod 2)) <
          Module.finrank (ZMod 2) D := by
        apply Submodule.finrank_lt_finrank_of_lt
        refine lt_of_le_of_ne inf_le_left ?_
        intro heq
        have hv : v ∈ D ⊓ LinearMap.ker (LinearMap.proj c : (Fin t → ZMod 2) →ₗ[ZMod 2] ZMod 2) :=
          by
            rw [heq]
            exact hvD
        exact hc (by simpa using (Submodule.mem_inf.1 hv).2)
      have hle : Module.finrank (ZMod 2)
          ↥(D ⊓ LinearMap.ker (LinearMap.proj c : (Fin t → ZMod 2) →ₗ[ZMod 2] ZMod 2)) ≤ d := by
        omega
      have e2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
      rw [e2]
      refine has_node ok Z
        ((LinearMap.proj c : (Fin t → ZMod 2) →ₗ[ZMod 2] ZMod 2) ∘ₗ F) (y0 c + 1) d (2 ^ d) (2 ^ d)
        ?_ ?_
      · refine ih _ y0 _ hle ?_ (fun x hx => hok x hx.1)
        rintro x ⟨hz, hx⟩
        refine Submodule.mem_inf.2 ⟨hZ x hz, ?_⟩
        have hx' : F x c ≠ y0 c + 1 := hx
        simpa using bw_z2_a _ _ hx'
      · refine ih _ (y0 + v) _ hle ?_ (fun x hx => hok x hx.1)
        rintro x ⟨hz, hx⟩
        refine Submodule.mem_inf.2 ⟨?_, ?_⟩
        · have e3 : F x - (y0 + v) = (F x - y0) - v := by abel
          rw [e3]
          exact D.sub_mem (hZ x hz) hvD
        · have hx' : F x c = y0 c + 1 := hx
          simpa using bw_z2_b _ _ _ hx' hc

theorem kr_q {ι : Type} [DecidableEq ι] (e : ι → ℕ) (h : ℕ) :
    ∀ (c : ℕ) (G : Finset ι), G.card ≤ c → (∀ i ∈ G, e i ≤ h) →
      ∃ A ⊆ G, ∑ i ∈ A, 2 ^ e i = min (∑ i ∈ G, 2 ^ e i) (2 ^ h) := by
  intro c
  induction c with
  | zero =>
    intro G hG _
    have hG0 : G = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hG)
    subst hG0
    exact ⟨∅, le_rfl, by simp⟩
  | succ c ih =>
    intro G hG he
    rcases G.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, le_rfl, by simp⟩
    · obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image G e hne
      have hsum : 2 ^ e i0 + ∑ i ∈ G.erase i0, 2 ^ e i = ∑ i ∈ G, 2 ^ e i :=
        Finset.add_sum_erase G (fun i => 2 ^ e i) hi0
      by_cases hR : 2 ^ h ≤ ∑ i ∈ G.erase i0, 2 ^ e i
      · obtain ⟨A, hA, hAs⟩ := ih (G.erase i0)
          (by rw [Finset.card_erase_of_mem hi0]; omega)
          (fun i hi => he i (Finset.mem_of_mem_erase hi))
        refine ⟨A, hA.trans (Finset.erase_subset _ _), ?_⟩
        rw [hAs, min_eq_right hR, min_eq_right (hR.trans (hsum ▸ Nat.le_add_left _ _))]
      · refine ⟨G, le_rfl, ?_⟩
        obtain ⟨a, ha⟩ : 2 ^ e i0 ∣ ∑ i ∈ G.erase i0, 2 ^ e i :=
          Finset.dvd_sum (fun i hi => Nat.pow_dvd_pow 2 (hmin i (Finset.mem_of_mem_erase hi)))
        obtain ⟨b, hb⟩ : 2 ^ e i0 ∣ 2 ^ h := Nat.pow_dvd_pow 2 (he i0 hi0)
        have hab : a < b :=
          lt_of_not_ge (fun hcon => hR (by rw [ha, hb]; exact Nat.mul_le_mul_left _ hcon))
        have hm : 2 ^ e i0 * (a + 1) ≤ 2 ^ e i0 * b := Nat.mul_le_mul_left _ hab
        rw [min_eq_left]
        rw [← hsum, ha, hb]
        linarith

theorem kr_split {ι : Type} [DecidableEq ι] (e : ι → ℕ) (h : ℕ) (G : Finset ι) (hc : 2 ≤ G.card)
    (hs : ∑ i ∈ G, 2 ^ e i ≤ 2 ^ (h + 1)) :
    ∃ A ⊆ G, A.Nonempty ∧ (G \ A).Nonempty ∧ ∑ i ∈ A, 2 ^ e i ≤ 2 ^ h ∧
      ∑ i ∈ G \ A, 2 ^ e i ≤ 2 ^ h := by
  by_cases hT : ∑ i ∈ G, 2 ^ e i ≤ 2 ^ h
  · obtain ⟨a, ha⟩ : G.Nonempty := Finset.card_pos.1 (by omega)
    have hsub : {a} ⊆ G := Finset.singleton_subset_iff.2 ha
    refine ⟨{a}, hsub, Finset.singleton_nonempty a, ?_, ?_, ?_⟩
    · apply Finset.card_pos.1
      have hcc := Finset.card_sdiff_add_card_eq_card hsub
      rw [Finset.card_singleton] at hcc
      omega
    · exact (Finset.sum_le_sum_of_subset hsub).trans hT
    · exact (Finset.sum_le_sum_of_subset Finset.sdiff_subset).trans hT
  · have hT := lt_of_not_ge hT
    have he : ∀ i ∈ G, e i ≤ h := by
      intro i hi
      have h1 : 2 ^ e i + ∑ j ∈ G.erase i, 2 ^ e j = ∑ j ∈ G, 2 ^ e j :=
        Finset.add_sum_erase G (fun j => 2 ^ e j) hi
      obtain ⟨j, hj⟩ : (G.erase i).Nonempty :=
        Finset.card_pos.1 (by rw [Finset.card_erase_of_mem hi]; omega)
      have h2 : 2 ^ e j ≤ ∑ j ∈ G.erase i, 2 ^ e j :=
        Finset.single_le_sum (f := fun j => 2 ^ e j) (fun _ _ => Nat.zero_le _) hj
      have h3 : 0 < 2 ^ e j := Nat.two_pow_pos _
      have h4 : 2 ^ e i < 2 ^ (h + 1) := by omega
      have h5 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h4
      omega
    obtain ⟨A, hA, hAs⟩ := kr_q e h G.card G le_rfl he
    rw [min_eq_right hT.le] at hAs
    have hsd := Finset.sum_sdiff (f := fun i => 2 ^ e i) hA
    have hp : 2 ^ (h + 1) = 2 ^ h + 2 ^ h := by ring
    have hpos : 0 < 2 ^ h := Nat.two_pow_pos _
    refine ⟨A, hA, ?_, ?_, hAs.le, by omega⟩
    · apply Finset.nonempty_of_sum_ne_zero (f := fun i => 2 ^ e i)
      omega
    · apply Finset.nonempty_of_sum_ne_zero (f := fun i => 2 ^ e i)
      omega

theorem has_kraft {ι : Type} [DecidableEq ι] (ok : V → O → Prop) (Z0 : V → Prop)
    (φ : ι → V →ₗ[ZMod 2] ZMod 2) (β : ι → ZMod 2) (ex cost : ι → ℕ) (G0 : Finset ι)
    (hitem : ∀ i ∈ G0, ∀ h, ex i ≤ h →
      Has ok (fun x => Z0 x ∧ φ i x + β i = 1) h (cost i)) :
    ∀ (c : ℕ) (G : Finset ι) (h : ℕ), G ⊆ G0 → G.card ≤ c → G.Nonempty →
      ∑ i ∈ G, 2 ^ ex i ≤ 2 ^ h →
      Has ok (fun x => Z0 x ∧ ∑ i ∈ G, (φ i x + β i) = 1) h (∑ i ∈ G, cost i) := by
  intro c
  induction c with
  | zero =>
    intro G h _ hc hne
    exact absurd (Finset.card_eq_zero.1 (Nat.le_zero.1 hc)) hne.ne_empty
  | succ c ih =>
    intro G h hG0 hc hne hs
    by_cases h1 : G.card ≤ 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 (le_antisymm h1 (Finset.card_pos.2 hne))
      have hi : i ∈ G0 := hG0 (Finset.mem_singleton_self i)
      rw [Finset.sum_singleton] at hs
      have hex : ex i ≤ h := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hs
      rw [Finset.sum_singleton]
      refine has_mono ok _ _ h h _ _ ?_ le_rfl le_rfl (hitem i hi h hex)
      rintro x ⟨hz, hx⟩
      rw [Finset.sum_singleton] at hx
      exact ⟨hz, hx⟩
    · have hcs : G.card ≤ ∑ i ∈ G, 2 ^ ex i := by
        have hh := Finset.card_nsmul_le_sum G (fun i => 2 ^ ex i) 1
          (fun i _ => Nat.one_le_two_pow)
        simpa using hh
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := by
        rcases h with _ | h'
        · simp at hs
          omega
        · exact ⟨h', rfl⟩
      obtain ⟨A, hA, hAn, hBn, hAs, hBs⟩ := kr_split ex h' G (by omega) hs
      have hcard : (G \ A).card + A.card = G.card := Finset.card_sdiff_add_card_eq_card hA
      have hAp := Finset.card_pos.2 hAn
      have hBp := Finset.card_pos.2 hBn
      have hsd : ∑ i ∈ G \ A, cost i + ∑ i ∈ A, cost i = ∑ i ∈ G, cost i := Finset.sum_sdiff hA
      rw [← hsd]
      refine has_node ok _ (∑ i ∈ A, φ i) (∑ i ∈ A, β i + 1) h' _ _ ?_ ?_
      · refine has_mono ok _ _ h' h' _ _ ?_ le_rfl le_rfl
          (ih (G \ A) h' (Finset.sdiff_subset.trans hG0) (by omega) hBn hBs)
        rintro x ⟨⟨hz0, hz⟩, hx⟩
        refine ⟨hz0, ?_⟩
        have hsd2 := Finset.sum_sdiff (f := fun i => φ i x + β i) hA
        have hAe : ∑ i ∈ A, (φ i x + β i) = (∑ i ∈ A, φ i) x + ∑ i ∈ A, β i := by
          rw [Finset.sum_add_distrib, LinearMap.sum_apply]
        apply bw_z2_d _ (∑ i ∈ A, (φ i x + β i))
        · rw [hsd2]
          exact hz
        · rw [hAe]
          intro hh
          exact hx ((bw_z2_c _ _).2 hh)
      · refine has_mono ok _ _ h' h' _ _ ?_ le_rfl le_rfl
          (ih A h' (hA.trans hG0) (by omega) hAn hAs)
        rintro x ⟨⟨hz0, _⟩, hx⟩
        refine ⟨hz0, ?_⟩
        have hAe : ∑ i ∈ A, (φ i x + β i) = (∑ i ∈ A, φ i) x + ∑ i ∈ A, β i := by
          rw [Finset.sum_add_distrib, LinearMap.sum_apply]
        rw [hAe]
        exact (bw_z2_c _ _).1 hx

end Trees

section Block
variable {n k t m : ℕ} (row : Fin m → Vec n →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
  (M : Fin m → Vec k →ₗ[ZMod 2] Vec t) (S T : Finset (Fin m))

abbrev okG (g : (Vec k ⧸ hidden M S T) → Bool) (x : Vec n × Vec k) (a : Fin m × Vec t) : Prop :=
  Answer row rhs M x a ∧ a ∈ Bg M S T g

def Zb (x : Vec n × Vec k) : Prop := ∑ i ∈ S \ T, (row i x.1 + rhs i) = 1

theorem sum_fail_of_oddDep (P : Finset (Fin m)) (hP : OddDep row rhs P) (x : Vec n) :
    ∑ i ∈ P, (row i x + rhs i) = 1 := by
  have h1 : (∑ i ∈ P, row i) = 0 := hP.1
  have h2 : (∑ i ∈ P, rhs i) = 1 := hP.2
  rw [Finset.sum_add_distrib, ← LinearMap.sum_apply, h1, h2]
  simp

theorem sum_split {β : Type} [AddCommMonoid β] (f : Fin m → β) (A B : Finset (Fin m)) :
    ∑ i ∈ A \ B, f i + ∑ i ∈ A ∩ B, f i = ∑ i ∈ A, f i := by
  have h := Finset.sum_sdiff (f := f) (Finset.inter_subset_left : A ∩ B ⊆ A)
  rwa [Finset.sdiff_inter_self_left] at h

theorem par_TS (hb : Best2 row rhs M S T) (x : Vec n × Vec k) (hx : Zb row rhs S T x) :
    ∑ i ∈ T \ S, (row i x.1 + rhs i) = 1 := by
  have hS := sum_fail_of_oddDep row rhs S (best_S row rhs M S T hb).1 x.1
  have hT := sum_fail_of_oddDep row rhs T (best_T row rhs M S T hb).1 x.1
  rw [← sum_split _ S T] at hS
  rw [← sum_split _ T S, Finset.inter_comm] at hT
  have hx' : ∑ i ∈ S \ T, (row i x.1 + rhs i) = 1 := hx
  rw [hx'] at hS
  have key : ∀ a b : ZMod 2, 1 + a = 1 → b + a = 1 → b = 1 := by decide
  exact key _ _ hS hT

theorem rank_map_add {k t : ℕ} (f : Vec k →ₗ[ZMod 2] Vec t) (A : Submodule (ZMod 2) (Vec k))
    (hA : LinearMap.ker f ≤ A) :
    Module.finrank (ZMod 2) (A.map f) + Module.finrank (ZMod 2) (LinearMap.ker f) =
      Module.finrank (ZMod 2) A := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (f.domRestrict A)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h1
  rw [← LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hA)]
  exact h1

noncomputable def ra (i : Fin m) : ℕ := Module.finrank (ZMod 2) ((hidden M S T).map (M i))

noncomputable def cc : ℕ :=
  Module.finrank (ZMod 2) (Vec k) - Module.finrank (ZMod 2) (hidden M S T)

theorem wt_excl (i : Fin m) (hi : i ∈ (S \ T) ∪ (T \ S)) :
    wt M i = 2 ^ cc M S T * 2 ^ ra M S T i := by
  have hk := ker_le_hidden M S T hi
  have h1 := rank_map_add (M i) (hidden M S T) hk
  have h2 := rank_map_add (M i) ⊤ le_top
  rw [Submodule.map_top, finrank_top] at h2
  have h3 : Module.finrank (ZMod 2) (hidden M S T) ≤ Module.finrank (ZMod 2) (Vec k) :=
    Submodule.finrank_le _
  unfold wt cc ra
  rw [← pow_add]
  congr 1
  omega

theorem excl_eq (hb : Best2 row rhs M S T) :
    ∑ i ∈ S \ T, wt M i = ∑ i ∈ T \ S, wt M i := by
  have h1 := sum_split (fun i => wt M i) S T
  have h2 := sum_split (fun i => wt M i) T S
  rw [Finset.inter_comm] at h2
  have h3 := wS_eq_wT row rhs M S T hb
  omega

theorem E_eq : ∑ i ∈ S \ T, wt M i = 2 ^ cc M S T * ∑ i ∈ S \ T, 2 ^ ra M S T i := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i hi => wt_excl M S T i (Finset.mem_union_left _ hi))

theorem E0_eq (hb : Best2 row rhs M S T) :
    ∑ i ∈ T \ S, 2 ^ ra M S T i = ∑ i ∈ S \ T, 2 ^ ra M S T i := by
  have h := excl_eq row rhs M S T hb
  rw [Finset.sum_congr rfl (fun i hi => wt_excl M S T i (Finset.mem_union_left _ hi)),
    Finset.sum_congr rfl (fun i hi => wt_excl M S T i (Finset.mem_union_right _ hi)),
    ← Finset.mul_sum, ← Finset.mul_sum] at h
  exact (Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) h).symm

theorem block_base_P (g : (Vec k ⧸ hidden M S T) → Bool) (u0 : Vec k) (h : ℕ)
    (P : Finset (Fin m)) (hPne : P.Nonempty)
    (hPsum : ∑ i ∈ P, 2 ^ ra M S T i = ∑ i ∈ S \ T, 2 ^ ra M S T i)
    (hcg : ∀ x : Vec n × Vec k, x.2 - u0 ∈ hidden M S T → P ⊆ cg M S T g x.2)
    (hpar : ∀ x : Vec n × Vec k, Zb row rhs S T x → ∑ i ∈ P, (row i x.1 + rhs i) = 1)
    (hh : ∑ i ∈ S \ T, 2 ^ ra M S T i ≤ 2 ^ h) :
    Has (okG row rhs M S T g) (fun x => Zb row rhs S T x ∧ x.2 - u0 ∈ hidden M S T) h
      (∑ i ∈ S \ T, 2 ^ ra M S T i) := by
  classical
  have K := has_kraft (okG row rhs M S T g)
    (fun x : Vec n × Vec k => Zb row rhs S T x ∧ x.2 - u0 ∈ hidden M S T)
    (fun i => (row i).comp (LinearMap.fst (ZMod 2) (Vec n) (Vec k))) rhs (ra M S T)
    (fun i => 2 ^ ra M S T i) P ?_ P.card P h le_rfl le_rfl hPne (by rw [hPsum]; exact hh)
  · rw [hPsum] at K
    refine has_mono _ _ _ h h _ _ ?_ le_rfl le_rfl K
    intro x hx
    exact ⟨hx, hpar x hx.1⟩
  · intro i hi h' hh'
    refine has_mono _ _ _ (ra M S T i) h' _ _ (fun x hx => hx) hh' le_rfl
      (has_read (okG row rhs M S T g) ((M i).comp (LinearMap.snd (ZMod 2) (Vec n) (Vec k)))
        (fun y => (i, y)) (ra M S T i) ((hidden M S T).map (M i)) (M i u0) _ le_rfl ?_ ?_)
    · rintro x ⟨⟨_, hx⟩, _⟩
      show M i x.2 - M i u0 ∈ (hidden M S T).map (M i)
      rw [← map_sub]
      exact Submodule.mem_map_of_mem hx
    · rintro x ⟨⟨_, hx⟩, hpi⟩
      have hpi' : row i x.1 + rhs i = 1 := hpi
      show (row i x.1 ≠ rhs i ∧ M i x.2 = M i x.2) ∧ (i, M i x.2) ∈ Bg M S T g
      refine ⟨⟨bw_z2_e _ _ hpi', rfl⟩, ?_⟩
      simp only [Bg, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x.2, rfl, hcg x hx hi⟩

theorem block_base (hST : S ≠ T) (hb : Best2 row rhs M S T) (g : (Vec k ⧸ hidden M S T) → Bool)
    (u0 : Vec k) (h : ℕ) (hh : ∑ i ∈ S \ T, 2 ^ ra M S T i ≤ 2 ^ h) :
    Has (okG row rhs M S T g) (fun x => Zb row rhs S T x ∧ x.2 - u0 ∈ hidden M S T) h
      (∑ i ∈ S \ T, 2 ^ ra M S T i) := by
  have hmk : ∀ x : Vec n × Vec k, x.2 - u0 ∈ hidden M S T →
      cg M S T g x.2 = cg M S T g u0 := by
    intro x hx
    have h1 : (Submodule.Quotient.mk x.2 : Vec k ⧸ hidden M S T) = Submodule.Quotient.mk u0 :=
      (Submodule.Quotient.eq _).2 hx
    unfold cg
    rw [h1]
  by_cases hg : g (Submodule.Quotient.mk u0) = true
  · refine block_base_P row rhs M S T g u0 h (S \ T)
      (sdiff_nonempty_of_wt M hST (wS_eq_wT row rhs M S T hb)) rfl ?_ (fun x hx => hx) hh
    intro x hx
    rw [hmk x hx]
    unfold cg
    rw [if_pos hg]
    exact Finset.sdiff_subset
  · refine block_base_P row rhs M S T g u0 h (T \ S)
      (sdiff_nonempty_of_wt M (Ne.symm hST) (wS_eq_wT row rhs M S T hb).symm)
      (E0_eq row rhs M S T hb) ?_ (fun x hx => par_TS row rhs M S T hb x hx) hh
    intro x hx
    rw [hmk x hx]
    unfold cg
    rw [if_neg hg]
    exact Finset.sdiff_subset

theorem zk1 : ∀ a b : ZMod 2, a ≠ b → a - (b + 1) = 0 := by decide

theorem block_ind (hST : S ≠ T) (hb : Best2 row rhs M S T) (g : (Vec k ⧸ hidden M S T) → Bool)
    (hE0 : 0 < ∑ i ∈ S \ T, 2 ^ ra M S T i) :
    ∀ (d : ℕ) (W : Submodule (ZMod 2) (Vec k)), hidden M S T ≤ W →
      Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) (hidden M S T) + d →
      ∀ (u0 : Vec k) (h : ℕ), (∑ i ∈ S \ T, 2 ^ ra M S T i) * 2 ^ d ≤ 2 ^ h →
      Has (okG row rhs M S T g) (fun x => Zb row rhs S T x ∧ x.2 - u0 ∈ W) h
        (2 ^ d * ∑ i ∈ S \ T, 2 ^ ra M S T i) := by
  intro d
  induction d with
  | zero =>
    intro W hW hd u0 h hh
    have hWe : hidden M S T = W := Submodule.eq_of_le_of_finrank_le hW (by simpa using hd)
    subst hWe
    simp only [pow_zero, one_mul, mul_one] at hh ⊢
    exact block_base row rhs M S T hST hb g u0 h hh
  | succ d ih =>
    intro W hW hd u0 h hh
    by_cases hWe : W = hidden M S T
    · subst hWe
      refine has_mono _ _ _ h h _ _ (fun x hx => hx) le_rfl ?_
        (block_base row rhs M S T hST hb g u0 h ?_)
      · exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
      · exact le_trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) hh
    · have hlt : hidden M S T < W := lt_of_le_of_ne hW (Ne.symm hWe)
      obtain ⟨v, hvW, hvH⟩ := SetLike.exists_of_lt hlt
      obtain ⟨l, hlv, hle⟩ := Submodule.exists_le_ker_of_notMem hvH
      have hlv1 : l v = 1 := (zmod2_cases (l v)).resolve_left hlv
      have hW'lt : W ⊓ LinearMap.ker l < W := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro heq
        have hv2 : v ∈ W ⊓ LinearMap.ker l := by rw [heq]; exact hvW
        exact hlv (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv2).2)
      have hfr := Submodule.finrank_lt_finrank_of_lt hW'lt
      have hW' : hidden M S T ≤ W ⊓ LinearMap.ker l := le_inf hW hle
      have h2 : 2 ≤ 2 ^ (d + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : 2 ≤ (∑ i ∈ S \ T, 2 ^ ra M S T i) * 2 ^ (d + 1) :=
        le_trans h2 (Nat.le_mul_of_pos_left _ hE0)
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := by
        rcases h with _ | h'
        · rw [pow_zero] at hh
          omega
        · exact ⟨h', rfl⟩
      have hh' : (∑ i ∈ S \ T, 2 ^ ra M S T i) * 2 ^ d ≤ 2 ^ h' := by
        rw [pow_succ, pow_succ, ← mul_assoc] at hh
        exact Nat.le_of_mul_le_mul_right hh (by norm_num)
      have e2 : 2 ^ (d + 1) * (∑ i ∈ S \ T, 2 ^ ra M S T i) =
          2 ^ d * (∑ i ∈ S \ T, 2 ^ ra M S T i) + 2 ^ d * (∑ i ∈ S \ T, 2 ^ ra M S T i) := by
        ring
      rw [e2]
      refine has_node _ _ (l.comp (LinearMap.snd (ZMod 2) (Vec n) (Vec k))) (l u0) h' _ _ ?_ ?_
      · refine has_mono _ _ _ h' h' _ _ ?_ le_rfl le_rfl
          (ih (W ⊓ LinearMap.ker l) hW' (by omega) (u0 + v) h' hh')
        rintro x ⟨⟨hz, hx⟩, hlx⟩
        refine ⟨hz, Submodule.mem_inf.2 ⟨?_, ?_⟩⟩
        · have e3 : x.2 - (u0 + v) = (x.2 - u0) - v := by abel
          rw [e3]
          exact W.sub_mem hx hvW
        · rw [LinearMap.mem_ker, map_sub, map_add, hlv1]
          have hlx' : l x.2 ≠ l u0 := hlx
          exact zk1 _ _ hlx'
      · refine has_mono _ _ _ h' h' _ _ ?_ le_rfl le_rfl
          (ih (W ⊓ LinearMap.ker l) hW' (by omega) u0 h' hh')
        rintro x ⟨⟨hz, hx⟩, hlx⟩
        refine ⟨hz, Submodule.mem_inf.2 ⟨hx, ?_⟩⟩
        rw [LinearMap.mem_ker, map_sub]
        have hlx' : l x.2 = l u0 := hlx
        rw [hlx', sub_self]

theorem block_top (hST : S ≠ T) (hb : Best2 row rhs M S T) (g : (Vec k ⧸ hidden M S T) → Bool)
    (e h : ℕ) (hE : ∑ i ∈ S \ T, wt M i ≤ 2 ^ e) (heh : e ≤ h) :
    Has (okG row rhs M S T g) (fun x => Zb row rhs S T x) h (∑ i ∈ S \ T, wt M i) := by
  have hE0 : 0 < ∑ i ∈ S \ T, 2 ^ ra M S T i := by
    obtain ⟨i, hi⟩ := sdiff_nonempty_of_wt M hST (wS_eq_wT row rhs M S T hb)
    exact lt_of_lt_of_le (Nat.two_pow_pos _)
      (Finset.single_le_sum (f := fun i => 2 ^ ra M S T i) (fun _ _ => Nat.zero_le _) hi)
  have hfr : Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (Vec k)) ≤
      Module.finrank (ZMod 2) (hidden M S T) + cc M S T := by
    rw [finrank_top]
    unfold cc
    omega
  have K := block_ind row rhs M S T hST hb g hE0 (cc M S T) ⊤ le_top hfr 0 h ?_
  · rw [E_eq M S T]
    refine has_mono _ _ _ h h _ _ ?_ le_rfl le_rfl K
    intro x hx
    exact ⟨hx, Submodule.mem_top⟩
  · rw [mul_comm, ← E_eq M S T]
    exact le_trans hE (Nat.pow_le_pow_right (by norm_num) heh)

theorem outer (hST : S ≠ T) (hb : Best2 row rhs M S T) (g : (Vec k ⧸ hidden M S T) → Bool)
    (H e : ℕ) (hE : ∑ i ∈ S \ T, wt M i ≤ 2 ^ e)
    (hC : ∑ i ∈ S ∩ T, wt M i + 2 ^ e ≤ 2 ^ H) :
    Has (okG row rhs M S T g) (fun _ => True) H (∑ i ∈ S, wt M i) := by
  classical
  let φ : Option (Fin m) → (Vec n × Vec k) →ₗ[ZMod 2] ZMod 2 := fun o =>
    Option.elim o ((∑ j ∈ S \ T, row j).comp (LinearMap.fst (ZMod 2) (Vec n) (Vec k)))
      (fun i => (row i).comp (LinearMap.fst (ZMod 2) (Vec n) (Vec k)))
  let β : Option (Fin m) → ZMod 2 := fun o => Option.elim o (∑ j ∈ S \ T, rhs j) rhs
  let ex : Option (Fin m) → ℕ := fun o =>
    Option.elim o e (fun i => Module.finrank (ZMod 2) (LinearMap.range (M i)))
  let cost : Option (Fin m) → ℕ := fun o => Option.elim o (∑ j ∈ S \ T, wt M j) (wt M)
  have K := has_kraft (okG row rhs M S T g) (fun _ => True) φ β ex cost
    (Finset.insertNone (S ∩ T)) ?_ (Finset.insertNone (S ∩ T)).card
    (Finset.insertNone (S ∩ T)) H le_rfl le_rfl ?_ ?_
  · have hcost : ∑ o ∈ Finset.insertNone (S ∩ T), cost o = ∑ i ∈ S, wt M i := by
      rw [Finset.sum_insertNone]
      exact sum_split (fun i => wt M i) S T
    rw [hcost] at K
    refine has_mono _ _ _ H H _ _ ?_ le_rfl le_rfl K
    intro x _
    refine ⟨trivial, ?_⟩
    rw [Finset.sum_insertNone]
    show (∑ j ∈ S \ T, row j) x.1 + ∑ j ∈ S \ T, rhs j +
      ∑ i ∈ S ∩ T, (row i x.1 + rhs i) = 1
    rw [LinearMap.sum_apply, ← Finset.sum_add_distrib, sum_split (fun i => row i x.1 + rhs i) S T]
    exact sum_fail_of_oddDep row rhs S (best_S row rhs M S T hb).1 x.1
  · intro o ho h hex
    cases o with
    | none =>
      refine has_mono _ _ _ h h _ _ ?_ le_rfl le_rfl (block_top row rhs M S T hST hb g e h hE hex)
      rintro x ⟨_, hx⟩
      show ∑ i ∈ S \ T, (row i x.1 + rhs i) = 1
      have hx' : (∑ j ∈ S \ T, row j) x.1 + ∑ j ∈ S \ T, rhs j = 1 := hx
      rw [LinearMap.sum_apply, ← Finset.sum_add_distrib] at hx'
      exact hx'
    | some i =>
      have hi : i ∈ S ∩ T := by simpa using ho
      have hex' : Module.finrank (ZMod 2) (LinearMap.range (M i)) ≤ h := hex
      refine has_mono _ _ _ (Module.finrank (ZMod 2) (LinearMap.range (M i))) h _ _
        (fun x hx => hx) hex' (le_of_eq rfl)
        (has_read (okG row rhs M S T g) ((M i).comp (LinearMap.snd (ZMod 2) (Vec n) (Vec k)))
          (fun y => (i, y)) (Module.finrank (ZMod 2) (LinearMap.range (M i)))
          (LinearMap.range (M i)) 0 _ le_rfl ?_ ?_)
      · intro x _
        show M i x.2 - 0 ∈ LinearMap.range (M i)
        rw [sub_zero]
        exact LinearMap.mem_range_self _ _
      · rintro x ⟨_, hpi⟩
        have hpi' : row i x.1 + rhs i = 1 := hpi
        show (row i x.1 ≠ rhs i ∧ M i x.2 = M i x.2) ∧ (i, M i x.2) ∈ Bg M S T g
        refine ⟨⟨bw_z2_e _ _ hpi', rfl⟩, ?_⟩
        simp only [Bg, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨x.2, rfl, ?_⟩
        rcases cg_cases M S T g x.2 with hc | hc <;> rw [hc]
        · exact (Finset.mem_inter.1 hi).1
        · exact (Finset.mem_inter.1 hi).2
  · exact ⟨none, by simp⟩
  · rw [Finset.sum_insertNone]
    show 2 ^ e + ∑ i ∈ S ∩ T, 2 ^ Module.finrank (ZMod 2) (LinearMap.range (M i)) ≤ 2 ^ H
    have hw : ∑ i ∈ S ∩ T, 2 ^ Module.finrank (ZMod 2) (LinearMap.range (M i)) =
        ∑ i ∈ S ∩ T, wt M i := rfl
    omega

theorem final_fits (hb : Best2 row rhs M S T) (g : (Vec k ⧸ hidden M S T) → Bool) (H : ℕ)
    (K : Has (okG row rhs M S T g) (fun _ => True) H (∑ i ∈ S, wt M i)) :
    ∃ (N J : Finset (List Bool)) (q : List Bool → (Vec n × Vec k) → Bool)
      (out : List Bool → Fin m × Vec t),
      Cert (Queries (Vec n × Vec k)) (Answer row rhs M) N J q out ∧
      (N \ J).card = ∑ i ∈ S, wt M i ∧ (N \ J).image out = Bg M S T g ∧
      ∀ p ∈ N \ J, p.length ≤ H := by
  classical
  obtain ⟨N, J, q, out, hs, hq, hv, hd, hc⟩ := K
  have hlow : ∑ i ∈ S, wt M i ≤ (((N \ J).image out).filter (fun b => b ∈ Bg M S T g)).card := by
    apply card_lower M
    intro u
    obtain ⟨P, hPs, hPo⟩ : ∃ P : Finset (Fin m),
        P ⊆ Rset M (((N \ J).image out).filter (fun b => b ∈ Bg M S T g)) u ∧
          OddDep row rhs P := by
      refine exists_oddDep row rhs _ (fun x => ?_)
      obtain ⟨p, hp, hcons⟩ := exists_leaf N J q hs (x, u)
      obtain ⟨ha, hbg⟩ := hv p hp (x, u) trivial hcons
      refine ⟨(out p).1, ?_, ha.1⟩
      simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 : ((out p).1, M (out p).1 u) = out p := Prod.ext rfl ha.2.symm
      rw [h1]
      exact ⟨Finset.mem_image_of_mem out hp, hbg⟩
    exact le_trans ((best_S row rhs M S T hb).2 P hPo) (Finset.sum_le_sum_of_subset hPs)
  have hB0sub : ((N \ J).image out).filter (fun b => b ∈ Bg M S T g) ⊆ Bg M S T g :=
    fun b hb => (Finset.mem_filter.1 hb).2
  have hB0eq : ((N \ J).image out).filter (fun b => b ∈ Bg M S T g) = Bg M S T g :=
    Finset.eq_of_subset_of_card_le hB0sub (by rw [card_Bg row rhs M S T hb g]; exact hlow)
  have hB0B : ((N \ J).image out).filter (fun b => b ∈ Bg M S T g) ⊆ (N \ J).image out :=
    Finset.filter_subset _ _
  have hB'c : ((N \ J).image out).card ≤ (N \ J).card := Finset.card_image_le
  have hB0c := Finset.card_le_card hB0B
  have hB'eq : ((N \ J).image out).filter (fun b => b ∈ Bg M S T g) = (N \ J).image out :=
    Finset.eq_of_subset_of_card_le hB0B (by omega)
  refine ⟨N, J, q, out, ⟨hs, hq, fun p hp x hx => (hv p hp x trivial hx).1⟩, ?_, ?_, hd⟩
  · omega
  · rw [← hB'eq, hB0eq]

end Block

end PEqualNP.Outside.L_pcx_349_aux

theorem PEqualNP.Outside.L_pcx_349 : ∀ (n k t : ℕ),
  let X := Fin n → ZMod 2
  let U := Fin k → ZMod 2
  let Y := Fin t → ZMod 2
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let queries := fun (V : Type) [AddCommGroup V] [Module (ZMod 2) V] =>
    {f : V → Bool | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}
  let cert := fun {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
      (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) =>
    shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
      (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → ok x (out p)
  ∀ (m : ℕ) (row : Fin m → X →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
      (M : Fin m → U →ₗ[ZMod 2] Y),
    let oddDep := fun S : Finset (Fin m) => S.sum row = 0 ∧ S.sum rhs = 1
    let wt := fun i : Fin m => 2^(Module.finrank (ZMod 2) (LinearMap.range (M i)))
    let answer := fun (z : X × U) (a : Fin m × Y) => row a.1 z.1 ≠ rhs a.1 ∧ a.2 = M a.1 z.2
    let best := fun S : Finset (Fin m) => oddDep S ∧ ∀ T, oddDep T → S.sum wt ≤ T.sum wt
    ∀ S T : Finset (Fin m), S ≠ T → (∀ P, best P ↔ P = S ∨ P = T) →
      let C := (S ∩ T).sum wt
      let E := (S \ T).sum wt
      let fits := fun (B : Finset (Fin m × Y)) (bound : ℕ → Prop) =>
        ∃ (N J : Finset (List Bool)) (q : List Bool → (X × U) → Bool)
          (out : List Bool → Fin m × Y), cert (queries (X × U)) answer N J q out ∧
          (N \ J).card = S.sum wt ∧ (N \ J).image out = B ∧
          ∀ p ∈ N \ J, bound p.length
      ∀ H e : ℕ, E ≤ 2^e → C + 2^e ≤ 2^H → ∀ B,
        fits B (fun _ => True) → fits B (fun z => z ≤ H) := by
  intro n k t X U Y shape queries cert m row rhs M oddDep wt answer best S T hST hbest C E fits
    H e hE hCe B hB
  obtain ⟨N, J, q, out, hc, hcard, him, -⟩ := hB
  obtain ⟨g, hg⟩ := PEqualNP.Outside.L_pcx_349_aux.Bg_of_realizable row rhs M S T hST hbest B
    ⟨N, J, q, out, hc, hcard, him⟩
  have K := PEqualNP.Outside.L_pcx_349_aux.outer row rhs M S T hST hbest g H e hE hCe
  obtain ⟨N2, J2, q2, out2, hc2, hcard2, him2, hd2⟩ :=
    PEqualNP.Outside.L_pcx_349_aux.final_fits row rhs M S T hbest g H K
  exact ⟨N2, J2, q2, out2, hc2, hcard2, by rw [him2, hg], hd2⟩

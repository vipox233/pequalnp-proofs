import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_818_aux

open Matrix

theorem reduce {β : Type*} [Fintype β] (f : β → β) (x : β) :
    ∀ k, ∃ k' < Fintype.card β, f^[k'] x = f^[k] x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < Fintype.card β
    · exact ⟨k, hk, rfl⟩
    · push_neg at hk
      obtain ⟨a, b, hab, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
        (fun m : Fin (Fintype.card β + 1) => f^[m.val] x) (by simp)
      have key : ∀ a b : Fin (Fintype.card β + 1), a.val < b.val → f^[a.val] x = f^[b.val] x →
          ∃ k' < Fintype.card β, f^[k'] x = f^[k] x := by
        intro a b hlt hfe
        have hb := b.isLt
        have e : f^[k] x = f^[(k - b.val) + a.val] x := by
          conv_lhs => rw [show k = (k - b.val) + b.val by omega]
          rw [Function.iterate_add_apply, Function.iterate_add_apply, hfe]
        obtain ⟨k', hk', he'⟩ := ih ((k - b.val) + a.val) (by omega)
        exact ⟨k', hk', he'.trans e.symm⟩
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
      · exact key a b h he
      · exact key b a h he.symm

theorem alive {s : ℕ} (f : Option (Fin s) → Option (Fin s)) (hf : f none = none)
    (x : Option (Fin s)) (h : f^[s] x ≠ none) : ∀ k, f^[k] x ≠ none := by
  intro k hk
  obtain ⟨k', hk', he⟩ := reduce f x k
  simp only [Fintype.card_option, Fintype.card_fin] at hk'
  apply h
  have e : f^[s] x = f^[s - k'] (f^[k'] x) := by
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  rw [e, he, hk, Function.iterate_fixed hf]

def Nm {s : ℕ} (nx : Fin s → Option (Fin s)) : Matrix (Fin s) (Fin s) ℤ :=
  Matrix.of fun i j => if nx i = some j then 1 else 0

theorem pow_Nm {s : ℕ} (nx : Fin s → Option (Fin s)) (k : ℕ) :
    Nm nx ^ k = Matrix.of fun i j =>
      if (fun x : Option (Fin s) => x.bind nx)^[k] (some i) = some j then (1:ℤ) else 0 := by
  have hn : ∀ m, (fun x : Option (Fin s) => x.bind nx)^[m] none = none :=
    fun m => Function.iterate_fixed rfl m
  induction k with
  | zero => ext i j; simp [Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ', ih]
    ext i j
    rw [Matrix.mul_apply]
    simp only [Nm, Matrix.of_apply, Function.iterate_succ_apply]
    cases h : nx i with
    | none => simp [h, hn]
    | some l =>
      rw [Finset.sum_eq_single l]
      · simp [h]
      · intro b _ hb
        simp [h, Ne.symm hb]
      · simp

theorem det_term {s : ℕ} (nx : Fin s → Option (Fin s))
    (h : ∀ i, (fun x : Option (Fin s) => x.bind nx)^[s] (some i) = none) :
    (1 - Nm nx).det = 1 := by
  have hz : Nm nx ^ s = 0 := by
    rw [pow_Nm]; ext i j; simp [h i]
  have hnil : IsNilpotent (Nm nx) := ⟨s, hz⟩
  have hc := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hnil
  have hc' : (Nm nx).charpoly = Polynomial.X ^ Fintype.card (Fin s) :=
    sub_eq_zero.mp hc.eq_zero
  have := Matrix.eval_charpoly (Nm nx) 1
  rw [hc'] at this
  simp at this
  exact this.symm

theorem det_nt {s : ℕ} (nx : Fin s → Option (Fin s)) (i0 : Fin s)
    (h : (fun x : Option (Fin s) => x.bind nx)^[s] (some i0) ≠ none) :
    (1 - Nm nx).det = 0 := by
  classical
  set f := fun x : Option (Fin s) => x.bind nx with hfdef
  have hal := alive f rfl (some i0) h
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun l => if ∀ k, f^[k] (some l) ≠ none then (1:ℤ) else 0, ?_, ?_⟩
  · intro hy
    have := congrFun hy i0
    simp [hal] at this
  · ext l
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.zero_apply]
    simp only [Matrix.mulVec, dotProduct, Nm, Matrix.of_apply]
    cases hl : nx l with
    | none =>
      have : ¬ ∀ k, f^[k] (some l) ≠ none := fun H => H 1 (by simp [f, hl])
      simp [this]
    | some j =>
      have hstep : f (some l) = some j := by simp [f, hl]
      have : (∀ k, f^[k] (some l) ≠ none) ↔ (∀ k, f^[k] (some j) ≠ none) := by
        constructor
        · intro H k
          have := H (k+1)
          rwa [Function.iterate_succ_apply, hstep] at this
        · intro H k
          cases k with
          | zero => simp
          | succ k =>
            rw [Function.iterate_succ_apply, hstep]
            exact H k
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [hl, Ne.symm hb]) (by simp)]
      simp [hl, this]

theorem det_expand {s : ℕ} (n : Fin s → Bool → Option (Fin s)) :
    (Matrix.of fun i j : Fin s => ∑ b : Bool,
      ((if i = j then (1:ℤ) else 0) - if n i b = some j then 1 else 0)).det
      = ∑ p : Fin s → Bool, (1 - Nm (fun i => n i (p i))).det := by
  have key := (Matrix.detRowAlternating (n := Fin s) (R := ℤ)).toMultilinearMap.map_sum
    (fun (i : Fin s) (b : Bool) =>
      (fun j : Fin s => (if i = j then (1:ℤ) else 0) - if n i b = some j then 1 else 0))
  have e1 : (Matrix.of fun i j : Fin s => ∑ b : Bool,
      ((if i = j then (1:ℤ) else 0) - if n i b = some j then 1 else 0))
      = fun i => ∑ b : Bool,
        (fun j : Fin s => (if i = j then (1:ℤ) else 0) - if n i b = some j then 1 else 0) := by
    ext i j; simp [Finset.sum_apply]
  rw [e1]
  simp only [AlternatingMap.coe_multilinearMap] at key
  refine key.trans ?_
  refine Finset.sum_congr rfl (fun p _ => ?_)
  show Matrix.det _ = _
  congr 1

def stp {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (p : Fin s → Bool) (x : Option (Fin s)) :
    Option (Fin s) := x.bind (fun i => n i (p i))

theorem det_eq {s : ℕ} (n : Fin s → Bool → Option (Fin s)) :
    (Matrix.of fun i j : Fin s => ∑ b : Bool,
      ((if i = j then (1:ℤ) else 0) - if n i b = some j then 1 else 0)).det
      = (((Finset.univ : Finset (Fin s → Bool)).filter (fun p =>
          ∀ i : Fin s, (stp n p)^[s] (some i) = none)).card : ℤ) := by
  rw [det_expand, ← Finset.sum_boole]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases hp : ∀ i : Fin s, (stp n p)^[s] (some i) = none
  · rw [if_pos hp]
    exact det_term _ hp
  · rw [if_neg hp]
    push_neg at hp
    obtain ⟨i0, hi0⟩ := hp
    exact det_nt _ i0 hi0

theorem integral {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (g : Fin s → Bool → ℤ)
    (v : Fin s → ℝ) (hv : ∀ i, 2*v i = ∑ b : Bool, (n i b).elim (g i b : ℝ) v) (i : Fin s) :
    ∃ z : ℤ, (((Matrix.of fun i j : Fin s => ∑ b : Bool,
      ((if i = j then (1:ℤ) else 0) - if n i b = some j then 1 else 0)).det : ℤ) : ℝ) * v i = z := by
  set M : Matrix (Fin s) (Fin s) ℤ := Matrix.of fun i j : Fin s => ∑ b : Bool,
      ((if i = j then (1:ℤ) else 0) - if n i b = some j then 1 else 0) with hM
  set hh : Fin s → ℤ := fun i => ∑ b : Bool, (n i b).elim (g i b) (fun _ => 0) with hhh
  have hrow : ∀ (b : Bool) (i : Fin s), ∑ j : Fin s, (((if i = j then (1:ℤ) else 0) -
      if n i b = some j then 1 else 0 : ℤ) : ℝ) * v j = v i - (n i b).elim 0 v := by
    intro b i
    cases h : n i b with
    | none => simp
    | some l => simp [sub_mul, Finset.sum_sub_distrib]
  have hMv : (M.map (Int.cast : ℤ → ℝ)) *ᵥ v = fun i => (hh i : ℝ) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hM, Matrix.of_apply]
    push_cast
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have h1 := hrow true i
    have h2 := hrow false i
    push_cast at h1 h2
    rw [Fintype.sum_bool, h1, h2]
    have := hv i
    rw [Fintype.sum_bool] at this
    simp only [hhh, Fintype.sum_bool]
    cases ht : n i true <;> cases hf : n i false <;> simp [ht, hf] at this ⊢ <;> linarith
  have hadj := Matrix.adjugate_mul (M.map (Int.cast : ℤ → ℝ))
  have e : (M.map (Int.cast : ℤ → ℝ)).adjugate *ᵥ ((M.map (Int.cast : ℤ → ℝ)) *ᵥ v)
      = (M.map (Int.cast : ℤ → ℝ)).det • v := by
    rw [Matrix.mulVec_mulVec, hadj, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hdet : (M.map (Int.cast : ℤ → ℝ)).det = (M.det : ℝ) := by
    have := RingHom.map_det (Int.castRingHom ℝ) M
    simp only [RingHom.mapMatrix_apply, eq_intCast] at this
    exact this.symm
  have hadj' : (M.map (Int.cast : ℤ → ℝ)).adjugate = M.adjugate.map (Int.cast : ℤ → ℝ) := by
    have := RingHom.map_adjugate (Int.castRingHom ℝ) M
    simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom] at this
    exact this.symm
  refine ⟨∑ j, M.adjugate i j * hh j, ?_⟩
  have := congrFun e i
  rw [hMv, hdet, hadj'] at this
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.map_apply] at this
  rw [← this]
  push_cast
  rfl

theorem iter_none {s : ℕ} (n : Fin s → Bool → Option (Fin s)) (p : Fin s → Bool) (k : ℕ) :
    (stp n p)^[k] none = none := Function.iterate_fixed rfl k

theorem flip_ne {s : ℕ} (p : Fin s → Bool) (l : Fin s) : Function.update p l (!p l) ≠ p := by
  intro h
  have := congrFun h l
  simp at this

theorem ring_unique {s : ℕ} (hs : 0 < s) (n : Fin s → Bool → Option (Fin s))
    (perm : Equiv.Perm (Fin s)) (c : Fin s → Bool)
    (h1 : ∀ i, n i (c i) = some (perm i) ∧ n i (!(c i)) = none)
    (h2 : ∀ i j : Fin s, ∃ k < s, (perm : Fin s → Fin s)^[k] i = j) (p : Fin s → Bool) :
    ¬ (∀ i, (stp n p)^[s] (some i) = none) ↔ p = c := by
  constructor
  · intro hnt
    by_contra hpc
    apply hnt
    obtain ⟨i0, hi0⟩ : ∃ i0, p i0 ≠ c i0 := by
      by_contra H
      push_neg at H
      exact hpc (funext H)
    intro j
    obtain ⟨k, hk, hkj⟩ := h2 j i0
    have claim : ∀ m ≤ k, (stp n p)^[m] (some j) = some ((perm : Fin s → Fin s)^[m] j) ∨
        (stp n p)^[m] (some j) = none := by
      intro m
      induction m with
      | zero => intro _; left; rfl
      | succ m ih =>
        intro hm
        rcases ih (by omega) with h | h
        · rw [Function.iterate_succ_apply', h]
          by_cases hp : p ((perm : Fin s → Fin s)^[m] j) = c ((perm : Fin s → Fin s)^[m] j)
          · left
            show n _ (p _) = _
            rw [hp, (h1 _).1, Function.iterate_succ_apply']
          · right
            have : p ((⇑perm)^[m] j) = !c ((⇑perm)^[m] j) := by
              cases hq : p ((⇑perm)^[m] j) <;> cases hc : c ((⇑perm)^[m] j) <;> simp_all
            show n _ (p _) = _
            rw [this, (h1 _).2]
        · right
          rw [Function.iterate_succ_apply', h]
          rfl
    have hk1 : (stp n p)^[k+1] (some j) = none := by
      rw [Function.iterate_succ_apply']
      rcases claim k le_rfl with h | h
      · rw [h, hkj]
        have : p i0 = !c i0 := by
          cases hq : p i0 <;> cases hc : c i0 <;> simp_all
        show n _ (p _) = _
        rw [this, (h1 i0).2]
      · rw [h]
        rfl
    have e : (stp n p)^[s] (some j) = (stp n p)^[s - (k+1)] ((stp n p)^[k+1] (some j)) := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rw [e, hk1, iter_none]
  · intro hpc hall
    rw [hpc] at hall
    have hit : ∀ m i, (stp n c)^[m] (some i) = some ((perm : Fin s → Fin s)^[m] i) := by
      intro m
      induction m with
      | zero => intro i; rfl
      | succ m ih =>
        intro i
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
        have : stp n c (some i) = some (perm i) := (h1 i).1
        rw [this, ih]
    have := hall ⟨0, hs⟩
    rw [hit] at this
    exact Option.some_ne_none _ this

theorem unique_ring {s : ℕ} (hs : 0 < s) (n : Fin s → Bool → Option (Fin s)) (p0 : Fin s → Bool)
    (hu : ∀ p, ¬ (∀ i, (stp n p)^[s] (some i) = none) ↔ p = p0) :
    ∃ (perm : Equiv.Perm (Fin s)) (c : Fin s → Bool),
      (∀ i, n i (c i) = some (perm i) ∧ n i (!(c i)) = none) ∧
      ∀ i j : Fin s, ∃ k < s, (perm : Fin s → Fin s)^[k] i = j := by
  have hnt0 := (hu p0).mpr rfl
  push_neg at hnt0
  obtain ⟨i0, hi0⟩ := hnt0
  have hal0 := alive (stp n p0) rfl (some i0) hi0
  have visit : ∀ x : Fin s, (∀ k, (stp n p0)^[k] (some x) ≠ none) →
      ∀ l, ∃ k, (stp n p0)^[k] (some x) = some l := by
    intro x hx l
    by_contra H
    push_neg at H
    have hsame : ∀ k, (stp n (Function.update p0 l (!p0 l)))^[k] (some x)
        = (stp n p0)^[k] (some x) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        cases hy : (stp n p0)^[k] (some x) with
        | none => rfl
        | some y =>
          have hyl : y ≠ l := fun e => H k (by rw [hy, e])
          show n y (Function.update p0 l (!p0 l) y) = n y (p0 y)
          rw [Function.update_of_ne hyl]
    have hnt : ¬ (∀ i, (stp n (Function.update p0 l (!p0 l)))^[s] (some i) = none) := by
      intro hall
      exact hx s ((hsame s).symm.trans (hall x))
    exact flip_ne p0 l ((hu _).mp hnt)
  have hall : ∀ l, ∀ k, (stp n p0)^[k] (some l) ≠ none := by
    intro l k
    obtain ⟨k0, hk0⟩ := visit i0 hal0 l
    have := hal0 (k + k0)
    rwa [Function.iterate_add_apply, hk0] at this
  have hne : ∀ l, n l (p0 l) ≠ none := fun l => hall l 1
  let σ : Fin s → Fin s := fun l => (n l (p0 l)).get (Option.isSome_iff_ne_none.mpr (hne l))
  have hσ : ∀ l, n l (p0 l) = some (σ l) := fun l => (Option.some_get _).symm
  have hit : ∀ k x, (stp n p0)^[k] (some x) = some (σ^[k] x) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      have : stp n p0 (some x) = some (σ x) := hσ x
      rw [this, ih]
  have hreach : ∀ i j, ∃ k, σ^[k] i = j := by
    intro i j
    obtain ⟨k, hk⟩ := visit i (hall i) j
    rw [hit] at hk
    exact ⟨k, Option.some_injective _ hk⟩
  have hsurj : Function.Surjective σ := by
    intro j
    obtain ⟨k, hk⟩ := hreach (σ j) j
    refine ⟨σ^[k] j, ?_⟩
    rw [← Function.iterate_succ_apply' σ k j, Function.iterate_succ_apply]
    exact hk
  have hinj : Function.Injective σ := Finite.injective_iff_surjective.mpr hsurj
  refine ⟨Equiv.ofBijective σ ⟨hinj, hsurj⟩, p0, ?_, ?_⟩
  · intro l
    refine ⟨hσ l, ?_⟩
    by_contra hni
    have hnt : ¬ (∀ x, (stp n (Function.update p0 l (!p0 l)))^[s] (some x) = none) := by
      have hsome : ∀ y : Fin s, stp n (Function.update p0 l (!p0 l)) (some y) ≠ none := by
        intro y
        show n y (Function.update p0 l (!p0 l) y) ≠ none
        by_cases hy : y = l
        · subst hy
          rw [Function.update_self]
          exact hni
        · rw [Function.update_of_ne hy]
          exact hne y
      have hk : ∀ k, ∃ y, (stp n (Function.update p0 l (!p0 l)))^[k] (some l) = some y := by
        intro k
        induction k with
        | zero => exact ⟨l, rfl⟩
        | succ k ih =>
          obtain ⟨y, hy⟩ := ih
          rw [Function.iterate_succ_apply', hy]
          exact Option.ne_none_iff_exists'.mp (hsome y)
      intro hall'
      obtain ⟨y, hy⟩ := hk s
      rw [hall' l] at hy
      simp at hy
    exact flip_ne p0 l ((hu _).mp hnt)
  · intro i j
    obtain ⟨k, hk⟩ := hreach i j
    obtain ⟨k', hk', he⟩ := reduce σ i k
    simp only [Fintype.card_fin] at hk'
    exact ⟨k', hk', he.trans hk⟩

end PEqualNP.Outside.L_lib_818_aux

theorem PEqualNP.Outside.L_lib_818 : ∀ s : ℕ, 0 < s → ∀ n : Fin s → Bool → Option (Fin s),
  let step := fun (p : Fin s → Bool) (x : Option (Fin s)) => x.bind (fun i => n i (p i))
  let F := ((Finset.univ : Finset (Fin s → Bool)).filter (fun p =>
    ∀ i : Fin s, (step p)^[s] (some i) = none)).card
  let ring := ∃ (perm : Equiv.Perm (Fin s)) (c : Fin s → Bool),
    (∀ i, n i (c i) = some (perm i) ∧ n i (!(c i)) = none) ∧
    ∀ i j : Fin s, ∃ k < s, (perm : Fin s → Fin s)^[k] i = j
  0 < F → F ≤ 2^s ∧ (F+1 = 2^s ↔ ring) ∧
    ∀ (g : Fin s → Bool → ℤ) (v : Fin s → ℝ),
      (∀ i, 2*v i = ∑ b : Bool, (n i b).elim (g i b : ℝ) v) →
      ∀ i, ∃ z : ℤ, (F : ℝ)*v i = z := by
  intro s hs n step F ring _
  have hF : F = ((Finset.univ : Finset (Fin s → Bool)).filter (fun p =>
      ∀ i : Fin s, (PEqualNP.Outside.L_lib_818_aux.stp n p)^[s] (some i) = none)).card := rfl
  have hring : ring = ∃ (perm : Equiv.Perm (Fin s)) (c : Fin s → Bool),
      (∀ i, n i (c i) = some (perm i) ∧ n i (!(c i)) = none) ∧
      ∀ i j : Fin s, ∃ k < s, (perm : Fin s → Fin s)^[k] i = j := rfl
  rw [hring, hF]
  refine ⟨?_, ?_, ?_⟩
  · refine (Finset.card_filter_le _ _).trans ?_
    simp
  · have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin s → Bool)))
      (fun p => ∀ i : Fin s, (PEqualNP.Outside.L_lib_818_aux.stp n p)^[s] (some i) = none)
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hsum
    constructor
    · intro h
      have h1 : ((Finset.univ : Finset (Fin s → Bool)).filter (fun p =>
          ¬ ∀ i : Fin s, (PEqualNP.Outside.L_lib_818_aux.stp n p)^[s] (some i) = none)).card = 1 := by
        omega
      obtain ⟨p0, hp0⟩ := Finset.card_eq_one.mp h1
      apply PEqualNP.Outside.L_lib_818_aux.unique_ring hs n p0
      intro p
      have := Finset.ext_iff.mp hp0 p
      simpa using this
    · rintro ⟨perm, c, h1, h2⟩
      have h3 : ((Finset.univ : Finset (Fin s → Bool)).filter (fun p =>
          ¬ ∀ i : Fin s, (PEqualNP.Outside.L_lib_818_aux.stp n p)^[s] (some i) = none)).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨c, ?_⟩
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact PEqualNP.Outside.L_lib_818_aux.ring_unique hs n perm c h1 h2 p
      omega
  · intro g v hv i
    obtain ⟨z, hz⟩ := PEqualNP.Outside.L_lib_818_aux.integral n g v hv i
    refine ⟨z, ?_⟩
    rw [← hz, PEqualNP.Outside.L_lib_818_aux.det_eq]
    push_cast
    rfl

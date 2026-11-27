import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_721

open Finset Classical

/-! ## Semilinear helpers -/

theorem sl_exists {μ κ : Type} [Fintype μ] [Fintype κ] {S : Set (κ → ℕ)}
    (hS : IsSemilinearSet S) (F : (μ → ℕ) →ₗ[ℕ] (κ → ℕ)) (c b : κ → ℕ) :
    IsSemilinearSet {v : μ → ℕ | ∃ u ∈ S, c + u = b + F v} := by
  apply IsSemilinearSet.proj'
  have h1 : IsSemilinearSet {w : μ ⊕ κ → ℕ | w ∘ Sum.inr ∈ S} :=
    hS.preimage (LinearMap.funLeft ℕ ℕ (Sum.inr : κ → μ ⊕ κ))
  have h2 := isSemilinearSet_setOfPred_eq c b (LinearMap.funLeft ℕ ℕ (Sum.inr : κ → μ ⊕ κ))
    (F.comp (LinearMap.funLeft ℕ ℕ (Sum.inl : μ → μ ⊕ κ)))
  convert h1.inter h2 using 1
  ext x
  exact Iff.rfl

theorem sl_lt {ι : Type} [Fintype ι] (i j : ι) : IsSemilinearSet {v : ι → ℕ | v i < v j} := by
  have h := isSemilinearSet_setOfPred_eq (M := ι ⊕ Unit → ℕ) (1 : ℕ) 0
    (LinearMap.proj (R := ℕ) (φ := fun _ : ι ⊕ Unit => ℕ) (Sum.inl i) +
      LinearMap.proj (R := ℕ) (φ := fun _ : ι ⊕ Unit => ℕ) (Sum.inr ()))
    (LinearMap.proj (R := ℕ) (φ := fun _ : ι ⊕ Unit => ℕ) (Sum.inl j))
  have h2 := h.proj
  convert h2 using 1
  ext v
  simp only [Set.mem_ofPred_eq, LinearMap.add_apply, LinearMap.coe_proj, Function.eval,
    Sum.elim_inl, Sum.elim_inr, zero_add]
  constructor
  · intro hv
    exact ⟨fun _ => v j - v i - 1, by simp only; omega⟩
  · rintro ⟨y, hy⟩
    omega

theorem sl_eq {ι : Type} [Fintype ι] (i j : ι) : IsSemilinearSet {v : ι → ℕ | v i = v j} := by
  have h := isSemilinearSet_setOfPred_eq (M := ι → ℕ) (0 : ℕ) 0
    (LinearMap.proj i : (ι → ℕ) →ₗ[ℕ] ℕ) (LinearMap.proj j : (ι → ℕ) →ₗ[ℕ] ℕ)
  convert h using 1
  ext v
  simp

theorem sl_const {ι : Type} [Fintype ι] (i : ι) (t : ℕ) :
    IsSemilinearSet {v : ι → ℕ | v i = t} := by
  have h := isSemilinearSet_setOfPred_eq (M := ι → ℕ) (0 : ℕ) t
    (LinearMap.proj i : (ι → ℕ) →ₗ[ℕ] ℕ) (0 : (ι → ℕ) →ₗ[ℕ] ℕ)
  convert h using 1
  ext v
  simp

theorem sl_sm (N s : ℕ) :
    IsSemilinearSet {v : Fin N ⊕ Fin s → ℕ | StrictMono (fun j => v (Sum.inr j))} := by
  have h := IsSemilinearSet.biInter_finset
    (s := (univ : Finset (Fin s × Fin s)).filter (fun p => p.1 < p.2))
    (t := fun p => {v : Fin N ⊕ Fin s → ℕ | v (Sum.inr p.1) < v (Sum.inr p.2)})
    (fun p _ => sl_lt _ _)
  convert h using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, mem_filter, mem_univ, true_and, StrictMono]
  constructor
  · intro hv p hp
    exact hv hp
  · intro hv a b hab
    exact hv (a, b) hab

theorem sl_low (s a : ℕ) : IsSemilinearSet {d : Fin s → ℕ | ∃ j, d j ≤ a} := by
  have h := IsSemilinearSet.iUnion (fun j : Fin s =>
    IsSemilinearSet.iUnion (fun t : Fin (a + 1) => sl_const j t.val))
  convert h using 1
  ext d
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, ⟨d j, by omega⟩, rfl⟩
  · rintro ⟨j, t, ht⟩
    exact ⟨j, by have := t.2; omega⟩

/-! ## Binary sums -/

theorem half_pow_sum_nat (E : Finset ℕ) (M : ℕ) (hE : ∀ x ∈ E, x ≤ M) :
    (∑ x ∈ E, (1 / 2 : ℚ) ^ x) * 2 ^ M = ((∑ y ∈ E.image (fun x => M - x), 2 ^ y : ℕ) : ℚ) := by
  rw [sum_image (fun x hx y hy h => by have := hE x hx; have := hE y hy; omega)]
  push_cast
  rw [sum_mul]
  apply sum_congr rfl
  intro x hx
  have := hE x hx
  rw [show (2 : ℚ) ^ M = 2 ^ (M - x) * 2 ^ x by rw [← pow_add]; congr 1; omega]
  rw [one_div, inv_pow]
  field_simp

theorem uniq_fs (E D : Finset ℕ)
    (h : ∑ x ∈ E, (1 / 2 : ℚ) ^ x = ∑ x ∈ D, (1 / 2 : ℚ) ^ x) : E = D := by
  set M := (E ∪ D).sup id
  have hE : ∀ x ∈ E, x ≤ M := fun x hx => le_sup (f := id) (mem_union_left _ hx)
  have hD : ∀ x ∈ D, x ≤ M := fun x hx => le_sup (f := id) (mem_union_right _ hx)
  have h1 := half_pow_sum_nat E M hE
  have h2 := half_pow_sum_nat D M hD
  rw [h] at h1
  rw [h1] at h2
  have h3 : (∑ y ∈ E.image (fun x => M - x), 2 ^ y) = ∑ y ∈ D.image (fun x => M - x), 2 ^ y := by
    exact_mod_cast h2
  have h4 : E.image (fun x => M - x) = D.image (fun x => M - x) :=
    equivBitIndices.symm.injective h3
  ext x
  constructor
  · intro hx
    have : M - x ∈ D.image (fun x => M - x) := h4 ▸ mem_image_of_mem _ hx
    obtain ⟨y, hy, hxy⟩ := mem_image.1 this
    have := hD y hy
    have := hE x hx
    rwa [show x = y by omega]
  · intro hx
    have : M - x ∈ E.image (fun x => M - x) := h4 ▸ mem_image_of_mem _ hx
    obtain ⟨y, hy, hxy⟩ := mem_image.1 this
    have := hE y hy
    have := hD x hx
    rwa [show x = y by omega]

theorem sum_lt_two (D : Finset ℕ) : ∑ x ∈ D, (1 / 2 : ℚ) ^ x < 2 := by
  set M := D.sup id
  have hsub : D ⊆ range (M + 1) := fun x hx =>
    mem_range.2 (Nat.lt_succ_of_le (le_sup (f := id) hx))
  have hg : ∀ n, ∑ x ∈ range n, (1 / 2 : ℚ) ^ x = 2 - 2 * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring
  calc _ ≤ ∑ x ∈ range (M + 1), (1 / 2 : ℚ) ^ x :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ < 2 := by
        rw [hg]
        have : (0 : ℚ) < (1 / 2) ^ (M + 1) := by positivity
        linarith

theorem rhs_lt_two {s : ℕ} (d : Fin s → ℕ) (hd : StrictMono d) :
    ∑ j, (1 / 2 : ℚ) ^ (d j) < 2 := by
  have : ∑ j, (1 / 2 : ℚ) ^ (d j) = ∑ x ∈ univ.image d, (1 / 2 : ℚ) ^ x := by
    rw [sum_image (fun x _ y _ hxy => hd.injective hxy)]
  rw [this]
  exact sum_lt_two _

theorem perm_of_inj {N s : ℕ} (e : Fin N → ℕ) (d : Fin s → ℕ) (he : Function.Injective e)
    (hd : StrictMono d) (h : ∑ i, (1 / 2 : ℚ) ^ (e i) = ∑ j, (1 / 2 : ℚ) ^ (d j)) :
    ∃ π : Fin N ≃ Fin s, ∀ i, e i = d (π i) := by
  have hE : ∑ i, (1 / 2 : ℚ) ^ (e i) = ∑ x ∈ univ.image e, (1 / 2 : ℚ) ^ x := by
    rw [sum_image (fun x _ y _ hxy => he hxy)]
  have hD : ∑ j, (1 / 2 : ℚ) ^ (d j) = ∑ x ∈ univ.image d, (1 / 2 : ℚ) ^ x := by
    rw [sum_image (fun x _ y _ hxy => hd.injective hxy)]
  rw [hE, hD] at h
  have heq := uniq_fs _ _ h
  have hr : Set.range e = Set.range d := by
    have := congrArg (fun F : Finset ℕ => (F : Set ℕ)) heq
    simpa [coe_image] using this
  refine ⟨(Equiv.ofInjective e he).trans
    ((Set.equivOfEq hr).trans (Equiv.ofInjective d hd.injective).symm), fun i => ?_⟩
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_ofInjective_symm hd.injective]
  rfl

/-! ## The relation of sums of powers of one half -/

def Q (N s : ℕ) : Set (Fin N ⊕ Fin s → ℕ) :=
  {v | StrictMono (fun j => v (Sum.inr j)) ∧
    ∑ i, (1 / 2 : ℚ) ^ (v (Sum.inl i)) = ∑ j, (1 / 2 : ℚ) ^ (v (Sum.inr j))}

def Perm (N s : ℕ) : Set (Fin N ⊕ Fin s → ℕ) :=
  {v | StrictMono (fun j => v (Sum.inr j)) ∧
    ∃ π : Fin N ≃ Fin s, ∀ i, v (Sum.inl i) = v (Sum.inr (π i))}

theorem perm_sl (N s : ℕ) : IsSemilinearSet (Perm N s) := by
  have h := (sl_sm N s).inter (IsSemilinearSet.iUnion (fun π : Fin N ≃ Fin s =>
    IsSemilinearSet.iInter (fun i : Fin N =>
      sl_eq (ι := Fin N ⊕ Fin s) (Sum.inl i) (Sum.inr (π i)))))
  convert h using 1
  ext v
  simp [Perm]

theorem perm_sub (N s : ℕ) : Perm N s ⊆ Q N s := by
  rintro v ⟨h1, π, h2⟩
  refine ⟨h1, ?_⟩
  simp_rw [h2]
  exact Equiv.sum_comp π (fun j => (1 / 2 : ℚ) ^ (v (Sum.inr j)))

theorem Q_inj {N s : ℕ} (v : Fin N ⊕ Fin s → ℕ) (hv : v ∈ Q N s)
    (hi : Function.Injective (fun i => v (Sum.inl i))) : v ∈ Perm N s := by
  obtain ⟨h1, h2⟩ := hv
  obtain ⟨π, hπ⟩ := perm_of_inj _ _ hi h1 h2
  exact ⟨h1, π, hπ⟩

def tau (M s : ℕ) (i : Fin (M + 2)) (j : Fin (M + 1)) : Fin (M + 1) ⊕ Fin s → Fin (M + 2) ⊕ Fin s
  | Sum.inl t => Sum.inl (Fin.cases (motive := fun _ => Fin (M + 2)) i
      (fun t' => i.succAbove (j.succAbove t')) t)
  | Sum.inr r => Sum.inr r

def Dup (M s : ℕ) (i : Fin (M + 2)) (j : Fin (M + 1)) : Set (Fin (M + 2) ⊕ Fin s → ℕ) :=
  {v | v (Sum.inl i) = v (Sum.inl (i.succAbove j))} ∩
  {v | ∃ u ∈ Q (M + 1) s, (Pi.single (Sum.inl 0) 1 : Fin (M + 1) ⊕ Fin s → ℕ) + u =
    0 + LinearMap.funLeft ℕ ℕ (tau M s i j) v}

theorem sum_two_out {M : ℕ} (f : Fin (M + 2) → ℚ) (i : Fin (M + 2)) (j : Fin (M + 1)) :
    ∑ t, f t = f i + f (i.succAbove j) + ∑ t, f (i.succAbove (j.succAbove t)) := by
  rw [Fin.sum_univ_succAbove f i, Fin.sum_univ_succAbove (fun t => f (i.succAbove t)) j]
  ring

theorem dup_iff {M s : ℕ} (i : Fin (M + 2)) (j : Fin (M + 1)) (v : Fin (M + 2) ⊕ Fin s → ℕ)
    (u : Fin (M + 1) ⊕ Fin s → ℕ) (he : v (Sum.inl i) = v (Sum.inl (i.succAbove j)))
    (hu : (Pi.single (Sum.inl 0) 1 : Fin (M + 1) ⊕ Fin s → ℕ) + u =
      0 + LinearMap.funLeft ℕ ℕ (tau M s i j) v) : v ∈ Q (M + 2) s ↔ u ∈ Q (M + 1) s := by
  have h0 : 1 + u (Sum.inl 0) = v (Sum.inl i) := by
    have := congrFun hu (Sum.inl 0)
    simpa [LinearMap.funLeft, tau] using this
  have hs : ∀ t : Fin M, u (Sum.inl t.succ) = v (Sum.inl (i.succAbove (j.succAbove t))) := by
    intro t
    have := congrFun hu (Sum.inl t.succ)
    simpa [LinearMap.funLeft, tau, Pi.single_apply, Fin.succ_ne_zero] using this
  have hr : ∀ r : Fin s, u (Sum.inr r) = v (Sum.inr r) := by
    intro r
    have := congrFun hu (Sum.inr r)
    simpa [LinearMap.funLeft, tau, Pi.single_apply] using this
  have hsum : ∑ t, (1 / 2 : ℚ) ^ (v (Sum.inl t)) = ∑ t, (1 / 2 : ℚ) ^ (u (Sum.inl t)) := by
    rw [sum_two_out (fun t => (1 / 2 : ℚ) ^ (v (Sum.inl t))) i j, Fin.sum_univ_succ]
    simp only [hs, ← he, ← h0]
    rw [pow_add]
    ring
  simp only [Q, Set.mem_ofPred_eq, hsum, hr]

theorem dup_sub {M s : ℕ} (i : Fin (M + 2)) (j : Fin (M + 1)) : Dup M s i j ⊆ Q (M + 2) s := by
  rintro v ⟨he, u, hu, h⟩
  exact (dup_iff i j v u he h).2 hu

theorem Q_ss (M s : ℕ) : Q (M + 2) s = Perm (M + 2) s ∪ ⋃ i, ⋃ j, Dup M s i j := by
  apply Set.Subset.antisymm
  · intro v hv
    by_cases hi : Function.Injective (fun i => v (Sum.inl i))
    · exact Or.inl (Q_inj v hv hi)
    right
    simp only [Function.Injective, not_forall] at hi
    obtain ⟨a, b, hab, hne⟩ := hi
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (Ne.symm hne)
    have hab' : v (Sum.inl a) = v (Sum.inl (a.succAbove j)) := by rw [hj]; exact hab
    have hpos : 1 ≤ v (Sum.inl a) := by
      by_contra hc
      have h0 : v (Sum.inl a) = 0 := by omega
      have hlt := rhs_lt_two _ hv.1
      rw [← hv.2, sum_two_out _ a j, ← hab', h0] at hlt
      have : (0 : ℚ) ≤ ∑ t, (1 / 2 : ℚ) ^ (v (Sum.inl (a.succAbove (j.succAbove t)))) :=
        sum_nonneg (fun _ _ => by positivity)
      simp at hlt this
      linarith
    set u : Fin (M + 1) ⊕ Fin s → ℕ := fun w => v (tau M s a j w) -
      (Pi.single (Sum.inl 0) 1 : Fin (M + 1) ⊕ Fin s → ℕ) w with hu
    have hequ : (Pi.single (Sum.inl 0) 1 : Fin (M + 1) ⊕ Fin s → ℕ) + u =
        0 + LinearMap.funLeft ℕ ℕ (tau M s a j) v := by
      funext w
      simp only [hu, Pi.add_apply, zero_add, LinearMap.funLeft_apply, Function.comp_apply]
      rcases w with t | r
      · by_cases ht : t = 0
        · subst ht
          simp [tau]
          omega
        · simp [Pi.single_apply, ht]
      · simp [Pi.single_apply]
    simp only [Set.mem_iUnion]
    exact ⟨a, j, hab', u, (dup_iff a j v u hab' hequ).1 hv, hequ⟩
  · rintro v (hv | hv)
    · exact perm_sub _ _ hv
    · simp only [Set.mem_iUnion] at hv
      obtain ⟨i, j, h⟩ := hv
      exact dup_sub i j h

theorem Q_le1 (N s : ℕ) (hN : N ≤ 1) : Q N s = Perm N s := by
  apply Set.Subset.antisymm
  · intro v hv
    apply Q_inj v hv
    intro x y _
    apply Fin.ext
    omega
  · exact perm_sub N s

theorem Q_sl : (N : ℕ) → ∀ s, IsSemilinearSet (Q N s)
  | 0 => fun s => by rw [Q_le1 0 s (by omega)]; exact perm_sl _ _
  | 1 => fun s => by rw [Q_le1 1 s (by omega)]; exact perm_sl _ _
  | M + 2 => fun s => by
      rw [Q_ss]
      refine (perm_sl _ _).union (IsSemilinearSet.iUnion fun i => IsSemilinearSet.iUnion fun j => ?_)
      exact (sl_eq _ _).inter (sl_exists (Q_sl (M + 1) s) _ _ _)

theorem Q_card : (N : ℕ) → ∀ s, ∀ v ∈ Q N s, s ≤ N
  | 0 => fun s v hv => by
      rw [Q_le1 0 s (by omega)] at hv
      obtain ⟨_, π, _⟩ := hv
      have := Fintype.card_congr π
      simp at this
      omega
  | 1 => fun s v hv => by
      rw [Q_le1 1 s (by omega)] at hv
      obtain ⟨_, π, _⟩ := hv
      have := Fintype.card_congr π
      simp at this
      omega
  | M + 2 => fun s v hv => by
      rw [Q_ss] at hv
      rcases hv with ⟨_, π, _⟩ | hv
      · have := Fintype.card_congr π
        simp at this
        omega
      · simp only [Set.mem_iUnion] at hv
        obtain ⟨i, j, _, u, hu, _⟩ := hv
        have := Q_card (M + 1) s u hu
        omega

/-! ## Affine exponents -/

noncomputable def affF {τ ι : Type} [Fintype τ] [Fintype ι] (s N : ℕ) (eq : τ ≃ Fin N)
    (L : τ → ι → ℕ) : (Fin s ⊕ ι → ℕ) →ₗ[ℕ] (Fin N ⊕ Fin s → ℕ) :=
  LinearMap.pi (Sum.elim (fun i' => ∑ t, L (eq.symm i') t • LinearMap.proj (Sum.inr t))
    (fun j => LinearMap.proj (Sum.inl j)))

theorem aff_sl {τ ι : Type} [Fintype τ] [Fintype ι] (s : ℕ) (c : τ → ℕ) (L : τ → ι → ℕ) :
    IsSemilinearSet {d : Fin s → ℕ | ∃ m : ι → ℕ, StrictMono d ∧
      ∑ i, (1 / 2 : ℚ) ^ (c i + ∑ t, L i t * m t) = ∑ j, (1 / 2 : ℚ) ^ (d j)} := by
  set N := Fintype.card τ
  set eq := Fintype.equivFin τ
  have h := (sl_exists (Q_sl N s) (affF s N eq L) 0
    (Sum.elim (fun i' => c (eq.symm i')) (fun _ => 0))).proj
  convert h using 1
  ext d
  simp only [Set.mem_ofPred_eq, zero_add]
  constructor
  · rintro ⟨m, hd, hsum⟩
    refine ⟨m, _, ?_, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa [affF] using hd
    · simp only [affF, Pi.add_apply, LinearMap.pi_apply, Sum.elim_inl, Sum.elim_inr,
        LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
        smul_eq_mul, zero_add]
      rw [← hsum]
      exact Equiv.sum_comp eq.symm (fun i => (1 / 2 : ℚ) ^ (c i + ∑ t, L i t * m t))
  · rintro ⟨m, u, ⟨hu1, hu2⟩, rfl⟩
    refine ⟨m, ?_, ?_⟩
    · simpa [affF] using hu1
    · simp only [affF, Pi.add_apply, LinearMap.pi_apply, Sum.elim_inl, Sum.elim_inr,
        LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
        smul_eq_mul, zero_add] at hu2
      rw [← hu2]
      exact (Equiv.sum_comp eq.symm (fun i => (1 / 2 : ℚ) ^ (c i + ∑ t, L i t * m t))).symm

theorem aff_card {τ : Type} [Fintype τ] (s : ℕ) (e : τ → ℕ) (d : Fin s → ℕ) (hd : StrictMono d)
    (h : ∑ i, (1 / 2 : ℚ) ^ (e i) = ∑ j, (1 / 2 : ℚ) ^ (d j)) : s ≤ Fintype.card τ := by
  set eq := Fintype.equivFin τ
  apply Q_card (Fintype.card τ) s (Sum.elim (fun i' => e (eq.symm i')) d)
  refine ⟨by simpa using hd, ?_⟩
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [← h]
  exact Equiv.sum_comp eq.symm (fun i => (1 / 2 : ℚ) ^ (e i))

/-! ## Formulas over a general set of variables -/

abbrev ClV (V : Type) := (V × Bool) × (V × Bool)

noncomputable def satV {V : Type} (A : Finset (ClV V)) (x : V → Bool) : Prop :=
  ∀ c ∈ A, x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2

theorem massF_eq (n : ℕ) (A : Finset ((Fin n × Bool) × (Fin n × Bool))) :
    (univ.filter (fun x : Fin n → Bool => ∀ c ∈ A, x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2)) =
      univ.filter (satV A) := by
  ext x
  simp [satV]

abbrev Ty (k : ℕ) := Finset ((Fin k × Bool) × Bool)

noncomputable def allow {k : ℕ} (T : Ty k) (σ : Fin k → Bool) : Finset Bool :=
  univ.filter (fun b => ∀ p ∈ T, p.2 = b → σ p.1.1 ≠ p.1.2)

noncomputable def pcOf {V : Type} {k : ℕ} (ι : Fin k → V) (A : Finset (ClV V)) : Finset (ClV (Fin k)) :=
  univ.filter (fun c => ((ι c.1.1, c.1.2), (ι c.2.1, c.2.2)) ∈ A)

noncomputable def typOf {V : Type} {k : ℕ} (ι : Fin k → V) (A : Finset (ClV V)) (y : V) : Ty k :=
  univ.filter (fun p => ((ι p.1.1, p.1.2), (y, p.2)) ∈ A ∨ ((y, p.2), (ι p.1.1, p.1.2)) ∈ A)

theorem fiber_eq {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (ι : Fin k → V) (hι : Function.Injective ι)
    (A : Finset (ClV V))
    (hcov : ∀ c ∈ A, (c.1.1 = c.2.1 ∧ c.1.2 ≠ c.2.2) ∨ c.1.1 ∈ Set.range ι ∨
      c.2.1 ∈ Set.range ι)
    (σ : Fin k → Bool) (x : V → Bool) :
    (satV A x ∧ x ∘ ι = σ) ↔ (satV (pcOf ι A) σ ∧
      ∀ v, x v ∈ (if h : v ∈ Set.range ι then ({σ (Classical.choose h)} : Finset Bool)
        else allow (typOf ι A v) σ)) := by
  constructor
  · rintro ⟨hs, rfl⟩
    refine ⟨?_, ?_⟩
    · intro c hc
      simp only [pcOf, mem_filter, mem_univ, true_and] at hc
      exact hs _ hc
    · intro v
      split_ifs with hv
      · rw [mem_singleton, Function.comp_apply, Classical.choose_spec hv]
      · simp only [allow, mem_filter, mem_univ, true_and]
        intro p hp hpv
        simp only [typOf, mem_filter, mem_univ, true_and] at hp
        rcases hp with hp | hp
        · rcases hs _ hp with h | h
          · exact h
          · exact absurd hpv.symm h
        · rcases hs _ hp with h | h
          · exact absurd hpv.symm h
          · exact h
  · rintro ⟨hp, hx⟩
    have hxι : x ∘ ι = σ := by
      funext u
      have h0 : ι u ∈ Set.range ι := ⟨u, rfl⟩
      have := hx (ι u)
      rw [dif_pos h0, mem_singleton] at this
      rw [Function.comp_apply, this, hι (Classical.choose_spec h0)]
    refine ⟨?_, hxι⟩
    intro c hc
    have hxu : ∀ u, x (ι u) = σ u := fun u => congrFun hxι u
    by_cases h1 : c.1.1 ∈ Set.range ι <;> by_cases h2 : c.2.1 ∈ Set.range ι
    · obtain ⟨u, hu⟩ := h1
      obtain ⟨w, hw⟩ := h2
      have hm : ((u, c.1.2), (w, c.2.2)) ∈ pcOf ι A := by
        simp only [pcOf, mem_filter, mem_univ, true_and, hu, hw]
        exact hc
      have := hp _ hm
      rw [← hu, ← hw, hxu, hxu]
      exact this
    · obtain ⟨u, hu⟩ := h1
      have hm : ((u, c.1.2), c.2.2) ∈ typOf ι A c.2.1 := by
        simp only [typOf, mem_filter, mem_univ, true_and, hu]
        left
        exact hc
      have hal := hx c.2.1
      rw [dif_neg h2] at hal
      simp only [allow, mem_filter, mem_univ, true_and] at hal
      by_cases hx2 : x c.2.1 = c.2.2
      · left
        have := hal _ hm hx2.symm
        rw [← hu, hxu]
        exact this
      · right
        exact hx2
    · obtain ⟨w, hw⟩ := h2
      have hm : ((w, c.2.2), c.1.2) ∈ typOf ι A c.1.1 := by
        simp only [typOf, mem_filter, mem_univ, true_and, hw]
        right
        exact hc
      have hal := hx c.1.1
      rw [dif_neg h1] at hal
      simp only [allow, mem_filter, mem_univ, true_and] at hal
      by_cases hx1 : x c.1.1 = c.1.2
      · right
        have := hal _ hm hx1.symm
        rw [← hw, hxu]
        exact this
      · left
        exact hx1
    · rcases hcov c hc with ⟨he, hne⟩ | h | h
      · by_contra hh
        simp only [not_or, not_not] at hh
        apply hne
        rw [← hh.1, ← hh.2, he]
      · exact absurd h h1
      · exact absurd h h2

theorem core {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (ι : Fin k → V) (hι : Function.Injective ι)
    (A : Finset (ClV V))
    (hcov : ∀ c ∈ A, (c.1.1 = c.2.1 ∧ c.1.2 ≠ c.2.2) ∨ c.1.1 ∈ Set.range ι ∨
      c.2.1 ∈ Set.range ι) :
    (univ.filter (satV A)).card = ∑ σ : Fin k → Bool, if satV (pcOf ι A) σ then
      ∏ y ∈ univ.filter (fun y => y ∉ Set.range ι), (allow (typOf ι A y) σ).card else 0 := by
  rw [card_eq_sum_card_fiberwise (f := fun x => x ∘ ι) (t := univ) (fun _ _ => mem_univ _)]
  apply sum_congr rfl
  intro σ _
  have hfib : (univ.filter (satV A)).filter (fun x => x ∘ ι = σ) =
      if satV (pcOf ι A) σ then Fintype.piFinset (fun v => if h : v ∈ Set.range ι then
        ({σ (Classical.choose h)} : Finset Bool) else allow (typOf ι A v) σ) else ∅ := by
    ext x
    rw [mem_filter, mem_filter]
    have := fiber_eq ι hι A hcov σ x
    split_ifs with hP
    · rw [Fintype.mem_piFinset]
      simp only [mem_univ, true_and]
      rw [this]
      simp only [hP, true_and]
    · simp only [mem_univ, true_and]
      rw [this]
      simp [hP]
  rw [hfib]
  split_ifs with hP
  · rw [Fintype.card_piFinset, ← prod_filter_mul_prod_filter_not univ (fun v => v ∈ Set.range ι)]
    rw [prod_eq_one (fun v hv => by simp only [mem_filter] at hv; simp [hv.2]), one_mul]
    apply prod_congr rfl
    intro v hv
    simp only [mem_filter] at hv
    simp [hv.2]
  · simp

theorem group_prod {V : Type} {k : ℕ} {M : Type} [CommMonoid M] (Y : Finset V) (typ : V → Ty k)
    (f : Ty k → M) :
    ∏ y ∈ Y, f (typ y) = ∏ T, f T ^ (Y.filter (fun y => typ y = T)).card := by
  rw [← prod_fiberwise Y typ (fun y => f (typ y))]
  apply prod_congr rfl
  intro T _
  rw [prod_congr rfl (g := fun _ => f T) (fun y hy => by rw [(mem_filter.1 hy).2]), prod_const]

noncomputable def dens (k : ℕ) (P : Finset (ClV (Fin k))) (m : Ty k → ℕ) : ℚ :=
  (∑ σ : Fin k → Bool, if satV P σ then ∏ T, ((allow T σ).card : ℚ) ^ (m T) else 0) /
    2 ^ (k + ∑ T, m T)

theorem core_dens {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (ι : Fin k → V) (hι : Function.Injective ι)
    (A : Finset (ClV V))
    (hcov : ∀ c ∈ A, (c.1.1 = c.2.1 ∧ c.1.2 ≠ c.2.2) ∨ c.1.1 ∈ Set.range ι ∨
      c.2.1 ∈ Set.range ι) :
    ((univ.filter (satV A)).card : ℚ) / 2 ^ (Fintype.card V) =
      dens k (pcOf ι A) (fun T => ((univ.filter (fun y => y ∉ Set.range ι)).filter
        (fun y => typOf ι A y = T)).card) := by
  unfold dens
  have hcard : Fintype.card V = k + ∑ T, ((univ.filter (fun y => y ∉ Set.range ι)).filter
      (fun y => typOf ι A y = T)).card := by
    rw [← card_eq_sum_card_fiberwise (f := typOf ι A) (fun _ _ => mem_univ _)]
    rw [← card_univ, ← card_filter_add_card_filter_not (s := univ) (fun y => y ∈ Set.range ι)]
    congr 1
    have : univ.filter (fun y => y ∈ Set.range ι) = univ.image ι := by
      ext y
      simp
    rw [this, card_image_of_injective _ hι, card_univ, Fintype.card_fin]
  rw [hcard, core ι hι A hcov]
  congr 1
  push_cast
  apply sum_congr rfl
  intro σ _
  split_ifs
  · exact group_prod _ (typOf ι A) (fun T => ((allow T σ).card : ℚ))
  · rfl

/-! ## Packing and a bounded cover (as in L_lib_617) -/

abbrev Cl (n : ℕ) := ClV (Fin n)

noncomputable def taut {n : ℕ} (c : Cl n) : Prop := c.1.1 = c.2.1 ∧ c.1.2 ≠ c.2.2

noncomputable def cover {n : ℕ} (A : Finset (Cl n)) (C : Finset (Fin n)) : Prop :=
  ∀ c ∈ A, taut c ∨ c.1.1 ∈ C ∨ c.2.1 ∈ C

noncomputable def dj {n : ℕ} (a b : Cl n) : Prop :=
  b.1.1 ≠ a.1.1 ∧ b.1.1 ≠ a.2.1 ∧ b.2.1 ≠ a.1.1 ∧ b.2.1 ≠ a.2.1

noncomputable def upd {n : ℕ} (c : Cl n) (x : Fin n → Bool) : Fin n → Bool :=
  Function.update (Function.update x c.1.1 c.1.2) c.2.1 c.2.2

theorem step {n : ℕ} (P : Finset (Cl n)) (c : Cl n) (hc : ¬ taut c)
    (hd : ∀ a ∈ P, dj a c) :
    4 * (univ.filter (satV (insert c P))).card ≤ 3 * (univ.filter (satV P)).card := by
  classical
  set s := univ.filter (satV P) with hs
  have hsplit := card_filter_add_card_filter_not
    (s := s) (fun x => x c.1.1 = c.1.2 ∧ x c.2.1 = c.2.2)
  have hins : univ.filter (satV (insert c P)) =
      s.filter (fun x => ¬ (x c.1.1 = c.1.2 ∧ x c.2.1 = c.2.2)) := by
    ext x
    simp only [hs, mem_filter, mem_univ, true_and, satV, mem_insert, forall_eq_or_imp]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, fun ⟨e1, e2⟩ => by rcases h1 with h | h <;> contradiction⟩
    · rintro ⟨h2, h1⟩
      refine ⟨?_, h2⟩
      by_contra hh
      push Not at hh
      exact h1 hh
  have hinj : (s.filter (fun x => ¬ (x c.1.1 = c.1.2 ∧ x c.2.1 = c.2.2))).card ≤
      ((s.filter (fun x => x c.1.1 = c.1.2 ∧ x c.2.1 = c.2.2)) ×ˢ
        ((univ : Finset (Bool × Bool)).erase (c.1.2, c.2.2))).card := by
    apply card_le_card_of_injOn (fun x => (upd c x, (x c.1.1, x c.2.1)))
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq, hs, mem_filter, mem_univ, true_and] at hx
      simp only [coe_product, Set.mem_prod, mem_coe, mem_filter, hs, mem_univ, true_and,
        mem_erase, ne_eq, and_true]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · intro a ha
        have h := hd a ha
        obtain ⟨d1, d2, d3, d4⟩ := h
        have e1 : upd c x a.1.1 = x a.1.1 := by
          unfold upd
          rw [Function.update_of_ne (Ne.symm d3), Function.update_of_ne (Ne.symm d1)]
        have e2 : upd c x a.2.1 = x a.2.1 := by
          unfold upd
          rw [Function.update_of_ne (Ne.symm d4), Function.update_of_ne (Ne.symm d2)]
        rw [e1, e2]
        exact hx.1 a ha
      · unfold upd
        by_cases h : c.1.1 = c.2.1
        · have : c.1.2 = c.2.2 := by
            by_contra hh; exact hc ⟨h, hh⟩
          rw [h, Function.update_self, this]
        · rw [Function.update_of_ne h, Function.update_self]
      · unfold upd
        rw [Function.update_self]
      · intro h
        apply hx.2
        exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · intro x _ y _ hxy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨h1, h2, h3⟩ := hxy
      funext i
      by_cases hi1 : i = c.1.1
      · rw [hi1, h2]
      by_cases hi2 : i = c.2.1
      · rw [hi2, h3]
      have := congrFun h1 i
      unfold upd at this
      rwa [Function.update_of_ne hi2, Function.update_of_ne hi1,
        Function.update_of_ne hi2, Function.update_of_ne hi1] at this
  rw [card_product, card_erase_of_mem (mem_univ _), card_univ] at hinj
  simp only [Fintype.card_prod, Fintype.card_bool] at hinj
  rw [hins]
  omega

theorem pack_bound {n : ℕ} (P : Finset (Cl n)) (h1 : ∀ a ∈ P, ¬ taut a)
    (h2 : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → dj a b) :
    4 ^ P.card * (univ.filter (satV P)).card ≤ 3 ^ P.card * 2 ^ n := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    simp only [card_empty, pow_zero, one_mul]
    calc _ ≤ Fintype.card (Fin n → Bool) := card_le_univ _
      _ = 2 ^ n := by simp
  | insert c P hcP ih =>
    have ih' := ih (fun a ha => h1 a (mem_insert_of_mem ha))
      (fun a ha b hb hab => h2 a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab)
    have hs := step P c (h1 c (mem_insert_self c P))
      (fun a ha => h2 a (mem_insert_of_mem ha) c (mem_insert_self c P)
        (fun h => hcP (h ▸ ha)))
    rw [card_insert_of_notMem hcP, pow_succ, pow_succ]
    calc 4 ^ P.card * 4 * (univ.filter (satV (insert c P))).card
        = 4 ^ P.card * (4 * (univ.filter (satV (insert c P))).card) := by ring
      _ ≤ 4 ^ P.card * (3 * (univ.filter (satV P)).card) := Nat.mul_le_mul_left _ hs
      _ = 3 * (4 ^ P.card * (univ.filter (satV P)).card) := by ring
      _ ≤ 3 * (3 ^ P.card * 2 ^ n) := Nat.mul_le_mul_left _ ih'
      _ = 3 ^ P.card * 3 * 2 ^ n := by ring

theorem pow_ineq (a q : ℕ) : 2 ^ a * 3 ^ (3 * a + 3 + q) < 4 ^ (3 * a + 3 + q) := by
  have h1 : 2 ^ a * 27 ^ (a + 1) < 64 ^ (a + 1) := by
    induction a with
    | zero => norm_num
    | succ a ih =>
      calc 2 ^ (a + 1) * 27 ^ (a + 1 + 1) = 54 * (2 ^ a * 27 ^ (a + 1)) := by ring
        _ < 54 * 64 ^ (a + 1) := by omega
        _ ≤ 64 ^ (a + 1 + 1) := by rw [pow_succ 64 (a + 1)]; omega
  have h3 : 3 ^ q ≤ 4 ^ q := Nat.pow_le_pow_left (by norm_num) q
  have e1 : 3 ^ (3 * a + 3 + q) = 27 ^ (a + 1) * 3 ^ q := by
    rw [show 3 * a + 3 + q = 3 * (a + 1) + q by ring, pow_add, pow_mul]
    norm_num
  have e2 : 4 ^ (3 * a + 3 + q) = 64 ^ (a + 1) * 4 ^ q := by
    rw [show 3 * a + 3 + q = 3 * (a + 1) + q by ring, pow_add, pow_mul]
    norm_num
  calc 2 ^ a * 3 ^ (3 * a + 3 + q) = (2 ^ a * 27 ^ (a + 1)) * 3 ^ q := by rw [e1]; ring
    _ < 64 ^ (a + 1) * 3 ^ q := mul_lt_mul_of_pos_right h1 (by positivity)
    _ ≤ 64 ^ (a + 1) * 4 ^ q := Nat.mul_le_mul_left _ h3
    _ = _ := by rw [e2]

theorem cover_bound (a n : ℕ) (A : Finset (Cl n))
    (hA : 2 ^ n ≤ 2 ^ a * (univ.filter (satV A)).card) :
    ∃ C : Finset (Fin n), C.card ≤ 6 * a + 4 ∧ cover A C := by
  classical
  set Fam := A.powerset.filter (fun P => (∀ a ∈ P, ¬ taut a) ∧
    ∀ a ∈ P, ∀ b ∈ P, a ≠ b → dj a b) with hFam
  have hne : Fam.Nonempty := ⟨∅, by simp [hFam]⟩
  obtain ⟨P, hP, hmax⟩ := exists_max_image Fam card hne
  simp only [hFam, mem_filter, mem_powerset] at hP
  obtain ⟨hPA, hP1, hP2⟩ := hP
  set C := P.biUnion (fun a => ({a.1.1, a.2.1} : Finset (Fin n))) with hC
  have hPk : P.card ≤ 3 * a + 2 := by
    by_contra hh
    have hb := pack_bound P hP1 hP2
    have hmono : (univ.filter (satV A)).card ≤ (univ.filter (satV P)).card :=
      card_le_card (fun z hz => by
        simp only [mem_filter, mem_univ, true_and] at hz ⊢
        exact fun c hc => hz c (hPA hc))
    obtain ⟨q, hq⟩ : ∃ q, P.card = 3 * a + 3 + q := ⟨P.card - (3 * a + 3), by omega⟩
    have hpi := pow_ineq a q
    rw [← hq] at hpi
    have h1 : 4 ^ P.card * 2 ^ n ≤ 2 ^ a * 3 ^ P.card * 2 ^ n := by
      calc 4 ^ P.card * 2 ^ n ≤ 4 ^ P.card * (2 ^ a * (univ.filter (satV A)).card) :=
            Nat.mul_le_mul_left _ hA
        _ ≤ 4 ^ P.card * (2 ^ a * (univ.filter (satV P)).card) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hmono)
        _ = 2 ^ a * (4 ^ P.card * (univ.filter (satV P)).card) := by ring
        _ ≤ 2 ^ a * (3 ^ P.card * 2 ^ n) := Nat.mul_le_mul_left _ hb
        _ = 2 ^ a * 3 ^ P.card * 2 ^ n := by ring
    have h2 := Nat.le_of_mul_le_mul_right h1 (by positivity)
    exact absurd h2 (not_le.2 hpi)
  refine ⟨C, ?_, ?_⟩
  · calc C.card ≤ ∑ a ∈ P, ({a.1.1, a.2.1} : Finset (Fin n)).card := card_biUnion_le
      _ ≤ ∑ a ∈ P, 2 := sum_le_sum (fun a _ => card_le_two)
      _ = 2 * P.card := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ 6 * a + 4 := by omega
  · intro cl hcl
    by_cases ht : taut cl
    · exact Or.inl ht
    right
    by_contra hh
    simp only [not_or] at hh
    obtain ⟨h1, h2⟩ := hh
    have hclP : cl ∉ P := by
      intro hm
      apply h1
      rw [hC, mem_biUnion]
      exact ⟨cl, hm, by simp⟩
    have hmem : ∀ a ∈ P, a.1.1 ∈ C ∧ a.2.1 ∈ C := by
      intro a ha
      rw [hC]
      exact ⟨mem_biUnion.2 ⟨a, ha, by simp⟩, mem_biUnion.2 ⟨a, ha, by simp⟩⟩
    have hin : insert cl P ∈ Fam := by
      simp only [hFam, mem_filter, mem_powerset]
      refine ⟨insert_subset hcl hPA, ?_, ?_⟩
      · intro a ha
        rcases mem_insert.1 ha with h | h
        · exact h ▸ ht
        · exact hP1 a h
      · intro a ha b hb hab
        rcases mem_insert.1 ha with h | h <;> rcases mem_insert.1 hb with h' | h'
        · exact absurd (h.trans h'.symm) hab
        · subst h
          obtain ⟨m1, m2⟩ := hmem b h'
          exact ⟨fun e => h1 (e ▸ m1), fun e => h2 (e ▸ m1), fun e => h1 (e ▸ m2),
            fun e => h2 (e ▸ m2)⟩
        · subst h'
          obtain ⟨m1, m2⟩ := hmem a h
          exact ⟨fun e => h1 (e.symm ▸ m1), fun e => h1 (e.symm ▸ m2),
            fun e => h2 (e.symm ▸ m1), fun e => h2 (e.symm ▸ m2)⟩
        · exact hP2 a h b h' hab
    have := hmax _ hin
    rw [card_insert_of_notMem hclP] at this
    omega

theorem decomp (a n : ℕ) (A : Finset (ClV (Fin n)))
    (h : 2 ^ n ≤ 2 ^ a * (univ.filter (satV A)).card) :
    ∃ k, k ≤ 6 * a + 4 ∧ ∃ (P : Finset (ClV (Fin k))) (m : Ty k → ℕ),
      ((univ.filter (satV A)).card : ℚ) / 2 ^ n = dens k P m := by
  obtain ⟨C, hC, hcov⟩ := cover_bound a n A h
  refine ⟨C.card, hC, ?_⟩
  set ι : Fin C.card → Fin n := fun u => (C.equivFin.symm u : Fin n) with hιdef
  have hι : Function.Injective ι := fun u w h => C.equivFin.symm.injective (Subtype.ext h)
  have hr : ∀ y, y ∈ Set.range ι ↔ y ∈ C := by
    intro y
    constructor
    · rintro ⟨u, rfl⟩
      exact (C.equivFin.symm u).2
    · intro hy
      exact ⟨C.equivFin ⟨y, hy⟩, by simp [hιdef]⟩
  have := core_dens ι hι A (fun c hc => by
    rcases hcov c hc with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ((hr _).2 h))
    · exact Or.inr (Or.inr ((hr _).2 h)))
  rw [Fintype.card_fin] at this
  exact ⟨_, _, this⟩

/-! ## Realizing every profile -/

noncomputable def liftV {k : ℕ} {Z : Type} (c : ClV (Fin k)) : ClV (Fin k ⊕ Z) :=
  ((Sum.inl c.1.1, c.1.2), (Sum.inl c.2.1, c.2.2))

noncomputable def realV (k : ℕ) (P : Finset (ClV (Fin k))) (m : Ty k → ℕ) :
    Finset (ClV (Fin k ⊕ (Σ T : Ty k, Fin (m T)))) :=
  P.image liftV ∪ (univ : Finset (Σ T : Ty k, Fin (m T))).biUnion
    (fun z => z.1.image (fun p => ((Sum.inl p.1.1, p.1.2), (Sum.inr z, p.2))))

theorem real_pc (k : ℕ) (P : Finset (ClV (Fin k))) (m : Ty k → ℕ) :
    pcOf Sum.inl (realV k P m) = P := by
  ext c
  simp only [pcOf, realV, mem_filter, mem_univ, true_and, mem_union, mem_image, mem_biUnion]
  constructor
  · rintro (⟨c', hc', he⟩ | ⟨z, p, -, he⟩)
    · have : c' = c := by
        have e1 := congrArg (fun q => q.1.1) he
        have e2 := congrArg (fun q => q.1.2) he
        have e3 := congrArg (fun q => q.2.1) he
        have e4 := congrArg (fun q => q.2.2) he
        simp only [liftV, Sum.inl.injEq] at e1 e2 e3 e4
        exact Prod.ext (Prod.ext e1 e2) (Prod.ext e3 e4)
      exact this ▸ hc'
    · have e3 := congrArg (fun q => q.2.1) he
      simp at e3
  · intro hc
    exact Or.inl ⟨c, hc, rfl⟩

theorem real_typ (k : ℕ) (P : Finset (ClV (Fin k))) (m : Ty k → ℕ)
    (z : Σ T : Ty k, Fin (m T)) : typOf Sum.inl (realV k P m) (Sum.inr z) = z.1 := by
  ext p
  simp only [typOf, realV, mem_filter, mem_univ, true_and, mem_union, mem_image, mem_biUnion]
  constructor
  · rintro ((⟨c', -, he⟩ | ⟨z', p', hp', he⟩) | (⟨c', -, he⟩ | ⟨z', p', -, he⟩))
    · have e3 := congrArg (fun q => q.2.1) he
      simp [liftV] at e3
    · have e1 := congrArg (fun q => q.1.1) he
      have e2 := congrArg (fun q => q.1.2) he
      have e3 := congrArg (fun q => q.2.1) he
      have e4 := congrArg (fun q => q.2.2) he
      simp only [Sum.inl.injEq, Sum.inr.injEq] at e1 e2 e3 e4
      subst e3
      have : p' = p := Prod.ext (Prod.ext e1 e2) e4
      exact this ▸ hp'
    · have e1 := congrArg (fun q => q.1.1) he
      simp [liftV] at e1
    · have e1 := congrArg (fun q => q.1.1) he
      simp at e1
  · intro hp
    exact Or.inl (Or.inr ⟨z, p, hp, rfl⟩)

noncomputable def renC {V W : Type} (e : V ≃ W) (c : ClV V) : ClV W := ((e c.1.1, c.1.2), (e c.2.1, c.2.2))

theorem rename_mass {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] (e : V ≃ W) (A : Finset (ClV V)) :
    (univ.filter (satV (A.image (renC e)))).card = (univ.filter (satV A)).card := by
  let E : (W → Bool) ≃ (V → Bool) :=
    { toFun := fun x => x ∘ e
      invFun := fun y => y ∘ e.symm
      left_inv := fun x => by funext w; simp
      right_inv := fun y => by funext v; simp }
  apply card_equiv E
  intro x
  simp only [mem_filter, mem_univ, true_and, satV]
  constructor
  · intro hx c hc
    exact hx (renC e c) (mem_image_of_mem _ hc)
  · intro hy c hc
    obtain ⟨c', hc', rfl⟩ := mem_image.1 hc
    exact hy c' hc'

theorem realize (k : ℕ) (P : Finset (ClV (Fin k))) (m : Ty k → ℕ) :
    ∃ (n : ℕ) (A : Finset (ClV (Fin n))),
      ((univ.filter (satV A)).card : ℚ) / 2 ^ n = dens k P m := by
  have hcard : Fintype.card (Fin k ⊕ (Σ T : Ty k, Fin (m T))) = k + ∑ T, m T := by
    simp [Fintype.card_sigma]
  have hcov : ∀ c ∈ realV k P m, (c.1.1 = c.2.1 ∧ c.1.2 ≠ c.2.2) ∨
      c.1.1 ∈ Set.range (Sum.inl : Fin k → Fin k ⊕ (Σ T : Ty k, Fin (m T))) ∨
      c.2.1 ∈ Set.range (Sum.inl : Fin k → Fin k ⊕ (Σ T : Ty k, Fin (m T))) := by
    intro c hc
    simp only [realV, mem_union, mem_image, mem_biUnion, mem_univ, true_and] at hc
    rcases hc with ⟨c', _, rfl⟩ | ⟨z, p, _, rfl⟩
    · exact Or.inr (Or.inl ⟨_, rfl⟩)
    · exact Or.inr (Or.inl ⟨_, rfl⟩)
  have hcore := core (Sum.inl : Fin k → Fin k ⊕ (Σ T : Ty k, Fin (m T))) Sum.inl_injective
    (realV k P m) hcov
  rw [real_pc] at hcore
  have hY : univ.filter (fun y : Fin k ⊕ (Σ T : Ty k, Fin (m T)) =>
      y ∉ Set.range (Sum.inl : Fin k → Fin k ⊕ (Σ T : Ty k, Fin (m T)))) =
      univ.map Function.Embedding.inr := by
    ext y
    rcases y with u | z <;> simp
  have hprod : ∀ σ : Fin k → Bool, ∏ y ∈ univ.filter (fun y : Fin k ⊕ (Σ T : Ty k, Fin (m T)) =>
      y ∉ Set.range (Sum.inl : Fin k → Fin k ⊕ (Σ T : Ty k, Fin (m T)))),
      (allow (typOf Sum.inl (realV k P m) y) σ).card = ∏ T, (allow T σ).card ^ m T := by
    intro σ
    rw [hY, prod_map]
    simp only [Function.Embedding.inr_apply, real_typ]
    rw [Fintype.prod_sigma]
    simp
  have hcore' : (univ.filter (satV (realV k P m))).card = ∑ σ : Fin k → Bool,
      if satV P σ then ∏ T, (allow T σ).card ^ m T else 0 := by
    rw [hcore]
    apply sum_congr rfl
    intro σ _
    split_ifs
    · convert hprod σ
    · rfl
  refine ⟨Fintype.card (Fin k ⊕ (Σ T : Ty k, Fin (m T))),
    (realV k P m).image (renC (Fintype.equivFin _)), ?_⟩
  rw [rename_mass, hcore', hcard]
  unfold dens
  push_cast
  rfl

/-! ## The density as a sum of powers of one half -/

noncomputable def G (k : ℕ) (P : Finset (ClV (Fin k))) (Sup : Finset (Ty k)) : Finset (Fin k → Bool) :=
  univ.filter (fun σ => satV P σ ∧ ∀ T ∈ Sup, (allow T σ).card ≠ 0)

noncomputable def LL {k : ℕ} (Sup : Finset (Ty k)) (σ : Fin k → Bool) (T : Ty k) : ℕ :=
  if T ∈ Sup ∧ (allow T σ).card = 1 then 1 else 0

theorem allow_le {k : ℕ} (T : Ty k) (σ : Fin k → Bool) : (allow T σ).card ≤ 2 := by
  calc _ ≤ (univ : Finset Bool).card := card_le_univ _
    _ = 2 := by simp

theorem factor {k : ℕ} (Sup : Finset (Ty k)) (σ : Fin k → Bool) (T : Ty k) (m' : Ty k → ℕ)
    (hT : T ∈ Sup → (allow T σ).card ≠ 0) :
    ((allow T σ).card : ℚ) ^ (if T ∈ Sup then 1 + m' T else 0) =
      2 ^ (if T ∈ Sup then 1 + m' T else 0) * (1 / 2 : ℚ) ^ (LL Sup σ T * (1 + m' T)) := by
  unfold LL
  by_cases hs : T ∈ Sup
  · have h0 := hT hs
    have h2 := allow_le T σ
    rcases (show (allow T σ).card = 1 ∨ (allow T σ).card = 2 by omega) with h | h
    · simp only [hs, h, and_self, if_true, Nat.cast_one, one_pow, one_mul]
      rw [← mul_pow]
      norm_num
    · simp [hs, h]
  · simp [hs]

theorem dens_eq (k : ℕ) (P : Finset (ClV (Fin k))) (Sup : Finset (Ty k)) (m' : Ty k → ℕ) :
    dens k P (fun T => if T ∈ Sup then 1 + m' T else 0) =
      ∑ σ ∈ G k P Sup, (1 / 2 : ℚ) ^ ((k + ∑ T, LL Sup σ T) + ∑ T, LL Sup σ T * m' T) := by
  unfold dens G
  beta_reduce
  rw [sum_filter, sum_div]
  apply sum_congr rfl
  intro σ _
  by_cases hP : satV P σ
  · by_cases hz : ∀ T ∈ Sup, (allow T σ).card ≠ 0
    · rw [if_pos hP, if_pos ⟨hP, hz⟩]
      rw [prod_congr rfl (fun T _ => factor Sup σ T m' (hz T)), prod_mul_distrib,
        prod_pow_eq_pow_sum, prod_pow_eq_pow_sum]
      have hexp : (k + ∑ T, LL Sup σ T) + ∑ T, LL Sup σ T * m' T =
          k + ∑ T, LL Sup σ T * (1 + m' T) := by
        rw [add_assoc, ← sum_add_distrib]
        congr 1
        apply sum_congr rfl
        intro T _
        ring
      rw [hexp, pow_add, pow_add]
      field_simp
      rw [← mul_pow]
      norm_num
    · rw [if_pos hP, if_neg (fun h => hz h.2)]
      have : ∏ T, ((allow T σ).card : ℚ) ^ (if T ∈ Sup then 1 + m' T else 0) = 0 := by
        simp only [not_forall, not_not] at hz
        obtain ⟨T, hT, h0⟩ := hz
        apply prod_eq_zero (mem_univ T)
        rw [if_pos hT, h0]
        simp
      rw [this, zero_div]
  · rw [if_neg hP, if_neg (fun h => hP h.1), zero_div]

/-! ## Assembly -/

noncomputable def Spec (a s : ℕ) (d : Fin s → ℕ) : Prop :=
  StrictMono d ∧ (∃ j : Fin s, d j ≤ a) ∧
    ∃ (n : ℕ) (A : Finset ((Fin n × Bool) × (Fin n × Bool))),
      ((univ.filter (satV A)).card : ℚ) / 2 ^ n = ∑ j : Fin s, (1 : ℚ) / 2 ^ (d j)

noncomputable def Ycfg (a s k : ℕ) (P : Finset (ClV (Fin k))) (Sup : Finset (Ty k)) : Set (Fin s → ℕ) :=
  {d | ∃ m' : Ty k → ℕ, StrictMono d ∧
    ∑ σ : ↥(G k P Sup), (1 / 2 : ℚ) ^ ((k + ∑ T, LL Sup σ.1 T) + ∑ T, LL Sup σ.1 T * m' T) =
      ∑ j, (1 / 2 : ℚ) ^ (d j)} ∩ {d | ∃ j, d j ≤ a}

theorem ycfg_sl (a s k : ℕ) (P : Finset (ClV (Fin k))) (Sup : Finset (Ty k)) :
    IsSemilinearSet (Ycfg a s k P Sup) :=
  (aff_sl s (fun σ : ↥(G k P Sup) => k + ∑ T, LL Sup σ.1 T)
    (fun σ T => LL Sup σ.1 T)).inter (sl_low s a)

theorem conv_sum {s : ℕ} (d : Fin s → ℕ) :
    ∑ j, (1 : ℚ) / 2 ^ (d j) = ∑ j, (1 / 2 : ℚ) ^ (d j) :=
  sum_congr rfl (fun j _ => by rw [one_div_pow])

theorem spec_sub (a s : ℕ) (d : Fin s → ℕ) (h : Spec a s d) :
    ∃ k, k ≤ 6 * a + 4 ∧ ∃ (P : Finset (ClV (Fin k))) (Sup : Finset (Ty k)),
      d ∈ Ycfg a s k P Sup := by
  obtain ⟨hsm, ⟨j0, hj0⟩, n, A, hA⟩ := h
  rw [conv_sum] at hA
  have hlow : (1 / 2 : ℚ) ^ a ≤ ((univ.filter (satV A)).card : ℚ) / 2 ^ n := by
    rw [hA]
    calc (1 / 2 : ℚ) ^ a ≤ (1 / 2) ^ (d j0) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hj0
      _ ≤ _ := single_le_sum (f := fun j => (1 / 2 : ℚ) ^ (d j)) (fun j _ => by positivity)
          (mem_univ j0)
  have hmass : 2 ^ n ≤ 2 ^ a * (univ.filter (satV A)).card := by
    have h2n : (0 : ℚ) < 2 ^ n := by positivity
    rw [le_div_iff₀ h2n] at hlow
    have : ((2 ^ n : ℕ) : ℚ) ≤ ((2 ^ a * (univ.filter (satV A)).card : ℕ) : ℚ) := by
      push_cast
      have h2a : (2 : ℚ) ^ a * (1 / 2) ^ a = 1 := by rw [← mul_pow]; norm_num
      calc (2 : ℚ) ^ n = 2 ^ a * ((1 / 2) ^ a * 2 ^ n) := by rw [← mul_assoc, h2a, one_mul]
        _ ≤ _ := by gcongr
    exact_mod_cast this
  obtain ⟨k, hk, P, m, hd⟩ := decomp a n A hmass
  set Sup : Finset (Ty k) := univ.filter (fun T => m T ≠ 0) with hSup
  have hm : (fun T => if T ∈ Sup then 1 + (m T - 1) else 0) = m := by
    funext T
    by_cases h : m T = 0
    · simp [hSup, h]
    · rw [if_pos (by simp [hSup, h])]
      omega
  have hd' : ((univ.filter (satV A)).card : ℚ) / 2 ^ n =
      dens k P (fun T => if T ∈ Sup then 1 + (m T - 1) else 0) := by
    rw [hm]
    exact hd
  refine ⟨k, hk, P, Sup, ⟨fun T => m T - 1, hsm, ?_⟩, ⟨j0, hj0⟩⟩
  rw [← hA, hd', dens_eq]
  exact sum_coe_sort (G k P Sup) (fun σ => (1 / 2 : ℚ) ^ ((k + ∑ T, LL Sup σ T) +
    ∑ T, LL Sup σ T * (m T - 1)))

theorem sub_spec (a s k : ℕ) (P : Finset (ClV (Fin k))) (Sup : Finset (Ty k)) (d : Fin s → ℕ)
    (h : d ∈ Ycfg a s k P Sup) : Spec a s d := by
  obtain ⟨⟨m', hsm, hsum⟩, hlow⟩ := h
  obtain ⟨n, A, hA⟩ := realize k P (fun T => if T ∈ Sup then 1 + m' T else 0)
  refine ⟨hsm, hlow, n, A, ?_⟩
  rw [hA, dens_eq, conv_sum, ← hsum]
  exact (sum_coe_sort _ _).symm

theorem main (a s : ℕ) : IsSemilinearSet {d : Fin s → ℕ | Spec a s d} ∧
    ∀ d, Spec a s d → s ≤ 2 ^ (6 * (a + 1)) := by
  constructor
  · have h := IsSemilinearSet.iUnion (fun k : Fin (6 * a + 5) =>
      IsSemilinearSet.iUnion (fun P : Finset (ClV (Fin k.val)) =>
        IsSemilinearSet.iUnion (fun Sup : Finset (Ty k.val) => ycfg_sl a s k.val P Sup)))
    convert h using 1
    ext d
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hd
      obtain ⟨k, hk, P, Sup, hm⟩ := spec_sub a s d hd
      exact ⟨⟨k, by omega⟩, P, Sup, hm⟩
    · rintro ⟨k, P, Sup, hm⟩
      exact sub_spec a s k.val P Sup d hm
  · intro d hd
    obtain ⟨k, hk, P, Sup, ⟨m', hsm, hsum⟩, _⟩ := spec_sub a s d hd
    have h1 := aff_card s _ d hsm hsum
    have h2 : Fintype.card ↥(G k P Sup) ≤ 2 ^ k := by
      rw [Fintype.card_coe]
      calc (G k P Sup).card ≤ (univ : Finset (Fin k → Bool)).card := card_le_univ _
        _ = 2 ^ k := by simp
    have h3 : 2 ^ k ≤ 2 ^ (6 * (a + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end PEqualNP.Outside.L_lib_721

open PEqualNP.Outside.L_lib_721 in
theorem PEqualNP.Outside.L_lib_721 : let mass := fun (n : ℕ) (A : Finset ((Fin n × Bool) × (Fin n × Bool))) =>
  (Finset.univ.filter (fun x : Fin n → Bool => ∀ c ∈ A,
    x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2)).card
∀ a s : ℕ,
  let spectrum := fun depths : Fin s → ℕ =>
    StrictMono depths ∧ (∃ j : Fin s, depths j ≤ a) ∧
      ∃ (n : ℕ) (A : Finset ((Fin n × Bool) × (Fin n × Bool))),
        (mass n A : ℚ) / 2 ^ n = ∑ j : Fin s, (1 : ℚ) / 2 ^ (depths j)
  IsSemilinearSet {x : Fin s → ℕ | spectrum x} ∧
    (∀ x : Fin s → ℕ, spectrum x → s ≤ 2 ^ (6 * (a + 1))) := by
  intro mass a s spectrum
  have key : ∀ d : Fin s → ℕ, spectrum d ↔ Spec a s d := by
    intro d
    simp only [spectrum, mass, Spec, massF_eq]
  have hset : {x : Fin s → ℕ | spectrum x} = {d | Spec a s d} := by
    ext d
    exact key d
  obtain ⟨h1, h2⟩ := main a s
  exact ⟨hset ▸ h1, fun x hx => h2 x ((key x).1 hx)⟩

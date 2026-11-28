import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25732

open Classical

def fitsDef (q s : ℕ) (G : Fin s → Fin s → Bool) (budget : ℕ) : Prop :=
  ∃ (π : Equiv.Perm (Fin s)) (rf cf : Fin s → Bool) (R C : Fin q → Finset (Fin s))
    (out : Finset (Fin s) → (Fin q → Bool) → Bool),
    ((Finset.univ : Finset (Fin s × Fin s)).filter (fun z =>
      out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
        Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ budget

def blowup {n : ℕ} (hn : 0 < n) (G : Fin n → Fin n → Bool) (b : ℕ) :
    Fin (n * b) → Fin (n * b) → Bool :=
  fun i j => G ⟨i.val % n, Nat.mod_lt _ hn⟩ ⟨j.val % n, Nat.mod_lt _ hn⟩

noncomputable def optDef {n : ℕ} (hn : 0 < n) (q : ℕ) (G : Fin n → Fin n → Bool) (b : ℕ) : ℕ :=
  sInf {e : ℕ | fitsDef q (n * b) (blowup hn G b) e}

-- Part 1: Exactness for q ≥ n

lemma fitsDef_zero_of_ge {n q : ℕ} (hn : 0 < n) (hq : n ≤ q) (G : Fin n → Fin n → Bool) (b : ℕ) :
    fitsDef q (n * b) (blowup hn G b) 0 := by
  let R : Fin q → Finset (Fin (n * b)) := fun j =>
    if j.val < n then Finset.univ.filter (fun u : Fin (n * b) => u.val % n = j.val) else ∅
  let C : Fin q → Finset (Fin (n * b)) := fun _ => ∅
  let out : Finset (Fin (n * b)) → (Fin q → Bool) → Bool := fun S sig =>
    if h : ∃ z : Fin (n * b) × Fin (n * b),
        ({z.1, z.2} : Finset (Fin (n * b))) = S ∧
        (fun j : Fin q => decide (z.1 ∈ R j)) = sig
    then blowup hn G b h.choose.1 h.choose.2 else false
  refine ⟨Equiv.refl _, fun _ => false, fun _ => false, R, C, out, ?_⟩
  have hfilt : ((Finset.univ : Finset (Fin (n * b) × Fin (n * b))).filter (fun z =>
      out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ (Equiv.refl _) z.2 ∈ C j)) ≠
        Bool.xor (blowup hn G b z.1 ((Equiv.refl _) z.2))
          (Bool.xor false false))) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro z _
    simp only [Equiv.refl_apply, C, Finset.notMem_empty, or_false, Bool.xor_false, not_not]
    have hex : ∃ w : Fin (n * b) × Fin (n * b),
        ({w.1, w.2} : Finset (Fin (n * b))) = {z.1, z.2} ∧
        (fun j : Fin q => decide (w.1 ∈ R j)) = (fun j : Fin q => decide (z.1 ∈ R j)) :=
      ⟨z, rfl, rfl⟩
    dsimp only [out]
    rw [dif_pos hex]
    have hw := hex.choose_spec
    set w := hex.choose
    have h1 : w.1.val % n = z.1.val % n := by
      let j₀ : Fin q := ⟨z.1.val % n, lt_of_lt_of_le (Nat.mod_lt _ hn) hq⟩
      have hj := congrFun hw.2 j₀
      have hzR : z.1 ∈ R j₀ := by
        simp [R, j₀, Nat.mod_lt _ hn]
      have hwR : w.1 ∈ R j₀ := by
        have : decide (w.1 ∈ R j₀) = true := by rw [hj]; exact decide_eq_true hzR
        exact of_decide_eq_true this
      simpa [R, j₀, Nat.mod_lt _ hn] using hwR
    have h2 : w.2.val % n = z.2.val % n := by
      have hm1 : w.2 ∈ ({z.1, z.2} : Finset (Fin (n * b))) := by
        rw [← hw.1]; simp
      have hm2 : z.2 ∈ ({w.1, w.2} : Finset (Fin (n * b))) := by
        rw [hw.1]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
      rcases hm1 with hw2z1 | hw2z2
      · rcases hm2 with hz2w1 | hz2w2
        · rw [hw2z1, ← h1, ← hz2w1]
        · rw [hz2w2]
      · rw [hw2z2]
    dsimp only [blowup]
    congr 1 <;> exact Fin.ext (by assumption)
  rw [hfilt, Finset.card_empty]

lemma optDef_eq_zero_of_ge {n q : ℕ} (hn : 0 < n) (hq : n ≤ q) (G : Fin n → Fin n → Bool) (b : ℕ) :
    optDef hn q G b = 0 := by
  exact Nat.eq_zero_of_le_zero (Nat.sInf_le (fitsDef_zero_of_ge hn hq G b))

-- Part 2: Exact type-count reformulation

abbrev VType (n q : ℕ) : Type :=
  Fin n × Fin n × Bool × Bool × (Fin q → Bool) × (Fin q → Bool)

def vtA {n q : ℕ} (t : VType n q) : Fin n := t.1
def vtB {n q : ℕ} (t : VType n q) : Fin n := t.2.1
def vtRf {n q : ℕ} (t : VType n q) : Bool := t.2.2.1
def vtCf {n q : ℕ} (t : VType n q) : Bool := t.2.2.2.1
def vtR {n q : ℕ} (t : VType n q) : Fin q → Bool := t.2.2.2.2.1
def vtC {n q : ℕ} (t : VType n q) : Fin q → Bool := t.2.2.2.2.2

def sigT {n q : ℕ} (t₁ t₂ : VType n q) : Fin q → Bool :=
  fun j => vtR t₁ j || vtC t₂ j

def valT {n q : ℕ} (G : Fin n → Fin n → Bool) (t₁ t₂ : VType n q) : Bool :=
  Bool.xor (G (vtA t₁) (vtB t₂)) (Bool.xor (vtRf t₁) (vtCf t₂))

def kerK {n q : ℕ} (G : Fin n → Fin n → Bool) (t₁ t₂ : VType n q) : ℕ :=
  if sigT t₁ t₂ = sigT t₂ t₁ ∧ valT G t₁ t₂ ≠ valT G t₂ t₁ then 1 else 0

lemma kerK_symm {n q : ℕ} (G : Fin n → Fin n → Bool) (t₁ t₂ : VType n q) :
    kerK G t₁ t₂ = kerK G t₂ t₁ := by
  dsimp only [kerK]
  by_cases h : sigT t₁ t₂ = sigT t₂ t₁ ∧ valT G t₁ t₂ ≠ valT G t₂ t₁
  · have h' : sigT t₂ t₁ = sigT t₁ t₂ ∧ valT G t₂ t₁ ≠ valT G t₁ t₂ :=
      ⟨h.1.symm, h.2.symm⟩
    rw [if_pos h, if_pos h']
  · have h' : ¬(sigT t₂ t₁ = sigT t₁ t₂ ∧ valT G t₂ t₁ ≠ valT G t₁ t₂) :=
      fun ⟨h1, h2⟩ => h ⟨h1.symm, h2.symm⟩
    rw [if_neg h, if_neg h']

lemma kerK_self {n q : ℕ} (G : Fin n → Fin n → Bool) (t : VType n q) :
    kerK G t t = 0 := by
  simp [kerK]

lemma kerK_le_one {n q : ℕ} (G : Fin n → Fin n → Bool) (t₁ t₂ : VType n q) :
    kerK G t₁ t₂ ≤ 1 := by
  dsimp only [kerK]; split_ifs <;> omega

def quadNat {n q : ℕ} (G : Fin n → Fin n → Bool) (N : VType n q → ℕ) : ℕ :=
  ∑ t₁ : VType n q, ∑ t₂ : VType n q, kerK G t₁ t₂ * N t₁ * N t₂

def ValidInt {n q : ℕ} (b : ℕ) (N : VType n q → ℕ) : Prop :=
  (∀ i : Fin n, ∑ t : VType n q, (if vtA t = i then N t else 0) = b) ∧
  (∀ j : Fin n, ∑ t : VType n q, (if vtB t = j then N t else 0) = b)

lemma card_mod_eq {n : ℕ} (hn : 0 < n) (b : ℕ) (i : Fin n) :
    (Finset.univ.filter (fun u : Fin (n * b) => u.val % n = i.val)).card = b := by
  have heq : Fintype.card {u : Fin (n * b) // u.val % n = i.val} = b := by
    let eqv : {u : Fin (n * b) // u.val % n = i.val} ≃ Fin b :=
      { toFun := fun u => ⟨u.val.val / n, (Nat.div_lt_iff_lt_mul hn).mpr (by rw [mul_comm b n]; exact u.val.isLt)⟩
        invFun := fun k => ⟨⟨k.val * n + i.val, by
          have hk : k.val + 1 ≤ b := k.isLt
          have h1 : (k.val + 1) * n ≤ b * n := Nat.mul_le_mul_right n hk
          rw [Nat.succ_mul] at h1
          have h2 : b * n = n * b := mul_comm b n
          omega⟩, by
          rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt i.isLt]⟩
        left_inv := fun u => by
          apply Subtype.ext; apply Fin.ext
          dsimp only
          have hdm := Nat.div_add_mod u.val.val n
          rw [u.property, mul_comm] at hdm
          exact hdm
        right_inv := fun k => by
          apply Fin.ext
          dsimp only
          rw [mul_comm k.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt i.isLt, add_zero] }
    exact (Fintype.card_congr eqv).trans (Fintype.card_fin b)
  rw [← Fintype.card_subtype]
  exact heq

lemma sum_kerK_comp {n q s : ℕ} (G : Fin n → Fin n → Bool) (τ : Fin s → VType n q) :
    (∑ u : Fin s, ∑ v : Fin s, kerK G (τ u) (τ v)) =
      quadNat G (fun t => (Finset.univ.filter (fun u : Fin s => τ u = t)).card) := by
  dsimp only [quadNat]
  have h1 : ∀ t₁ : VType n q,
      (∑ u ∈ Finset.univ.filter (fun u : Fin s => τ u = t₁),
        ∑ v : Fin s, kerK G (τ u) (τ v)) =
      ∑ t₂ : VType n q, kerK G t₁ t₂ *
        (Finset.univ.filter (fun u : Fin s => τ u = t₁)).card *
        (Finset.univ.filter (fun u : Fin s => τ u = t₂)).card := by
    intro t₁
    have hinner : ∀ u ∈ Finset.univ.filter (fun u : Fin s => τ u = t₁),
        (∑ v : Fin s, kerK G (τ u) (τ v)) =
          ∑ t₂ : VType n q, kerK G t₁ t₂ *
            (Finset.univ.filter (fun v : Fin s => τ v = t₂)).card := by
      intro u hu
      have htu : τ u = t₁ := (Finset.mem_filter.mp hu).2
      rw [htu]
      rw [← Finset.sum_fiberwise_of_maps_to (g := τ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun t₂ _ => ?_
      rw [Finset.sum_congr rfl (fun v hv => by rw [(Finset.mem_filter.mp hv).2]),
        Finset.sum_const, smul_eq_mul, mul_comm]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t₂ _ => ?_
    ring
  rw [← Finset.sum_fiberwise_of_maps_to (g := τ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  exact Finset.sum_congr rfl fun t₁ _ => h1 t₁

lemma exists_validInt_of_fitsDef {n q b budget : ℕ} (hn : 0 < n) (G : Fin n → Fin n → Bool)
    (hfit : fitsDef q (n * b) (blowup hn G b) budget) :
    ∃ N : VType n q → ℕ, ValidInt b N ∧ quadNat G N ≤ 2 * budget := by
  rcases hfit with ⟨π, rf, cf, R, C, out, hcard⟩
  let τ : Fin (n * b) → VType n q := fun u =>
    (⟨u.val % n, Nat.mod_lt _ hn⟩, ⟨(π u).val % n, Nat.mod_lt _ hn⟩,
     rf u, cf (π u), fun j => decide (u ∈ R j), fun j => decide (π u ∈ C j))
  let N : VType n q → ℕ := fun t => (Finset.univ.filter (fun u : Fin (n * b) => τ u = t)).card
  refine ⟨N, ⟨?_, ?_⟩, ?_⟩
  · intro i
    have hfib : (∑ t : VType n q, (if vtA t = i then N t else 0)) =
        (Finset.univ.filter (fun u : Fin (n * b) => vtA (τ u) = i)).card := by
      rw [Finset.card_eq_sum_ones,
        ← Finset.sum_fiberwise_of_maps_to (g := τ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases ht : vtA t = i
      · rw [if_pos ht]
        have hfeq : (Finset.univ.filter (fun u : Fin (n * b) => vtA (τ u) = i)).filter (fun u => τ u = t) =
            Finset.univ.filter (fun u : Fin (n * b) => τ u = t) := by
          ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
          intro hu; rw [hu, ht]
        rw [hfeq, Finset.sum_const, smul_eq_mul, mul_one]
      · rw [if_neg ht]
        have hfeq : (Finset.univ.filter (fun u : Fin (n * b) => vtA (τ u) = i)).filter (fun u => τ u = t) = ∅ := by
          ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          rintro ⟨h1, h2⟩; rw [h2] at h1; exact ht h1
        rw [hfeq, Finset.sum_empty]
    rw [hfib]
    have hfilt : Finset.univ.filter (fun u : Fin (n * b) => vtA (τ u) = i) =
        Finset.univ.filter (fun u : Fin (n * b) => u.val % n = i.val) := by
      ext u; simp [vtA, τ, Fin.ext_iff]
    rw [hfilt, card_mod_eq hn b i]
  · intro j
    have hfib : (∑ t : VType n q, (if vtB t = j then N t else 0)) =
        (Finset.univ.filter (fun u : Fin (n * b) => vtB (τ u) = j)).card := by
      rw [Finset.card_eq_sum_ones,
        ← Finset.sum_fiberwise_of_maps_to (g := τ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases ht : vtB t = j
      · rw [if_pos ht]
        have hfeq : (Finset.univ.filter (fun u : Fin (n * b) => vtB (τ u) = j)).filter (fun u => τ u = t) =
            Finset.univ.filter (fun u : Fin (n * b) => τ u = t) := by
          ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
          intro hu; rw [hu, ht]
        rw [hfeq, Finset.sum_const, smul_eq_mul, mul_one]
      · rw [if_neg ht]
        have hfeq : (Finset.univ.filter (fun u : Fin (n * b) => vtB (τ u) = j)).filter (fun u => τ u = t) = ∅ := by
          ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          rintro ⟨h1, h2⟩; rw [h2] at h1; exact ht h1
        rw [hfeq, Finset.sum_empty]
    rw [hfib]
    have hbij : (Finset.univ.filter (fun u : Fin (n * b) => vtB (τ u) = j)).card =
        (Finset.univ.filter (fun w : Fin (n * b) => w.val % n = j.val)).card := by
      refine Finset.card_bij (fun u _ => π u) ?_ ?_ ?_
      · intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, vtB, τ, Fin.ext_iff] at hu ⊢
        exact hu
      · intro u₁ _ u₂ _ h; exact π.injective h
      · intro w hw
        refine ⟨π.symm w, ?_, π.apply_symm_apply w⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, vtB, τ, Fin.ext_iff,
          Equiv.apply_symm_apply] at hw ⊢
        exact hw
    rw [hbij, card_mod_eq hn b j]
  · rw [← sum_kerK_comp G τ]
    let err : Fin (n * b) → Fin (n * b) → ℕ := fun u v =>
      if out {u, v} (fun j => decide (u ∈ R j ∨ π v ∈ C j)) ≠
          Bool.xor (blowup hn G b u (π v)) (Bool.xor (rf u) (cf (π v)))
      then 1 else 0
    have hpair : ∀ u v : Fin (n * b), kerK G (τ u) (τ v) ≤ err u v + err v u := by
      intro u v
      have hsig_uv : (fun j : Fin q => decide (u ∈ R j ∨ π v ∈ C j)) = sigT (τ u) (τ v) := by
        funext j; simp [sigT, vtR, vtC, τ]
      have hsig_vu : (fun j : Fin q => decide (v ∈ R j ∨ π u ∈ C j)) = sigT (τ v) (τ u) := by
        funext j; simp [sigT, vtR, vtC, τ]
      have hval_uv : Bool.xor (blowup hn G b u (π v)) (Bool.xor (rf u) (cf (π v))) = valT G (τ u) (τ v) := rfl
      have hval_vu : Bool.xor (blowup hn G b v (π u)) (Bool.xor (rf v) (cf (π u))) = valT G (τ v) (τ u) := rfl
      dsimp only [kerK]
      split_ifs with h
      · dsimp only [err]
        rw [hsig_uv, hsig_vu, hval_uv, hval_vu]
        by_cases h1 : out {u, v} (sigT (τ u) (τ v)) ≠ valT G (τ u) (τ v)
        · rw [if_pos h1]; omega
        · push_neg at h1
          have h2 : out {v, u} (sigT (τ v) (τ u)) ≠ valT G (τ v) (τ u) := by
            rw [Finset.pair_comm v u, ← h.1, h1]
            exact h.2
          rw [if_pos h2]; omega
      · omega
    have hsum1 : (∑ u : Fin (n * b), ∑ v : Fin (n * b), kerK G (τ u) (τ v)) ≤
        ∑ u : Fin (n * b), ∑ v : Fin (n * b), (err u v + err v u) :=
      Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hpair u v
    have hsum2 : (∑ u : Fin (n * b), ∑ v : Fin (n * b), (err u v + err v u)) =
        2 * (∑ u : Fin (n * b), ∑ v : Fin (n * b), err u v) := by
      simp_rw [Finset.sum_add_distrib]
      have hswap : (∑ u : Fin (n * b), ∑ v : Fin (n * b), err v u) =
          ∑ u : Fin (n * b), ∑ v : Fin (n * b), err u v := Finset.sum_comm
      rw [hswap]; ring
    have hsum3 : (∑ u : Fin (n * b), ∑ v : Fin (n * b), err u v) =
        ((Finset.univ : Finset (Fin (n * b) × Fin (n * b))).filter (fun z =>
          out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
            Bool.xor (blowup hn G b z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card := by
      rw [← Fintype.sum_prod_type', Finset.card_filter]
    omega

lemma fitsDef_of_validInt {n q b : ℕ} (hn : 0 < n) (G : Fin n → Fin n → Bool)
    (N : VType n q → ℕ) (hN : ValidInt b N) :
    fitsDef q (n * b) (blowup hn G b) (quadNat G N / 2) := by
  -- Step 1: assign types τ : Fin (n * b) → VType n q realizing N with vtA (τ u) = u % n
  have hRowEquiv : ∀ i : Fin n,
      Nonempty ({u : Fin (n * b) // u.val % n = i.val} ≃
        Σ t : {t : VType n q // vtA t = i}, Fin (N t.val)) := by
    intro i
    refine ⟨Fintype.equivOfCardEq ?_⟩
    rw [Fintype.card_subtype, card_mod_eq hn b i, Fintype.card_sigma]
    simp only [Fintype.card_fin]
    have hs : (∑ t : {t : VType n q // vtA t = i}, N t.val) =
        ∑ t : VType n q, (if vtA t = i then N t else 0) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun t _ => t.val) ?_ ?_ ?_ ?_
      · intro t _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.property⟩
      · intro t₁ _ t₂ _ h; exact Subtype.ext h
      · intro t ht; exact ⟨⟨t, (Finset.mem_filter.mp ht).2⟩, Finset.mem_univ _, rfl⟩
      · intro _ _; rfl
    rw [hs, hN.1 i]
  have hex_e : ∃ e : ∀ i : Fin n,
      {u : Fin (n * b) // u.val % n = i.val} ≃
        Σ t : {t : VType n q // vtA t = i}, Fin (N t.val), True :=
    ⟨fun i => (hRowEquiv i).some, trivial⟩
  obtain ⟨e, _⟩ := hex_e
  let Φ : Fin (n * b) ≃ Σ t : VType n q, Fin (N t) :=
    { toFun := fun u =>
        let p := e ⟨u.val % n, Nat.mod_lt _ hn⟩ ⟨u, rfl⟩
        ⟨p.1.val, p.2⟩
      invFun := fun tk => ((e (vtA tk.1)).symm ⟨⟨tk.1, rfl⟩, tk.2⟩).val
      left_inv := fun u => by
        dsimp only
        set i : Fin n := ⟨u.val % n, Nat.mod_lt _ hn⟩
        set p := e i ⟨u, rfl⟩
        have htr : ∀ (i₀ j₀ : Fin n) (hij : j₀ = i₀)
            (p₀ : Σ x : {x : VType n q // vtA x = i₀}, Fin (N x.val))
            (hp₀ : vtA p₀.1.val = j₀),
            ((e j₀).symm ⟨⟨p₀.1.val, hp₀⟩, p₀.2⟩).val = ((e i₀).symm p₀).val := by
          intro i₀ j₀ hij p₀ hp₀; subst hij; rfl
        rw [htr i (vtA p.1.val) p.1.property p rfl]
        exact congrArg Subtype.val ((e i).symm_apply_apply ⟨u, rfl⟩)
      right_inv := fun tk => by
        rcases tk with ⟨t, k⟩
        dsimp only
        set u0 := (e (vtA t)).symm ⟨⟨t, rfl⟩, k⟩
        have hi : (⟨u0.val.val % n, Nat.mod_lt _ hn⟩ : Fin n) = vtA t := Fin.ext u0.property
        have htr : ∀ (j : Fin n) (hj : j = vtA t) (hu : u0.val.val % n = j.val),
            (⟨(e j ⟨u0.val, hu⟩).1.val, (e j ⟨u0.val, hu⟩).2⟩ : Σ x : VType n q, Fin (N x)) =
            ⟨(e (vtA t) u0).1.val, (e (vtA t) u0).2⟩ := by
          intro j hj hu; subst hj; rfl
        rw [htr _ hi rfl]
        have heu : e (vtA t) u0 = ⟨⟨t, rfl⟩, k⟩ := (e (vtA t)).apply_symm_apply ⟨⟨t, rfl⟩, k⟩
        rw [heu] }
  let τ : Fin (n * b) → VType n q := fun u => (Φ u).1
  have hτA : ∀ u : Fin (n * b), vtA (τ u) = ⟨u.val % n, Nat.mod_lt _ hn⟩ := fun u =>
    (e ⟨u.val % n, Nat.mod_lt _ hn⟩ ⟨u, rfl⟩).1.property
  have hτ_card : ∀ t : VType n q,
      (Finset.univ.filter (fun u : Fin (n * b) => τ u = t)).card = N t := by
    intro t
    rw [← Fintype.card_subtype]
    let eqv : {u : Fin (n * b) // τ u = t} ≃ Fin (N t) :=
      { toFun := fun u => cast (congrArg (fun x => Fin (N x)) u.property) (Φ u.val).2
        invFun := fun k => ⟨Φ.symm ⟨t, k⟩, by dsimp only [τ]; rw [Φ.apply_symm_apply]⟩
        left_inv := fun u => by
          apply Subtype.ext
          dsimp only
          have hgen : ∀ (p : Σ x : VType n q, Fin (N x)) (hp : p.1 = t),
              (⟨t, cast (congrArg (fun x => Fin (N x)) hp) p.2⟩ : Σ x : VType n q, Fin (N x)) = p := by
            intro ⟨t', k'⟩ hp; dsimp only at hp; subst hp; rfl
          rw [hgen (Φ u.val) u.property, Φ.symm_apply_apply]
        right_inv := fun k => by
          dsimp only
          have hφ : Φ (Φ.symm ⟨t, k⟩) = ⟨t, k⟩ := Φ.apply_symm_apply ⟨t, k⟩
          have hgen : ∀ (p : Σ x : VType n q, Fin (N x)) (hp : p = ⟨t, k⟩) (hp1 : p.1 = t),
              cast (congrArg (fun x => Fin (N x)) hp1) p.2 = k := by
            intro p hp hp1; subst hp; rfl
          exact hgen (Φ (Φ.symm ⟨t, k⟩)) hφ (by rw [Φ.apply_symm_apply]) }
    exact (Fintype.card_congr eqv).trans (Fintype.card_fin (N t))
  -- Step 2: construct π : Equiv.Perm (Fin (n * b)) with (π u) % n = vtB (τ u)
  have hColEquiv : ∀ j : Fin n,
      Nonempty ({u : Fin (n * b) // vtB (τ u) = j} ≃ {w : Fin (n * b) // (⟨w.val % n, Nat.mod_lt _ hn⟩ : Fin n) = j}) := by
    intro j
    refine ⟨Fintype.equivOfCardEq ?_⟩
    rw [Fintype.card_subtype, Fintype.card_subtype]
    have h1 : (Finset.univ.filter (fun u : Fin (n * b) => vtB (τ u) = j)).card = b := by
      rw [Finset.card_eq_sum_ones,
        ← Finset.sum_fiberwise_of_maps_to (g := τ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      have : (∑ t : VType n q, ∑ u ∈ (Finset.univ.filter (fun u : Fin (n * b) => vtB (τ u) = j)).filter (fun u => τ u = t), 1) =
          ∑ t : VType n q, (if vtB t = j then N t else 0) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases ht : vtB t = j
        · rw [if_pos ht]
          have hfeq : (Finset.univ.filter (fun u : Fin (n * b) => vtB (τ u) = j)).filter (fun u => τ u = t) =
              Finset.univ.filter (fun u : Fin (n * b) => τ u = t) := by
            ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
            intro hu; rw [hu, ht]
          rw [hfeq, Finset.sum_const, smul_eq_mul, mul_one, hτ_card t]
        · rw [if_neg ht]
          have hfeq : (Finset.univ.filter (fun u : Fin (n * b) => vtB (τ u) = j)).filter (fun u => τ u = t) = ∅ := by
            ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            rintro ⟨h1, h2⟩; rw [h2] at h1; exact ht h1
          rw [hfeq, Finset.sum_empty]
      rw [this, hN.2 j]
    have h2 : (Finset.univ.filter (fun w : Fin (n * b) => (⟨w.val % n, Nat.mod_lt _ hn⟩ : Fin n) = j)).card = b := by
      have : Finset.univ.filter (fun w : Fin (n * b) => (⟨w.val % n, Nat.mod_lt _ hn⟩ : Fin n) = j) =
          Finset.univ.filter (fun w : Fin (n * b) => w.val % n = j.val) := by
        ext w; simp [Fin.ext_iff]
      rw [this, card_mod_eq hn b j]
    rw [h1, h2]
  have hex_p : ∃ p : ∀ j : Fin n,
      {u : Fin (n * b) // vtB (τ u) = j} ≃
        {w : Fin (n * b) // (⟨w.val % n, Nat.mod_lt _ hn⟩ : Fin n) = j}, True :=
    ⟨fun j => (hColEquiv j).some, trivial⟩
  obtain ⟨p, _⟩ := hex_p
  let π : Equiv.Perm (Fin (n * b)) :=
    (Equiv.sigmaFiberEquiv (fun u : Fin (n * b) => vtB (τ u))).symm.trans
      ((Equiv.sigmaCongrRight p).trans
        (Equiv.sigmaFiberEquiv (fun w : Fin (n * b) => (⟨w.val % n, Nat.mod_lt _ hn⟩ : Fin n))))
  have hπB : ∀ u : Fin (n * b), (⟨(π u).val % n, Nat.mod_lt _ hn⟩ : Fin n) = vtB (τ u) := by
    intro u
    exact (p (vtB (τ u)) ⟨u, rfl⟩).property
  -- Step 3: define rf, cf, R, C, out
  let rf : Fin (n * b) → Bool := fun u => vtRf (τ u)
  let cf : Fin (n * b) → Bool := fun w => vtCf (τ (π.symm w))
  let R : Fin q → Finset (Fin (n * b)) := fun j => Finset.univ.filter (fun u => vtR (τ u) j = true)
  let C : Fin q → Finset (Fin (n * b)) := fun j => Finset.univ.filter (fun w => vtC (τ (π.symm w)) j = true)
  let out : Finset (Fin (n * b)) → (Fin q → Bool) → Bool := fun S σ =>
    if h1 : ∃ u v : Fin (n * b), ({u, v} : Finset _) = S ∧ sigT (τ u) (τ v) = σ ∧ u ≤ v
    then valT G (τ h1.choose) (τ h1.choose_spec.choose)
    else if h2 : ∃ u v : Fin (n * b), ({u, v} : Finset _) = S ∧ sigT (τ u) (τ v) = σ
    then valT G (τ h2.choose) (τ h2.choose_spec.choose)
    else false
  refine ⟨π, rf, cf, R, C, out, ?_⟩
  let err : Fin (n * b) → Fin (n * b) → ℕ := fun u v =>
    if out {u, v} (fun j => decide (u ∈ R j ∨ π v ∈ C j)) ≠
        Bool.xor (blowup hn G b u (π v)) (Bool.xor (rf u) (cf (π v)))
    then 1 else 0
  have hsig_eq : ∀ u v : Fin (n * b),
      (fun j : Fin q => decide (u ∈ R j ∨ π v ∈ C j)) = sigT (τ u) (τ v) := by
    intro u v; funext j; simp [R, C, sigT]
  have hval_eq : ∀ u v : Fin (n * b),
      Bool.xor (blowup hn G b u (π v)) (Bool.xor (rf u) (cf (π v))) = valT G (τ u) (τ v) := by
    intro u v
    dsimp only [blowup, rf, cf, valT]
    rw [hτA u, hπB v, Equiv.symm_apply_apply]
  have hpair_le : ∀ u v : Fin (n * b), err u v + err v u ≤ kerK G (τ u) (τ v) := by
    intro u v
    have huniq_le : ∀ (a₁ a₂ c₁ c₂ : Fin (n * b)),
        ({c₁, c₂} : Finset (Fin (n * b))) = {a₁, a₂} → a₁ ≤ a₂ → c₁ ≤ c₂ → c₁ = a₁ ∧ c₂ = a₂ := by
      intro a₁ a₂ c₁ c₂ hset ha12 hc12
      have hc1 : c₁ ∈ ({a₁, a₂} : Finset (Fin (n * b))) := by rw [← hset]; simp
      have hc2 : c₂ ∈ ({a₁, a₂} : Finset (Fin (n * b))) := by rw [← hset]; simp
      have ha1 : a₁ ∈ ({c₁, c₂} : Finset (Fin (n * b))) := by rw [hset]; simp
      have ha2 : a₂ ∈ ({c₁, c₂} : Finset (Fin (n * b))) := by rw [hset]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2 ha1 ha2
      rcases hc1 with hc1 | hc1 <;> rcases hc2 with hc2 | hc2
      · rw [hc1, hc2] at ha2
        have : a₂ = a₁ := by rcases ha2 with h | h <;> exact h
        exact ⟨hc1, hc2.trans this.symm⟩
      · exact ⟨hc1, hc2⟩
      · rw [hc1, hc2] at hc12
        have heq : a₁ = a₂ := le_antisymm ha12 hc12
        exact ⟨hc1.trans heq.symm, hc2.trans heq⟩
      · rw [hc1, hc2] at ha1
        have : a₁ = a₂ := by rcases ha1 with h | h <;> exact h
        exact ⟨hc1.trans this.symm, hc2⟩
    dsimp only [err]
    rw [hsig_eq u v, hsig_eq v u, hval_eq u v, hval_eq v u]
    by_cases hsig : sigT (τ u) (τ v) = sigT (τ v) (τ u)
    · by_cases hval : valT G (τ u) (τ v) = valT G (τ v) (τ u)
      · have hmatch : ∀ a₁ a₂ : Fin (n * b), ({a₁, a₂} : Finset (Fin (n * b))) = {u, v} →
            valT G (τ a₁) (τ a₂) = valT G (τ u) (τ v) := by
          intro a₁ a₂ hset
          have ha1 : a₁ ∈ ({u, v} : Finset (Fin (n * b))) := by rw [← hset]; simp
          have ha2 : a₂ ∈ ({u, v} : Finset (Fin (n * b))) := by rw [← hset]; simp
          have hu : u ∈ ({a₁, a₂} : Finset (Fin (n * b))) := by rw [hset]; simp
          have hv : v ∈ ({a₁, a₂} : Finset (Fin (n * b))) := by rw [hset]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha1 ha2 hu hv
          rcases ha1 with ha1 | ha1 <;> rcases ha2 with ha2 | ha2
          · rw [ha1, ha2] at hv ⊢
            have huv : v = u := by rcases hv with h | h <;> exact h
            rw [huv]
          · rw [ha1, ha2]
          · rw [ha1, ha2]; exact hval.symm
          · rw [ha1, ha2] at hu ⊢
            have huv : u = v := by rcases hu with h | h <;> exact h
            rw [huv]
        have hout_uv : out {u, v} (sigT (τ u) (τ v)) = valT G (τ u) (τ v) := by
          dsimp only [out]
          split_ifs with h1 h2
          · exact hmatch _ _ h1.choose_spec.choose_spec.1
          · exact hmatch _ _ h2.choose_spec.choose_spec.1
          · exact absurd ⟨u, v, rfl, rfl⟩ h2
        have hout_vu : out {v, u} (sigT (τ v) (τ u)) = valT G (τ v) (τ u) := by
          rw [Finset.pair_comm v u, ← hsig, hout_uv, hval]
        rw [if_neg (not_not.mpr hout_uv), if_neg (not_not.mpr hout_vu)]; omega
      · have hker : kerK G (τ u) (τ v) = 1 := by simp [kerK, hsig, hval]
        rw [hker]
        rcases le_total u v with huv | hvu
        · have h1 : ∃ a₁ a₂ : Fin (n * b), ({a₁, a₂} : Finset (Fin (n * b))) = {u, v} ∧
              sigT (τ a₁) (τ a₂) = sigT (τ u) (τ v) ∧ a₁ ≤ a₂ := ⟨u, v, rfl, rfl, huv⟩
          have hout : out {u, v} (sigT (τ u) (τ v)) = valT G (τ u) (τ v) := by
            dsimp only [out]; rw [dif_pos h1]
            have hspec := h1.choose_spec.choose_spec
            have ⟨ha, hb⟩ := huniq_le u v _ _ hspec.1 huv hspec.2.2
            exact congrArg₂ (fun x y => valT G (τ x) (τ y)) ha hb
          rw [if_neg (not_not.mpr hout)]
          split_ifs <;> omega
        · have h1 : ∃ a₁ a₂ : Fin (n * b), ({a₁, a₂} : Finset (Fin (n * b))) = {v, u} ∧
              sigT (τ a₁) (τ a₂) = sigT (τ v) (τ u) ∧ a₁ ≤ a₂ := ⟨v, u, rfl, rfl, hvu⟩
          have hout : out {v, u} (sigT (τ v) (τ u)) = valT G (τ v) (τ u) := by
            dsimp only [out]; rw [dif_pos h1]
            have hspec := h1.choose_spec.choose_spec
            have ⟨ha, hb⟩ := huniq_le v u _ _ hspec.1 hvu hspec.2.2
            exact congrArg₂ (fun x y => valT G (τ x) (τ y)) ha hb
          rw [if_neg (not_not.mpr hout)]
          split_ifs <;> omega
    · have huniq_sig : ∀ a₁ a₂ : Fin (n * b), ({a₁, a₂} : Finset (Fin (n * b))) = {u, v} →
          sigT (τ a₁) (τ a₂) = sigT (τ u) (τ v) → a₁ = u ∧ a₂ = v := by
        intro a₁ a₂ hset hs
        have ha1 : a₁ ∈ ({u, v} : Finset (Fin (n * b))) := by rw [← hset]; simp
        have ha2 : a₂ ∈ ({u, v} : Finset (Fin (n * b))) := by rw [← hset]; simp
        have hu : u ∈ ({a₁, a₂} : Finset (Fin (n * b))) := by rw [hset]; simp
        have hv : v ∈ ({a₁, a₂} : Finset (Fin (n * b))) := by rw [hset]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha1 ha2 hu hv
        rcases ha1 with ha1 | ha1 <;> rcases ha2 with ha2 | ha2
        · rw [ha1, ha2] at hv
          have huv : v = u := by rcases hv with h | h <;> exact h
          exact ⟨ha1, ha2.trans huv.symm⟩
        · exact ⟨ha1, ha2⟩
        · rw [ha1, ha2] at hs; exact absurd hs.symm hsig
        · rw [ha1, ha2] at hu
          have huv : u = v := by rcases hu with h | h <;> exact h
          exact ⟨ha1.trans huv.symm, ha2⟩
      have hout_uv : out {u, v} (sigT (τ u) (τ v)) = valT G (τ u) (τ v) := by
        dsimp only [out]
        split_ifs with h1 h2
        · have ⟨ha, hb⟩ := huniq_sig _ _ h1.choose_spec.choose_spec.1 h1.choose_spec.choose_spec.2.1
          exact congrArg₂ (fun x y => valT G (τ x) (τ y)) ha hb
        · have ⟨ha, hb⟩ := huniq_sig _ _ h2.choose_spec.choose_spec.1 h2.choose_spec.choose_spec.2
          exact congrArg₂ (fun x y => valT G (τ x) (τ y)) ha hb
        · exact absurd ⟨u, v, rfl, rfl⟩ h2
      have huniq_sig' : ∀ a₁ a₂ : Fin (n * b), ({a₁, a₂} : Finset (Fin (n * b))) = {v, u} →
          sigT (τ a₁) (τ a₂) = sigT (τ v) (τ u) → a₁ = v ∧ a₂ = u := by
        intro a₁ a₂ hset hs
        have ha1 : a₁ ∈ ({v, u} : Finset (Fin (n * b))) := by rw [← hset]; simp
        have ha2 : a₂ ∈ ({v, u} : Finset (Fin (n * b))) := by rw [← hset]; simp
        have hu : u ∈ ({a₁, a₂} : Finset (Fin (n * b))) := by rw [hset]; simp
        have hv : v ∈ ({a₁, a₂} : Finset (Fin (n * b))) := by rw [hset]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha1 ha2 hu hv
        rcases ha1 with ha1 | ha1 <;> rcases ha2 with ha2 | ha2
        · rw [ha1, ha2] at hu
          have huv : u = v := by rcases hu with h | h <;> exact h
          exact ⟨ha1, ha2.trans huv.symm⟩
        · exact ⟨ha1, ha2⟩
        · rw [ha1, ha2] at hs; exact absurd hs hsig
        · rw [ha1, ha2] at hv
          have huv : v = u := by rcases hv with h | h <;> exact h
          exact ⟨ha1.trans huv.symm, ha2⟩
      have hout_vu : out {v, u} (sigT (τ v) (τ u)) = valT G (τ v) (τ u) := by
        dsimp only [out]
        split_ifs with h1 h2
        · have ⟨ha, hb⟩ := huniq_sig' _ _ h1.choose_spec.choose_spec.1 h1.choose_spec.choose_spec.2.1
          exact congrArg₂ (fun x y => valT G (τ x) (τ y)) ha hb
        · have ⟨ha, hb⟩ := huniq_sig' _ _ h2.choose_spec.choose_spec.1 h2.choose_spec.choose_spec.2
          exact congrArg₂ (fun x y => valT G (τ x) (τ y)) ha hb
        · exact absurd ⟨v, u, rfl, rfl⟩ h2
      rw [if_neg (not_not.mpr hout_uv), if_neg (not_not.mpr hout_vu)]; omega
  have hsum_le : 2 * (∑ u : Fin (n * b), ∑ v : Fin (n * b), err u v) ≤ quadNat G N := by
    have h2 : 2 * (∑ u : Fin (n * b), ∑ v : Fin (n * b), err u v) =
        ∑ u : Fin (n * b), ∑ v : Fin (n * b), (err u v + err v u) := by
      simp_rw [Finset.sum_add_distrib]
      have hswap : (∑ u : Fin (n * b), ∑ v : Fin (n * b), err v u) =
          ∑ u : Fin (n * b), ∑ v : Fin (n * b), err u v := Finset.sum_comm
      rw [hswap]; ring
    rw [h2]
    have hq_eq : (fun t => (Finset.univ.filter (fun u : Fin (n * b) => τ u = t)).card) = N :=
      funext hτ_card
    calc (∑ u : Fin (n * b), ∑ v : Fin (n * b), (err u v + err v u))
        ≤ ∑ u : Fin (n * b), ∑ v : Fin (n * b), kerK G (τ u) (τ v) :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hpair_le u v
      _ = quadNat G (fun t => (Finset.univ.filter (fun u : Fin (n * b) => τ u = t)).card) :=
          sum_kerK_comp G τ
      _ = quadNat G N := by rw [hq_eq]
  have hcard_eq : ((Finset.univ : Finset (Fin (n * b) × Fin (n * b))).filter (fun z =>
      out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
        Bool.xor (blowup hn G b z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card =
      ∑ u : Fin (n * b), ∑ v : Fin (n * b), err u v := by
    rw [← Fintype.sum_prod_type', Finset.card_filter]
  omega

lemma two_mul_optDef_le_quadNat {n q b : ℕ} (hn : 0 < n) (G : Fin n → Fin n → Bool)
    (N : VType n q → ℕ) (hN : ValidInt b N) :
    2 * optDef hn q G b ≤ quadNat G N := by
  have hle : optDef hn q G b ≤ quadNat G N / 2 := Nat.sInf_le (fitsDef_of_validInt hn G N hN)
  omega

lemma exists_validInt_optDef {n q b : ℕ} (hn : 0 < n) (G : Fin n → Fin n → Bool) :
    ∃ N : VType n q → ℕ, ValidInt b N ∧ quadNat G N ≤ 2 * optDef hn q G b := by
  have hne : {e : ℕ | fitsDef q (n * b) (blowup hn G b) e}.Nonempty := by
    refine ⟨(n * b) * (n * b), Equiv.refl _, fun _ => false, fun _ => false,
      fun _ => ∅, fun _ => ∅, fun _ _ => false, ?_⟩
    calc ((Finset.univ : Finset (Fin (n * b) × Fin (n * b))).filter _).card
        ≤ (Finset.univ : Finset (Fin (n * b) × Fin (n * b))).card := Finset.card_filter_le _ _
      _ = (n * b) * (n * b) := by simp
  exact exists_validInt_of_fitsDef hn G (Nat.sInf_mem hne)

-- Part 3: Density of rational solutions in real solutions of a rational linear system

lemma rational_density_of_linear_system :
    ∀ (d m : ℕ) (A : Fin m → Fin d → ℚ) (b : Fin m → ℚ) (x : Fin d → ℝ),
      (∀ j, ∑ i, (A j i : ℝ) * x i = (b j : ℝ)) →
      ∀ ε : ℝ, 0 < ε →
        ∃ y : Fin d → ℚ, (∀ j, ∑ i, A j i * y i = b j) ∧ ∀ i, |(y i : ℝ) - x i| < ε := by
  intro d
  induction d with
  | zero =>
    intro m A b x hx ε _
    refine ⟨Fin.elim0, fun j => ?_, fun i => Fin.elim0 i⟩
    have hj := hx j
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hj ⊢
    exact Rat.cast_injective (α := ℝ) (by simpa using hj)
  | succ d ih =>
    intro m A b x hx ε hε
    by_cases hall0 : ∀ j i, A j i = 0
    · have hb0 : ∀ j, b j = 0 := fun j => by
        have hj := hx j
        simp only [hall0, Rat.cast_zero, zero_mul, Finset.sum_const_zero] at hj
        exact Rat.cast_injective (α := ℝ) (by simpa using hj.symm)
      have hex : ∀ i : Fin (d + 1), ∃ q : ℚ, |(q : ℝ) - x i| < ε := fun i => by
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x i - ε < x i + ε by linarith)
        exact ⟨q, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
      refine ⟨fun i => (hex i).choose, fun j => ?_, fun i => (hex i).choose_spec⟩
      simp [hall0, hb0]
    · push_neg at hall0
      rcases hall0 with ⟨j₀, i₀, hp⟩
      set p : ℚ := A j₀ i₀
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
      let A' : Fin m → Fin d → ℚ := fun j k =>
        A j (i₀.succAbove k) - (A j i₀ / p) * A j₀ (i₀.succAbove k)
      let b' : Fin m → ℚ := fun j => b j - (A j i₀ / p) * b j₀
      let x' : Fin d → ℝ := fun k => x (i₀.succAbove k)
      have hx_i0 : x i₀ = ((b j₀ : ℝ) - ∑ k : Fin d, (A j₀ (i₀.succAbove k) : ℝ) * x' k) / (p : ℝ) := by
        have hj0 := hx j₀
        rw [Fin.sum_univ_succAbove _ i₀] at hj0
        have h1 : (p : ℝ) * x i₀ = (b j₀ : ℝ) - ∑ k : Fin d, (A j₀ (i₀.succAbove k) : ℝ) * x' k := by
          dsimp only [p, x']; linarith
        exact eq_div_of_mul_eq hpR (by linarith)
      have hx' : ∀ j : Fin m, ∑ k : Fin d, (A' j k : ℝ) * x' k = (b' j : ℝ) := by
        intro j
        have hj := hx j
        have hj0 := hx j₀
        rw [Fin.sum_univ_succAbove _ i₀] at hj hj0
        have hsum : (∑ k : Fin d, (A' j k : ℝ) * x' k) =
            (∑ k : Fin d, (A j (i₀.succAbove k) : ℝ) * x' k) -
              ((A j i₀ : ℝ) / (p : ℝ)) * (∑ k : Fin d, (A j₀ (i₀.succAbove k) : ℝ) * x' k) := by
          simp only [A', Rat.cast_sub, Rat.cast_mul, Rat.cast_div, sub_mul, Finset.sum_sub_distrib,
            mul_assoc, Finset.mul_sum]
        rw [hsum]
        dsimp only [b', p, x'] at hj hj0 ⊢
        simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div]
        have hmul : ((A j i₀ : ℝ) / (A j₀ i₀ : ℝ)) * (A j₀ i₀ : ℝ) = (A j i₀ : ℝ) :=
          div_mul_cancel₀ _ hpR
        calc (∑ k : Fin d, (A j (i₀.succAbove k) : ℝ) * x (i₀.succAbove k)) -
              (A j i₀ : ℝ) / (A j₀ i₀ : ℝ) * ∑ k : Fin d, (A j₀ (i₀.succAbove k) : ℝ) * x (i₀.succAbove k)
            = ((b j : ℝ) - (A j i₀ : ℝ) * x i₀) -
              (A j i₀ : ℝ) / (A j₀ i₀ : ℝ) * ((b j₀ : ℝ) - (A j₀ i₀ : ℝ) * x i₀) := by
              rw [show ∑ k : Fin d, (A j (i₀.succAbove k) : ℝ) * x (i₀.succAbove k) = (b j : ℝ) - (A j i₀ : ℝ) * x i₀ by linarith,
                show ∑ k : Fin d, (A j₀ (i₀.succAbove k) : ℝ) * x (i₀.succAbove k) = (b j₀ : ℝ) - (A j₀ i₀ : ℝ) * x i₀ by linarith]
          _ = (b j : ℝ) - (A j i₀ : ℝ) / (A j₀ i₀ : ℝ) * (b j₀ : ℝ) := by
              have : (A j i₀ : ℝ) / (A j₀ i₀ : ℝ) * ((A j₀ i₀ : ℝ) * x i₀) = (A j i₀ : ℝ) * x i₀ := by
                rw [← mul_assoc, hmul]
              linarith
      let M : ℝ := 1 + ∑ k : Fin d, |((A j₀ (i₀.succAbove k) : ℝ) / (p : ℝ))|
      have hM_ge : 1 ≤ M := by
        dsimp only [M]
        have hnn : 0 ≤ ∑ k : Fin d, |((A j₀ (i₀.succAbove k) : ℝ) / (p : ℝ))| :=
          Finset.sum_nonneg fun k _ => abs_nonneg _
        linarith
      have hM_pos : 0 < M := by linarith
      let δ : ℝ := ε / M
      have hδ_pos : 0 < δ := div_pos hε hM_pos
      have hδ_le : δ ≤ ε := div_le_self (le_of_lt hε) hM_ge
      obtain ⟨y', hy'_eq, hy'_close⟩ := ih m A' b' x' hx' δ hδ_pos
      let y0 : ℚ := (b j₀ - ∑ k : Fin d, A j₀ (i₀.succAbove k) * y' k) / p
      let y : Fin (d + 1) → ℚ := Fin.insertNth i₀ y0 y'
      refine ⟨y, ?_, ?_⟩
      · intro j
        rw [Fin.sum_univ_succAbove _ i₀]
        simp only [y, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        have hj' := hy'_eq j
        have hsum : (∑ k : Fin d, A' j k * y' k) =
            (∑ k : Fin d, A j (i₀.succAbove k) * y' k) -
              (A j i₀ / p) * (∑ k : Fin d, A j₀ (i₀.succAbove k) * y' k) := by
          simp only [A', sub_mul, Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]
        rw [hsum] at hj'
        dsimp only [y0, b'] at hj' ⊢
        have hmul : A j i₀ * ((b j₀ - ∑ k : Fin d, A j₀ (i₀.succAbove k) * y' k) / p) =
            (A j i₀ / p) * b j₀ - (A j i₀ / p) * ∑ k : Fin d, A j₀ (i₀.succAbove k) * y' k := by
          ring
        linarith
      · intro i
        refine Fin.succAboveCases i₀ ?_ (fun k => ?_) i
        · simp only [y, Fin.insertNth_apply_same]
          have hdiff : (y0 : ℝ) - x i₀ =
              ∑ k : Fin d, ((A j₀ (i₀.succAbove k) : ℝ) / (p : ℝ)) * (x' k - (y' k : ℝ)) := by
            rw [hx_i0]
            dsimp only [y0]
            simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_sum, Rat.cast_mul]
            rw [← sub_div, sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib, Finset.sum_div]
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
          rw [hdiff]
          calc |∑ k : Fin d, ((A j₀ (i₀.succAbove k) : ℝ) / (p : ℝ)) * (x' k - (y' k : ℝ))|
              ≤ ∑ k : Fin d, |((A j₀ (i₀.succAbove k) : ℝ) / (p : ℝ)) * (x' k - (y' k : ℝ))| :=
                Finset.abs_sum_le_sum_abs _ _
            _ = ∑ k : Fin d, |((A j₀ (i₀.succAbove k) : ℝ) / (p : ℝ))| * |(y' k : ℝ) - x' k| := by
                refine Finset.sum_congr rfl fun k _ => by rw [abs_mul, abs_sub_comm]
            _ ≤ ∑ k : Fin d, |((A j₀ (i₀.succAbove k) : ℝ) / (p : ℝ))| * δ :=
                Finset.sum_le_sum fun k _ =>
                  mul_le_mul_of_nonneg_left (le_of_lt (hy'_close k)) (abs_nonneg _)
            _ = (∑ k : Fin d, |((A j₀ (i₀.succAbove k) : ℝ) / (p : ℝ))|) * δ := by
                rw [← Finset.sum_mul]
            _ < M * δ := by
                have hlt : (∑ k : Fin d, |((A j₀ (i₀.succAbove k) : ℝ) / (p : ℝ))|) < M := by
                  dsimp only [M]; linarith
                exact mul_lt_mul_of_pos_right hlt hδ_pos
            _ = ε := mul_div_cancel₀ ε (ne_of_gt hM_pos)
        · simp only [y, Fin.insertNth_apply_succAbove]
          exact lt_of_lt_of_le (hy'_close k) hδ_le

-- Part 4: Continuous quadratic minimization on the polytope, stationarity, rational minimizer, and Hall matching

def Polytope (n q : ℕ) : Set (VType n q → ℝ) :=
  {x | (∀ t, 0 ≤ x t) ∧
       (∀ i : Fin n, ∑ t : VType n q, (if vtA t = i then x t else 0) = 1) ∧
       (∀ j : Fin n, ∑ t : VType n q, (if vtB t = j then x t else 0) = 1)}

def quadR {n q : ℕ} (G : Fin n → Fin n → Bool) (x : VType n q → ℝ) : ℝ :=
  ∑ t₁ : VType n q, ∑ t₂ : VType n q, (kerK G t₁ t₂ : ℝ) * x t₁ * x t₂

def bilinR {n q : ℕ} (G : Fin n → Fin n → Bool) (x y : VType n q → ℝ) : ℝ :=
  ∑ t₁ : VType n q, ∑ t₂ : VType n q, (kerK G t₁ t₂ : ℝ) * x t₁ * y t₂

lemma bilinR_symm {n q : ℕ} (G : Fin n → Fin n → Bool) (x y : VType n q → ℝ) :
    bilinR G x y = bilinR G y x := by
  dsimp only [bilinR]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t₂ _ => Finset.sum_congr rfl fun t₁ _ => ?_
  rw [kerK_symm]; ring

lemma quadR_add_smul {n q : ℕ} (G : Fin n → Fin n → Bool) (x v : VType n q → ℝ) (c : ℝ) :
    quadR G (fun t => x t + c * v t) = quadR G x + 2 * c * bilinR G x v + c ^ 2 * quadR G v := by
  have h1 : quadR G (fun t => x t + c * v t) =
      quadR G x + c * bilinR G x v + c * bilinR G v x + c ^ 2 * quadR G v := by
    dsimp only [quadR, bilinR]
    simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
    have ha : (∑ t₁ : VType n q, ∑ t₂ : VType n q, (kerK G t₁ t₂ : ℝ) * x t₁ * (c * v t₂)) =
        c * ∑ t₁ : VType n q, ∑ t₂ : VType n q, (kerK G t₁ t₂ : ℝ) * x t₁ * v t₂ := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t₁ _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t₂ _ => by ring
    have hb : (∑ t₁ : VType n q, ∑ t₂ : VType n q, (kerK G t₁ t₂ : ℝ) * (c * v t₁) * x t₂) =
        c * ∑ t₁ : VType n q, ∑ t₂ : VType n q, (kerK G t₁ t₂ : ℝ) * v t₁ * x t₂ := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t₁ _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t₂ _ => by ring
    have hc : (∑ t₁ : VType n q, ∑ t₂ : VType n q, (kerK G t₁ t₂ : ℝ) * (c * v t₁) * (c * v t₂)) =
        c ^ 2 * ∑ t₁ : VType n q, ∑ t₂ : VType n q, (kerK G t₁ t₂ : ℝ) * v t₁ * v t₂ := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t₁ _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t₂ _ => by ring
    rw [ha, hb, hc]
    ring
  rw [h1, bilinR_symm G v x]; ring

lemma quadR_nonneg_of_nonneg {n q : ℕ} (G : Fin n → Fin n → Bool) (x : VType n q → ℝ)
    (hx : ∀ t, 0 ≤ x t) : 0 ≤ quadR G x := by
  refine Finset.sum_nonneg fun t₁ _ => Finset.sum_nonneg fun t₂ _ => ?_
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hx t₁)) (hx t₂)

lemma polytope_nonempty (n q : ℕ) : (Polytope n q).Nonempty := by
  let diagT : Fin n → VType n q := fun i => (i, i, false, false, fun _ => false, fun _ => false)
  let x : VType n q → ℝ := fun t => if ∃ i : Fin n, t = diagT i then 1 else 0
  refine ⟨x, fun t => by dsimp only [x]; split_ifs <;> norm_num, fun i => ?_, fun j => ?_⟩
  · rw [Finset.sum_eq_single (diagT i)]
    · simp [x, vtA, diagT]
    · intro t _ hne
      by_cases hA : vtA t = i
      · rw [if_pos hA]
        dsimp only [x]
        rw [if_neg]
        rintro ⟨i', rfl⟩
        have : i' = i := hA
        exact hne (by rw [this])
      · rw [if_neg hA]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single (diagT j)]
    · simp [x, vtB, diagT]
    · intro t _ hne
      by_cases hB : vtB t = j
      · rw [if_pos hB]
        dsimp only [x]
        rw [if_neg]
        rintro ⟨j', rfl⟩
        have : j' = j := hB
        exact hne (by rw [this])
      · rw [if_neg hB]
    · intro h; exact absurd (Finset.mem_univ _) h

lemma cont_finset_sum {α ι : Type*} [TopologicalSpace α] (s : Finset ι) (f : ι → α → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) : Continuous (fun a => ∑ i ∈ s, f i a) := by
  induction s using Finset.cons_induction with
  | empty => simpa using continuous_const
  | cons a s ha ih =>
    simp only [Finset.sum_cons]
    exact (hf a (Finset.mem_cons_self a s)).add
      (ih fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi)))

lemma polytope_isCompact (n q : ℕ) : IsCompact (Polytope n q) := by
  have hbox : IsCompact (Set.pi Set.univ (fun _ : VType n q => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset ?_ ?_
  · have hc1 : IsClosed {x : VType n q → ℝ | ∀ t, 0 ≤ x t} := by
      rw [show {x : VType n q → ℝ | ∀ t, 0 ≤ x t} = ⋂ t, {x | 0 ≤ x t} by ext; simp]
      exact isClosed_iInter fun t => isClosed_le continuous_const (continuous_apply t)
    have hc2 : IsClosed {x : VType n q → ℝ | ∀ i : Fin n, ∑ t : VType n q, (if vtA t = i then x t else 0) = 1} := by
      rw [show {x : VType n q → ℝ | ∀ i : Fin n, ∑ t : VType n q, (if vtA t = i then x t else 0) = 1} =
        ⋂ i : Fin n, {x | ∑ t : VType n q, (if vtA t = i then x t else 0) = 1} by ext; simp]
      refine isClosed_iInter fun i => isClosed_eq ?_ continuous_const
      refine cont_finset_sum _ (fun t (x : VType n q → ℝ) => if vtA t = i then x t else 0) fun t _ => ?_
      by_cases h : vtA t = i <;> simp [h, continuous_apply, continuous_const]
    have hc3 : IsClosed {x : VType n q → ℝ | ∀ j : Fin n, ∑ t : VType n q, (if vtB t = j then x t else 0) = 1} := by
      rw [show {x : VType n q → ℝ | ∀ j : Fin n, ∑ t : VType n q, (if vtB t = j then x t else 0) = 1} =
        ⋂ j : Fin n, {x | ∑ t : VType n q, (if vtB t = j then x t else 0) = 1} by ext; simp]
      refine isClosed_iInter fun j => isClosed_eq ?_ continuous_const
      refine cont_finset_sum _ (fun t (x : VType n q → ℝ) => if vtB t = j then x t else 0) fun t _ => ?_
      by_cases h : vtB t = j <;> simp [h, continuous_apply, continuous_const]
    exact hc1.inter (hc2.inter hc3)
  · intro x hx t _
    refine ⟨hx.1 t, ?_⟩
    have hle : (if vtA t = vtA t then x t else 0) ≤
        ∑ t' : VType n q, (if vtA t' = vtA t then x t' else 0) :=
      Finset.single_le_sum (f := fun t' => if vtA t' = vtA t then x t' else 0)
        (fun t' _ => by split_ifs <;> [exact hx.1 t'; exact le_refl 0]) (Finset.mem_univ t)
    simpa [hx.2.1 (vtA t)] using hle

lemma exists_rational_minimizer {n q : ℕ} (hn : 0 < n) (G : Fin n → Fin n → Bool) :
    ∃ (S : Finset (VType n q)) (yQ : VType n q → ℚ),
      (∀ t ∈ S, 0 < yQ t) ∧
      (∀ t ∉ S, yQ t = 0) ∧
      (fun t => (yQ t : ℝ)) ∈ Polytope n q ∧
      (∀ x ∈ Polytope n q, quadR G (fun t => (yQ t : ℝ)) ≤ quadR G x) ∧
      (∀ v : VType n q → ℝ,
        (∀ t ∉ S, v t = 0) →
        (∀ i : Fin n, ∑ t : VType n q, (if vtA t = i then v t else 0) = 0) →
        (∀ j : Fin n, ∑ t : VType n q, (if vtB t = j then v t else 0) = 0) →
        bilinR G (fun t => (yQ t : ℝ)) v = 0) := by
  -- Step 1: minimize quadR G on Polytope n q
  have hcont : Continuous (quadR (q := q) G) := by
    refine cont_finset_sum _ (fun t₁ (x : VType n q → ℝ) => ∑ t₂ : VType n q, (kerK G t₁ t₂ : ℝ) * x t₁ * x t₂) fun t₁ _ => ?_
    refine cont_finset_sum _ (fun t₂ (x : VType n q → ℝ) => (kerK G t₁ t₂ : ℝ) * x t₁ * x t₂) fun t₂ _ => ?_
    exact (continuous_const.mul (continuous_apply t₁)).mul (continuous_apply t₂)
  obtain ⟨xstar, hxstar_mem, hxstar_min⟩ :=
    (polytope_isCompact n q).exists_isMinOn (polytope_nonempty n q) hcont.continuousOn
  let S : Finset (VType n q) := Finset.univ.filter (fun t => 0 < xstar t)
  have hS_ne : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h0 : ∀ t, xstar t = 0 := fun t => by
      have hnt : t ∉ S := by rw [hemp]; exact Finset.notMem_empty t
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnt
      exact le_antisymm hnt (hxstar_mem.1 t)
    have h1 := hxstar_mem.2.1 ⟨0, hn⟩
    have hsum0 : (∑ t : VType n q, (if vtA t = ⟨0, hn⟩ then xstar t else 0)) = 0 :=
      Finset.sum_eq_zero fun t _ => by rw [h0 t]; split_ifs <;> rfl
    rw [hsum0] at h1
    norm_num at h1
  let m₀ : ℝ := S.inf' hS_ne xstar
  have hm₀_pos : 0 < m₀ := by
    rw [Finset.lt_inf'_iff]
    intro t ht; exact (Finset.mem_filter.mp ht).2
  have hm₀_le : ∀ t ∈ S, m₀ ≤ xstar t := fun t ht => Finset.inf'_le xstar ht
  have hxstar_zero : ∀ t ∉ S, xstar t = 0 := fun t ht => by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at ht
    exact le_antisymm ht (hxstar_mem.1 t)
  -- Step 2: stationarity on margin-zero vectors supported on S
  have hstat : ∀ v : VType n q → ℝ,
      (∀ t ∉ S, v t = 0) →
      (∀ i : Fin n, ∑ t : VType n q, (if vtA t = i then v t else 0) = 0) →
      (∀ j : Fin n, ∑ t : VType n q, (if vtB t = j then v t else 0) = 0) →
      bilinR G xstar v = 0 := by
    intro v hv_supp hvA hvB
    by_contra hne
    set g := bilinR G xstar v
    set q2 := quadR G v
    set M : ℝ := 1 + ∑ t ∈ S, |v t|
    have hM_pos : 0 < M := by
      have hnn : 0 ≤ ∑ t ∈ S, |v t| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    have hv_le_M : ∀ t ∈ S, |v t| ≤ M := fun t ht => by
      have h1 : |v t| ≤ ∑ t' ∈ S, |v t'| :=
        Finset.single_le_sum (f := fun t' => |v t'|) (fun _ _ => abs_nonneg _) ht
      linarith
    set step : ℝ := min (m₀ / M) (|g| / (|q2| + 1))
    have hstep_pos : 0 < step :=
      lt_min (div_pos hm₀_pos hM_pos) (div_pos (abs_pos.mpr hne) (by linarith [abs_nonneg q2]))
    set ε : ℝ := if 0 < g then -step else step
    have hε_abs : |ε| = step := by
      dsimp only [ε]; split_ifs
      · exact (abs_neg step).trans (abs_of_pos hstep_pos)
      · exact abs_of_pos hstep_pos
    have hε_g : ε * g = -step * |g| := by
      dsimp only [ε]; split_ifs with hg
      · rw [abs_of_pos hg]
      · have hgn : g < 0 := lt_of_le_of_ne (not_lt.mp hg) hne
        rw [abs_of_neg hgn]; ring
    have hmem : (fun t => xstar t + ε * v t) ∈ Polytope n q := by
      refine ⟨fun t => ?_, fun i => ?_, fun j => ?_⟩
      · by_cases ht : t ∈ S
        · have h1 : |ε * v t| ≤ m₀ := by
            rw [abs_mul, hε_abs]
            calc step * |v t| ≤ (m₀ / M) * M :=
                  mul_le_mul (min_le_left _ _) (hv_le_M t ht) (abs_nonneg _) (le_of_lt (div_pos hm₀_pos hM_pos))
              _ = m₀ := div_mul_cancel₀ m₀ (ne_of_gt hM_pos)
          have h2 : -(ε * v t) ≤ m₀ := le_trans (neg_le_abs _) h1
          linarith [hm₀_le t ht]
        · dsimp only; rw [hv_supp t ht, mul_zero, add_zero]; exact hxstar_mem.1 t
      · calc (∑ t : VType n q, (if vtA t = i then xstar t + ε * v t else 0))
            = (∑ t : VType n q, (if vtA t = i then xstar t else 0)) +
              ε * (∑ t : VType n q, (if vtA t = i then v t else 0)) := by
                rw [Finset.mul_sum, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun t _ => by split_ifs <;> ring
          _ = 1 := by rw [hxstar_mem.2.1 i, hvA i, mul_zero, add_zero]
      · calc (∑ t : VType n q, (if vtB t = j then xstar t + ε * v t else 0))
            = (∑ t : VType n q, (if vtB t = j then xstar t else 0)) +
              ε * (∑ t : VType n q, (if vtB t = j then v t else 0)) := by
                rw [Finset.mul_sum, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun t _ => by split_ifs <;> ring
          _ = 1 := by rw [hxstar_mem.2.2 j, hvB j, mul_zero, add_zero]
    have hmin : quadR G xstar ≤ quadR G (fun t => xstar t + ε * v t) := hxstar_min hmem
    rw [quadR_add_smul] at hmin
    have hsq : ε ^ 2 * q2 ≤ step * |g| := by
      have hε2 : ε ^ 2 = step ^ 2 := by
        rw [← sq_abs ε, hε_abs]
      rw [hε2]
      have hq_le : q2 ≤ |q2| + 1 := by linarith [le_abs_self q2]
      have hst_le : step ≤ |g| / (|q2| + 1) := min_le_right _ _
      calc step ^ 2 * q2 ≤ step ^ 2 * (|q2| + 1) :=
            mul_le_mul_of_nonneg_left hq_le (sq_nonneg step)
        _ = step * (step * (|q2| + 1)) := by ring
        _ ≤ step * |g| := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hstep_pos)
            have hpos : 0 < |q2| + 1 := by linarith [abs_nonneg q2]
            exact (le_div_iff₀ hpos).mp hst_le
    have hneg : 2 * ε * g + ε ^ 2 * q2 ≤ -step * |g| := by
      have : 2 * ε * g = 2 * (ε * g) := by ring
      rw [this, hε_g]
      linarith
    have hpos_sg : 0 < step * |g| := mul_pos hstep_pos (abs_pos.mpr hne)
    linarith
  -- Step 3: Lagrange multipliers α, β : Fin n → ℝ via orthogonal_orthogonal
  let E := EuclideanSpace ℝ {t : VType n q // t ∈ S}
  let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] E :=
    { toFun := fun p => WithLp.toLp 2 (fun s : {t // t ∈ S} => p.1 (vtA s.val) + p.2 (vtB s.val))
      map_add' := fun p₁ p₂ => by
        ext s
        change (p₁.1 (vtA s.val) + p₂.1 (vtA s.val)) + (p₁.2 (vtB s.val) + p₂.2 (vtB s.val)) =
          (p₁.1 (vtA s.val) + p₁.2 (vtB s.val)) + (p₂.1 (vtA s.val) + p₂.2 (vtB s.val))
        ring
      map_smul' := fun c p => by
        ext s
        change c * p.1 (vtA s.val) + c * p.2 (vtB s.val) = c * (p.1 (vtA s.val) + p.2 (vtB s.val))
        ring }
  let W : Submodule ℝ E := LinearMap.range L
  let gVec : E := WithLp.toLp 2 (fun s : {t // t ∈ S} => ∑ t₁ : VType n q, (kerK G t₁ s.val : ℝ) * xstar t₁)
  have hgVec_mem : gVec ∈ W := by
    rw [← Submodule.orthogonal_orthogonal W]
    intro w hw
    let v : VType n q → ℝ := fun t => if h : t ∈ S then w ⟨t, h⟩ else 0
    have hv_supp : ∀ t ∉ S, v t = 0 := fun t ht => dif_neg ht
    have hvA : ∀ i : Fin n, ∑ t : VType n q, (if vtA t = i then v t else 0) = 0 := by
      intro i
      have h0 : @inner ℝ E _ (L (Pi.single i 1, 0)) w = 0 :=
        hw (L (Pi.single i 1, 0)) (LinearMap.mem_range_self L _)
      rw [EuclideanSpace.inner_eq_star_dotProduct] at h0
      simp only [dotProduct, star_trivial, PiLp.toLp_apply, L, LinearMap.coe_mk, AddHom.coe_mk,
        Pi.zero_apply, add_zero] at h0
      have hsum : (∑ t : VType n q, (if vtA t = i then v t else 0)) =
          ∑ s : {t // t ∈ S}, w.ofLp s * (Pi.single (M := fun _ : Fin n => ℝ) i 1) (vtA s.val) := by
        rw [← Finset.sum_subset (Finset.subset_univ S) (fun t _ ht => by simp [hv_supp t ht])]
        rw [← Finset.sum_attach S]
        refine Finset.sum_congr rfl fun s _ => ?_
        dsimp only [v]
        rw [dif_pos s.property]
        by_cases h : vtA s.val = i
        · simp [h]
        · simp [h, Pi.single_eq_of_ne h]
      rw [hsum]; exact h0
    have hvB : ∀ j : Fin n, ∑ t : VType n q, (if vtB t = j then v t else 0) = 0 := by
      intro j
      have h0 : @inner ℝ E _ (L (0, Pi.single j 1)) w = 0 :=
        hw (L (0, Pi.single j 1)) (LinearMap.mem_range_self L _)
      rw [EuclideanSpace.inner_eq_star_dotProduct] at h0
      simp only [dotProduct, star_trivial, PiLp.toLp_apply, L, LinearMap.coe_mk, AddHom.coe_mk,
        Pi.zero_apply, zero_add] at h0
      have hsum : (∑ t : VType n q, (if vtB t = j then v t else 0)) =
          ∑ s : {t // t ∈ S}, w.ofLp s * (Pi.single (M := fun _ : Fin n => ℝ) j 1) (vtB s.val) := by
        rw [← Finset.sum_subset (Finset.subset_univ S) (fun t _ ht => by simp [hv_supp t ht])]
        rw [← Finset.sum_attach S]
        refine Finset.sum_congr rfl fun s _ => ?_
        dsimp only [v]
        rw [dif_pos s.property]
        by_cases h : vtB s.val = j
        · simp [h]
        · simp [h, Pi.single_eq_of_ne h]
      rw [hsum]; exact h0
    have hst := hstat v hv_supp hvA hvB
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial, PiLp.toLp_apply, gVec]
    have hsum : (∑ s : {t // t ∈ S}, (∑ t₁ : VType n q, (kerK G t₁ s.val : ℝ) * xstar t₁) * w.ofLp s) =
        bilinR G xstar v := by
      dsimp only [bilinR]
      rw [Finset.sum_comm]
      rw [← Finset.sum_subset (Finset.subset_univ S) (fun t _ ht => by simp [hv_supp t ht])]
      rw [← Finset.sum_attach S]
      refine Finset.sum_congr rfl fun s _ => ?_
      dsimp only [v]
      rw [dif_pos s.property, Finset.sum_mul]
    rw [hsum]; exact hst
  rcases hgVec_mem with ⟨⟨αR, βR⟩, hαβ⟩
  have hlagR : ∀ t ∈ S, (∑ t₁ ∈ S, (kerK G t₁ t : ℝ) * xstar t₁) = αR (vtA t) + βR (vtB t) := by
    intro t ht
    have h1 : (L (αR, βR)).ofLp ⟨t, ht⟩ = gVec.ofLp ⟨t, ht⟩ := by rw [hαβ]
    simp only [L, gVec, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply] at h1
    rw [h1]
    exact Finset.sum_subset (Finset.subset_univ S) (f := fun t₁ => (kerK G t₁ t : ℝ) * xstar t₁)
      (fun t₁ _ ht₁ => by rw [hxstar_zero t₁ ht₁, mul_zero])
  -- Step 4: apply rational_density_of_linear_system to (xstar|_S, αR, βR)
  let VIdx := {t : VType n q // t ∈ S} ⊕ Fin n ⊕ Fin n
  let EIdx := Fin n ⊕ Fin n ⊕ {t : VType n q // t ∈ S}
  let eV : Fin (Fintype.card VIdx) ≃ VIdx := (Fintype.equivFin VIdx).symm
  let eE : Fin (Fintype.card EIdx) ≃ EIdx := (Fintype.equivFin EIdx).symm
  let A_sys : Fin (Fintype.card EIdx) → Fin (Fintype.card VIdx) → ℚ := fun r c =>
    match eE r, eV c with
    | Sum.inl i, Sum.inl s => if vtA s.val = i then 1 else 0
    | Sum.inr (Sum.inl j), Sum.inl s => if vtB s.val = j then 1 else 0
    | Sum.inr (Sum.inr s₂), Sum.inl s₁ => (kerK G s₁.val s₂.val : ℚ)
    | Sum.inr (Sum.inr s₂), Sum.inr (Sum.inl i) => if vtA s₂.val = i then -1 else 0
    | Sum.inr (Sum.inr s₂), Sum.inr (Sum.inr j) => if vtB s₂.val = j then -1 else 0
    | _, _ => 0
  let b_sys : Fin (Fintype.card EIdx) → ℚ := fun r =>
    match eE r with
    | Sum.inl _ => 1
    | Sum.inr (Sum.inl _) => 1
    | Sum.inr (Sum.inr _) => 0
  let x_sys : Fin (Fintype.card VIdx) → ℝ := fun c =>
    match eV c with
    | Sum.inl s => xstar s.val
    | Sum.inr (Sum.inl i) => αR i
    | Sum.inr (Sum.inr j) => βR j
  have hx_sys : ∀ r, ∑ c, (A_sys r c : ℝ) * x_sys c = (b_sys r : ℝ) := by
    intro r
    rw [Fintype.sum_equiv eV _ (fun v => (A_sys r (eV.symm v) : ℝ) * x_sys (eV.symm v))
      (fun c => by simp)]
    simp only [A_sys, b_sys, x_sys, Equiv.apply_symm_apply]
    rcases he : eE r with i | (j | s₂)
    · rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Rat.cast_zero, zero_mul, Finset.sum_const_zero, add_zero, Rat.cast_one]
      have h1 : (∑ s : {t // t ∈ S}, (Rat.cast (K := ℝ) (if vtA s.val = i then (1 : ℚ) else 0)) * xstar s.val) =
          ∑ t ∈ S, (if vtA t = i then xstar t else 0) := by
        rw [← Finset.sum_attach S]
        refine Finset.sum_congr rfl fun s _ => by split_ifs <;> simp
      rw [h1, Finset.sum_subset (Finset.subset_univ S) (fun t _ ht => by simp [hxstar_zero t ht])]
      exact hxstar_mem.2.1 i
    · rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Rat.cast_zero, zero_mul, Finset.sum_const_zero, add_zero, Rat.cast_one]
      have h1 : (∑ s : {t // t ∈ S}, (Rat.cast (K := ℝ) (if vtB s.val = j then (1 : ℚ) else 0)) * xstar s.val) =
          ∑ t ∈ S, (if vtB t = j then xstar t else 0) := by
        rw [← Finset.sum_attach S]
        refine Finset.sum_congr rfl fun s _ => by split_ifs <;> simp
      rw [h1, Finset.sum_subset (Finset.subset_univ S) (fun t _ ht => by simp [hxstar_zero t ht])]
      exact hxstar_mem.2.2 j
    · rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Rat.cast_zero]
      have h1 : (∑ s₁ : {t // t ∈ S}, (Rat.cast (K := ℝ) (kerK G s₁.val s₂.val : ℚ)) * xstar s₁.val) =
          ∑ t₁ ∈ S, (kerK G t₁ s₂.val : ℝ) * xstar t₁ := by
        rw [← Finset.sum_attach S]
        refine Finset.sum_congr rfl fun s₁ _ => by simp
      have h2 : (∑ i : Fin n, (Rat.cast (K := ℝ) (if vtA s₂.val = i then (-1 : ℚ) else 0)) * αR i) = -αR (vtA s₂.val) := by
        rw [Finset.sum_eq_single (vtA s₂.val)]
        · simp
        · intro i _ hne; simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      have h3 : (∑ j : Fin n, (Rat.cast (K := ℝ) (if vtB s₂.val = j then (-1 : ℚ) else 0)) * βR j) = -βR (vtB s₂.val) := by
        rw [Finset.sum_eq_single (vtB s₂.val)]
        · simp
        · intro j _ hne; simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [h1, h2, h3, hlagR s₂.val s₂.property]; ring
  obtain ⟨y_sys, hy_eq, hy_close⟩ := rational_density_of_linear_system _ _ A_sys b_sys x_sys hx_sys m₀ hm₀_pos
  let yQ : VType n q → ℚ := fun t => if h : t ∈ S then y_sys (eV.symm (Sum.inl ⟨t, h⟩)) else 0
  let αQ : Fin n → ℚ := fun i => y_sys (eV.symm (Sum.inr (Sum.inl i)))
  let βQ : Fin n → ℚ := fun j => y_sys (eV.symm (Sum.inr (Sum.inr j)))
  have hyQ_pos : ∀ t ∈ S, 0 < yQ t := by
    intro t ht
    have hcl := hy_close (eV.symm (Sum.inl ⟨t, ht⟩))
    simp only [x_sys, Equiv.apply_symm_apply] at hcl
    have hlt : 0 < (yQ t : ℝ) := by
      dsimp only [yQ]; rw [dif_pos ht]
      have h1 := (abs_lt.mp hcl).1
      linarith [hm₀_le t ht]
    exact_mod_cast hlt
  have hyQ_zero : ∀ t ∉ S, yQ t = 0 := fun t ht => dif_neg ht
  have hyQ_nonneg : ∀ t, 0 ≤ yQ t := fun t => by
    by_cases ht : t ∈ S
    · exact le_of_lt (hyQ_pos t ht)
    · rw [hyQ_zero t ht]
  have hyQ_row : ∀ i : Fin n, ∑ t : VType n q, (if vtA t = i then yQ t else 0) = 1 := by
    intro i
    have hr := hy_eq (eE.symm (Sum.inl i))
    rw [Fintype.sum_equiv eV _ (fun v => A_sys (eE.symm (Sum.inl i)) (eV.symm v) * y_sys (eV.symm v))
      (fun c => by simp)] at hr
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hr
    simp only [A_sys, b_sys, Equiv.apply_symm_apply, zero_mul, Finset.sum_const_zero, add_zero] at hr
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun t _ ht => by simp [hyQ_zero t ht]),
      ← Finset.sum_attach S]
    rw [← hr]
    refine Finset.sum_congr rfl fun s _ => by dsimp only [yQ]; rw [dif_pos s.property]; split_ifs <;> ring
  have hyQ_col : ∀ j : Fin n, ∑ t : VType n q, (if vtB t = j then yQ t else 0) = 1 := by
    intro j
    have hr := hy_eq (eE.symm (Sum.inr (Sum.inl j)))
    rw [Fintype.sum_equiv eV _ (fun v => A_sys (eE.symm (Sum.inr (Sum.inl j))) (eV.symm v) * y_sys (eV.symm v))
      (fun c => by simp)] at hr
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hr
    simp only [A_sys, b_sys, Equiv.apply_symm_apply, zero_mul, Finset.sum_const_zero, add_zero] at hr
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun t _ ht => by simp [hyQ_zero t ht]),
      ← Finset.sum_attach S]
    rw [← hr]
    refine Finset.sum_congr rfl fun s _ => by dsimp only [yQ]; rw [dif_pos s.property]; split_ifs <;> ring
  have hlagQ : ∀ t ∈ S, (∑ t₁ ∈ S, (kerK G t₁ t : ℚ) * yQ t₁) = αQ (vtA t) + βQ (vtB t) := by
    intro t ht
    have hr := hy_eq (eE.symm (Sum.inr (Sum.inr ⟨t, ht⟩)))
    rw [Fintype.sum_equiv eV _ (fun v => A_sys (eE.symm (Sum.inr (Sum.inr ⟨t, ht⟩))) (eV.symm v) * y_sys (eV.symm v))
      (fun c => by simp)] at hr
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hr
    simp only [A_sys, b_sys, Equiv.apply_symm_apply] at hr
    have h1 : (∑ s₁ : {t // t ∈ S}, (kerK G s₁.val t : ℚ) * y_sys (eV.symm (Sum.inl s₁))) =
        ∑ t₁ ∈ S, (kerK G t₁ t : ℚ) * yQ t₁ := by
      rw [← Finset.sum_attach S]
      refine Finset.sum_congr rfl fun s₁ _ => by dsimp only [yQ]; rw [dif_pos s₁.property]
    have h2 : (∑ i : Fin n, (if vtA t = i then (-1 : ℚ) else 0) * y_sys (eV.symm (Sum.inr (Sum.inl i)))) = -αQ (vtA t) := by
      rw [Finset.sum_eq_single (vtA t)]
      · simp [αQ]
      · intro i _ hne; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have h3 : (∑ j : Fin n, (if vtB t = j then (-1 : ℚ) else 0) * y_sys (eV.symm (Sum.inr (Sum.inr j)))) = -βQ (vtB t) := by
      rw [Finset.sum_eq_single (vtB t)]
      · simp [βQ]
      · intro j _ hne; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1, h2, h3] at hr
    linarith
  let yR : VType n q → ℝ := fun t => (yQ t : ℝ)
  have hyR_mem : yR ∈ Polytope n q := by
    refine ⟨fun t => by dsimp only [yR]; exact_mod_cast hyQ_nonneg t, fun i => ?_, fun j => ?_⟩
    · have h := congrArg (Rat.cast (K := ℝ)) (hyQ_row i)
      simpa [yR, apply_ite] using h
    · have h := congrArg (Rat.cast (K := ℝ)) (hyQ_col j)
      simpa [yR, apply_ite] using h
  have hstatQ : ∀ v : VType n q → ℝ,
      (∀ t ∉ S, v t = 0) →
      (∀ i : Fin n, ∑ t : VType n q, (if vtA t = i then v t else 0) = 0) →
      (∀ j : Fin n, ∑ t : VType n q, (if vtB t = j then v t else 0) = 0) →
      bilinR G yR v = 0 := by
    intro v hv_supp hvA hvB
    dsimp only [bilinR]
    rw [Finset.sum_comm]
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun t _ ht => by simp [hv_supp t ht])]
    have hinner : ∀ t ∈ S, (∑ t₁ : VType n q, (kerK G t₁ t : ℝ) * yR t₁ * v t) =
        ((αQ (vtA t) : ℝ) + (βQ (vtB t) : ℝ)) * v t := by
      intro t ht
      rw [← Finset.sum_mul,
        ← Finset.sum_subset (Finset.subset_univ S) (fun t₁ _ ht₁ => by simp [yR, hyQ_zero t₁ ht₁])]
      have hcast := congrArg (Rat.cast (K := ℝ)) (hlagQ t ht)
      simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, Rat.cast_add] at hcast
      rw [hcast]
    rw [Finset.sum_congr rfl hinner]
    simp_rw [add_mul, Finset.sum_add_distrib]
    have hA0 : (∑ t ∈ S, (αQ (vtA t) : ℝ) * v t) = 0 := by
      rw [Finset.sum_subset (Finset.subset_univ S) (fun t _ ht => by simp [hv_supp t ht])]
      rw [← Finset.sum_fiberwise_of_maps_to (g := vtA) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_eq_zero fun i _ => ?_
      have h1 : (∑ t ∈ Finset.univ.filter (fun t : VType n q => vtA t = i), (αQ (vtA t) : ℝ) * v t) =
          (αQ i : ℝ) * ∑ t : VType n q, (if vtA t = i then v t else 0) := by
        rw [← Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t ht => by rw [(Finset.mem_filter.mp ht).2]
      rw [h1, hvA i, mul_zero]
    have hB0 : (∑ t ∈ S, (βQ (vtB t) : ℝ) * v t) = 0 := by
      rw [Finset.sum_subset (Finset.subset_univ S) (fun t _ ht => by simp [hv_supp t ht])]
      rw [← Finset.sum_fiberwise_of_maps_to (g := vtB) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_eq_zero fun j _ => ?_
      have h1 : (∑ t ∈ Finset.univ.filter (fun t : VType n q => vtB t = j), (βQ (vtB t) : ℝ) * v t) =
          (βQ j : ℝ) * ∑ t : VType n q, (if vtB t = j then v t else 0) := by
        rw [← Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t ht => by rw [(Finset.mem_filter.mp ht).2]
      rw [h1, hvB j, mul_zero]
    rw [hA0, hB0, add_zero]
  have hyR_min : quadR G yR = quadR G xstar := by
    let diff : VType n q → ℝ := fun t => yR t - xstar t
    have hsupp : ∀ t ∉ S, diff t = 0 := fun t ht => by
      simp [diff, yR, hyQ_zero t ht, hxstar_zero t ht]
    have hA : ∀ i : Fin n, ∑ t : VType n q, (if vtA t = i then diff t else 0) = 0 := fun i => by
      have : (∑ t : VType n q, (if vtA t = i then diff t else 0)) =
          (∑ t : VType n q, (if vtA t = i then yR t else 0)) -
          (∑ t : VType n q, (if vtA t = i then xstar t else 0)) := by
        rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun t _ => by split_ifs <;> simp [diff]
      rw [this, hyR_mem.2.1 i, hxstar_mem.2.1 i, sub_self]
    have hB : ∀ j : Fin n, ∑ t : VType n q, (if vtB t = j then diff t else 0) = 0 := fun j => by
      have : (∑ t : VType n q, (if vtB t = j then diff t else 0)) =
          (∑ t : VType n q, (if vtB t = j then yR t else 0)) -
          (∑ t : VType n q, (if vtB t = j then xstar t else 0)) := by
        rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun t _ => by split_ifs <;> simp [diff]
      rw [this, hyR_mem.2.2 j, hxstar_mem.2.2 j, sub_self]
    have h1 := hstat diff hsupp hA hB
    have h2 := hstatQ diff hsupp hA hB
    have hsub : quadR G yR - quadR G xstar = bilinR G yR diff + bilinR G xstar diff := by
      have hyx : bilinR G yR xstar = bilinR G xstar yR := bilinR_symm G yR xstar
      dsimp only [quadR, bilinR, diff] at hyx ⊢
      have hd1 : (∑ t₁ : VType n q, ∑ t₂ : VType n q, (kerK G t₁ t₂ : ℝ) * yR t₁ * (yR t₂ - xstar t₂)) =
          (∑ t₁ : VType n q, ∑ t₂ : VType n q, (kerK G t₁ t₂ : ℝ) * yR t₁ * yR t₂) -
          (∑ t₁ : VType n q, ∑ t₂ : VType n q, (kerK G t₁ t₂ : ℝ) * yR t₁ * xstar t₂) := by
        simp_rw [mul_sub, Finset.sum_sub_distrib]
      have hd2 : (∑ t₁ : VType n q, ∑ t₂ : VType n q, (kerK G t₁ t₂ : ℝ) * xstar t₁ * (yR t₂ - xstar t₂)) =
          (∑ t₁ : VType n q, ∑ t₂ : VType n q, (kerK G t₁ t₂ : ℝ) * xstar t₁ * yR t₂) -
          (∑ t₁ : VType n q, ∑ t₂ : VType n q, (kerK G t₁ t₂ : ℝ) * xstar t₁ * xstar t₂) := by
        simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [hd1, hd2, hyx]; ring
    linarith
  exact ⟨S, yQ, hyQ_pos, hyQ_zero, hyR_mem, fun x hx => by rw [hyR_min]; exact hxstar_min hx, hstatQ⟩

lemma exists_supported_matching {n q : ℕ} (G : Fin n → Fin n → Bool)
    (S : Finset (VType n q)) (yR : VType n q → ℝ)
    (hyR_mem : yR ∈ Polytope n q) (hyR_zero : ∀ t ∉ S, yR t = 0) :
    ∃ uM : VType n q → ℕ,
      (∀ t ∉ S, uM t = 0) ∧ ValidInt 1 uM ∧ quadNat G uM ≤ 2 * Nat.choose n 2 := by
  let nbr : Fin n → Finset (Fin n) := fun i =>
    Finset.univ.filter (fun j : Fin n => ∃ t ∈ S, vtA t = i ∧ vtB t = j)
  have hHall : ∀ I : Finset (Fin n), I.card ≤ (I.biUnion nbr).card := by
    intro I
    have hR : (I.card : ℝ) ≤ ((I.biUnion nbr).card : ℝ) := by
      calc (I.card : ℝ)
          = ∑ i ∈ I, (1 : ℝ) := by simp
        _ = ∑ i ∈ I, ∑ t : VType n q, (if vtA t = i then yR t else 0) :=
            Finset.sum_congr rfl fun i _ => (hyR_mem.2.1 i).symm
        _ = ∑ t : VType n q, (if vtA t ∈ I then yR t else 0) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun t _ => ?_
            by_cases ht : vtA t ∈ I
            · rw [if_pos ht, Finset.sum_eq_single (vtA t)]
              · simp
              · intro i _ hne; simp [Ne.symm hne]
              · intro h; exact absurd ht h
            · rw [if_neg ht]
              refine Finset.sum_eq_zero fun i hi => if_neg fun (h : vtA t = i) => ht (h ▸ hi)
        _ ≤ ∑ t : VType n q, (if vtB t ∈ I.biUnion nbr then yR t else 0) := by
            refine Finset.sum_le_sum fun t _ => ?_
            by_cases hA : vtA t ∈ I
            · rw [if_pos hA]
              by_cases hS : t ∈ S
              · have hB : vtB t ∈ I.biUnion nbr :=
                  Finset.mem_biUnion.mpr ⟨vtA t, hA, Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, hS, rfl, rfl⟩⟩
                rw [if_pos hB]
              · rw [hyR_zero t hS]; split_ifs <;> linarith
            · rw [if_neg hA]
              split_ifs
              · exact hyR_mem.1 t
              · exact le_refl 0
        _ = ∑ j ∈ I.biUnion nbr, ∑ t : VType n q, (if vtB t = j then yR t else 0) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun t _ => ?_
            by_cases ht : vtB t ∈ I.biUnion nbr
            · rw [if_pos ht, Finset.sum_eq_single (vtB t)]
              · simp
              · intro j _ hne; simp [Ne.symm hne]
              · intro h; exact absurd ht h
            · rw [if_neg ht]
              exact (Finset.sum_eq_zero fun j hj => if_neg fun (h : vtB t = j) => ht (h ▸ hj)).symm
        _ = ∑ j ∈ I.biUnion nbr, (1 : ℝ) := Finset.sum_congr rfl fun j _ => hyR_mem.2.2 j
        _ = ((I.biUnion nbr).card : ℝ) := by simp
    exact_mod_cast hR
  obtain ⟨σ, hσ_inj, hσ_mem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective nbr).mp hHall
  have hσ_bij : Function.Bijective σ := (Finite.injective_iff_bijective).mp hσ_inj
  have hex_tM : ∃ tM : Fin n → VType n q, ∀ i : Fin n, tM i ∈ S ∧ vtA (tM i) = i ∧ vtB (tM i) = σ i :=
    ⟨fun i => (Finset.mem_filter.mp (hσ_mem i)).2.choose,
     fun i => (Finset.mem_filter.mp (hσ_mem i)).2.choose_spec⟩
  obtain ⟨tM, htM⟩ := hex_tM
  have htM_inj : Function.Injective tM := fun i₁ i₂ h => by
    have := congrArg vtA h; rw [(htM i₁).2.1, (htM i₂).2.1] at this; exact this
  let uM : VType n q → ℕ := fun t => if ∃ i : Fin n, tM i = t then 1 else 0
  have huM_supp : ∀ t ∉ S, uM t = 0 := fun t ht => if_neg fun ⟨i, hi⟩ => ht (hi ▸ (htM i).1)
  have huM_valid : ValidInt 1 uM := by
    refine ⟨fun i => ?_, fun j => ?_⟩
    · rw [Finset.sum_eq_single (tM i)]
      · simp [uM, (htM i).2.1]
      · intro t _ hne
        by_cases hA : vtA t = i
        · rw [if_pos hA]; dsimp only [uM]; rw [if_neg]
          rintro ⟨i', rfl⟩
          have : i' = i := by rw [← (htM i').2.1]; exact hA
          exact hne (by rw [this])
        · rw [if_neg hA]
      · intro h; exact absurd (Finset.mem_univ _) h
    · obtain ⟨i₀, hi₀⟩ := hσ_bij.2 j
      rw [Finset.sum_eq_single (tM i₀)]
      · simp [uM, (htM i₀).2.2, hi₀]
      · intro t _ hne
        by_cases hB : vtB t = j
        · rw [if_pos hB]; dsimp only [uM]; rw [if_neg]
          rintro ⟨i', rfl⟩
          have : σ i' = σ i₀ := by rw [← (htM i').2.2, hB, hi₀]
          exact hne (by rw [hσ_inj this])
        · rw [if_neg hB]
      · intro h; exact absurd (Finset.mem_univ _) h
  have hquad_uM : quadNat G uM ≤ 2 * Nat.choose n 2 := by
    have hsum : quadNat G uM = ∑ i : Fin n, ∑ j : Fin n, kerK G (tM i) (tM j) := by
      dsimp only [quadNat]
      have hstep : ∀ f : VType n q → ℕ, (∑ t : VType n q, f t * uM t) = ∑ i : Fin n, f (tM i) := by
        intro f
        rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image tM))]
        · rw [Finset.sum_image (fun i _ j _ h => htM_inj h)]
          refine Finset.sum_congr rfl fun i _ => by simp [uM]
        · intro t _ ht
          have hno : ¬∃ i : Fin n, tM i = t := fun ⟨i, hi⟩ => ht (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
          simp [uM, hno]
      have h1 : (∑ t₁ : VType n q, ∑ t₂ : VType n q, kerK G t₁ t₂ * uM t₁ * uM t₂) =
          ∑ t₁ : VType n q, (∑ t₂ : VType n q, kerK G t₁ t₂ * uM t₂) * uM t₁ := by
        refine Finset.sum_congr rfl fun t₁ _ => ?_
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun t₂ _ => by ring
      rw [h1, hstep (fun t₁ => ∑ t₂ : VType n q, kerK G t₁ t₂ * uM t₂)]
      refine Finset.sum_congr rfl fun i _ => hstep (fun t₂ => kerK G (tM i) t₂)
    rw [hsum]
    have hle : (∑ i : Fin n, ∑ j : Fin n, kerK G (tM i) (tM j)) ≤
        ∑ i : Fin n, ∑ j : Fin n, (if i = j then 0 else 1) := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      split_ifs with h
      · subst h; rw [kerK_self]
      · exact kerK_le_one G _ _
    have hcnt : (∑ i : Fin n, ∑ j : Fin n, (if i = j then 0 else 1)) = n * (n - 1) := by
      have hinner : ∀ i : Fin n, (∑ j : Fin n, (if i = j then 0 else 1)) = n - 1 := by
        intro i
        have h1 : (∑ j : Fin n, (if i = j then 0 else 1)) + (∑ j : Fin n, (if i = j then 1 else 0)) = n := by
          rw [← Finset.sum_add_distrib]
          simp only [show ∀ j : Fin n, (if i = j then 0 else 1) + (if i = j then 1 else 0) = 1 by
            intro j; split_ifs <;> rfl, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
        have h2 : (∑ j : Fin n, (if i = j then 1 else 0)) = 1 := by simp
        omega
      simp [hinner]
    have hch : 2 * Nat.choose n 2 = n * (n - 1) := by
      rw [Nat.choose_two_right]
      have hev : Even (n * (n - 1)) := Nat.even_mul_pred_self n
      rcases hev with ⟨k, hk⟩
      omega
    omega
  exact ⟨uM, huM_supp, huM_valid, hquad_uM⟩

lemma exists_D_for_pair {n q : ℕ} (hn : 0 < n) (G : Fin n → Fin n → Bool) :
    ∃ D : ℕ, 0 < D ∧ ∀ b : ℕ, 0 < b →
      b ^ 2 * optDef hn q G D ≤ D ^ 2 * optDef hn q G b ∧
      D ^ 2 * optDef hn q G b ≤ b ^ 2 * optDef hn q G D + (b % D) ^ 2 * D ^ 2 * Nat.choose n 2 := by
  obtain ⟨S, yQ, hyQ_pos, hyQ_zero, hyR_mem, hyR_min_all, hstatQ⟩ := exists_rational_minimizer (q := q) hn G
  let yR : VType n q → ℝ := fun t => (yQ t : ℝ)
  have hyQ_nonneg : ∀ t, 0 ≤ yQ t := fun t => by
    by_cases ht : t ∈ S
    · exact le_of_lt (hyQ_pos t ht)
    · rw [hyQ_zero t ht]
  -- Step 5: clear denominators D > 0 to build Nstar
  let D : ℕ := ∏ t : VType n q, (yQ t).den
  have hD_pos : 0 < D := Finset.prod_pos fun t _ => (yQ t).pos
  let Nstar : VType n q → ℕ := fun t => (D / (yQ t).den) * (yQ t).num.toNat
  have hNstar_cast : ∀ t : VType n q, (Nstar t : ℝ) = (D : ℝ) * yR t := by
    intro t
    have hdvd : (yQ t).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ t)
    have hnum_nn : 0 ≤ (yQ t).num := Rat.num_nonneg.mpr (hyQ_nonneg t)
    have hq : (Nstar t : ℚ) = (D : ℚ) * yQ t := by
      dsimp only [Nstar]
      rw [Nat.cast_mul, Nat.cast_div hdvd (by exact_mod_cast (yQ t).den_nz)]
      have htn : ((yQ t).num.toNat : ℚ) = ((yQ t).num : ℚ) := by
        exact_mod_cast Int.toNat_of_nonneg hnum_nn
      rw [htn]
      conv_rhs => rw [← Rat.num_div_den (yQ t)]
      ring
    have hr := congrArg (Rat.cast (K := ℝ)) hq
    simpa [yR] using hr
  have hNstar_valid : ValidInt D Nstar := by
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have hR : ((∑ t : VType n q, (if vtA t = i then Nstar t else 0) : ℕ) : ℝ) = (D : ℝ) := by
        simp only [Nat.cast_sum, apply_ite, Nat.cast_zero, hNstar_cast]
        rw [show (∑ t : VType n q, if vtA t = i then (D : ℝ) * yR t else 0) =
            (D : ℝ) * ∑ t : VType n q, (if vtA t = i then yR t else 0) by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t _ => by split_ifs <;> ring]
        rw [hyR_mem.2.1 i, mul_one]
      exact_mod_cast hR
    · have hR : ((∑ t : VType n q, (if vtB t = j then Nstar t else 0) : ℕ) : ℝ) = (D : ℝ) := by
        simp only [Nat.cast_sum, apply_ite, Nat.cast_zero, hNstar_cast]
        rw [show (∑ t : VType n q, if vtB t = j then (D : ℝ) * yR t else 0) =
            (D : ℝ) * ∑ t : VType n q, (if vtB t = j then yR t else 0) by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t _ => by split_ifs <;> ring]
        rw [hyR_mem.2.2 j, mul_one]
      exact_mod_cast hR
  have hquad_Nstar : (quadNat G Nstar : ℝ) = (D : ℝ) ^ 2 * quadR G yR := by
    dsimp only [quadNat, quadR]
    simp only [Nat.cast_sum, Nat.cast_mul, hNstar_cast]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t₂ _ => by ring
  -- Lower bound for every b > 0: b^2 * quadR G yR ≤ 2 * optDef hn q G b
  have hlb_all : ∀ b : ℕ, 0 < b → (b : ℝ) ^ 2 * quadR G yR ≤ (2 * optDef hn q G b : ℝ) := by
    intro b hb
    obtain ⟨Nb, hNb_val, hNb_le⟩ := exists_validInt_optDef (q := q) (b := b) hn G
    let xb : VType n q → ℝ := fun t => (Nb t : ℝ) / (b : ℝ)
    have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    have hxb_mem : xb ∈ Polytope n q := by
      refine ⟨fun t => div_nonneg (Nat.cast_nonneg _) (le_of_lt hbR), fun i => ?_, fun j => ?_⟩
      · have h1 := congrArg (Nat.cast (R := ℝ)) (hNb_val.1 i)
        simp only [Nat.cast_sum, apply_ite, Nat.cast_zero] at h1
        rw [show (∑ t : VType n q, if vtA t = i then xb t else 0) =
            (∑ t : VType n q, if vtA t = i then (Nb t : ℝ) else 0) / (b : ℝ) by
              rw [Finset.sum_div]; refine Finset.sum_congr rfl fun t _ => by split_ifs <;> simp [xb]]
        rw [h1, div_self (ne_of_gt hbR)]
      · have h1 := congrArg (Nat.cast (R := ℝ)) (hNb_val.2 j)
        simp only [Nat.cast_sum, apply_ite, Nat.cast_zero] at h1
        rw [show (∑ t : VType n q, if vtB t = j then xb t else 0) =
            (∑ t : VType n q, if vtB t = j then (Nb t : ℝ) else 0) / (b : ℝ) by
              rw [Finset.sum_div]; refine Finset.sum_congr rfl fun t _ => by split_ifs <;> simp [xb]]
        rw [h1, div_self (ne_of_gt hbR)]
    have hmin_b : quadR G yR ≤ quadR G xb := hyR_min_all xb hxb_mem
    have hq_xb : (b : ℝ) ^ 2 * quadR G xb = (quadNat G Nb : ℝ) := by
      dsimp only [quadR, quadNat, xb]
      simp only [Nat.cast_sum, Nat.cast_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t₂ _ => ?_
      field_simp [ne_of_gt hbR]
    have hleR : (quadNat G Nb : ℝ) ≤ (2 * optDef hn q G b : ℝ) := by exact_mod_cast hNb_le
    calc (b : ℝ) ^ 2 * quadR G yR ≤ (b : ℝ) ^ 2 * quadR G xb :=
          mul_le_mul_of_nonneg_left hmin_b (sq_nonneg _)
      _ = (quadNat G Nb : ℝ) := hq_xb
      _ ≤ (2 * optDef hn q G b : ℝ) := hleR
  have hoptD_eq : (2 * optDef hn q G D : ℝ) = (D : ℝ) ^ 2 * quadR G yR := by
    have h1 := hlb_all D hD_pos
    have h2 : (2 * optDef hn q G D : ℝ) ≤ (quadNat G Nstar : ℝ) := by
      exact_mod_cast two_mul_optDef_le_quadNat hn G Nstar hNstar_valid
    rw [hquad_Nstar] at h2
    linarith
  -- Step 6: supported perfect matching via Hall's Marriage Theorem
  obtain ⟨uM, huM_supp, huM_valid, hquad_uM⟩ :=
    exists_supported_matching G S yR hyR_mem (fun t ht => by simp [yR, hyQ_zero t ht])
  -- Step 7: prove both inequalities for D and every b > 0
  refine ⟨D, hD_pos, fun b hb => ⟨?_, ?_⟩⟩
  · -- First inequality: b^2 * opt D ≤ D^2 * opt b
    have h1 : (2 : ℝ) * ((b : ℝ) ^ 2 * (optDef hn q G D : ℝ)) ≤
        (2 : ℝ) * ((D : ℝ) ^ 2 * (optDef hn q G b : ℝ)) := by
      calc (2 : ℝ) * ((b : ℝ) ^ 2 * (optDef hn q G D : ℝ))
          = (b : ℝ) ^ 2 * (2 * optDef hn q G D : ℝ) := by ring
        _ = (b : ℝ) ^ 2 * ((D : ℝ) ^ 2 * quadR G yR) := by rw [hoptD_eq]
        _ = (D : ℝ) ^ 2 * ((b : ℝ) ^ 2 * quadR G yR) := by ring
        _ ≤ (D : ℝ) ^ 2 * (2 * optDef hn q G b : ℝ) :=
            mul_le_mul_of_nonneg_left (hlb_all b hb) (sq_nonneg _)
        _ = (2 : ℝ) * ((D : ℝ) ^ 2 * (optDef hn q G b : ℝ)) := by ring
    have h2 : (b : ℝ) ^ 2 * (optDef hn q G D : ℝ) ≤ (D : ℝ) ^ 2 * (optDef hn q G b : ℝ) := by linarith
    exact_mod_cast h2
  · -- Second inequality: D^2 * opt b ≤ b^2 * opt D + (b % D)^2 * D^2 * C(n, 2)
    set m := b / D
    set r := b % D
    have hbmr : b = m * D + r := by
      have := Nat.div_add_mod b D; rw [mul_comm] at this; exact this.symm
    let Nb : VType n q → ℕ := fun t => m * Nstar t + r * uM t
    have hNb_valid : ValidInt b Nb := by
      refine ⟨fun i => ?_, fun j => ?_⟩
      · calc (∑ t : VType n q, if vtA t = i then m * Nstar t + r * uM t else 0)
            = m * (∑ t : VType n q, if vtA t = i then Nstar t else 0) +
              r * (∑ t : VType n q, if vtA t = i then uM t else 0) := by
                rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun t _ => by split_ifs <;> ring
          _ = m * D + r * 1 := by rw [hNstar_valid.1 i, huM_valid.1 i]
          _ = b := by omega
      · calc (∑ t : VType n q, if vtB t = j then m * Nstar t + r * uM t else 0)
            = m * (∑ t : VType n q, if vtB t = j then Nstar t else 0) +
              r * (∑ t : VType n q, if vtB t = j then uM t else 0) := by
                rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun t _ => by split_ifs <;> ring
          _ = m * D + r * 1 := by rw [hNstar_valid.2 j, huM_valid.2 j]
          _ = b := by omega
    let v : VType n q → ℝ := fun t => (uM t : ℝ) - yR t
    have hv_supp : ∀ t ∉ S, v t = 0 := fun t ht => by
      simp [v, huM_supp t ht, yR, hyQ_zero t ht]
    have hvA : ∀ i : Fin n, ∑ t : VType n q, (if vtA t = i then v t else 0) = 0 := fun i => by
      have h1 := congrArg (Nat.cast (R := ℝ)) (huM_valid.1 i)
      simp only [Nat.cast_sum, apply_ite, Nat.cast_zero, Nat.cast_one] at h1
      have h2 : (∑ t : VType n q, if vtA t = i then v t else 0) =
          (∑ t : VType n q, if vtA t = i then (uM t : ℝ) else 0) -
          (∑ t : VType n q, if vtA t = i then yR t else 0) := by
        rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun t _ => by split_ifs <;> simp [v]
      rw [h2, h1, hyR_mem.2.1 i, sub_self]
    have hvB : ∀ j : Fin n, ∑ t : VType n q, (if vtB t = j then v t else 0) = 0 := fun j => by
      have h1 := congrArg (Nat.cast (R := ℝ)) (huM_valid.2 j)
      simp only [Nat.cast_sum, apply_ite, Nat.cast_zero, Nat.cast_one] at h1
      have h2 : (∑ t : VType n q, if vtB t = j then v t else 0) =
          (∑ t : VType n q, if vtB t = j then (uM t : ℝ) else 0) -
          (∑ t : VType n q, if vtB t = j then yR t else 0) := by
        rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun t _ => by split_ifs <;> simp [v]
      rw [h2, h1, hyR_mem.2.2 j, sub_self]
    have hbv0 : bilinR G yR v = 0 := hstatQ v hv_supp hvA hvB
    have hNb_eq : (fun t => (Nb t : ℝ)) = fun t => (b : ℝ) * yR t + (r : ℝ) * v t := by
      funext t
      have hbmrR : (b : ℝ) = (m : ℝ) * (D : ℝ) + (r : ℝ) := by exact_mod_cast hbmr
      dsimp only [Nb, v]
      simp only [Nat.cast_add, Nat.cast_mul, hNstar_cast]
      rw [hbmrR]; ring
    have hquad_Nb : (quadNat G Nb : ℝ) = (b : ℝ) ^ 2 * quadR G yR + (r : ℝ) ^ 2 * quadR G v := by
      have h1 : (quadNat G Nb : ℝ) = quadR G (fun t => (Nb t : ℝ)) := by
        dsimp only [quadNat, quadR]; simp
      rw [h1, hNb_eq, quadR_add_smul]
      have hsc1 : quadR G (fun t => (b : ℝ) * yR t) = (b : ℝ) ^ 2 * quadR G yR := by
        dsimp only [quadR]; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t₁ _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t₂ _ => by ring
      have hsc2 : bilinR G (fun t => (b : ℝ) * yR t) v = (b : ℝ) * bilinR G yR v := by
        dsimp only [bilinR]; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t₁ _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t₂ _ => by ring
      rw [hsc1, hsc2, hbv0]; ring
    have hquad_v_le : quadR G v ≤ 2 * (Nat.choose n 2 : ℝ) := by
      have huM_eq : (fun t => (uM t : ℝ)) = fun t => yR t + 1 * v t := by
        funext t; dsimp only [v]; ring
      have hexp : (quadNat G uM : ℝ) = quadR G yR + quadR G v := by
        have h1 : (quadNat G uM : ℝ) = quadR G (fun t => (uM t : ℝ)) := by
          dsimp only [quadNat, quadR]; simp
        rw [h1, huM_eq, quadR_add_smul, hbv0]; ring
      have hnn : 0 ≤ quadR G yR := quadR_nonneg_of_nonneg G yR hyR_mem.1
      have hle : (quadNat G uM : ℝ) ≤ 2 * (Nat.choose n 2 : ℝ) := by exact_mod_cast hquad_uM
      linarith
    have hoptb_le : (2 * optDef hn q G b : ℝ) ≤ (quadNat G Nb : ℝ) := by
      exact_mod_cast two_mul_optDef_le_quadNat hn G Nb hNb_valid
    have hineq : (2 : ℝ) * ((D : ℝ) ^ 2 * (optDef hn q G b : ℝ)) ≤
        (2 : ℝ) * ((b : ℝ) ^ 2 * (optDef hn q G D : ℝ) + (r : ℝ) ^ 2 * (D : ℝ) ^ 2 * (Nat.choose n 2 : ℝ)) := by
      calc (2 : ℝ) * ((D : ℝ) ^ 2 * (optDef hn q G b : ℝ))
          = (D : ℝ) ^ 2 * (2 * optDef hn q G b : ℝ) := by ring
        _ ≤ (D : ℝ) ^ 2 * (quadNat G Nb : ℝ) :=
            mul_le_mul_of_nonneg_left hoptb_le (sq_nonneg _)
        _ = (D : ℝ) ^ 2 * ((b : ℝ) ^ 2 * quadR G yR + (r : ℝ) ^ 2 * quadR G v) := by rw [hquad_Nb]
        _ ≤ (D : ℝ) ^ 2 * ((b : ℝ) ^ 2 * quadR G yR + (r : ℝ) ^ 2 * (2 * (Nat.choose n 2 : ℝ))) := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            have := mul_le_mul_of_nonneg_left hquad_v_le (sq_nonneg (r : ℝ))
            linarith
        _ = (b : ℝ) ^ 2 * ((D : ℝ) ^ 2 * quadR G yR) +
            2 * ((r : ℝ) ^ 2 * (D : ℝ) ^ 2 * (Nat.choose n 2 : ℝ)) := by ring
        _ = (b : ℝ) ^ 2 * (2 * optDef hn q G D : ℝ) +
            2 * ((r : ℝ) ^ 2 * (D : ℝ) ^ 2 * (Nat.choose n 2 : ℝ)) := by rw [← hoptD_eq]
        _ = (2 : ℝ) * ((b : ℝ) ^ 2 * (optDef hn q G D : ℝ) +
            (r : ℝ) ^ 2 * (D : ℝ) ^ 2 * (Nat.choose n 2 : ℝ)) := by ring
    have hineq' : (D : ℝ) ^ 2 * (optDef hn q G b : ℝ) ≤
        (b : ℝ) ^ 2 * (optDef hn q G D : ℝ) + (r : ℝ) ^ 2 * (D : ℝ) ^ 2 * (Nat.choose n 2 : ℝ) := by
      linarith
    exact_mod_cast hineq'

-- Part 5: Common multiple across all q and G

lemma lift_to_multiple {n q D₀ D : ℕ} (hn : 0 < n) (G : Fin n → Fin n → Bool)
    (hD₀ : 0 < D₀) (hdvd : D₀ ∣ D) (hD : 0 < D)
    (hwork : ∀ b : ℕ, 0 < b →
      b ^ 2 * optDef hn q G D₀ ≤ D₀ ^ 2 * optDef hn q G b ∧
      D₀ ^ 2 * optDef hn q G b ≤ b ^ 2 * optDef hn q G D₀ + (b % D₀) ^ 2 * D₀ ^ 2 * Nat.choose n 2) :
    ∀ b : ℕ, 0 < b →
      b ^ 2 * optDef hn q G D ≤ D ^ 2 * optDef hn q G b ∧
      D ^ 2 * optDef hn q G b ≤ b ^ 2 * optDef hn q G D + (b % D) ^ 2 * D ^ 2 * Nat.choose n 2 := by
  rcases hdvd with ⟨k, rfl⟩
  have hk : 0 < k := by
    by_contra h; have hk0 : k = 0 := by omega
    rw [hk0, mul_zero] at hD; omega
  have hD_at := hwork (D₀ * k) hD
  have hmod0 : (D₀ * k) % D₀ = 0 := Nat.mul_mod_right D₀ k
  rw [hmod0] at hD_at
  have hopt_mul : optDef hn q G (D₀ * k) = k ^ 2 * optDef hn q G D₀ := by
    have hD₀2 : 0 < D₀ ^ 2 := by positivity
    have h1 : D₀ ^ 2 * (k ^ 2 * optDef hn q G D₀) = (D₀ * k) ^ 2 * optDef hn q G D₀ := by ring
    have h2 : D₀ ^ 2 * optDef hn q G (D₀ * k) = D₀ ^ 2 * (k ^ 2 * optDef hn q G D₀) := by
      have ha : D₀ ^ 2 * (k ^ 2 * optDef hn q G D₀) ≤ D₀ ^ 2 * optDef hn q G (D₀ * k) := by
        rw [h1]; exact hD_at.1
      have hb : D₀ ^ 2 * optDef hn q G (D₀ * k) ≤ D₀ ^ 2 * (k ^ 2 * optDef hn q G D₀) := by
        rw [h1]; simpa using hD_at.2
      exact le_antisymm hb ha
    exact Nat.eq_of_mul_eq_mul_left hD₀2 h2
  intro b hb
  have hb_at := hwork b hb
  rw [hopt_mul]
  constructor
  · calc b ^ 2 * (k ^ 2 * optDef hn q G D₀)
        = k ^ 2 * (b ^ 2 * optDef hn q G D₀) := by ring
      _ ≤ k ^ 2 * (D₀ ^ 2 * optDef hn q G b) := Nat.mul_le_mul_left (k ^ 2) hb_at.1
      _ = (D₀ * k) ^ 2 * optDef hn q G b := by ring
  · have hmod_le : b % D₀ ≤ b % (D₀ * k) := by
      have h1 : b % D₀ = (b % (D₀ * k)) % D₀ := by
        conv_lhs => rw [← Nat.div_add_mod b (D₀ * k)]
        rw [mul_assoc, Nat.mul_add_mod]
      rw [h1]
      exact Nat.mod_le _ _
    have hmod_sq : (b % D₀) ^ 2 ≤ (b % (D₀ * k)) ^ 2 := Nat.pow_le_pow_left hmod_le 2
    calc (D₀ * k) ^ 2 * optDef hn q G b
        = k ^ 2 * (D₀ ^ 2 * optDef hn q G b) := by ring
      _ ≤ k ^ 2 * (b ^ 2 * optDef hn q G D₀ + (b % D₀) ^ 2 * D₀ ^ 2 * Nat.choose n 2) :=
          Nat.mul_le_mul_left (k ^ 2) hb_at.2
      _ = b ^ 2 * (k ^ 2 * optDef hn q G D₀) + (b % D₀) ^ 2 * (D₀ * k) ^ 2 * Nat.choose n 2 := by ring
      _ ≤ b ^ 2 * (k ^ 2 * optDef hn q G D₀) + (b % (D₀ * k)) ^ 2 * (D₀ * k) ^ 2 * Nat.choose n 2 := by
          refine Nat.add_le_add_left ?_ _
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hmod_sq)

lemma main_proof (n : ℕ) (hn : 0 < n) :
    ∃ D : ℕ, 0 < D ∧ ∀ q : ℕ, ∀ G : Fin n → Fin n → Bool, ∀ b : ℕ, 0 < b →
      b ^ 2 * optDef hn q G D ≤ D ^ 2 * optDef hn q G b ∧
      D ^ 2 * optDef hn q G b ≤ b ^ 2 * optDef hn q G D + (b % D) ^ 2 * D ^ 2 * Nat.choose n 2 := by
  let PIdx := Fin n × (Fin n → Fin n → Bool)
  have hex : ∀ p : PIdx, ∃ D₀ : ℕ, 0 < D₀ ∧ ∀ b : ℕ, 0 < b →
      b ^ 2 * optDef hn p.1.val p.2 D₀ ≤ D₀ ^ 2 * optDef hn p.1.val p.2 b ∧
      D₀ ^ 2 * optDef hn p.1.val p.2 b ≤
        b ^ 2 * optDef hn p.1.val p.2 D₀ + (b % D₀) ^ 2 * D₀ ^ 2 * Nat.choose n 2 :=
    fun p => exists_D_for_pair hn p.2
  have hex_f : ∃ f : PIdx → ℕ, ∀ p : PIdx, 0 < f p ∧ ∀ b : ℕ, 0 < b →
      b ^ 2 * optDef hn p.1.val p.2 (f p) ≤ (f p) ^ 2 * optDef hn p.1.val p.2 b ∧
      (f p) ^ 2 * optDef hn p.1.val p.2 b ≤
        b ^ 2 * optDef hn p.1.val p.2 (f p) + (b % f p) ^ 2 * (f p) ^ 2 * Nat.choose n 2 :=
    ⟨fun p => (hex p).choose, fun p => (hex p).choose_spec⟩
  obtain ⟨f, hf⟩ := hex_f
  let D : ℕ := ∏ p : PIdx, f p
  have hD_pos : 0 < D := Finset.prod_pos fun p _ => (hf p).1
  refine ⟨D, hD_pos, fun q G b hb => ?_⟩
  by_cases hq : q < n
  · let p : PIdx := (⟨q, hq⟩, G)
    exact lift_to_multiple hn G (hf p).1 (Finset.dvd_prod_of_mem f (Finset.mem_univ p)) hD_pos (hf p).2 b hb
  · have hge : n ≤ q := Nat.le_of_not_lt hq
    rw [optDef_eq_zero_of_ge hn hge G D, optDef_eq_zero_of_ge hn hge G b]
    simp

end PEqualNP.Outside.L_meta_25732

theorem PEqualNP.Outside.L_meta_25732 :
∀ (n : ℕ) (hn : 0 < n), ∃ D : ℕ, 0 < D ∧ ∀ q : ℕ,
  let fits := fun (s : ℕ) (G : Fin s → Fin s → Bool) (budget : ℕ) =>
    ∃ (π : Equiv.Perm (Fin s)) (rf cf : Fin s → Bool) (R C : Fin q → Finset (Fin s))
      (out : Finset (Fin s) → (Fin q → Bool) → Bool),
      ((Finset.univ : Finset (Fin s × Fin s)).filter (fun z =>
        out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
          Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ budget
  ∀ G : Fin n → Fin n → Bool,
    let opt := fun (b : ℕ) => sInf {e : ℕ | fits (n*b)
      (fun i j => G ⟨i.val % n, Nat.mod_lt _ hn⟩ ⟨j.val % n, Nat.mod_lt _ hn⟩) e}
    ∀ b : ℕ, 0 < b →
      b^2 * opt D ≤ D^2 * opt b ∧
      D^2 * opt b ≤ b^2 * opt D + (b%D)^2 * D^2 * Nat.choose n 2 := by
  intro n hn
  obtain ⟨D, hD, hmain⟩ := PEqualNP.Outside.L_meta_25732.main_proof n hn
  exact ⟨D, hD, fun q G b hb => hmain q G b hb⟩

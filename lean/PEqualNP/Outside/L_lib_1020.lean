import PEqualNP.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace PEqualNP.Outside.L_lib_1020_aux

open scoped BigOperators Matrix

private lemma pow_eq_pow_iff_modEq {q : ℕ} {ζ : ℂ} (hq : 2 ≤ q) (hζ : IsPrimitiveRoot ζ q)
    (x y : ℕ) : ζ ^ x = ζ ^ y ↔ x % q = y % q := by
  have hq0 : 0 < q := by omega
  have hx : ζ ^ x = ζ ^ (x % q) := by
    conv_lhs => rw [← Nat.div_add_mod x q, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have hy : ζ ^ y = ζ ^ (y % q) := by
    conv_lhs => rw [← Nat.div_add_mod y q, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  rw [hx, hy]
  constructor
  · intro h
    exact hζ.pow_inj (Nat.mod_lt x hq0) (Nat.mod_lt y hq0) h
  · intro h
    rw [h]

private def phaseColor {b q : ℕ} (s : (Fin b × Fin 2) × (Fin b × Fin 2) → ℕ)
    (r : Fin b) (j : Fin b × Fin 2) : ZMod q :=
  (s ((r, 1), j) : ZMod q) - (s ((r, 0), j) : ZMod q)

private lemma det_block2_ne_zero_iff {b q : ℕ} {ζ : ℂ} (hq : 2 ≤ q) (hζ : IsPrimitiveRoot ζ q)
    (s : (Fin b × Fin 2) × (Fin b × Fin 2) → ℕ) (π : Equiv.Perm (Fin b × Fin 2)) :
    Matrix.det (fun i j => if i.1 = (π j).1 then ζ ^ (s (i, j)) else 0 :
        Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ) ≠ 0 ↔
      ∀ r : Fin b,
        phaseColor (q := q) s r (π.symm (r, 0)) ≠ phaseColor (q := q) s r (π.symm (r, 1)) := by
  let M : Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ :=
    fun i j => if i.1 = (π j).1 then ζ ^ (s (i, j)) else 0
  let N : Matrix (Fin b × Fin 2) (Fin b × Fin 2) ℂ := M.submatrix id π.symm
  have hMN : N.det = (Equiv.Perm.sign π.symm : ℂ) * M.det := by
    have h1 : Nᵀ = Mᵀ.submatrix π.symm id := rfl
    rw [← Matrix.det_transpose N, h1, Matrix.det_permute, Matrix.det_transpose]
  have hsign : (Equiv.Perm.sign π.symm : ℂ) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π.symm) with h | h <;> simp [h]
  have hM_iff_N : M.det ≠ 0 ↔ N.det ≠ 0 := by
    rw [hMN]
    exact ⟨fun h => mul_ne_zero hsign h, fun h => right_ne_zero_of_mul h⟩
  rw [hM_iff_N]
  let B : Fin b → Matrix (Fin 2) (Fin 2) ℂ :=
    fun r a c => ζ ^ (s ((r, a), π.symm (r, c)))
  have hN_eq : N.reindex (Equiv.prodComm (Fin b) (Fin 2)) (Equiv.prodComm (Fin b) (Fin 2)) =
      Matrix.blockDiagonal B := by
    ext ⟨a, r⟩ ⟨c, r'⟩
    change (if r = (π (π.symm (r', c))).1 then ζ ^ (s ((r, a), π.symm (r', c))) else 0) =
      Matrix.blockDiagonal B (a, r) (c, r')
    rw [Equiv.apply_symm_apply, Matrix.blockDiagonal_apply]
    by_cases hrr : r = r'
    · subst hrr
      simp [B]
    · simp [hrr]
  have hdetN : N.det = ∏ r : Fin b, (B r).det := by
    rw [← Matrix.det_reindex_self (Equiv.prodComm (Fin b) (Fin 2)) N, hN_eq,
      Matrix.det_blockDiagonal]
  rw [hdetN, Finset.prod_ne_zero_iff]
  simp only [Finset.mem_univ, true_implies]
  refine forall_congr' fun r => ?_
  rw [Matrix.det_fin_two]
  simp only [B, sub_ne_zero, ← pow_add]
  rw [ne_eq, pow_eq_pow_iff_modEq hq hζ, ← ZMod.natCast_eq_natCast_iff']
  push_cast
  simp only [phaseColor, ne_eq]
  constructor <;> intro h heq <;> apply h
  · linear_combination -heq
  · linear_combination -heq

private lemma cauchy_schwarz_zmod {α : Type*} [DecidableEq α] {q : ℕ} (hq : 2 ≤ q)
    (A : Finset α) (φ : α → ZMod q) :
    q * ((A ×ˢ A).filter (fun p => φ p.1 ≠ φ p.2)).card ≤ (q - 1) * A.card ^ 2 := by
  have : NeZero q := ⟨by omega⟩
  let cnt : ZMod q → ℕ := fun c => (A.filter (fun x => φ x = c)).card
  have hsum_cnt : ∑ c : ZMod q, cnt c = A.card := by
    have h1 := Finset.card_eq_sum_card_fiberwise (f := φ) (s := A) (t := (Finset.univ : Finset (ZMod q)))
      (fun x _ => Finset.mem_univ _)
    exact h1.symm
  have hsplit : ((A ×ˢ A).filter (fun p => φ p.1 ≠ φ p.2)).card +
      ∑ c : ZMod q, (cnt c) ^ 2 = A.card ^ 2 := by
    have hsame : ((A ×ˢ A).filter (fun p => φ p.1 = φ p.2)).card = ∑ c : ZMod q, (cnt c) ^ 2 := by
      have hbi : (A ×ˢ A).filter (fun p => φ p.1 = φ p.2) =
          (Finset.univ : Finset (ZMod q)).biUnion
            (fun c => (A.filter (fun x => φ x = c)) ×ˢ (A.filter (fun x => φ x = c))) := by
        ext ⟨x, y⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_univ,
          true_and]
        constructor
        · rintro ⟨⟨hx, hy⟩, hxy⟩
          exact ⟨φ x, ⟨hx, rfl⟩, ⟨hy, hxy.symm⟩⟩
        · rintro ⟨c, ⟨hx, hcx⟩, ⟨hy, hcy⟩⟩
          exact ⟨⟨hx, hy⟩, hcx.trans hcy.symm⟩
      rw [hbi, Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.card_product, sq]
      · intro c1 _ c2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        rintro ⟨x, y⟩ h1 h2
        simp only [Finset.mem_product, Finset.mem_filter] at h1 h2
        exact hne (h1.1.2.symm.trans h2.1.2)
    have hpart : ((A ×ˢ A).filter (fun p => φ p.1 ≠ φ p.2)).card +
        ((A ×ˢ A).filter (fun p => φ p.1 = φ p.2)).card = (A ×ˢ A).card := by
      rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
      calc ∑ p ∈ A ×ˢ A, ((if φ p.1 ≠ φ p.2 then 1 else 0) + (if φ p.1 = φ p.2 then 1 else 0))
          = ∑ _p ∈ A ×ˢ A, 1 := by
              refine Finset.sum_congr rfl fun p _ => ?_
              by_cases h : φ p.1 = φ p.2 <;> simp [h]
        _ = (A ×ˢ A).card := by simp
    rw [hsame, Finset.card_product, ← sq] at hpart
    exact hpart
  have hcs_int : ((∑ c : ZMod q, (cnt c : ℤ)) ^ 2) ≤ (q : ℤ) * ∑ c : ZMod q, ((cnt c : ℤ) ^ 2) := by
    have hnn : (0 : ℤ) ≤ ∑ c : ZMod q, ∑ d : ZMod q, ((cnt c : ℤ) - (cnt d : ℤ)) ^ 2 :=
      Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ => sq_nonneg _
    have hexp : ∑ c : ZMod q, ∑ d : ZMod q, ((cnt c : ℤ) - (cnt d : ℤ)) ^ 2 =
        2 * ((q : ℤ) * ∑ c : ZMod q, (cnt c : ℤ) ^ 2) - 2 * (∑ c : ZMod q, (cnt c : ℤ)) ^ 2 := by
      have h1 : ∀ c : ZMod q, ∑ d : ZMod q, ((cnt c : ℤ) - (cnt d : ℤ)) ^ 2 =
          (q : ℤ) * (cnt c : ℤ) ^ 2 - 2 * (cnt c : ℤ) * (∑ d : ZMod q, (cnt d : ℤ)) +
            ∑ d : ZMod q, (cnt d : ℤ) ^ 2 := by
        intro c
        calc ∑ d : ZMod q, ((cnt c : ℤ) - (cnt d : ℤ)) ^ 2
            = ∑ d : ZMod q, ((cnt c : ℤ) ^ 2 - 2 * (cnt c : ℤ) * (cnt d : ℤ) + (cnt d : ℤ) ^ 2) := by
                refine Finset.sum_congr rfl fun d _ => by ring
          _ = (∑ _d : ZMod q, (cnt c : ℤ) ^ 2) -
              (∑ d : ZMod q, 2 * (cnt c : ℤ) * (cnt d : ℤ)) +
              (∑ d : ZMod q, (cnt d : ℤ) ^ 2) := by
                rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          _ = (q : ℤ) * (cnt c : ℤ) ^ 2 -
              2 * (cnt c : ℤ) * (∑ d : ZMod q, (cnt d : ℤ)) +
              ∑ d : ZMod q, (cnt d : ℤ) ^ 2 := by
                rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, ← Finset.mul_sum]
      simp_rw [h1]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
        Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      have hmul : ∑ c : ZMod q, 2 * (cnt c : ℤ) = 2 * ∑ c : ZMod q, (cnt c : ℤ) := by
        rw [← Finset.mul_sum]
      rw [hmul]
      ring
    linarith
  have hcs : A.card ^ 2 ≤ q * ∑ c : ZMod q, (cnt c) ^ 2 := by
    have hcast : ((A.card ^ 2 : ℕ) : ℤ) ≤ ((q * ∑ c : ZMod q, (cnt c) ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [← hsum_cnt]
      push_cast
      exact hcs_int
    exact_mod_cast hcast
  have hq1 : (q - 1) * A.card ^ 2 + A.card ^ 2 = q * A.card ^ 2 := by
    have : q = (q - 1) + 1 := by omega
    conv_rhs => rw [this]
    ring
  have hmul_split : q * ((A ×ˢ A).filter (fun p => φ p.1 ≠ φ p.2)).card +
      q * ∑ c : ZMod q, (cnt c) ^ 2 = q * A.card ^ 2 := by
    rw [← mul_add, hsplit]
  omega

private lemma good_equiv_bound {α : Type*} [DecidableEq α] {q : ℕ} (hq : 2 ≤ q) :
    ∀ m k : ℕ, k ≤ m → ∀ (A : Finset α), A.card = 2 * m →
      ∀ (φ : Fin m → α → ZMod q),
      let good := (Finset.univ : Finset ((Fin m × Fin 2) ≃ {x // x ∈ A})).filter
        (fun f => ∀ r : Fin m, k ≤ r.val → φ r (f (r, 0)).1 ≠ φ r (f (r, 1)).1)
      good.card * q ^ (m - k) * (∏ j ∈ Finset.Ico k m, (2 * j + 1)) ≤
        (2 * m).factorial * (q - 1) ^ (m - k) * (∏ j ∈ Finset.Ico k m, (2 * j + 2)) := by
  classical
  intro m
  induction m with
  | zero =>
    intro k hk A hA φ
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [Nat.sub_self, pow_zero, mul_one, Finset.Ico_self, Finset.prod_empty, mul_zero,
      Nat.factorial_zero]
    calc ((Finset.univ : Finset ((Fin 0 × Fin 2) ≃ {x // x ∈ A})).filter _).card
        ≤ (Finset.univ : Finset ((Fin 0 × Fin 2) ≃ {x // x ∈ A})).card := Finset.card_filter_le _ _
      _ = Fintype.card ((Fin 0 × Fin 2) ≃ {x // x ∈ A}) := Finset.card_univ
      _ = (Fintype.card {x // x ∈ A}).factorial := by
          have hcard : Fintype.card (Fin 0 × Fin 2) = Fintype.card {x // x ∈ A} := by
            simp [hA]
          let e0 : (Fin 0 × Fin 2) ≃ {x // x ∈ A} := Fintype.equivOfCardEq hcard
          rw [Fintype.card_congr (Equiv.equivCongr e0 (Equiv.refl _)), Fintype.card_perm]
      _ = 1 := by simp [hA]
  | succ n ih =>
    intro k hk A hA φ
    by_cases hkn : k = n + 1
    · subst hkn
      simp only [Nat.sub_self, pow_zero, mul_one, Finset.Ico_self, Finset.prod_empty]
      calc ((Finset.univ : Finset ((Fin (n + 1) × Fin 2) ≃ {x // x ∈ A})).filter _).card
          ≤ (Finset.univ : Finset ((Fin (n + 1) × Fin 2) ≃ {x // x ∈ A})).card :=
            Finset.card_filter_le _ _
        _ = Fintype.card ((Fin (n + 1) × Fin 2) ≃ {x // x ∈ A}) := Finset.card_univ
        _ = (2 * (n + 1)).factorial := by
            have hcard : Fintype.card (Fin (n + 1) × Fin 2) = Fintype.card {x // x ∈ A} := by
              simp [hA]; ring
            let e0 : (Fin (n + 1) × Fin 2) ≃ {x // x ∈ A} := Fintype.equivOfCardEq hcard
            rw [Fintype.card_congr (Equiv.equivCongr e0 (Equiv.refl _)), Fintype.card_perm]
            simp [hA]
    · have hkn_le : k ≤ n := by omega
      let P : Finset (α × α) := (A ×ˢ A).filter (fun p => φ (Fin.last n) p.1 ≠ φ (Fin.last n) p.2)
      let rem : α × α → Finset α := fun p => (A.erase p.1).erase p.2
      let goodFull := (Finset.univ : Finset ((Fin (n + 1) × Fin 2) ≃ {x // x ∈ A})).filter
        (fun f => ∀ r : Fin (n + 1), k ≤ r.val → φ r (f (r, 0)).1 ≠ φ r (f (r, 1)).1)
      let goodRem : (p : α × α) → Finset ((Fin n × Fin 2) ≃ {x // x ∈ rem p}) := fun p =>
        (Finset.univ : Finset ((Fin n × Fin 2) ≃ {x // x ∈ rem p})).filter
          (fun g => ∀ r : Fin n, k ≤ r.val →
            φ r.castSucc (g (r, 0)).1 ≠ φ r.castSucc (g (r, 1)).1)
      have hcard_split : goodFull.card = ∑ p ∈ P, (goodRem p).card := by
        have hfib := Finset.card_eq_sum_card_fiberwise
          (f := fun f : (Fin (n + 1) × Fin 2) ≃ {x // x ∈ A} =>
            ((f (Fin.last n, 0)).1, (f (Fin.last n, 1)).1))
          (s := goodFull) (t := P)
        have hmaps : ∀ f ∈ goodFull, ((f (Fin.last n, 0)).1, (f (Fin.last n, 1)).1) ∈ P := by
          intro f hf
          simp only [goodFull, Finset.mem_filter, Finset.mem_univ, true_and] at hf
          simp only [P, Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨(f (Fin.last n, 0)).2, (f (Fin.last n, 1)).2⟩, hf (Fin.last n) (by simp; omega)⟩
        rw [hfib hmaps]
        refine Finset.sum_congr rfl fun p hp => ?_
        simp only [P, Finset.mem_filter, Finset.mem_product] at hp
        rcases hp with ⟨⟨hp1, hp2⟩, hp_ne_phi⟩
        have hp_ne : p.1 ≠ p.2 := fun h => hp_ne_phi (by rw [h])
        refine Finset.card_bij
          (fun f hf =>
            let hpair : (f (Fin.last n, 0)).1 = p.1 ∧ (f (Fin.last n, 1)).1 = p.2 :=
              Prod.mk.inj (Finset.mem_filter.mp hf).2
            ({ toFun := fun z =>
                 ⟨(f (z.1.castSucc, z.2)).1, by
                   simp only [rem, Finset.mem_erase]
                   refine ⟨?_, ?_, (f (z.1.castSucc, z.2)).2⟩
                   · intro heq
                     have hinj : (z.1.castSucc, z.2) = (Fin.last n, 1) :=
                       f.injective (Subtype.ext (heq.trans hpair.2.symm))
                     exact Fin.castSucc_ne_last z.1 (Prod.mk.inj hinj).1
                   · intro heq
                     have hinj : (z.1.castSucc, z.2) = (Fin.last n, 0) :=
                       f.injective (Subtype.ext (heq.trans hpair.1.symm))
                     exact Fin.castSucc_ne_last z.1 (Prod.mk.inj hinj).1⟩
               invFun := fun y =>
                 let z := f.symm ⟨y.1, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase y.2)⟩
                 have hne_last : z.1 ≠ Fin.last n := by
                   intro hlast
                   have hy2 := y.2
                   simp only [rem, Finset.mem_erase] at hy2
                   have hfz : f z = ⟨y.1, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase y.2)⟩ :=
                     f.apply_symm_apply _
                   have hz_eq : z = (Fin.last n, z.2) := Prod.ext hlast rfl
                   rw [hz_eq] at hfz
                   have hz2_cases : z.2 = 0 ∨ z.2 = 1 := by omega
                   rcases hz2_cases with hz0 | hz1
                   · rw [hz0] at hfz
                     exact hy2.2.1 ((congr_arg Subtype.val hfz).symm.trans hpair.1)
                   · rw [hz1] at hfz
                     exact hy2.1 ((congr_arg Subtype.val hfz).symm.trans hpair.2)
                 (z.1.castPred hne_last, z.2)
               left_inv := fun z => by
                 ext
                 · simp
                 · simp
               right_inv := fun y => by
                 apply Subtype.ext
                 simp } : (Fin n × Fin 2) ≃ {x // x ∈ rem p}))
          ?_ ?_ ?_
        · intro f hf
          simp only [Finset.mem_filter, goodFull, Finset.mem_univ, true_and] at hf
          simp only [goodRem, Finset.mem_filter, Finset.mem_univ, true_and]
          intro r hr
          exact hf.1 r.castSucc (by simpa using hr)
        · intro f1 hf1 f2 hf2 heq
          have hp1_eq := Prod.mk.inj (Finset.mem_filter.mp hf1).2
          have hp2_eq := Prod.mk.inj (Finset.mem_filter.mp hf2).2
          ext ⟨r, t⟩
          refine Fin.lastCases ?_ ?_ r
          · fin_cases t
            · exact hp1_eq.1.trans hp2_eq.1.symm
            · exact hp1_eq.2.trans hp2_eq.2.symm
          · intro r0
            have h := congr_arg (fun g : (Fin n × Fin 2) ≃ {x // x ∈ rem p} => (g (r0, t)).1) heq
            exact h
        · intro g hg
          simp only [goodRem, Finset.mem_filter, Finset.mem_univ, true_and] at hg
          let f : (Fin (n + 1) × Fin 2) ≃ {x // x ∈ A} :=
            { toFun := fun z =>
                Fin.lastCases
                  (if z.2 = 0 then ⟨p.1, hp1⟩ else ⟨p.2, hp2⟩)
                  (fun r0 => ⟨(g (r0, z.2)).1,
                    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (g (r0, z.2)).2)⟩)
                  z.1
              invFun := fun y =>
                if h1 : y.1 = p.1 then (Fin.last n, 0)
                else if h2 : y.1 = p.2 then (Fin.last n, 1)
                else
                  let z := g.symm ⟨y.1, by simp [rem, h1, h2, y.2]⟩
                  (z.1.castSucc, z.2)
              left_inv := fun ⟨r, t⟩ => by
                refine Fin.lastCases ?_ ?_ r
                · fin_cases t
                  · simp
                  · simp [hp_ne.symm]
                · intro r0
                  have hmem := (g (r0, t)).2
                  simp only [rem, Finset.mem_erase] at hmem
                  simp [hmem.1, hmem.2.1]
              right_inv := fun y => by
                apply Subtype.ext
                by_cases h1 : y.1 = p.1
                · simp [h1]
                · by_cases h2 : y.1 = p.2
                  · simp [h2, hp_ne.symm]
                  · simp [h1, h2] }
          refine ⟨f, ?_, ?_⟩
          · simp only [Finset.mem_filter, goodFull, Finset.mem_univ, true_and]
            refine ⟨fun r => ?_, ?_⟩
            · refine Fin.lastCases ?_ ?_ r
              · intro _
                simpa [f] using hp_ne_phi
              · intro r0 hr
                have hr0 : k ≤ r0.val := by simpa using hr
                simpa [f] using hg r0 hr0
            · ext <;> simp [f]
          · ext ⟨r0, t⟩
            simp [f]
      have hrem_card : ∀ p ∈ P, (rem p).card = 2 * n := by
        intro p hp
        simp only [P, Finset.mem_filter, Finset.mem_product] at hp
        have hp_ne : p.1 ≠ p.2 := fun h => hp.2 (by rw [h])
        have hmem2 : p.2 ∈ A.erase p.1 := Finset.mem_erase.mpr ⟨hp_ne.symm, hp.1.2⟩
        simp only [rem, Finset.card_erase_of_mem hmem2, Finset.card_erase_of_mem hp.1.1]
        omega
      have hih_p : ∀ p ∈ P,
          (goodRem p).card * q ^ (n - k) * (∏ j ∈ Finset.Ico k n, (2 * j + 1)) ≤
            (2 * n).factorial * (q - 1) ^ (n - k) * (∏ j ∈ Finset.Ico k n, (2 * j + 2)) :=
        fun p hp => ih k hkn_le (rem p) (hrem_card p hp) (fun r => φ r.castSucc)
      have hcs : q * P.card ≤ (q - 1) * (2 * n + 2) ^ 2 := by
        have h := cauchy_schwarz_zmod hq A (φ (Fin.last n))
        rw [hA] at h
        simpa [P, mul_add] using h
      have hpow_q : q ^ (n + 1 - k) = q * q ^ (n - k) := by
        have : n + 1 - k = (n - k) + 1 := by omega
        rw [this, pow_succ, mul_comm]
      have hpow_q1 : (q - 1) ^ (n + 1 - k) = (q - 1) * (q - 1) ^ (n - k) := by
        have : n + 1 - k = (n - k) + 1 := by omega
        rw [this, pow_succ, mul_comm]
      have hprod_odd : (∏ j ∈ Finset.Ico k (n + 1), (2 * j + 1)) =
          (2 * n + 1) * (∏ j ∈ Finset.Ico k n, (2 * j + 1)) := by
        rw [Finset.prod_Ico_succ_top hkn_le, mul_comm]
      have hprod_even : (∏ j ∈ Finset.Ico k (n + 1), (2 * j + 2)) =
          (2 * n + 2) * (∏ j ∈ Finset.Ico k n, (2 * j + 2)) := by
        rw [Finset.prod_Ico_succ_top hkn_le, mul_comm]
      have hfact : (2 * (n + 1)).factorial = (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
        have h1 : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
        rw [h1, Nat.factorial_succ, Nat.factorial_succ]
        ring
      change goodFull.card * q ^ (n + 1 - k) * (∏ j ∈ Finset.Ico k (n + 1), (2 * j + 1)) ≤ _
      rw [hcard_split, hpow_q, hpow_q1, hprod_odd, hprod_even, hfact]
      calc (∑ p ∈ P, (goodRem p).card) * (q * q ^ (n - k)) *
            ((2 * n + 1) * ∏ j ∈ Finset.Ico k n, (2 * j + 1))
          = q * (2 * n + 1) *
              ∑ p ∈ P, ((goodRem p).card * q ^ (n - k) * ∏ j ∈ Finset.Ico k n, (2 * j + 1)) := by
                rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
                refine Finset.sum_congr rfl fun p _ => by ring
        _ ≤ q * (2 * n + 1) *
              ∑ _p ∈ P, ((2 * n).factorial * (q - 1) ^ (n - k) * ∏ j ∈ Finset.Ico k n, (2 * j + 2)) :=
                Nat.mul_le_mul_left _ (Finset.sum_le_sum hih_p)
        _ = (q * P.card) *
              ((2 * n + 1) * (2 * n).factorial * (q - 1) ^ (n - k) *
                ∏ j ∈ Finset.Ico k n, (2 * j + 2)) := by
                rw [Finset.sum_const, smul_eq_mul]
                ring
        _ ≤ ((q - 1) * (2 * n + 2) ^ 2) *
              ((2 * n + 1) * (2 * n).factorial * (q - 1) ^ (n - k) *
                ∏ j ∈ Finset.Ico k n, (2 * j + 2)) :=
                Nat.mul_le_mul_right _ hcs
        _ = (2 * n + 2) * (2 * n + 1) * (2 * n).factorial * ((q - 1) * (q - 1) ^ (n - k)) *
              ((2 * n + 2) * ∏ j ∈ Finset.Ico k n, (2 * j + 2)) := by ring

private lemma foldl_zero_eq_replicate (k : ℕ) :
    (List.range k).foldl (fun h (_ : ℕ) => (0 : ℂ) :: h) ([] : List ℂ) = List.replicate k 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp [List.replicate_succ]

private lemma foldl_eq_replicate_of_zero {Q : Type} (obs : Q → ℂ) (ask : ℕ → List ℂ → Q) :
    ∀ k : ℕ, (∀ j < k, obs (ask j (List.replicate j 0)) = 0) →
      (List.range k).foldl (fun h j => obs (ask j h) :: h) ([] : List ℂ) =
        List.replicate k 0 := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hzero
    rw [List.range_succ, List.foldl_append]
    rw [ih (fun j hj => hzero j (Nat.lt_succ_of_lt hj))]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [hzero k (Nat.lt_succ_self k), List.replicate_succ]

private lemma card_filter_add_not {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  calc ∑ x ∈ s, ((if p x then 1 else 0) + (if ¬ p x then 1 else 0))
      = ∑ _x ∈ s, 1 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hx : p x <;> simp [hx]
    _ = s.card := by simp

private lemma exists_fixed_list_of_good {G Q : Type} [Fintype G] [DecidableEq G]
    (F : Q → G → ℂ) (t R : ℕ) (hR : 0 < R)
    (ask : Fin R → ℕ → List ℂ → Q) (accept : Fin R → List ℂ → Bool)
    (h0 : 3 * ((Finset.univ : Finset (Fin R)).filter (fun u =>
        accept u ((List.range t).foldl (fun h (_ : ℕ) => (0 : ℂ) :: h) ([] : List ℂ)))).card ≤ R)
    (hG : ∀ x : G, 2 * R ≤ 3 * ((Finset.univ : Finset (Fin R)).filter (fun u =>
        accept u ((List.range t).foldl (fun h j => F (ask u j h) x :: h) ([] : List ℂ)))).card) :
    ∃ L : Fin t → Q,
      Fintype.card G ≤ 2 * ((Finset.univ : Finset G).filter (fun x => ∃ i : Fin t, F (L i) x ≠ 0)).card := by
  classical
  let run : (Q → ℂ) → Fin R → List ℂ := fun obs u =>
    (List.range t).foldl (fun h j => obs (ask u j h) :: h) ([] : List ℂ)
  let yes : (Q → ℂ) → ℕ := fun obs =>
    ((Finset.univ : Finset (Fin R)).filter (fun u => accept u (run obs u))).card
  let B : Finset (Fin R) :=
    (Finset.univ : Finset (Fin R)).filter (fun u => accept u (run (fun _ => 0) u) = false)
  have hB_card : B.card = R - yes (fun _ => 0) := by
    have hcomp := card_filter_add_not (Finset.univ : Finset (Fin R))
      (fun u => accept u (run (fun _ => 0) u) = true)
    have hB_eq : B = (Finset.univ : Finset (Fin R)).filter
        (fun u => ¬ accept u (run (fun _ => 0) u) = true) := by
      ext u; simp [B]
    rw [Finset.card_univ, Fintype.card_fin] at hcomp
    change yes (fun _ => 0) + _ = R at hcomp
    rw [← hB_eq] at hcomp
    omega
  have hB_pos : 0 < B.card := by
    change 3 * yes (fun _ => 0) ≤ R at h0
    omega
  have hB_ne : B.Nonempty := Finset.card_pos.mp hB_pos
  let Lu : Fin R → Fin t → Q := fun u i => ask u i.val (List.replicate i.val 0)
  let missed : Fin R → ℕ := fun u =>
    ((Finset.univ : Finset G).filter (fun x => ∀ i : Fin t, F (Lu u i) x = 0)).card
  obtain ⟨u0, hu0B, hu0_min⟩ := Finset.exists_min_image B missed hB_ne
  refine ⟨Lu u0, ?_⟩
  have hsum_le : B.card * missed u0 ≤ ∑ u ∈ B, missed u := by
    calc B.card * missed u0
        = ∑ _u ∈ B, missed u0 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ u ∈ B, missed u := Finset.sum_le_sum (fun u hu => hu0_min u hu)
  have hswap : (∑ u ∈ B, missed u) =
      ∑ x : G, (B.filter (fun u => ∀ i : Fin t, F (Lu u i) x = 0)).card := by
    simp only [missed, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  have hper_x : ∀ x : G,
      (B.filter (fun u => ∀ i : Fin t, F (Lu u i) x = 0)).card ≤ R - yes (fun s => F s x) := by
    intro x
    have hsub : B.filter (fun u => ∀ i : Fin t, F (Lu u i) x = 0) ⊆
        (Finset.univ : Finset (Fin R)).filter
          (fun u => ¬ accept u (run (fun s => F s x) u) = true) := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, B] at hu ⊢
      rcases hu with ⟨hu0, hzero⟩
      have hrun_eq : run (fun s => F s x) u = run (fun _ => 0) u := by
        have h1 : run (fun s => F s x) u = List.replicate t 0 :=
          foldl_eq_replicate_of_zero (fun s => F s x) (ask u) t (fun j hj => hzero ⟨j, hj⟩)
        have h2 : run (fun _ => 0) u = List.replicate t 0 := foldl_zero_eq_replicate t
        rw [h1, h2]
      rw [hrun_eq, hu0]
      decide
    have hle := Finset.card_le_card hsub
    have hcomp := card_filter_add_not (Finset.univ : Finset (Fin R))
      (fun u => accept u (run (fun s => F s x) u) = true)
    rw [Finset.card_univ, Fintype.card_fin] at hcomp
    change yes (fun s => F s x) + _ = R at hcomp
    omega
  have htotal : 3 * (∑ u ∈ B, missed u) ≤ R * Fintype.card G := by
    rw [hswap, Finset.mul_sum]
    calc ∑ x : G, 3 * (B.filter (fun u => ∀ i : Fin t, F (Lu u i) x = 0)).card
        ≤ ∑ x : G, 3 * (R - yes (fun s => F s x)) :=
          Finset.sum_le_sum (fun x _ => Nat.mul_le_mul_left 3 (hper_x x))
      _ ≤ ∑ _x : G, R := by
          refine Finset.sum_le_sum fun x _ => ?_
          have hx := hG x
          change 2 * R ≤ 3 * yes (fun s => F s x) at hx
          omega
      _ = Fintype.card G * R := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ = R * Fintype.card G := by ring
  have hdB : 2 * R ≤ 3 * B.card := by
    change 3 * yes (fun _ => 0) ≤ R at h0
    omega
  have hmissed_le : 2 * missed u0 ≤ Fintype.card G := by
    have hcomb : R * (2 * missed u0) ≤ R * Fintype.card G := by
      calc R * (2 * missed u0)
          = (2 * R) * missed u0 := by ring
        _ ≤ (3 * B.card) * missed u0 := Nat.mul_le_mul_right _ hdB
        _ = 3 * (B.card * missed u0) := by ring
        _ ≤ 3 * (∑ u ∈ B, missed u) := Nat.mul_le_mul_left 3 hsum_le
        _ ≤ R * Fintype.card G := htotal
    exact Nat.le_of_mul_le_mul_left hcomb hR
  have hcompG := card_filter_add_not (Finset.univ : Finset G)
    (fun x => ∃ i : Fin t, F (Lu u0 i) x ≠ 0)
  rw [Finset.card_univ] at hcompG
  have hnot_eq : (Finset.univ : Finset G).filter (fun x => ¬ ∃ i : Fin t, F (Lu u0 i) x ≠ 0) =
      (Finset.univ : Finset G).filter (fun x => ∀ i : Fin t, F (Lu u0 i) x = 0) := by
    ext x
    simp
  rw [hnot_eq] at hcompG
  change ((Finset.univ : Finset G).filter (fun x => ∃ i : Fin t, F (Lu u0 i) x ≠ 0)).card +
    missed u0 = Fintype.card G at hcompG
  omega

private lemma bernoulli_nat (x y : ℕ) : ∀ t : ℕ, 0 < t →
    x ^ t + t * x ^ (t - 1) * y ≤ (x + y) ^ t := by
  intro t
  induction t with
  | zero => intro h; omega
  | succ n ih =>
    intro _
    cases n with
    | zero => simp
    | succ m =>
      have hm := ih (Nat.succ_pos m)
      have hmul := Nat.mul_le_mul_right (x + y) hm
      rw [← pow_succ] at hmul
      calc x ^ (m + 2) + (m + 2) * x ^ (m + 1) * y
          ≤ (x ^ (m + 1) + (m + 1) * x ^ m * y) * (x + y) := by
            have hnn : 0 ≤ (m + 1) * x ^ m * y ^ 2 := Nat.zero_le _
            have hexp : (x ^ (m + 1) + (m + 1) * x ^ m * y) * (x + y) =
                (x ^ (m + 2) + (m + 2) * x ^ (m + 1) * y) + (m + 1) * x ^ m * y ^ 2 := by ring
            omega
        _ ≤ (x + y) ^ (m + 2) := hmul

private lemma main_proof (b q : ℕ) (ζ : ℂ) (hb : 0 < b) (hq : 2 ≤ q) (hζ : IsPrimitiveRoot ζ q) :
    let I := Fin b × Fin 2
    let S := I × I → Fin q
    let D := fun (s : S) (π : Equiv.Perm I) =>
      Matrix.det (fun i j => if i.1 = (π j).1 then ζ ^ (s (i, j)).val else 0 : Matrix I I ℂ)
    let good := fun t : ℕ =>
      ∃ (R : ℕ) (ask : Fin R → ℕ → List ℂ → S) (accept : Fin R → List ℂ → Bool),
        0 < R ∧
        let run := fun (obs : S → ℂ) (u : Fin R) =>
          (List.range t).foldl (fun h j => obs (ask u j h) :: h) ([] : List ℂ)
        let yes := fun obs : S → ℂ =>
          ((Finset.univ : Finset (Fin R)).filter (fun u => accept u (run obs u))).card
        3 * yes (fun _ => 0) ≤ R ∧ ∀ π : Equiv.Perm I, 2 * R ≤ 3 * yes (fun s => D s π)
    (∀ t k : ℕ, good t → k ≤ b →
      q ^ (b - k) * (∏ j ∈ Finset.Ico k b, (2 * j + 1)) ≤
        2 * t * (q - 1) ^ (b - k) * (∏ j ∈ Finset.Ico k b, (2 * j + 2))) ∧
    (∃ (R t : ℕ) (list : Fin R → Fin t → S), 0 < R ∧ 0 < t ∧
      t * (q - 1) ^ b ≤ 2 * q ^ b + (q - 1) ^ b ∧ ∀ π : Equiv.Perm I,
      2 * R ≤ 3 * ((Finset.univ : Finset (Fin R)).filter
        (fun u => ∃ i : Fin t, D (list u i) π ≠ 0)).card) := by
  classical
  have : NeZero q := ⟨by omega⟩
  intro I S D good
  constructor
  · intro t k hgood hkb
    rcases hgood with ⟨R, ask, accept, hR, h0, hG⟩
    obtain ⟨L, hL⟩ := exists_fixed_list_of_good D t R hR ask accept h0 hG
    have hcard_perm : Fintype.card (Equiv.Perm I) = (2 * b).factorial := by
      rw [Fintype.card_perm]
      have hI : Fintype.card I = 2 * b := by simp [I]; ring
      rw [hI]
    have hunion : ((Finset.univ : Finset (Equiv.Perm I)).filter
        (fun π => ∃ i : Fin t, D (L i) π ≠ 0)).card ≤
        ∑ i : Fin t, ((Finset.univ : Finset (Equiv.Perm I)).filter (fun π => D (L i) π ≠ 0)).card := by
      have hsub : (Finset.univ : Finset (Equiv.Perm I)).filter (fun π => ∃ i : Fin t, D (L i) π ≠ 0) ⊆
          (Finset.univ : Finset (Fin t)).biUnion
            (fun i => (Finset.univ : Finset (Equiv.Perm I)).filter (fun π => D (L i) π ≠ 0)) := by
        intro π hπ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hπ ⊢
        exact hπ
      exact le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
    have hhits_bound : ∀ s : S,
        ((Finset.univ : Finset (Equiv.Perm I)).filter (fun π => D s π ≠ 0)).card *
          q ^ (b - k) * (∏ j ∈ Finset.Ico k b, (2 * j + 1)) ≤
        (2 * b).factorial * (q - 1) ^ (b - k) * (∏ j ∈ Finset.Ico k b, (2 * j + 2)) := by
      intro s
      let A : Finset I := Finset.univ
      have hA : A.card = 2 * b := by simp [A, I]; ring
      let φ : Fin b → I → ZMod q := phaseColor (q := q) (fun e => (s e).val)
      have hbound := good_equiv_bound hq b k hkb A hA φ
      have hcard_le : ((Finset.univ : Finset (Equiv.Perm I)).filter (fun π => D s π ≠ 0)).card ≤
          ((Finset.univ : Finset ((Fin b × Fin 2) ≃ {x // x ∈ A})).filter
            (fun f => ∀ r : Fin b, k ≤ r.val → φ r (f (r, 0)).1 ≠ φ r (f (r, 1)).1)).card := by
        let eU : I ≃ {x // x ∈ A} :=
          { toFun := fun i => ⟨i, Finset.mem_univ i⟩
            invFun := fun x => x.1
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        refine Finset.card_le_card_of_injOn (fun π : Equiv.Perm I => π.symm.trans eU) ?_ ?_
        · intro π hπ
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
          have hdet := (det_block2_ne_zero_iff hq hζ (fun e => (s e).val) π).mp hπ
          intro r _
          exact hdet r
        · intro π1 _ π2 _ h
          have hsym : π1.symm = π2.symm := by
            apply Equiv.ext
            intro z
            exact eU.injective (Equiv.congr_fun h z)
          exact Equiv.symm_bijective.injective hsym
      exact le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcard_le)) hbound
    have hmul_le : (2 * b).factorial * (q ^ (b - k) * ∏ j ∈ Finset.Ico k b, (2 * j + 1)) ≤
        (2 * b).factorial * (2 * t * (q - 1) ^ (b - k) * ∏ j ∈ Finset.Ico k b, (2 * j + 2)) := by
      calc (2 * b).factorial * (q ^ (b - k) * ∏ j ∈ Finset.Ico k b, (2 * j + 1))
          = Fintype.card (Equiv.Perm I) * (q ^ (b - k) * ∏ j ∈ Finset.Ico k b, (2 * j + 1)) := by
              rw [hcard_perm]
        _ ≤ (2 * ∑ i : Fin t, ((Finset.univ : Finset (Equiv.Perm I)).filter
              (fun π => D (L i) π ≠ 0)).card) *
            (q ^ (b - k) * ∏ j ∈ Finset.Ico k b, (2 * j + 1)) :=
              Nat.mul_le_mul_right _ (le_trans hL (Nat.mul_le_mul_left 2 hunion))
        _ = 2 * ∑ i : Fin t, (((Finset.univ : Finset (Equiv.Perm I)).filter
              (fun π => D (L i) π ≠ 0)).card * q ^ (b - k) *
                ∏ j ∈ Finset.Ico k b, (2 * j + 1)) := by
              rw [mul_assoc, Finset.sum_mul]
              congr 1
              refine Finset.sum_congr rfl fun i _ => by ring
        _ ≤ 2 * ∑ _i : Fin t, ((2 * b).factorial * (q - 1) ^ (b - k) *
              ∏ j ∈ Finset.Ico k b, (2 * j + 2)) :=
              Nat.mul_le_mul_left 2 (Finset.sum_le_sum fun i _ => hhits_bound (L i))
        _ = (2 * b).factorial * (2 * t * (q - 1) ^ (b - k) *
              ∏ j ∈ Finset.Ico k b, (2 * j + 2)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
              ring
    exact Nat.le_of_mul_le_mul_left hmul_le (Nat.factorial_pos (2 * b))
  · let A := q ^ b
    let B := (q - 1) ^ b
    have hB_pos : 0 < B := Nat.pow_pos (by omega)
    have hBA : B ≤ A := Nat.pow_le_pow_left (by omega) b
    let t := (2 * A) / B + 1
    have ht_pos : 0 < t := Nat.succ_pos _
    have ht_ub : t * B ≤ 2 * A + B := by
      change ((2 * A) / B + 1) * B ≤ 2 * A + B
      rw [Nat.add_mul, one_mul]
      exact Nat.add_le_add_right (Nat.div_mul_le_self (2 * A) B) B
    have ht_lb : 2 * A ≤ t * B := by
      have hmod := Nat.div_add_mod (2 * A) B
      have hlt := Nat.mod_lt (2 * A) hB_pos
      change 2 * A ≤ ((2 * A) / B + 1) * B
      rw [Nat.add_mul, one_mul, mul_comm ((2 * A) / B) B]
      omega
    let C := Fin t → (I → Fin q)
    let R := Fintype.card C
    have hR_pos : 0 < R := Fintype.card_pos
    let eR : Fin R ≃ C := (Fintype.equivFin C).symm
    let colS : (I → Fin q) → S := fun c e =>
      if e.1.2.val = 1 then c e.2 else ⟨0, by omega⟩
    let list : Fin R → Fin t → S := fun u i => colS (eR u i)
    refine ⟨R, t, list, hR_pos, ht_pos, ht_ub, fun π => ?_⟩
    have hcol_good : ((Finset.univ : Finset (I → Fin q)).filter (fun c => D (colS c) π ≠ 0)).card =
        (q * (q - 1)) ^ b := by
      have hpred : ∀ c : I → Fin q, D (colS c) π ≠ 0 ↔
          ∀ r : Fin b, c (π.symm (r, 0)) ≠ c (π.symm (r, 1)) := by
        intro c
        rw [det_block2_ne_zero_iff hq hζ (fun e => (colS c e).val) π]
        refine forall_congr' fun r => ?_
        simp only [phaseColor, colS, Fin.val_one, Fin.val_zero, ↓reduceIte, zero_ne_one,
          Nat.cast_zero, sub_zero, ne_eq, ZMod.natCast_eq_natCast_iff']
        rw [Nat.mod_eq_of_lt (c (π.symm (r, 0))).isLt, Nat.mod_eq_of_lt (c (π.symm (r, 1))).isLt]
        exact not_congr Fin.ext_iff.symm
      let pairs : Finset (Fin q × Fin q) :=
        (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 ≠ p.2)
      have hpairs_card : pairs.card = q * (q - 1) := by
        have hsplit := card_filter_add_not (Finset.univ : Finset (Fin q × Fin q))
          (fun p => p.1 ≠ p.2)
        have hnot : (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => ¬ p.1 ≠ p.2) =
            (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 = p.2) := by
          ext p; simp
        rw [hnot, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hsplit
        have hdiag : ((Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 = p.2)).card = q := by
          calc ((Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 = p.2)).card
              = (Finset.univ : Finset (Fin q)).card := by
                refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
                · intro _ _; exact Finset.mem_univ _
                · intro p1 hp1 p2 hp2 h
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
                  exact Prod.ext h (hp1.symm.trans (h.trans hp2))
                · intro x _; exact ⟨(x, x), by simp, rfl⟩
            _ = q := by simp
        have hmul : q * (q - 1) + q = q * q := by
          cases q with
          | zero => omega
          | succ q' => simp; ring
        change pairs.card + _ = q * q at hsplit
        omega
      calc ((Finset.univ : Finset (I → Fin q)).filter (fun c => D (colS c) π ≠ 0)).card
          = ((Finset.univ : Finset (Fin b → Fin q × Fin q)).filter
              (fun f => ∀ r : Fin b, f r ∈ pairs)).card := by
            refine Finset.card_bij (fun c _ r => (c (π.symm (r, 0)), c (π.symm (r, 1)))) ?_ ?_ ?_
            · intro c hc
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
              intro r
              simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and]
              exact (hpred c).mp hc r
            · intro c1 _ c2 _ h
              funext j
              have hj := Equiv.symm_apply_apply π j
              rw [← hj]
              have h' := congr_fun h (π j).1
              have hpair : π j = ((π j).1, (π j).2) := rfl
              have ht2 : (π j).2 = 0 ∨ (π j).2 = 1 := by omega
              rcases ht2 with h0 | h1
              · rw [hpair, h0]; exact (Prod.mk.inj h').1
              · rw [hpair, h1]; exact (Prod.mk.inj h').2
            · intro f hf
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
              let c : I → Fin q := fun j => if (π j).2 = 0 then (f (π j).1).1 else (f (π j).1).2
              refine ⟨c, ?_, ?_⟩
              · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                rw [hpred]
                intro r
                have hfr := hf r
                simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hfr
                simpa [c] using hfr
              · funext r
                ext <;> simp [c]
        _ = (Fintype.piFinset (fun _ : Fin b => pairs)).card := by
            congr 1; ext f; simp [Fintype.mem_piFinset]
        _ = (q * (q - 1)) ^ b := by
            rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
              hpairs_card]
    let bad1 : Finset (I → Fin q) :=
      (Finset.univ : Finset (I → Fin q)).filter (fun c => D (colS c) π = 0)
    have hcard_col : Fintype.card (I → Fin q) = A * A := by
      simp only [Fintype.card_fun, Fintype.card_fin, I, Fintype.card_prod, A]
      rw [mul_comm b 2, pow_mul, sq, mul_pow]
    have hbad1_card : bad1.card = A * (A - B) := by
      have hcomp := card_filter_add_not (Finset.univ : Finset (I → Fin q))
        (fun c => D (colS c) π ≠ 0)
      have hnot : (Finset.univ : Finset (I → Fin q)).filter (fun c => ¬ D (colS c) π ≠ 0) = bad1 := by
        ext c; simp [bad1]
      rw [hnot, hcol_good, Finset.card_univ, hcard_col] at hcomp
      have hmulAB : (q * (q - 1)) ^ b = A * B := by simp only [A, B, mul_pow]
      rw [hmulAB] at hcomp
      have hsub : A * (A - B) + A * B = A * A := by
        rw [← mul_add, Nat.sub_add_cancel hBA]
      omega
    have hR_eq : R = (A * A) ^ t := by
      simp only [R, C, Fintype.card_fun, Fintype.card_fin, hcard_col]
    have hbad_all : ((Finset.univ : Finset (Fin R)).filter
        (fun u => ¬ ∃ i : Fin t, D (list u i) π ≠ 0)).card = (A * (A - B)) ^ t := by
      calc ((Finset.univ : Finset (Fin R)).filter
              (fun u => ¬ ∃ i : Fin t, D (list u i) π ≠ 0)).card
          = (Fintype.piFinset (fun _ : Fin t => bad1)).card := by
            refine Finset.card_bij (fun u _ => eR u) ?_ ?_ ?_
            · intro u hu
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_not] at hu
              simp only [Fintype.mem_piFinset, bad1, Finset.mem_filter, Finset.mem_univ, true_and]
              exact hu
            · intro u1 _ u2 _ h
              exact eR.injective h
            · intro f hf
              simp only [Fintype.mem_piFinset, bad1, Finset.mem_filter, Finset.mem_univ, true_and] at hf
              refine ⟨eR.symm f, ?_, eR.apply_symm_apply f⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_not, list,
                eR.apply_symm_apply]
              exact hf
        _ = (A * (A - B)) ^ t := by
            rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
              hbad1_card]
    have hbern : 3 * (A - B) ^ t ≤ A ^ t := by
      have h1 := bernoulli_nat (A - B) B t ht_pos
      rw [Nat.sub_add_cancel hBA] at h1
      have h2 : 2 * (A - B) ^ t ≤ t * (A - B) ^ (t - 1) * B := by
        have ht1 : (A - B) ^ t = (A - B) ^ (t - 1) * (A - B) := by
          rw [← pow_succ, Nat.sub_add_cancel ht_pos]
        rw [ht1]
        calc 2 * ((A - B) ^ (t - 1) * (A - B))
            = (A - B) ^ (t - 1) * (2 * (A - B)) := by ring
          _ ≤ (A - B) ^ (t - 1) * (2 * A) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 (Nat.sub_le A B))
          _ ≤ (A - B) ^ (t - 1) * (t * B) := Nat.mul_le_mul_left _ ht_lb
          _ = t * (A - B) ^ (t - 1) * B := by ring
      omega
    have hbad_le : 3 * (A * (A - B)) ^ t ≤ R := by
      rw [hR_eq, mul_pow, mul_pow]
      calc 3 * (A ^ t * (A - B) ^ t)
          = A ^ t * (3 * (A - B) ^ t) := by ring
        _ ≤ A ^ t * A ^ t := Nat.mul_le_mul_left _ hbern
    have hcompR := card_filter_add_not (Finset.univ : Finset (Fin R))
      (fun u => ∃ i : Fin t, D (list u i) π ≠ 0)
    rw [Finset.card_univ, Fintype.card_fin, hbad_all] at hcompR
    omega

end PEqualNP.Outside.L_lib_1020_aux

theorem PEqualNP.Outside.L_lib_1020 :
  ∀ (b q : ℕ) (ζ : ℂ), 0 < b → 2 ≤ q → IsPrimitiveRoot ζ q →
  let I := Fin b × Fin 2
  let S := I × I → Fin q
  let D := fun (s : S) (π : Equiv.Perm I) =>
    Matrix.det (fun i j => if i.1 = (π j).1 then ζ^(s (i,j)).val else 0 : Matrix I I ℂ)
  let good := fun t : ℕ =>
    ∃ (R : ℕ) (ask : Fin R → ℕ → List ℂ → S) (accept : Fin R → List ℂ → Bool),
      0 < R ∧
      let run := fun (obs : S → ℂ) (u : Fin R) =>
        (List.range t).foldl (fun h j => obs (ask u j h) :: h) ([] : List ℂ)
      let yes := fun obs : S → ℂ =>
        ((Finset.univ : Finset (Fin R)).filter (fun u => accept u (run obs u))).card
      3*yes (fun _ => 0) ≤ R ∧ ∀ π : Equiv.Perm I, 2*R ≤ 3*yes (fun s => D s π)
  (∀ t k : ℕ, good t → k ≤ b →
    q^(b-k) * (∏ j ∈ Finset.Ico k b, (2*j+1)) ≤
      2*t*(q-1)^(b-k) * (∏ j ∈ Finset.Ico k b, (2*j+2))) ∧
  (∃ (R t : ℕ) (list : Fin R → Fin t → S), 0 < R ∧ 0 < t ∧
    t*(q-1)^b ≤ 2*q^b+(q-1)^b ∧ ∀ π : Equiv.Perm I,
    2*R ≤ 3*((Finset.univ : Finset (Fin R)).filter
      (fun u => ∃ i : Fin t, D (list u i) π ≠ 0)).card) := by
  intro b q ζ hb hq hζ
  exact PEqualNP.Outside.L_lib_1020_aux.main_proof b q ζ hb hq hζ

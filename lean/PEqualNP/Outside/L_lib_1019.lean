import PEqualNP.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace PEqualNP.Outside.L_lib_1019_aux

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

private lemma main_proof (b q : ℕ) (ζ : ℂ) (hb : 0 < b) (hq : 2 ≤ q) (hζ : IsPrimitiveRoot ζ q) :
    let I := Fin b × Fin 2
    let S := I × I → Fin q
    let D := fun (s : S) (π : Equiv.Perm I) =>
      Matrix.det (fun i j => if i.1 = (π j).1 then ζ ^ (s (i, j)).val else 0 : Matrix I I ℂ)
    let hits := fun s : S => ((Finset.univ : Finset (Equiv.Perm I)).filter (fun π => D s π ≠ 0)).card
    let col := fun (c : I → Fin q) (e : I × I) => if e.1.2.val = 1 then (c e.2).val else (0 : ℕ)
    (∀ (s : S) (k : ℕ), k ≤ b →
      hits s * q ^ (b - k) * (∏ j ∈ Finset.Ico k b, (2 * j + 1)) ≤
        (2 * b).factorial * (q - 1) ^ (b - k) * (∏ j ∈ Finset.Ico k b, (2 * j + 2))) ∧
    (∀ π : Equiv.Perm I, ((Finset.univ : Finset (I → Fin q)).filter (fun c =>
      Matrix.det (fun i j => if i.1 = (π j).1 then ζ ^ (col c (i, j)) else 0 : Matrix I I ℂ) ≠ 0)).card
        = (q * (q - 1)) ^ b) ∧
    ((∃ s : S, ∀ π : Equiv.Perm I, D s π ≠ 0) ↔ 2 * b ≤ q) := by
  classical
  have : NeZero q := ⟨by omega⟩
  intro I S D hits col
  refine ⟨?_, ?_, ?_⟩
  · intro s k hkb
    let A : Finset I := Finset.univ
    have hA : A.card = 2 * b := by
      simp [A, I]; ring
    let φ : Fin b → I → ZMod q := phaseColor (q := q) (fun e => (s e).val)
    have hbound := good_equiv_bound hq b k hkb A hA φ
    have hcard_le : hits s ≤
        ((Finset.univ : Finset ((Fin b × Fin 2) ≃ {x // x ∈ A})).filter
          (fun f => ∀ r : Fin b, k ≤ r.val → φ r (f (r, 0)).1 ≠ φ r (f (r, 1)).1)).card := by
      let eU : I ≃ {x // x ∈ A} :=
        { toFun := fun i => ⟨i, Finset.mem_univ i⟩
          invFun := fun x => x.1
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      refine Finset.card_le_card_of_injOn
        (fun π : Equiv.Perm I => π.symm.trans eU) ?_ ?_
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
  · intro π
    have hpred : ∀ c : I → Fin q,
        (Matrix.det (fun i j => if i.1 = (π j).1 then ζ ^ (col c (i, j)) else 0 :
          Matrix I I ℂ) ≠ 0) ↔
        ∀ r : Fin b, c (π.symm (r, 0)) ≠ c (π.symm (r, 1)) := by
      intro c
      rw [det_block2_ne_zero_iff hq hζ (col c) π]
      refine forall_congr' fun r => ?_
      simp only [phaseColor, col, Fin.val_one, Fin.val_zero, ↓reduceIte, zero_ne_one, Nat.cast_zero,
        sub_zero, ne_eq, ZMod.natCast_eq_natCast_iff']
      rw [Nat.mod_eq_of_lt (c (π.symm (r, 0))).isLt, Nat.mod_eq_of_lt (c (π.symm (r, 1))).isLt]
      exact not_congr Fin.ext_iff.symm
    let pairs : Finset (Fin q × Fin q) :=
      (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 ≠ p.2)
    have hpairs_card : pairs.card = q * (q - 1) := by
      have hsplit : pairs.card +
          ((Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 = p.2)).card = q * q := by
        rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
        calc ∑ p : Fin q × Fin q, ((if p.1 ≠ p.2 then 1 else 0) + (if p.1 = p.2 then 1 else 0))
            = ∑ _p : Fin q × Fin q, 1 := by
                refine Finset.sum_congr rfl fun p _ => ?_
                by_cases h : p.1 = p.2 <;> simp [h]
          _ = q * q := by simp
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
      omega
    calc ((Finset.univ : Finset (I → Fin q)).filter (fun c =>
            Matrix.det (fun i j => if i.1 = (π j).1 then ζ ^ (col c (i, j)) else 0 :
              Matrix I I ℂ) ≠ 0)).card
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
            have ht : (π j).2 = 0 ∨ (π j).2 = 1 := by omega
            rcases ht with h0 | h1
            · rw [hpair, h0]
              exact (Prod.mk.inj h').1
            · rw [hpair, h1]
              exact (Prod.mk.inj h').2
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
          congr 1
          ext f
          simp [Fintype.mem_piFinset]
      _ = (q * (q - 1)) ^ b := by
          rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            hpairs_card]
  · constructor
    · rintro ⟨s, hs⟩
      by_contra hlt
      push Not at hlt
      let φ0 : I → ZMod q := phaseColor (q := q) (fun e => (s e).val) ⟨0, hb⟩
      have hcard_lt : Fintype.card (ZMod q) < Fintype.card I := by
        rw [ZMod.card]
        simp [I]
        omega
      obtain ⟨j0, j1, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt φ0 hcard_lt
      have hex_perm : ∃ π : Equiv.Perm I, π.symm (⟨0, hb⟩, 0) = j0 ∧ π.symm (⟨0, hb⟩, 1) = j1 := by
        let a0 : I := (⟨0, hb⟩, 0)
        let a1 : I := (⟨0, hb⟩, 1)
        have ha_ne : a0 ≠ a1 := fun h => absurd (Prod.mk.inj h).2 (by decide)
        let σ1 : Equiv.Perm I := Equiv.swap a0 j0
        let σ2 : Equiv.Perm I := Equiv.swap (σ1 a1) j1
        let τ : Equiv.Perm I := σ1.trans σ2
        refine ⟨τ.symm, ?_, ?_⟩
        · change σ2 (σ1 a0) = j0
          have hσ1a0 : σ1 a0 = j0 := Equiv.swap_apply_left a0 j0
          rw [hσ1a0]
          have h1 : j0 ≠ σ1 a1 := by
            intro h
            have h2 : σ1 a0 = σ1 a1 := hσ1a0.trans h
            exact ha_ne (σ1.injective h2)
          exact Equiv.swap_apply_of_ne_of_ne h1 hne
        · change σ2 (σ1 a1) = j1
          exact Equiv.swap_apply_left (σ1 a1) j1
      rcases hex_perm with ⟨π, hπ0, hπ1⟩
      have hdet := (det_block2_ne_zero_iff hq hζ (fun e => (s e).val) π).mp (hs π) ⟨0, hb⟩
      rw [hπ0, hπ1] at hdet
      exact hdet heq
    · intro hle
      let c : I → Fin q := fun j => ⟨2 * j.1.val + j.2.val, by omega⟩
      have hc_inj : Function.Injective c := by
        intro j0 j1 h
        have hv : 2 * j0.1.val + j0.2.val = 2 * j1.1.val + j1.2.val := congr_arg Fin.val h
        apply Prod.ext
        · apply Fin.ext
          omega
        · apply Fin.ext
          omega
      let s : S := fun e => if e.1.2.val = 1 then c e.2 else ⟨0, by omega⟩
      refine ⟨s, fun π => ?_⟩
      rw [det_block2_ne_zero_iff hq hζ (fun e => (s e).val) π]
      intro r
      simp only [phaseColor, s, Fin.val_one, Fin.val_zero, ↓reduceIte, zero_ne_one, Nat.cast_zero,
        sub_zero, ne_eq, ZMod.natCast_eq_natCast_iff']
      rw [Nat.mod_eq_of_lt (c (π.symm (r, 0))).isLt, Nat.mod_eq_of_lt (c (π.symm (r, 1))).isLt]
      intro hval
      have hceq : c (π.symm (r, 0)) = c (π.symm (r, 1)) := Fin.ext hval
      have hpeq := π.symm.injective (hc_inj hceq)
      have h01 : (0 : Fin 2) = 1 := (Prod.mk.inj hpeq).2
      exact absurd h01 (by decide)

end PEqualNP.Outside.L_lib_1019_aux

theorem PEqualNP.Outside.L_lib_1019 :
  ∀ (b q : ℕ) (ζ : ℂ), 0 < b → 2 ≤ q → IsPrimitiveRoot ζ q →
  let I := Fin b × Fin 2
  let S := I × I → Fin q
  let D := fun (s : S) (π : Equiv.Perm I) =>
    Matrix.det (fun i j => if i.1 = (π j).1 then ζ^(s (i,j)).val else 0 : Matrix I I ℂ)
  let hits := fun s : S => ((Finset.univ : Finset (Equiv.Perm I)).filter (fun π => D s π ≠ 0)).card
  let col := fun (c : I → Fin q) (e : I × I) => if e.1.2.val = 1 then (c e.2).val else (0 : ℕ)
  (∀ (s : S) (k : ℕ), k ≤ b →
    hits s * q^(b-k) * (∏ j ∈ Finset.Ico k b, (2*j+1)) ≤
      (2*b).factorial * (q-1)^(b-k) * (∏ j ∈ Finset.Ico k b, (2*j+2))) ∧
  (∀ π : Equiv.Perm I, ((Finset.univ : Finset (I → Fin q)).filter (fun c =>
    Matrix.det (fun i j => if i.1 = (π j).1 then ζ^(col c (i,j)) else 0 : Matrix I I ℂ) ≠ 0)).card
      = (q*(q-1))^b) ∧
  ((∃ s : S, ∀ π : Equiv.Perm I, D s π ≠ 0) ↔ 2*b ≤ q) := by
  intro b q ζ hb hq hζ
  exact PEqualNP.Outside.L_lib_1019_aux.main_proof b q ζ hb hq hζ

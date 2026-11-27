import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25681_aux

def ix {k : ℕ} (hk : 0 < k) (pos : ℕ) : Fin k := ⟨pos % k, Nat.mod_lt _ hk⟩

def distMod {k : ℕ} (l r : Fin k) : ℕ := (r.val + k - l.val) % k

lemma ix_eq_iff {k : ℕ} (hk : 0 < k) (a b : ℕ) : ix hk a = ix hk b ↔ a % k = b % k := by
  simp [ix, Fin.ext_iff]

lemma ix_mod_left {k : ℕ} (hk : 0 < k) (a b : ℕ) :
    ix hk (a % k + b) = ix hk (a + b) := by
  rw [ix_eq_iff, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma ix_val_add {k : ℕ} (hk : 0 < k) (a b : ℕ) :
    ix hk ((ix hk a).val + b) = ix hk (a + b) :=
  ix_mod_left hk a b

lemma ix_add_sub {k : ℕ} (hk : 0 < k) (a : Fin k) (m s : ℕ) (hs : s < k) :
    ix hk ((ix hk (a.val + m)).val + k - s % k) = ix hk (a.val + m + k - s) := by
  rw [Nat.mod_eq_of_lt hs]
  simp only [ix, Fin.ext_iff]
  have h1 : (a.val + m) % k < k := Nat.mod_lt _ hk
  have hle1 : s ≤ (a.val + m) % k + k := by omega
  have hle2 : s ≤ a.val + m + k := by omega
  have hmod : ((a.val + m) % k + k - s) % k = ((a.val + m) % k + (k - s)) % k := by
    congr 1; omega
  have hmod2 : (a.val + m + k - s) % k = (a.val + m + (k - s)) % k := by
    congr 1; omega
  rw [hmod, hmod2, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma ix_shift_add {k : ℕ} (hk : 0 < k) (a : Fin k) (m1 m2 : ℕ) :
    ix hk ((ix hk (a.val + m1)).val + m2) = ix hk (a.val + (m1 + m2)) := by
  simp only [ix, Fin.ext_iff]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]

lemma ix_add_k {k : ℕ} (hk : 0 < k) (a : ℕ) : ix hk (a + k) = ix hk a := by
  rw [ix_eq_iff, Nat.add_mod_right]

lemma ix_self {k : ℕ} (hk : 0 < k) (a : Fin k) : ix hk a.val = a := by
  ext
  exact Nat.mod_eq_of_lt a.2

lemma ix_add_sub_cancel {k : ℕ} (hk : 0 < k) (a : Fin k) (d : ℕ) (hd : d ≤ k) :
    ix hk ((ix hk (a.val + k - d)).val + d) = a := by
  have h1 : a.val + k - d + d = a.val + k := by omega
  have h2 : ix hk ((ix hk (a.val + k - d)).val + d) = ix hk (a.val + k - d + d) :=
    ix_mod_left hk (a.val + k - d) d
  rw [h2, h1, ix_add_k, ix_self]

lemma distMod_ix_add {k : ℕ} (hk : 0 < k) (j : Fin k) (a b : ℕ) (ha : a < k) (hb : b < k) :
    distMod (ix hk (j.val + a)) (ix hk (j.val + b)) =
      if a ≤ b then b - a else k - (a - b) := by
  unfold distMod
  simp only [ix]
  have hja : (j.val + a) % k < k := Nat.mod_lt _ hk
  have hjb : (j.val + b) % k < k := Nat.mod_lt _ hk
  split_ifs with hab
  · have hstep : ((j.val + b) % k + k - (j.val + a) % k) % k = (b - a) % k := by
      have hmod1 : (j.val + b) % k = ((j.val + a) % k + (b - a)) % k := by
        symm
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        congr 1; omega
      rw [hmod1]
      by_cases hlt : (j.val + a) % k + (b - a) < k
      · rw [Nat.mod_eq_of_lt hlt]
        have hsub : (j.val + a) % k + (b - a) + k - (j.val + a) % k = (b - a) + k := by omega
        rw [hsub, Nat.add_mod_right]
      · have hlt2 : (j.val + a) % k + (b - a) - k < k := by omega
        have hmod2 : ((j.val + a) % k + (b - a)) % k = (j.val + a) % k + (b - a) - k := by
          have hadd : (j.val + a) % k + (b - a) = ((j.val + a) % k + (b - a) - k) + k := by omega
          conv_lhs => rw [hadd]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
        rw [hmod2]
        have hsub : (j.val + a) % k + (b - a) - k + k - (j.val + a) % k = b - a := by omega
        rw [hsub]
    rw [hstep, Nat.mod_eq_of_lt (by omega)]
  · have hmod1 : (j.val + a) % k = ((j.val + b) % k + (a - b)) % k := by
      symm
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      congr 1; omega
    rw [hmod1]
    by_cases hlt : (j.val + b) % k + (a - b) < k
    · rw [Nat.mod_eq_of_lt hlt]
      have hsub : (j.val + b) % k + k - ((j.val + b) % k + (a - b)) = k - (a - b) := by omega
      rw [hsub, Nat.mod_eq_of_lt (by omega)]
    · have hlt2 : (j.val + b) % k + (a - b) - k < k := by omega
      have hmod2 : ((j.val + b) % k + (a - b)) % k = (j.val + b) % k + (a - b) - k := by
        have hadd : (j.val + b) % k + (a - b) = ((j.val + b) % k + (a - b) - k) + k := by omega
        conv_lhs => rw [hadd]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
      rw [hmod2]
      have hsub : (j.val + b) % k + k - ((j.val + b) % k + (a - b) - k) = (k - (a - b)) + k := by
        omega
      rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

lemma distMod_ix_shift {k : ℕ} (hk : 0 < k) (l : Fin k) (d : ℕ) (hd : d < k) :
    distMod l (ix hk (l.val + d)) = d := by
  have h1 : l = ix hk (l.val + 0) := by simp [ix_self]
  conv_lhs => arg 1; rw [h1]
  rw [distMod_ix_add hk l 0 d hk hd]
  simp

lemma arc_distMod_le {k R : ℕ} (hk : 0 < k) (hRk : R < k) (j : Fin k) (a b : ℕ)
    (ha : a ≤ R) (hb : b ≤ R) :
    distMod (ix hk (j.val + a)) (ix hk (j.val + b)) ≤ R ∨
      distMod (ix hk (j.val + b)) (ix hk (j.val + a)) ≤ R := by
  by_cases hab : a ≤ b
  · left
    rw [distMod_ix_add hk j a b (by omega) (by omega)]
    simp only [hab, ↓reduceIte]
    omega
  · right
    rw [distMod_ix_add hk j b a (by omega) (by omega)]
    have hba : b ≤ a := by omega
    simp only [hba, ↓reduceIte]
    omega

lemma arc_distMod_eq_R {k R : ℕ} (hk : 0 < k) (h2R : 2 * R < k) (j : Fin k) (a b : ℕ)
    (ha : a ≤ R) (hb : b ≤ R)
    (hdist : distMod (ix hk (j.val + a)) (ix hk (j.val + b)) = R) :
    a = 0 ∧ b = R := by
  rw [distMod_ix_add hk j a b (by omega) (by omega)] at hdist
  split_ifs at hdist with hab
  · omega
  · omega

lemma ix_add_inj {k : ℕ} (hk : 0 < k) (d : ℕ) :
    Function.Injective (fun j : Fin k => ix hk (j.val + d)) := by
  intro j1 j2 h
  rw [ix_eq_iff] at h
  have hsub : (j1.val + d) % k = (j2.val + d) % k := h
  have hlt1 : j1.val < k := j1.2
  have hlt2 : j2.val < k := j2.2
  have hmod : (j1.val + d) % k = (j1.val + d % k) % k := by
    symm; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have hmod2 : (j2.val + d) % k = (j2.val + d % k) % k := by
    symm; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [hmod, hmod2] at hsub
  have hd : d % k < k := Nat.mod_lt _ hk
  ext
  by_cases h1 : j1.val + d % k < k <;> by_cases h2 : j2.val + d % k < k
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hsub
    omega
  · have hm2 : (j2.val + d % k) % k = j2.val + d % k - k := by
      have ha : j2.val + d % k = (j2.val + d % k - k) + k := by omega
      conv_lhs => rw [ha]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [Nat.mod_eq_of_lt h1, hm2] at hsub
    omega
  · have hm1 : (j1.val + d % k) % k = j1.val + d % k - k := by
      have ha : j1.val + d % k = (j1.val + d % k - k) + k := by omega
      conv_lhs => rw [ha]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hm1, Nat.mod_eq_of_lt h2] at hsub
    omega
  · have hm1 : (j1.val + d % k) % k = j1.val + d % k - k := by
      have ha : j1.val + d % k = (j1.val + d % k - k) + k := by omega
      conv_lhs => rw [ha]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have hm2 : (j2.val + d % k) % k = j2.val + d % k - k := by
      have ha : j2.val + d % k = (j2.val + d % k - k) + k := by omega
      conv_lhs => rw [ha]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hm1, hm2] at hsub
    omega

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

lemma cyclic_band_rank_bound {k R : ℕ} (hk : 0 < k) (h2R : 2 * R < k) (σ : ℕ)
    (M : Matrix (Fin k) (Fin k) (ZMod 2)) (m : Fin k → ZMod 2)
    (hband : ∀ l r : Fin k, R < distMod l r → R < distMod r l → M l r = 0)
    (hdiag : ∀ i : Fin k, M (ix hk (i.val + σ)) (ix hk (i.val + σ + R)) = m i) :
    (k - 2 * R) * (Finset.univ.filter (fun i : Fin k => m i ≠ 0)).card ≤ k * M.rank := by
  classical
  let L : ℕ := k - 2 * R
  have hper_t : ∀ t : Fin k,
      ((Finset.univ : Finset (Fin L)).filter (fun j => m (ix hk (t.val + j.val)) ≠ 0)).card ≤
        M.rank := by
    intro t
    let S : Finset (Fin L) :=
      (Finset.univ : Finset (Fin L)).filter (fun j => m (ix hk (t.val + j.val)) ≠ 0)
    let eS : Fin S.card ≃o S := S.orderIsoOfFin rfl
    let colIdx : Fin S.card → Fin k := fun q => ix hk (t.val + (eS q).1.val + σ + R)
    let rowIdx : Fin S.card → Fin k := fun p => ix hk (t.val + (eS p).1.val + σ)
    have hdiag_eq : ∀ p : Fin S.card, M (rowIdx p) (colIdx p) = 1 := by
      intro p
      have hmem : m (ix hk (t.val + (eS p).1.val)) ≠ 0 := (Finset.mem_filter.mp (eS p).2).2
      have h1 : rowIdx p = ix hk ((ix hk (t.val + (eS p).1.val)).val + σ) := by
        simp only [rowIdx]
        exact (ix_val_add hk (t.val + (eS p).1.val) σ).symm
      have h2 : colIdx p = ix hk ((ix hk (t.val + (eS p).1.val)).val + σ + R) := by
        simp only [colIdx]
        rw [Nat.add_assoc (t.val + (eS p).1.val) σ R, Nat.add_assoc _ σ R]
        exact (ix_val_add hk (t.val + (eS p).1.val) (σ + R)).symm
      rw [h1, h2, hdiag]
      exact zmod2_eq_one_of_ne_zero hmem
    have hupper : ∀ p q : Fin S.card, p < q → M (rowIdx p) (colIdx q) = 0 := by
      intro p q hpq
      have hlt : (eS p).1.val < (eS q).1.val := eS.strictMono hpq
      have hqp_lt : (eS q).1.val < L := (eS q).1.2
      let base : Fin k := ix hk (t.val + σ)
      have hrp : rowIdx p = ix hk (base.val + (eS p).1.val) := by
        simp only [rowIdx, base]
        rw [ix_val_add]
        congr 1; omega
      have hcq : colIdx q = ix hk (base.val + ((eS q).1.val + R)) := by
        simp only [colIdx, base]
        rw [ix_val_add]
        congr 1; omega
      have ha_lt : (eS p).1.val < k := by omega
      have hb_lt : (eS q).1.val + R < k := by omega
      have hd1 : distMod (rowIdx p) (colIdx q) = (eS q).1.val + R - (eS p).1.val := by
        rw [hrp, hcq, distMod_ix_add hk base _ _ ha_lt hb_lt]
        have hle : (eS p).1.val ≤ (eS q).1.val + R := by omega
        simp only [hle, ↓reduceIte]
      have hd2 : distMod (colIdx q) (rowIdx p) = k - ((eS q).1.val + R - (eS p).1.val) := by
        rw [hrp, hcq, distMod_ix_add hk base _ _ hb_lt ha_lt]
        have hgt : ¬ (eS q).1.val + R ≤ (eS p).1.val := by omega
        simp only [hgt, ↓reduceIte]
      exact hband _ _ (by omega) (by omega)
    let vecs : Fin S.card → LinearMap.range M.mulVecLin :=
      fun q => ⟨M.mulVecLin (Pi.single (M := fun _ => ZMod 2) (colIdx q) 1),
        ⟨Pi.single (M := fun _ => ZMod 2) (colIdx q) 1, rfl⟩⟩
    have hli : LinearIndependent (ZMod 2) vecs := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hzero_vec :
          (∑ q : Fin S.card, c q • M.mulVecLin (Pi.single (M := fun _ => ZMod 2) (colIdx q) 1)) = 0 := by
        have hval := congrArg Subtype.val hc
        simpa [vecs] using hval
      have heval : ∀ p : Fin S.card, (∑ q : Fin S.card, c q * M (rowIdx p) (colIdx q)) = 0 := by
        intro p
        have hp := congrFun hzero_vec (rowIdx p)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
          Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at hp
        have hcol : ∀ q : Fin S.card,
            (∑ j : Fin k, M (rowIdx p) j * Pi.single (M := fun _ => ZMod 2) (colIdx q) 1 j) =
              M (rowIdx p) (colIdx q) := by
          intro q
          have hterm : ∀ j : Fin k,
              M (rowIdx p) j * Pi.single (M := fun _ => ZMod 2) (colIdx q) 1 j =
                if j = colIdx q then M (rowIdx p) (colIdx q) else 0 := by
            intro j
            by_cases hj : j = colIdx q
            · subst hj; simp
            · simp [hj]
          simp_rw [hterm]
          simp
        simp_rw [hcol] at hp
        exact hp
      have hval : ∀ n : ℕ, ∀ (hn : n < S.card), c ⟨n, hn⟩ = 0 := by
        intro n
        induction n using Nat.strong_induction_on with
        | ind n ih =>
          intro hn
          let p : Fin S.card := ⟨n, hn⟩
          have hp0 := heval p
          have hsplit : (∑ q : Fin S.card, c q * M (rowIdx p) (colIdx q)) = c p := by
            rw [Finset.sum_eq_single p]
            · rw [hdiag_eq p, mul_one]
            · intro q _ hqp
              by_cases hlt : q < p
              · rw [ih q.val hlt q.2, zero_mul]
              · have hgt : p < q := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hqp)
                rw [hupper p q hgt, mul_zero]
            · intro hp_abs
              exact absurd (Finset.mem_univ p) hp_abs
          rw [hsplit] at hp0
          exact hp0
      intro p
      exact hval p.val p.2
    have hcard_le : Fintype.card (Fin S.card) ≤ Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) :=
      hli.fintype_card_le_finrank
    simpa [Matrix.rank] using hcard_le
  have hsum_le :
      (∑ t : Fin k, ((Finset.univ : Finset (Fin L)).filter
        (fun j => m (ix hk (t.val + j.val)) ≠ 0)).card) ≤ k * M.rank := by
    calc
      (∑ t : Fin k, ((Finset.univ : Finset (Fin L)).filter
          (fun j => m (ix hk (t.val + j.val)) ≠ 0)).card)
          ≤ ∑ _t : Fin k, M.rank := Finset.sum_le_sum fun t _ => hper_t t
      _ = k * M.rank := by simp
  have hsum_eq :
      (∑ t : Fin k, ((Finset.univ : Finset (Fin L)).filter
        (fun j => m (ix hk (t.val + j.val)) ≠ 0)).card) =
      L * (Finset.univ.filter (fun i : Fin k => m i ≠ 0)).card := by
    have hcard : ∀ t : Fin k,
        ((Finset.univ : Finset (Fin L)).filter (fun j => m (ix hk (t.val + j.val)) ≠ 0)).card =
          ∑ j : Fin L, if m (ix hk (t.val + j.val)) ≠ 0 then 1 else 0 := by
      intro t
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    simp_rw [hcard]
    rw [Finset.sum_comm]
    have hinner : ∀ j : Fin L,
        (∑ t : Fin k, if m (ix hk (t.val + j.val)) ≠ 0 then 1 else 0) =
          (Finset.univ.filter (fun i : Fin k => m i ≠ 0)).card := by
      intro j
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      have hbij : Function.Bijective (fun t : Fin k => ix hk (t.val + j.val)) :=
        (Finite.injective_iff_bijective.mp (ix_add_inj hk j.val))
      exact Fintype.sum_bijective (fun t : Fin k => ix hk (t.val + j.val)) hbij _ _ fun _ => rfl
    simp_rw [hinner]
    simp
  rw [← hsum_eq]
  exact hsum_le

lemma matrix_rank_add_le {k : ℕ} (A B : Matrix (Fin k) (Fin k) (ZMod 2)) :
    (A + B).rank ≤ A.rank + B.rank := by
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro y ⟨x, rfl⟩
    have heq : (A + B).mulVecLin x = A.mulVecLin x + B.mulVecLin x := by
      simp
    rw [heq]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  have h1 : (A + B).rank ≤ Module.finrank (ZMod 2)
      (↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin)) :=
    Submodule.finrank_mono hle
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  change (A + B).rank ≤ Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) +
    Module.finrank (ZMod 2) (LinearMap.range B.mulVecLin)
  omega

lemma matrix_rank_outer_le_one {k : ℕ} (u v : Fin k → ZMod 2) :
    (Matrix.of fun i j => u i * v j).rank ≤ 1 := by
  let M : Matrix (Fin k) (Fin k) (ZMod 2) := Matrix.of fun i j => u i * v j
  have hle : LinearMap.range M.mulVecLin ≤ Submodule.span (ZMod 2) {u} := by
    rintro y ⟨x, rfl⟩
    have heq : M.mulVecLin x = (dotProduct v x) • u := by
      ext i
      simp only [M, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
  have h1 : M.rank ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {u}) :=
    Submodule.finrank_mono hle
  let φ : ZMod 2 →ₗ[ZMod 2] Submodule.span (ZMod 2) {u} :=
    { toFun := fun a => ⟨a • u, Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton u))⟩
      map_add' := fun a b => by ext x; simp; ring
      map_smul' := fun c a => by ext x; simp; ring }
  have hφ_surj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [Submodule.mem_span_singleton] at hy
    rcases hy with ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφ_surj
  have hr := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrange, finrank_top] at hr
  have hdim1 : Module.finrank (ZMod 2) (ZMod 2) = 1 := Module.finrank_self (ZMod 2)
  rw [hdim1] at hr
  change M.rank ≤ 1
  omega

lemma matrix_rank_sym_outer_le_two {k : ℕ} (u v : Fin k → ZMod 2) :
    (Matrix.of fun i j => u i * v j + v i * u j).rank ≤ 2 := by
  have heq : (Matrix.of fun i j => u i * v j + v i * u j) =
      (Matrix.of fun i j => u i * v j) + (Matrix.of fun i j => v i * u j) := by
    ext i j; rfl
  rw [heq]
  exact le_trans (matrix_rank_add_le _ _)
    (Nat.add_le_add (matrix_rank_outer_le_one u v) (matrix_rank_outer_le_one v u))

lemma matrix_rank_sum_le {k : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin k) (Fin k) (ZMod 2)) :
    (∑ i ∈ s, f i).rank ≤ ∑ i ∈ s, (f i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    have h0 : LinearMap.range (0 : Matrix (Fin k) (Fin k) (ZMod 2)).mulVecLin = ⊥ := by
      ext y; simp
    change Module.finrank (ZMod 2)
      (LinearMap.range (0 : Matrix (Fin k) (Fin k) (ZMod 2)).mulVecLin) ≤ 0
    rw [h0]
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (matrix_rank_add_le _ _) (Nat.add_le_add_left ih _)

def chi (z : ZMod 2) : ℤ := if z = 0 then 1 else -1

lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> decide

lemma chi_zero : chi 0 = 1 := rfl

lemma chi_one : chi 1 = -1 := by decide

lemma chi_le_one (a : ZMod 2) : chi a ≤ 1 := by
  fin_cases a <;> decide

lemma chi_abs_le_one (a : ZMod 2) : -1 ≤ chi a ∧ chi a ≤ 1 := by
  fin_cases a <;> decide

lemma sum_chi_linear {s : ℕ} (φ : (Fin s → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    (∑ x : Fin s → ZMod 2, chi (φ x)) = if φ = 0 then (2 : ℤ) ^ s else 0 := by
  split_ifs with hφ
  · subst hφ
    simp [chi_zero]
  · have hne : ∃ x0 : Fin s → ZMod 2, φ x0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hφ (LinearMap.ext h)
    rcases hne with ⟨x0, hx0⟩
    have hx0_one : φ x0 = 1 := zmod2_eq_one_of_ne_zero hx0
    have hx00 : x0 + x0 = 0 := funext fun i => zmod2_add_self (x0 i)
    have hbij : Function.Bijective (fun x : Fin s → ZMod 2 => x + x0) :=
      ⟨fun x y h => by
        have := congrArg (fun z => z + x0) h
        simpa [add_assoc, hx00] using this,
       fun y => ⟨y + x0, by simp [add_assoc, hx00]⟩⟩
    have hshift : (∑ x : Fin s → ZMod 2, chi (φ x)) =
        ∑ x : Fin s → ZMod 2, chi (φ (x + x0)) :=
      (Fintype.sum_bijective (fun x => x + x0) hbij _ _ fun _ => rfl).symm
    have hneg : (∑ x : Fin s → ZMod 2, chi (φ (x + x0))) =
        -(∑ x : Fin s → ZMod 2, chi (φ x)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [map_add, hx0_one, chi_add, chi_one]
      ring
    linarith

lemma card_submodule_zmod2 {s : ℕ} (K : Submodule (ZMod 2) (Fin s → ZMod 2)) [Fintype K] :
    Fintype.card K = 2 ^ Module.finrank (ZMod 2) K := by
  let b := Module.finBasis (ZMod 2) K
  have hcard : Fintype.card K = Fintype.card (Fin (Module.finrank (ZMod 2) K) → ZMod 2) :=
    Fintype.card_congr b.equivFun.toEquiv
  rw [hcard]
  simp

lemma rank_comp_injective_bound {k s : ℕ}
    (T : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (L : (Fin s → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (hL : Function.Injective L) :
    Module.finrank (ZMod 2) (LinearMap.range T) ≤
      Module.finrank (ZMod 2) (LinearMap.range (T.comp L)) + (k - s) := by
  have hrT := LinearMap.finrank_range_add_finrank_ker T
  have hrTL := LinearMap.finrank_range_add_finrank_ker (T.comp L)
  have hdim_k : Module.finrank (ZMod 2) (Fin k → ZMod 2) = k := by simp
  have hdim_s : Module.finrank (ZMod 2) (Fin s → ZMod 2) = s := by simp
  rw [hdim_k] at hrT
  rw [hdim_s] at hrTL
  let φ : LinearMap.ker (T.comp L) →ₗ[ZMod 2] LinearMap.ker T :=
    { toFun := fun x => ⟨L x.1, x.2⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp }
  have hφ_inj : Function.Injective φ := by
    intro x y h
    ext
    exact congrFun (hL (congrArg Subtype.val h)) _
  have hker_le : Module.finrank (ZMod 2) (LinearMap.ker (T.comp L)) ≤
      Module.finrank (ZMod 2) (LinearMap.ker T) :=
    LinearMap.finrank_le_finrank_of_injective hφ_inj
  have hs_le : s ≤ k := by
    have := LinearMap.finrank_le_finrank_of_injective hL
    simpa using this
  omega

lemma rank_postcomp_bound {k s : ℕ}
    (A : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (B : (Fin s → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) :
    Module.finrank (ZMod 2) (LinearMap.range B) ≤
      Module.finrank (ZMod 2) (LinearMap.range (A.comp B)) +
        Module.finrank (ZMod 2) (LinearMap.ker A) := by
  let R := LinearMap.range B
  let A_res : R →ₗ[ZMod 2] (Fin s → ZMod 2) := A.domRestrict R
  have hr := LinearMap.finrank_range_add_finrank_ker A_res
  have hrange_eq : LinearMap.range A_res = LinearMap.range (A.comp B) := by
    ext y
    constructor
    · rintro ⟨⟨x, ⟨z, rfl⟩⟩, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨⟨B z, ⟨z, rfl⟩⟩, rfl⟩
  let ι : LinearMap.ker A_res →ₗ[ZMod 2] LinearMap.ker A :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      map_add' := fun x y => by ext; rfl
      map_smul' := fun c x => by ext; rfl }
  have hι_inj : Function.Injective ι := by
    intro x y h
    have hv : x.1.1 = y.1.1 := by
      simpa [ι] using congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext hv)
  have hker_le : Module.finrank (ZMod 2) (LinearMap.ker A_res) ≤
      Module.finrank (ZMod 2) (LinearMap.ker A) :=
    LinearMap.finrank_le_finrank_of_injective hι_inj
  rw [hrange_eq] at hr
  have hR : Module.finrank (ZMod 2) R = Module.finrank (ZMod 2) (LinearMap.range B) := rfl
  rw [hR] at hr
  omega

lemma finrank_ker_transpose_eq {k s : ℕ}
    (L : (Fin s → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (hL : Function.Injective L) :
    let Lt : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2) :=
      { toFun := fun w j => dotProduct (L (Pi.single (M := fun _ => ZMod 2) j 1)) w
        map_add' := fun w1 w2 => by ext j; simp [dotProduct_add]
        map_smul' := fun c w => by ext j; simp [dotProduct_smul] }
    Module.finrank (ZMod 2) (LinearMap.ker Lt) = k - s := by
  intro Lt
  let M : Matrix (Fin k) (Fin s) (ZMod 2) :=
    Matrix.of fun i j => L (Pi.single (M := fun _ => ZMod 2) j 1) i
  have hM_mulVec : M.mulVecLin = L := by
    apply LinearMap.ext
    intro x
    ext i
    simp only [M, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]
    have hx : x = ∑ j : Fin s, x j • Pi.single (M := fun _ => ZMod 2) j 1 := by
      ext j'
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hterm : ∀ j : Fin s,
          x j * Pi.single (M := fun _ => ZMod 2) j 1 j' = if j = j' then x j' else 0 := by
        intro j
        by_cases h : j = j'
        · subst h; simp
        · simp [h]
      simp_rw [hterm]
      simp
    conv_rhs => rw [hx, map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  have hMt_mulVec : M.transpose.mulVecLin = Lt := by
    apply LinearMap.ext
    intro w
    ext j
    simp only [M, Lt, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply, Matrix.mulVec,
      dotProduct, Matrix.transpose_apply, Matrix.of_apply]
  have hM_rank : M.rank = s := by
    change Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) = s
    rw [hM_mulVec]
    have hker : LinearMap.ker L = ⊥ := LinearMap.ker_eq_bot.mpr hL
    have hr := LinearMap.finrank_range_add_finrank_ker L
    rw [hker] at hr
    simp at hr
    exact hr
  have hLt_rank : Module.finrank (ZMod 2) (LinearMap.range Lt) = s := by
    rw [← hMt_mulVec]
    change M.transpose.rank = s
    rw [Matrix.rank_transpose, hM_rank]
  have hrLt := LinearMap.finrank_range_add_finrank_ker Lt
  have hdim_k : Module.finrank (ZMod 2) (Fin k → ZMod 2) = k := by simp
  rw [hdim_k, hLt_rank] at hrLt
  omega

lemma walsh_quadratic_bound {k s : ℕ} (hs : s ≤ k)
    (F : (Fin k → ZMod 2) → ZMod 2)
    (P : Matrix (Fin k) (Fin k) (ZMod 2))
    (hpolar_shift : ∀ u v w : Fin k → ZMod 2,
      F (u + v + w) + F (u + v) + F (u + w) + F u = dotProduct v (P.mulVec w))
    (L : (Fin s → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (hL : Function.Injective L)
    (base : Fin k → ZMod 2)
    (ell : (Fin s → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (c : ZMod 2) :
    let bias : ℤ := ∑ x : Fin s → ZMod 2, chi (F (base + L x) + ell x + c)
    bias ^ 2 * (2 : ℤ) ^ (P.rank - 2 * (k - s)) ≤ (2 : ℤ) ^ (2 * s) := by
  classical
  intro bias
  let G : (Fin s → ZMod 2) → ZMod 2 := fun x => F (base + L x) + ell x + c
  let Lt : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2) :=
    { toFun := fun w j => dotProduct (L (Pi.single (M := fun _ => ZMod 2) j 1)) w
      map_add' := fun w1 w2 => by ext j; simp [dotProduct_add]
      map_smul' := fun c w => by ext j; simp [dotProduct_smul] }
  have hLt_dot : ∀ (x : Fin s → ZMod 2) (w : Fin k → ZMod 2),
      dotProduct (L x) w = dotProduct x (Lt w) := by
    intro x w
    have hx : x = ∑ j : Fin s, x j • Pi.single (M := fun _ => ZMod 2) j 1 := by
      ext j'
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hterm : ∀ j : Fin s,
          x j * Pi.single (M := fun _ => ZMod 2) j 1 j' = if j = j' then x j' else 0 := by
        intro j
        by_cases h : j = j'
        · subst h; simp
        · simp [h]
      simp_rw [hterm]
      simp
    conv_lhs => rw [hx, map_sum]
    simp only [dotProduct, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, Lt,
      LinearMap.coe_mk, AddHom.coe_mk]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  let U : (Fin s → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2) := Lt.comp (P.mulVecLin.comp L)
  let K : Submodule (ZMod 2) (Fin s → ZMod 2) := LinearMap.ker U
  have hG_diff : ∀ x h : Fin s → ZMod 2,
      G (x + h) + G x = dotProduct x (U h) + (F (base + L h) + F base + ell h) := by
    intro x h
    have h1 := hpolar_shift base (L x) (L h)
    have h2 : F (base + L (x + h)) + F (base + L x) =
        dotProduct (L x) (P.mulVec (L h)) + F (base + L h) + F base := by
      rw [map_add, ← add_assoc]
      have h3 := congrArg (fun t => t + F (base + L h) + F base) h1
      have hlhs : F (base + L x + L h) + F (base + L x) + F (base + L h) + F base +
          F (base + L h) + F base = F (base + L x + L h) + F (base + L x) := by
        have hz1 : F (base + L h) + F (base + L h) = 0 := zmod2_add_self _
        have hz2 : F base + F base = 0 := zmod2_add_self _
        calc
          F (base + L x + L h) + F (base + L x) + F (base + L h) + F base +
              F (base + L h) + F base
              = F (base + L x + L h) + F (base + L x) +
                (F (base + L h) + F (base + L h)) + (F base + F base) := by ring
          _ = F (base + L x + L h) + F (base + L x) := by rw [hz1, hz2]; ring
      rw [hlhs] at h3
      exact h3
    have hdot : dotProduct (L x) (P.mulVec (L h)) = dotProduct x (U h) := by
      simpa [U, Matrix.mulVecLin_apply] using hLt_dot x (P.mulVec (L h))
    simp only [G]
    rw [map_add ell x h]
    have hcancel : F (base + L (x + h)) + (ell x + ell h) + c + (F (base + L x) + ell x + c) =
        F (base + L (x + h)) + F (base + L x) + ell h + (ell x + ell x) + (c + c) := by ring
    rw [hcancel, zmod2_add_self, zmod2_add_self, h2, hdot]
    ring
  have hbias_sq : bias ^ 2 =
      ∑ h : Fin s → ZMod 2,
        chi (F (base + L h) + F base + ell h) * ∑ x : Fin s → ZMod 2, chi (dotProduct x (U h)) := by
    have hsq : bias ^ 2 = ∑ x : Fin s → ZMod 2, ∑ y : Fin s → ZMod 2, chi (G x + G y) := by
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro y _
      rw [← chi_add]
    rw [hsq]
    have hshift : ∀ x : Fin s → ZMod 2,
        (∑ y : Fin s → ZMod 2, chi (G x + G y)) =
          ∑ h : Fin s → ZMod 2, chi (G (x + h) + G x) := by
      intro x
      have hxx : x + x = 0 := funext fun i => zmod2_add_self (x i)
      have hbij : Function.Bijective (fun h : Fin s → ZMod 2 => x + h) :=
        ⟨fun h1 h2 heq => by
          have := congrArg (fun z => x + z) heq
          simpa [← add_assoc, hxx] using this,
         fun y => ⟨x + y, by simp [← add_assoc, hxx]⟩⟩
      refine (Fintype.sum_bijective (fun h => x + h) hbij _ _ ?_).symm
      intro h
      rw [add_comm (G x) (G (x + h))]
    simp_rw [hshift]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro h _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [hG_diff x h, chi_add, mul_comm]
  have hinner : ∀ h : Fin s → ZMod 2,
      (∑ x : Fin s → ZMod 2, chi (dotProduct x (U h))) =
        if h ∈ K then (2 : ℤ) ^ s else 0 := by
    intro h
    let φ : (Fin s → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun x => dotProduct x (U h)
        map_add' := fun x1 x2 => by simp [add_dotProduct]
        map_smul' := fun a x => by simp [smul_dotProduct] }
    have hφ0 : φ = 0 ↔ h ∈ K := by
      constructor
      · intro h0
        show U h = 0
        ext j
        have hj := congrArg (fun f => f (Pi.single (M := fun _ => ZMod 2) j 1)) h0
        simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply, dotProduct] at hj
        have hterm : ∀ i : Fin s,
            Pi.single (M := fun _ => ZMod 2) j 1 i * U h i = if i = j then U h j else 0 := by
          intro i
          by_cases hij : i = j
          · subst hij; simp
          · simp [hij]
        simp_rw [hterm] at hj
        simpa using hj
      · intro hK
        have hU0 : U h = 0 := hK
        ext x
        simp [φ, hU0]
    have hsum : (∑ x : Fin s → ZMod 2, chi (dotProduct x (U h))) =
        if φ = 0 then (2 : ℤ) ^ s else 0 := sum_chi_linear φ
    rw [hsum]
    by_cases hmem : h ∈ K
    · have h0 : φ = 0 := hφ0.mpr hmem
      simp only [h0, hmem, ↓reduceIte]
    · have h0 : φ ≠ 0 := mt hφ0.mp hmem
      simp only [h0, hmem, ↓reduceIte]
  have hbias_le_card : bias ^ 2 ≤ (Fintype.card K : ℤ) * (2 : ℤ) ^ s := by
    rw [hbias_sq]
    simp_rw [hinner]
    have hterm : ∀ h : Fin s → ZMod 2,
        chi (F (base + L h) + F base + ell h) * (if h ∈ K then (2 : ℤ) ^ s else 0) ≤
          if h ∈ K then (2 : ℤ) ^ s else 0 := by
      intro h
      split_ifs
      · have h1 := chi_le_one (F (base + L h) + F base + ell h)
        have h2 : (0 : ℤ) ≤ (2 : ℤ) ^ s := by positivity
        nlinarith
      · simp
    calc
      ∑ h : Fin s → ZMod 2,
          chi (F (base + L h) + F base + ell h) * (if h ∈ K then (2 : ℤ) ^ s else 0)
          ≤ ∑ h : Fin s → ZMod 2, if h ∈ K then (2 : ℤ) ^ s else 0 :=
        Finset.sum_le_sum fun h _ => hterm h
      _ = ((Finset.univ.filter (fun h : Fin s → ZMod 2 => h ∈ K)).card : ℤ) * (2 : ℤ) ^ s := by
        rw [← Finset.sum_filter]
        simp
      _ = (Fintype.card K : ℤ) * (2 : ℤ) ^ s := by
        congr 1
        exact_mod_cast (Fintype.card_subtype (fun h : Fin s → ZMod 2 => h ∈ K)).symm
  have hcardK : (Fintype.card K : ℤ) = (2 : ℤ) ^ Module.finrank (ZMod 2) K := by
    exact_mod_cast card_submodule_zmod2 K
  rw [hcardK] at hbias_le_card
  have hrank_bound : P.rank ≤ Module.finrank (ZMod 2) (LinearMap.range U) + 2 * (k - s) := by
    have h1 := rank_comp_injective_bound P.mulVecLin L hL
    have h2 := rank_postcomp_bound Lt (P.mulVecLin.comp L)
    have h3 : Module.finrank (ZMod 2) (LinearMap.ker Lt) = k - s :=
      finrank_ker_transpose_eq L hL
    change Module.finrank (ZMod 2) (LinearMap.range P.mulVecLin) ≤
      Module.finrank (ZMod 2) (LinearMap.range (Lt.comp (P.mulVecLin.comp L))) + 2 * (k - s)
    omega
  have hrU := LinearMap.finrank_range_add_finrank_ker U
  have hdim_s : Module.finrank (ZMod 2) (Fin s → ZMod 2) = s := by simp
  rw [hdim_s] at hrU
  have hexp_le : Module.finrank (ZMod 2) K + (P.rank - 2 * (k - s)) ≤ s := by
    change Module.finrank (ZMod 2) (LinearMap.ker U) + (P.rank - 2 * (k - s)) ≤ s
    omega
  have hpow_pos : (0 : ℤ) ≤ (2 : ℤ) ^ (P.rank - 2 * (k - s)) := by positivity
  calc
    bias ^ 2 * (2 : ℤ) ^ (P.rank - 2 * (k - s))
        ≤ ((2 : ℤ) ^ Module.finrank (ZMod 2) K * (2 : ℤ) ^ s) *
            (2 : ℤ) ^ (P.rank - 2 * (k - s)) :=
      mul_le_mul_of_nonneg_right hbias_le_card hpow_pos
    _ = (2 : ℤ) ^ (Module.finrank (ZMod 2) K + (P.rank - 2 * (k - s)) + s) := by
      rw [← pow_add, ← pow_add]
      ring
    _ ≤ (2 : ℤ) ^ (s + s) := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    _ = (2 : ℤ) ^ (2 * s) := by
      congr 1; omega

lemma polar_of_affine_prod {k : ℕ}
    (α β : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) (c1 c2 : ZMod 2)
    (u v w : Fin k → ZMod 2) :
    let G := fun x => (α x + c1) * (β x + c2)
    G (u + v + w) + G (u + v) + G (u + w) + G u = α v * β w + α w * β v := by
  intro G
  simp only [G, map_add]
  have h1 :
      (α u + α v + α w + c1) * (β u + β v + β w + c2) +
        (α u + α v + c1) * (β u + β v + c2) +
        (α u + α w + c1) * (β u + β w + c2) +
        (α u + c1) * (β u + c2) =
      (α v * β w + α w * β v) +
        ((α u * β u + α u * β u) + (α u * β u + α u * β u)) +
        (α u * β v + α u * β v) + (α u * β w + α u * β w) +
        (α v * β u + α v * β u) + (α w * β u + α w * β u) +
        (α v * β v + α v * β v) + (α w * β w + α w * β w) +
        ((α u * c2 + α u * c2) + (α u * c2 + α u * c2)) +
        (α v * c2 + α v * c2) + (α w * c2 + α w * c2) +
        ((c1 * β u + c1 * β u) + (c1 * β u + c1 * β u)) +
        (c1 * β v + c1 * β v) + (c1 * β w + c1 * β w) +
        ((c1 * c2 + c1 * c2) + (c1 * c2 + c1 * c2)) := by ring
  rw [h1]
  simp only [zmod2_add_self, add_zero]

lemma polar_of_linear {k : ℕ} (ℓ : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) (c0 : ZMod 2)
    (u v w : Fin k → ZMod 2) :
    let G := fun x => ℓ x + c0
    G (u + v + w) + G (u + v) + G (u + w) + G u = 0 := by
  intro G
  simp only [G, map_add]
  have h1 :
      ℓ u + ℓ v + ℓ w + c0 + (ℓ u + ℓ v + c0) + (ℓ u + ℓ w + c0) + (ℓ u + c0) =
      ((ℓ u + ℓ u) + (ℓ u + ℓ u)) + (ℓ v + ℓ v) + (ℓ w + ℓ w) + ((c0 + c0) + (c0 + c0)) := by
    ring
  rw [h1]
  simp only [zmod2_add_self, add_zero]

def linRowA {k : ℕ} (hk : 0 < k) (i : Fin k) : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  { toFun := fun w => w (ix hk (i.val + k - 1)) + w i + w (ix hk (i.val + 1))
    map_add' := fun x y => by simp only [Pi.add_apply]; ring
    map_smul' := fun c x => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

def linRowB {k : ℕ} (hk : 0 < k) (i : Fin k) : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  { toFun := fun w => w i + w (ix hk (i.val + 1)) + w (ix hk (i.val + 2))
    map_add' := fun x y => by simp only [Pi.add_apply]; ring
    map_smul' := fun c x => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

def linColA {k : ℕ} (hk : 0 < k) (i : Fin k) : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  { toFun := fun w => w (ix hk (i.val + k - 4)) + w (ix hk (i.val + k - 2)) + w i
    map_add' := fun x y => by simp only [Pi.add_apply]; ring
    map_smul' := fun c x => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

def linColB {k : ℕ} (hk : 0 < k) (i : Fin k) : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  { toFun := fun w =>
      w (ix hk (i.val + k - 3)) + w (ix hk (i.val + k - 1)) + w (ix hk (i.val + 1))
    map_add' := fun x y => by simp only [Pi.add_apply]; ring
    map_smul' := fun c x => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

def unitVec {k : ℕ} (j i : Fin k) : ZMod 2 := if i = j then 1 else 0

lemma eval_linRowA_unit {k : ℕ} (hk : 0 < k) (i l : Fin k) :
    linRowA hk i (unitVec l) =
      (if ix hk (i.val + k - 1) = l then 1 else 0) +
      (if i = l then 1 else 0) +
      (if ix hk (i.val + 1) = l then 1 else 0) := rfl

lemma eval_linRowB_unit {k : ℕ} (hk : 0 < k) (i l : Fin k) :
    linRowB hk i (unitVec l) =
      (if i = l then 1 else 0) +
      (if ix hk (i.val + 1) = l then 1 else 0) +
      (if ix hk (i.val + 2) = l then 1 else 0) := rfl

lemma eval_linColA_unit {k : ℕ} (hk : 0 < k) (i l : Fin k) :
    linColA hk i (unitVec l) =
      (if ix hk (i.val + k - 4) = l then 1 else 0) +
      (if ix hk (i.val + k - 2) = l then 1 else 0) +
      (if i = l then 1 else 0) := rfl

lemma eval_linColB_unit {k : ℕ} (hk : 0 < k) (i l : Fin k) :
    linColB hk i (unitVec l) =
      (if ix hk (i.val + k - 3) = l then 1 else 0) +
      (if ix hk (i.val + k - 1) = l then 1 else 0) +
      (if ix hk (i.val + 1) = l then 1 else 0) := rfl

lemma linRow_support {k : ℕ} (hk : 0 < k) (hk11 : 11 ≤ k) (i l : Fin k) :
    (linRowA hk i (unitVec l) ≠ 0 →
      ∃ d : ℕ, d ≤ 2 ∧ l = ix hk ((ix hk (i.val + k - 1)).val + d)) ∧
    (linRowB hk i (unitVec l) ≠ 0 →
      ∃ d : ℕ, 1 ≤ d ∧ d ≤ 3 ∧ l = ix hk ((ix hk (i.val + k - 1)).val + d)) := by
  have hbase : ∀ d : ℕ, ix hk ((ix hk (i.val + k - 1)).val + d) = ix hk (i.val + k - 1 + d) :=
    fun d => ix_mod_left hk (i.val + k - 1) d
  have h0 : ix hk ((ix hk (i.val + k - 1)).val + 0) = ix hk (i.val + k - 1) := by
    rw [hbase, Nat.add_zero]
  have h1 : ix hk ((ix hk (i.val + k - 1)).val + 1) = i := ix_add_sub_cancel hk i 1 (by omega)
  have h2 : ix hk ((ix hk (i.val + k - 1)).val + 2) = ix hk (i.val + 1) := by
    rw [hbase, show i.val + k - 1 + 2 = (i.val + 1) + k by omega, ix_add_k]
  have h3 : ix hk ((ix hk (i.val + k - 1)).val + 3) = ix hk (i.val + 2) := by
    rw [hbase, show i.val + k - 1 + 3 = (i.val + 2) + k by omega, ix_add_k]
  constructor
  · intro hne
    rw [eval_linRowA_unit] at hne
    by_cases c0 : ix hk (i.val + k - 1) = l
    · exact ⟨0, by omega, by rw [h0, c0]⟩
    · by_cases c1 : i = l
      · exact ⟨1, by omega, by rw [h1, c1]⟩
      · by_cases c2 : ix hk (i.val + 1) = l
        · exact ⟨2, by omega, by rw [h2, c2]⟩
        · simp [c0, c1, c2] at hne
  · intro hne
    rw [eval_linRowB_unit] at hne
    by_cases c1 : i = l
    · exact ⟨1, by omega, by omega, by rw [h1, c1]⟩
    · by_cases c2 : ix hk (i.val + 1) = l
      · exact ⟨2, by omega, by omega, by rw [h2, c2]⟩
      · by_cases c3 : ix hk (i.val + 2) = l
        · exact ⟨3, by omega, by omega, by rw [h3, c3]⟩
        · simp [c1, c2, c3] at hne

lemma linCol_support {k : ℕ} (hk : 0 < k) (hk11 : 11 ≤ k) (i l : Fin k) :
    (linColA hk i (unitVec l) ≠ 0 →
      ∃ d : ℕ, d ≤ 4 ∧ l = ix hk ((ix hk (i.val + k - 4)).val + d)) ∧
    (linColB hk i (unitVec l) ≠ 0 →
      ∃ d : ℕ, 1 ≤ d ∧ d ≤ 5 ∧ l = ix hk ((ix hk (i.val + k - 4)).val + d)) := by
  have hbase : ∀ d : ℕ, ix hk ((ix hk (i.val + k - 4)).val + d) = ix hk (i.val + k - 4 + d) :=
    fun d => ix_mod_left hk (i.val + k - 4) d
  have h0 : ix hk ((ix hk (i.val + k - 4)).val + 0) = ix hk (i.val + k - 4) := by
    rw [hbase, Nat.add_zero]
  have h1 : ix hk ((ix hk (i.val + k - 4)).val + 1) = ix hk (i.val + k - 3) := by
    rw [hbase, show i.val + k - 4 + 1 = i.val + k - 3 by omega]
  have h2 : ix hk ((ix hk (i.val + k - 4)).val + 2) = ix hk (i.val + k - 2) := by
    rw [hbase, show i.val + k - 4 + 2 = i.val + k - 2 by omega]
  have h3 : ix hk ((ix hk (i.val + k - 4)).val + 3) = ix hk (i.val + k - 1) := by
    rw [hbase, show i.val + k - 4 + 3 = i.val + k - 1 by omega]
  have h4 : ix hk ((ix hk (i.val + k - 4)).val + 4) = i := ix_add_sub_cancel hk i 4 (by omega)
  have h5 : ix hk ((ix hk (i.val + k - 4)).val + 5) = ix hk (i.val + 1) := by
    rw [hbase, show i.val + k - 4 + 5 = (i.val + 1) + k by omega, ix_add_k]
  constructor
  · intro hne
    rw [eval_linColA_unit] at hne
    by_cases c0 : ix hk (i.val + k - 4) = l
    · exact ⟨0, by omega, by rw [h0, c0]⟩
    · by_cases c2 : ix hk (i.val + k - 2) = l
      · exact ⟨2, by omega, by rw [h2, c2]⟩
      · by_cases c4 : i = l
        · exact ⟨4, by omega, by rw [h4, c4]⟩
        · simp [c0, c2, c4] at hne
  · intro hne
    rw [eval_linColB_unit] at hne
    by_cases c1 : ix hk (i.val + k - 3) = l
    · exact ⟨1, by omega, by omega, by rw [h1, c1]⟩
    · by_cases c3 : ix hk (i.val + k - 1) = l
      · exact ⟨3, by omega, by omega, by rw [h3, c3]⟩
      · by_cases c5 : ix hk (i.val + 1) = l
        · exact ⟨5, by omega, by omega, by rw [h5, c5]⟩
        · simp [c1, c3, c5] at hne

def ProwTerm {k : ℕ} (hk : 0 < k) (i : Fin k) : Matrix (Fin k) (Fin k) (ZMod 2) :=
  Matrix.of fun l r =>
    linRowA hk i (unitVec l) * linRowB hk i (unitVec r) +
      linRowA hk i (unitVec r) * linRowB hk i (unitVec l)

def PcolTerm {k : ℕ} (hk : 0 < k) (i : Fin k) : Matrix (Fin k) (Fin k) (ZMod 2) :=
  Matrix.of fun l r =>
    linColA hk i (unitVec l) * linColB hk i (unitVec r) +
      linColA hk i (unitVec r) * linColB hk i (unitVec l)

lemma ProwTerm_band {k : ℕ} (hk : 0 < k) (hk11 : 11 ≤ k) (i l r : Fin k)
    (h1 : 3 < distMod l r) (h2 : 3 < distMod r l) :
    ProwTerm hk i l r = 0 := by
  simp only [ProwTerm, Matrix.of_apply]
  have ht1 : linRowA hk i (unitVec l) * linRowB hk i (unitVec r) = 0 := by
    by_contra hne
    have hA : linRowA hk i (unitVec l) ≠ 0 := left_ne_zero_of_mul hne
    have hB : linRowB hk i (unitVec r) ≠ 0 := right_ne_zero_of_mul hne
    rcases (linRow_support hk hk11 i l).1 hA with ⟨da, hda, rfl⟩
    rcases (linRow_support hk hk11 i r).2 hB with ⟨db, _, hdb, rfl⟩
    rcases arc_distMod_le hk (by omega : 3 < k) (ix hk (i.val + k - 1)) da db
      (by omega) (by omega) with hle | hle <;> omega
  have ht2 : linRowA hk i (unitVec r) * linRowB hk i (unitVec l) = 0 := by
    by_contra hne
    have hA : linRowA hk i (unitVec r) ≠ 0 := left_ne_zero_of_mul hne
    have hB : linRowB hk i (unitVec l) ≠ 0 := right_ne_zero_of_mul hne
    rcases (linRow_support hk hk11 i r).1 hA with ⟨da, hda, rfl⟩
    rcases (linRow_support hk hk11 i l).2 hB with ⟨db, _, hdb, rfl⟩
    rcases arc_distMod_le hk (by omega : 3 < k) (ix hk (i.val + k - 1)) da db
      (by omega) (by omega) with hle | hle <;> omega
  rw [ht1, ht2, add_zero]

lemma PcolTerm_band {k : ℕ} (hk : 0 < k) (hk11 : 11 ≤ k) (i l r : Fin k)
    (h1 : 5 < distMod l r) (h2 : 5 < distMod r l) :
    PcolTerm hk i l r = 0 := by
  simp only [PcolTerm, Matrix.of_apply]
  have ht1 : linColA hk i (unitVec l) * linColB hk i (unitVec r) = 0 := by
    by_contra hne
    have hA : linColA hk i (unitVec l) ≠ 0 := left_ne_zero_of_mul hne
    have hB : linColB hk i (unitVec r) ≠ 0 := right_ne_zero_of_mul hne
    rcases (linCol_support hk hk11 i l).1 hA with ⟨da, hda, rfl⟩
    rcases (linCol_support hk hk11 i r).2 hB with ⟨db, _, hdb, rfl⟩
    rcases arc_distMod_le hk (by omega : 5 < k) (ix hk (i.val + k - 4)) da db
      (by omega) (by omega) with hle | hle <;> omega
  have ht2 : linColA hk i (unitVec r) * linColB hk i (unitVec l) = 0 := by
    by_contra hne
    have hA : linColA hk i (unitVec r) ≠ 0 := left_ne_zero_of_mul hne
    have hB : linColB hk i (unitVec l) ≠ 0 := right_ne_zero_of_mul hne
    rcases (linCol_support hk hk11 i r).1 hA with ⟨da, hda, rfl⟩
    rcases (linCol_support hk hk11 i l).2 hB with ⟨db, _, hdb, rfl⟩
    rcases arc_distMod_le hk (by omega : 5 < k) (ix hk (i.val + k - 4)) da db
      (by omega) (by omega) with hle | hle <;> omega
  rw [ht1, ht2, add_zero]

lemma ProwTerm_outer {k : ℕ} (hk : 0 < k) (hk11 : 11 ≤ k) (i i' : Fin k) :
    ProwTerm hk i' (ix hk (i.val + (k - 1))) (ix hk (i.val + (k - 1) + 3)) =
      if i' = i then 1 else 0 := by
  let l := ix hk (i.val + (k - 1))
  let r := ix hk (i.val + (k - 1) + 3)
  have hl_eq : l = ix hk (i.val + k - 1) := by
    simp only [l]; congr 1; omega
  have hr_eq : r = ix hk (i.val + 2) := by
    simp only [r]
    rw [show i.val + (k - 1) + 3 = (i.val + 2) + k by omega, ix_add_k]
  have hdist : distMod l r = 3 := by
    have h1 : r = ix hk (l.val + 3) := by
      simp only [l, r]
      exact (ix_val_add hk (i.val + (k - 1)) 3).symm
    rw [h1]
    exact distMod_ix_shift hk l 3 (by omega)
  change ProwTerm hk i' l r = if i' = i then 1 else 0
  split_ifs with hii'
  · subst i'
    rw [hl_eq, hr_eq]
    simp only [ProwTerm, Matrix.of_apply, eval_linRowA_unit, eval_linRowB_unit]
    have hne01 : ix hk (i.val + k - 1) ≠ i := by
      intro h
      have := distMod_ix_shift hk (ix hk (i.val + k - 1)) 1 (by omega)
      rw [ix_add_sub_cancel hk i 1 (by omega), h] at this
      simp [distMod] at this
    have hne02 : ix hk (i.val + k - 1) ≠ ix hk (i.val + 1) := by
      intro h
      have hsub := distMod_ix_add hk (ix hk (i.val + k - 1)) 0 2 hk (by omega)
      have h0 : ix hk ((ix hk (i.val + k - 1)).val + 0) = ix hk (i.val + k - 1) := by
        simp [ix_self]
      have h2 : ix hk ((ix hk (i.val + k - 1)).val + 2) = ix hk (i.val + 1) := by
        rw [ix_val_add, show i.val + k - 1 + 2 = (i.val + 1) + k by omega, ix_add_k]
      rw [h0, h2, h] at hsub
      simp [distMod] at hsub
    have hne03 : ix hk (i.val + k - 1) ≠ ix hk (i.val + 2) := by
      intro h
      rw [hl_eq, hr_eq, h] at hdist
      simp [distMod] at hdist
    have hne13 : i ≠ ix hk (i.val + 2) := by
      intro h
      have := distMod_ix_shift hk i 2 (by omega)
      rw [← h] at this
      simp [distMod] at this
    have hne23 : ix hk (i.val + 1) ≠ ix hk (i.val + 2) := by
      intro h
      have := distMod_ix_add hk i 1 2 (by omega) (by omega)
      rw [h] at this
      simp [distMod] at this
    simp only [hne01.symm, hne02.symm, hne03, hne03.symm, hne13, hne23, ↓reduceIte]
    decide
  · simp only [ProwTerm, Matrix.of_apply]
    have ht1 : linRowA hk i' (unitVec l) * linRowB hk i' (unitVec r) = 0 := by
      by_contra hne
      rcases (linRow_support hk hk11 i' l).1 (left_ne_zero_of_mul hne) with ⟨da, hda, hla⟩
      rcases (linRow_support hk hk11 i' r).2 (right_ne_zero_of_mul hne) with ⟨db, _, hdb, hrb⟩
      rw [hla, hrb] at hdist
      have ⟨ha0, _⟩ := arc_distMod_eq_R hk (by omega : 2 * 3 < k)
        (ix hk (i'.val + k - 1)) da db (by omega) (by omega) hdist
      subst ha0
      simp only [Nat.add_zero, ix_self] at hla
      have hleq : ix hk (i'.val + (k - 1)) = ix hk (i.val + (k - 1)) := by
        have : ix hk (i'.val + (k - 1)) = ix hk (i'.val + k - 1) := by congr 1; omega
        rw [this, ← hla]
      exact hii' (ix_add_inj hk (k - 1) hleq)
    have ht2 : linRowA hk i' (unitVec r) * linRowB hk i' (unitVec l) = 0 := by
      by_contra hne
      rcases (linRow_support hk hk11 i' r).1 (left_ne_zero_of_mul hne) with ⟨da, hda, hra⟩
      rcases (linRow_support hk hk11 i' l).2 (right_ne_zero_of_mul hne) with ⟨db, hdb1, hdb, hlb⟩
      rw [hlb, hra] at hdist
      have ⟨hb0, _⟩ := arc_distMod_eq_R hk (by omega : 2 * 3 < k)
        (ix hk (i'.val + k - 1)) db da (by omega) (by omega) hdist
      omega
    rw [ht1, ht2, add_zero]

lemma PcolTerm_outer {k : ℕ} (hk : 0 < k) (hk11 : 11 ≤ k) (i i' : Fin k) :
    PcolTerm hk i' (ix hk (i.val + (k - 4))) (ix hk (i.val + (k - 4) + 5)) =
      if i' = i then 1 else 0 := by
  let l := ix hk (i.val + (k - 4))
  let r := ix hk (i.val + (k - 4) + 5)
  have hl_eq : l = ix hk (i.val + k - 4) := by
    simp only [l]; congr 1; omega
  have hr_eq : r = ix hk (i.val + 1) := by
    simp only [r]
    rw [show i.val + (k - 4) + 5 = (i.val + 1) + k by omega, ix_add_k]
  have hdist : distMod l r = 5 := by
    have h1 : r = ix hk (l.val + 5) := by
      simp only [l, r]
      exact (ix_val_add hk (i.val + (k - 4)) 5).symm
    rw [h1]
    exact distMod_ix_shift hk l 5 (by omega)
  change PcolTerm hk i' l r = if i' = i then 1 else 0
  split_ifs with hii'
  · subst i'
    rw [hl_eq, hr_eq]
    simp only [PcolTerm, Matrix.of_apply, eval_linColA_unit, eval_linColB_unit]
    let j0 := ix hk (i.val + k - 4)
    have hbase : ∀ d : ℕ, ix hk (j0.val + d) = ix hk (i.val + k - 4 + d) :=
      fun d => ix_val_add hk (i.val + k - 4) d
    have hp0 : ix hk (i.val + k - 4) = ix hk (j0.val + 0) := by simp [j0, ix_self]
    have hp1 : ix hk (i.val + k - 3) = ix hk (j0.val + 1) := by
      rw [hbase]; congr 1; omega
    have hp2 : ix hk (i.val + k - 2) = ix hk (j0.val + 2) := by
      rw [hbase]; congr 1; omega
    have hp3 : ix hk (i.val + k - 1) = ix hk (j0.val + 3) := by
      rw [hbase]; congr 1; omega
    have hp4 : i = ix hk (j0.val + 4) := (ix_add_sub_cancel hk i 4 (by omega)).symm
    have hp5 : ix hk (i.val + 1) = ix hk (j0.val + 5) := by
      rw [hbase, show i.val + k - 4 + 5 = (i.val + 1) + k by omega, ix_add_k]
    have hne : ∀ a b : ℕ, a < 6 → b < 6 → a ≠ b → ix hk (j0.val + a) ≠ ix hk (j0.val + b) := by
      intro a b ha hb hab heq
      have hdm := distMod_ix_add hk j0 a b (by omega) (by omega)
      rw [heq] at hdm
      simp only [distMod, Nat.add_sub_cancel_left, Nat.mod_self] at hdm
      split_ifs at hdm <;> omega
    rw [hp0, hp1, hp2, hp3, hp5, hp4]
    have c1 := hne 2 0 (by omega) (by omega) (by omega)
    have c2 := hne 4 0 (by omega) (by omega) (by omega)
    have c3 := hne 1 5 (by omega) (by omega) (by omega)
    have c4 := hne 3 5 (by omega) (by omega) (by omega)
    have c5 := hne 0 5 (by omega) (by omega) (by omega)
    have c6 := hne 2 5 (by omega) (by omega) (by omega)
    have c7 := hne 4 5 (by omega) (by omega) (by omega)
    have c8 := hne 1 0 (by omega) (by omega) (by omega)
    have c9 := hne 3 0 (by omega) (by omega) (by omega)
    have c10 := hne 5 0 (by omega) (by omega) (by omega)
    simp only [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, ↓reduceIte]
    decide
  · simp only [PcolTerm, Matrix.of_apply]
    have ht1 : linColA hk i' (unitVec l) * linColB hk i' (unitVec r) = 0 := by
      by_contra hne
      rcases (linCol_support hk hk11 i' l).1 (left_ne_zero_of_mul hne) with ⟨da, hda, hla⟩
      rcases (linCol_support hk hk11 i' r).2 (right_ne_zero_of_mul hne) with ⟨db, _, hdb, hrb⟩
      rw [hla, hrb] at hdist
      have ⟨ha0, _⟩ := arc_distMod_eq_R hk (by omega : 2 * 5 < k)
        (ix hk (i'.val + k - 4)) da db (by omega) (by omega) hdist
      subst ha0
      simp only [Nat.add_zero, ix_self] at hla
      have hleq : ix hk (i'.val + (k - 4)) = ix hk (i.val + (k - 4)) := by
        have : ix hk (i'.val + (k - 4)) = ix hk (i'.val + k - 4) := by congr 1; omega
        rw [this, ← hla]
      exact hii' (ix_add_inj hk (k - 4) hleq)
    have ht2 : linColA hk i' (unitVec r) * linColB hk i' (unitVec l) = 0 := by
      by_contra hne
      rcases (linCol_support hk hk11 i' r).1 (left_ne_zero_of_mul hne) with ⟨da, hda, hra⟩
      rcases (linCol_support hk hk11 i' l).2 (right_ne_zero_of_mul hne) with ⟨db, hdb1, hdb, hlb⟩
      rw [hlb, hra] at hdist
      have ⟨hb0, _⟩ := arc_distMod_eq_R hk (by omega : 2 * 5 < k)
        (ix hk (i'.val + k - 4)) db da (by omega) (by omega) hdist
      omega
    rw [ht1, ht2, add_zero]

lemma dotProduct_lin_prod {k : ℕ}
    (α β : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) (v w : Fin k → ZMod 2) :
    α v * β w + α w * β v =
      dotProduct v ((Matrix.of fun l r =>
        α (unitVec l) * β (unitVec r) + α (unitVec r) * β (unitVec l)).mulVec w) := by
  have hlin : ∀ (f : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) (x : Fin k → ZMod 2),
      f x = ∑ j : Fin k, x j * f (unitVec j) := by
    intro f x
    have hx : x = ∑ j : Fin k, x j • unitVec j := by
      ext j'
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unitVec]
      have hterm : ∀ j : Fin k, x j * (if j' = j then (1 : ZMod 2) else 0) =
          if j = j' then x j' else 0 := by
        intro j
        by_cases h : j = j'
        · subst h; simp
        · simp [Ne.symm h, h]
      simp_rw [hterm]
      simp
    conv_lhs => rw [hx, map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [hlin α v, hlin β w, hlin α w, hlin β v]
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  have hswap : (∑ r : Fin k, ∑ l : Fin k, w r * α (unitVec r) * (v l * β (unitVec l))) =
      ∑ l : Fin k, ∑ r : Fin k, v l * (α (unitVec r) * β (unitVec l) * w r) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro l _
    refine Finset.sum_congr rfl ?_
    intro r _
    ring
  rw [hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro r _
  ring

end PEqualNP.Outside.L_meta_25681_aux

open PEqualNP.Outside.L_meta_25681_aux in
theorem PEqualNP.Outside.L_meta_25681 :
    ∀ (k : ℕ) (hk : 0 < k), 11 ≤ k →
  let W := Fin k → ZMod 2
  let ix := fun pos : ℕ => (⟨pos % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (w : W) (j : Fin k) => w (ix (j.val+k-s%k))
  let run := fun (d s f : ℕ) (w name c : W) =>
    let z := rot s w + name
    let y := fun mid : Fin k => z mid + z (ix (mid.val+d)) + z (ix (mid.val+k-d%k))
    fun siteOut : Fin k => y siteOut + (1+y (ix (siteOut.val+1))) * y (ix (siteOut.val+2)) + rot f w siteOut + c siteOut
  ∀ (u v cr cc a b : W),
    let F := fun raw : W => dotProduct a (run 1 1 0 raw u cr) + dotProduct b (run 2 3 4 raw v cc)
    let unit := fun (j i : Fin k) => (if i = j then 1 else 0 : ZMod 2)
    let P : Matrix (Fin k) (Fin k) (ZMod 2) := fun left right =>
      F (unit left + unit right) + F (unit left) + F (unit right) + F 0
    let wt := fun mask : W => (Finset.univ.filter (fun index => mask index ≠ 0)).card
    let r := P.rank
    (k-10)*wt b ≤ k*r ∧ (k-6)*wt a ≤ k*(r+2*wt b) ∧
    ∀ (s : ℕ) (hs : s ≤ k) (L : (Fin s → ZMod 2) →ₗ[ZMod 2] W), Function.Injective L →
      ∀ (base : W) (ell : (Fin s → ZMod 2) →ₗ[ZMod 2] ZMod 2) (c : ZMod 2),
        let bias := ∑ x : Fin s → ZMod 2,
          (if F (base + L x) + ell x + c = 0 then (1 : ℤ) else -1)
        bias^2 * (2 : ℤ)^(r-2*(k-s)) ≤ (2 : ℤ)^(2*s) := by
  intro k hk hk11 W ix0 rot run u v cr cc a b F unit P wt r
  have hix0 : ix0 = PEqualNP.Outside.L_meta_25681_aux.ix hk := rfl
  have hunit : unit = unitVec := rfl
  let Prow : Matrix (Fin k) (Fin k) (ZMod 2) :=
    ∑ i : Fin k, a i • ProwTerm hk i
  let Pcol : Matrix (Fin k) (Fin k) (ZMod 2) :=
    ∑ i : Fin k, b i • PcolTerm hk i
  have hrow_y1 : ∀ (w : W) (i : Fin k),
      rot 1 w (ix0 (i.val + 1)) +
        rot 1 w (ix0 ((ix0 (i.val + 1)).val + 1)) +
        rot 1 w (ix0 ((ix0 (i.val + 1)).val + k - 1 % k)) =
      linRowA hk i w := by
    intro w i
    simp only [rot, hix0, linRowA, LinearMap.coe_mk, AddHom.coe_mk]
    have h1 : PEqualNP.Outside.L_meta_25681_aux.ix hk
        ((PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + 1)).val + k - 1 % k) = i := by
      rw [ix_add_sub hk i 1 1 (by omega), show i.val + 1 + k - 1 = i.val + k by omega,
        ix_add_k, ix_self]
    have h2 : PEqualNP.Outside.L_meta_25681_aux.ix hk
        ((PEqualNP.Outside.L_meta_25681_aux.ix hk
          ((PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + 1)).val + 1)).val + k - 1 % k) =
        PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + 1) := by
      rw [ix_shift_add hk i 1 1, ix_add_sub hk i 2 1 (by omega),
        show i.val + 2 + k - 1 = (i.val + 1) + k by omega, ix_add_k]
    have h3 : PEqualNP.Outside.L_meta_25681_aux.ix hk
        ((PEqualNP.Outside.L_meta_25681_aux.ix hk
          ((PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + 1)).val + k - 1 % k)).val +
            k - 1 % k) =
        PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + k - 1) := by
      rw [h1, Nat.mod_eq_of_lt (by omega : 1 < k)]
    rw [h3, h2, h1]
    ring
  have hrow_y2 : ∀ (w : W) (i : Fin k),
      rot 1 w (ix0 (i.val + 2)) +
        rot 1 w (ix0 ((ix0 (i.val + 2)).val + 1)) +
        rot 1 w (ix0 ((ix0 (i.val + 2)).val + k - 1 % k)) =
      linRowB hk i w := by
    intro w i
    simp only [rot, hix0, linRowB, LinearMap.coe_mk, AddHom.coe_mk]
    have h1 : PEqualNP.Outside.L_meta_25681_aux.ix hk
        ((PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + 2)).val + k - 1 % k) =
        PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + 1) := by
      rw [ix_add_sub hk i 2 1 (by omega), show i.val + 2 + k - 1 = (i.val + 1) + k by omega,
        ix_add_k]
    have h2 : PEqualNP.Outside.L_meta_25681_aux.ix hk
        ((PEqualNP.Outside.L_meta_25681_aux.ix hk
          ((PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + 2)).val + 1)).val + k - 1 % k) =
        PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + 2) := by
      rw [ix_shift_add hk i 2 1, ix_add_sub hk i 3 1 (by omega),
        show i.val + 3 + k - 1 = (i.val + 2) + k by omega, ix_add_k]
    have h3 : PEqualNP.Outside.L_meta_25681_aux.ix hk
        ((PEqualNP.Outside.L_meta_25681_aux.ix hk
          ((PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + 2)).val + k - 1 % k)).val +
            k - 1 % k) = i := by
      rw [h1, ix_add_sub hk i 1 1 (by omega), show i.val + 1 + k - 1 = i.val + k by omega,
        ix_add_k, ix_self]
    rw [h3, h2, h1]
    ring
  have hcol_y1 : ∀ (w : W) (i : Fin k),
      rot 3 w (ix0 (i.val + 1)) +
        rot 3 w (ix0 ((ix0 (i.val + 1)).val + 2)) +
        rot 3 w (ix0 ((ix0 (i.val + 1)).val + k - 2 % k)) =
      linColA hk i w := by
    intro w i
    simp only [rot, hix0, linColA, LinearMap.coe_mk, AddHom.coe_mk]
    have h1 : PEqualNP.Outside.L_meta_25681_aux.ix hk
        ((PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + 1)).val + k - 3 % k) =
        PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + k - 2) := by
      rw [ix_add_sub hk i 1 3 (by omega)]
      congr 1; omega
    have h2 : PEqualNP.Outside.L_meta_25681_aux.ix hk
        ((PEqualNP.Outside.L_meta_25681_aux.ix hk
          ((PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + 1)).val + 2)).val + k - 3 % k) = i := by
      rw [ix_shift_add hk i 1 2, ix_add_sub hk i 3 3 (by omega),
        show i.val + 3 + k - 3 = i.val + k by omega, ix_add_k, ix_self]
    have h3 : PEqualNP.Outside.L_meta_25681_aux.ix hk
        ((PEqualNP.Outside.L_meta_25681_aux.ix hk
          ((PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + 1)).val + k - 2 % k)).val +
            k - 3 % k) =
        PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + k - 4) := by
      rw [ix_add_sub hk i 1 2 (by omega), show i.val + 1 + k - 2 = i.val + (k - 1) by omega,
        ix_add_sub hk i (k - 1) 3 (by omega),
        show i.val + (k - 1) + k - 3 = (i.val + k - 4) + k by omega, ix_add_k]
    rw [h1, h2, h3]
    ring
  have hcol_y2 : ∀ (w : W) (i : Fin k),
      rot 3 w (ix0 (i.val + 2)) +
        rot 3 w (ix0 ((ix0 (i.val + 2)).val + 2)) +
        rot 3 w (ix0 ((ix0 (i.val + 2)).val + k - 2 % k)) =
      linColB hk i w := by
    intro w i
    simp only [rot, hix0, linColB, LinearMap.coe_mk, AddHom.coe_mk]
    have h1 : PEqualNP.Outside.L_meta_25681_aux.ix hk
        ((PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + 2)).val + k - 3 % k) =
        PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + k - 1) := by
      rw [ix_add_sub hk i 2 3 (by omega)]
      congr 1; omega
    have h2 : PEqualNP.Outside.L_meta_25681_aux.ix hk
        ((PEqualNP.Outside.L_meta_25681_aux.ix hk
          ((PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + 2)).val + 2)).val + k - 3 % k) =
        PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + 1) := by
      rw [ix_shift_add hk i 2 2, ix_add_sub hk i 4 3 (by omega),
        show i.val + 4 + k - 3 = (i.val + 1) + k by omega, ix_add_k]
    have h3 : PEqualNP.Outside.L_meta_25681_aux.ix hk
        ((PEqualNP.Outside.L_meta_25681_aux.ix hk
          ((PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + 2)).val + k - 2 % k)).val +
            k - 3 % k) =
        PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + k - 3) := by
      rw [ix_add_sub hk i 2 2 (by omega), show i.val + 2 + k - 2 = i.val + k by omega,
        ix_add_k, ix_self, Nat.mod_eq_of_lt (by omega : 3 < k)]
    rw [h1, h2, h3]
    ring
  have hpolar_row_site : ∀ (i : Fin k) (x y z : W),
      run 1 1 0 (x + y + z) u cr i + run 1 1 0 (x + y) u cr i +
        run 1 1 0 (x + z) u cr i + run 1 1 0 x u cr i =
      linRowA hk i y * linRowB hk i z + linRowA hk i z * linRowB hk i y := by
    intro i x y z
    let c1 : ZMod 2 :=
      1 + (u (ix0 (i.val + 1)) + u (ix0 ((ix0 (i.val + 1)).val + 1)) +
        u (ix0 ((ix0 (i.val + 1)).val + k - 1 % k)))
    let c2 : ZMod 2 :=
      u (ix0 (i.val + 2)) + u (ix0 ((ix0 (i.val + 2)).val + 1)) +
        u (ix0 ((ix0 (i.val + 2)).val + k - 1 % k))
    let c0 : ZMod 2 :=
      u i + u (ix0 (i.val + 1)) + u (ix0 (i.val + k - 1 % k)) + cr i
    let ℓ : W →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun w =>
          rot 1 w i + rot 1 w (ix0 (i.val + 1)) + rot 1 w (ix0 (i.val + k - 1 % k)) + rot 0 w i
        map_add' := fun w1 w2 => by simp only [rot, W, Pi.add_apply]; ring
        map_smul' := fun s w => by simp only [rot, W, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
    have hrun_eq : ∀ w : W,
        run 1 1 0 w u cr i = (ℓ w + c0) + (linRowA hk i w + c1) * (linRowB hk i w + c2) := by
      intro w
      simp only [run, ℓ, LinearMap.coe_mk, AddHom.coe_mk, c0, c1, c2]
      dsimp only [W]
      simp only [Pi.add_apply]
      rw [← hrow_y1 w i, ← hrow_y2 w i]
      ring
    simp_rw [hrun_eq]
    have hlin := polar_of_linear ℓ c0 x y z
    have hquad := polar_of_affine_prod (linRowA hk i) (linRowB hk i) c1 c2 x y z
    dsimp only at hlin hquad
    calc
      (ℓ (x + y + z) + c0) + (linRowA hk i (x + y + z) + c1) * (linRowB hk i (x + y + z) + c2) +
          ((ℓ (x + y) + c0) + (linRowA hk i (x + y) + c1) * (linRowB hk i (x + y) + c2)) +
          ((ℓ (x + z) + c0) + (linRowA hk i (x + z) + c1) * (linRowB hk i (x + z) + c2)) +
          ((ℓ x + c0) + (linRowA hk i x + c1) * (linRowB hk i x + c2))
          = ((ℓ (x + y + z) + c0) + (ℓ (x + y) + c0) + (ℓ (x + z) + c0) + (ℓ x + c0)) +
            ((linRowA hk i (x + y + z) + c1) * (linRowB hk i (x + y + z) + c2) +
              (linRowA hk i (x + y) + c1) * (linRowB hk i (x + y) + c2) +
              (linRowA hk i (x + z) + c1) * (linRowB hk i (x + z) + c2) +
              (linRowA hk i x + c1) * (linRowB hk i x + c2)) := by ring
      _ = 0 + (linRowA hk i y * linRowB hk i z + linRowA hk i z * linRowB hk i y) := by
        rw [hlin, hquad]
      _ = linRowA hk i y * linRowB hk i z + linRowA hk i z * linRowB hk i y := by rw [zero_add]
  have hpolar_col_site : ∀ (i : Fin k) (x y z : W),
      run 2 3 4 (x + y + z) v cc i + run 2 3 4 (x + y) v cc i +
        run 2 3 4 (x + z) v cc i + run 2 3 4 x v cc i =
      linColA hk i y * linColB hk i z + linColA hk i z * linColB hk i y := by
    intro i x y z
    let c1 : ZMod 2 :=
      1 + (v (ix0 (i.val + 1)) + v (ix0 ((ix0 (i.val + 1)).val + 2)) +
        v (ix0 ((ix0 (i.val + 1)).val + k - 2 % k)))
    let c2 : ZMod 2 :=
      v (ix0 (i.val + 2)) + v (ix0 ((ix0 (i.val + 2)).val + 2)) +
        v (ix0 ((ix0 (i.val + 2)).val + k - 2 % k))
    let c0 : ZMod 2 :=
      v i + v (ix0 (i.val + 2)) + v (ix0 (i.val + k - 2 % k)) + cc i
    let ℓ : W →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun w =>
          rot 3 w i + rot 3 w (ix0 (i.val + 2)) + rot 3 w (ix0 (i.val + k - 2 % k)) + rot 4 w i
        map_add' := fun w1 w2 => by simp only [rot, W, Pi.add_apply]; ring
        map_smul' := fun s w => by simp only [rot, W, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
    have hrun_eq : ∀ w : W,
        run 2 3 4 w v cc i = (ℓ w + c0) + (linColA hk i w + c1) * (linColB hk i w + c2) := by
      intro w
      simp only [run, ℓ, LinearMap.coe_mk, AddHom.coe_mk, c0, c1, c2]
      dsimp only [W]
      simp only [Pi.add_apply]
      rw [← hcol_y1 w i, ← hcol_y2 w i]
      ring
    simp_rw [hrun_eq]
    have hlin := polar_of_linear ℓ c0 x y z
    have hquad := polar_of_affine_prod (linColA hk i) (linColB hk i) c1 c2 x y z
    dsimp only at hlin hquad
    calc
      (ℓ (x + y + z) + c0) + (linColA hk i (x + y + z) + c1) * (linColB hk i (x + y + z) + c2) +
          ((ℓ (x + y) + c0) + (linColA hk i (x + y) + c1) * (linColB hk i (x + y) + c2)) +
          ((ℓ (x + z) + c0) + (linColA hk i (x + z) + c1) * (linColB hk i (x + z) + c2)) +
          ((ℓ x + c0) + (linColA hk i x + c1) * (linColB hk i x + c2))
          = ((ℓ (x + y + z) + c0) + (ℓ (x + y) + c0) + (ℓ (x + z) + c0) + (ℓ x + c0)) +
            ((linColA hk i (x + y + z) + c1) * (linColB hk i (x + y + z) + c2) +
              (linColA hk i (x + y) + c1) * (linColB hk i (x + y) + c2) +
              (linColA hk i (x + z) + c1) * (linColB hk i (x + z) + c2) +
              (linColA hk i x + c1) * (linColB hk i x + c2)) := by ring
      _ = 0 + (linColA hk i y * linColB hk i z + linColA hk i z * linColB hk i y) := by
        rw [hlin, hquad]
      _ = linColA hk i y * linColB hk i z + linColA hk i z * linColB hk i y := by rw [zero_add]
  have hpolar_F : ∀ x y z : W,
      F (x + y + z) + F (x + y) + F (x + z) + F x =
        dotProduct y ((Prow + Pcol).mulVec z) := by
    intro x y z
    have hsplit :
        F (x + y + z) + F (x + y) + F (x + z) + F x =
          (∑ i : Fin k, a i *
            (run 1 1 0 (x + y + z) u cr i + run 1 1 0 (x + y) u cr i +
              run 1 1 0 (x + z) u cr i + run 1 1 0 x u cr i)) +
          (∑ i : Fin k, b i *
            (run 2 3 4 (x + y + z) v cc i + run 2 3 4 (x + y) v cc i +
              run 2 3 4 (x + z) v cc i + run 2 3 4 x v cc i)) := by
      simp only [F, dotProduct]
      simp_rw [mul_add, Finset.sum_add_distrib]
      ring
    rw [hsplit]
    simp_rw [hpolar_row_site, hpolar_col_site]
    have hrow_dot :
        (∑ i : Fin k, a i * (linRowA hk i y * linRowB hk i z + linRowA hk i z * linRowB hk i y)) =
          dotProduct y (Prow.mulVec z) := by
      have hterm : ∀ i : Fin k,
          a i * (linRowA hk i y * linRowB hk i z + linRowA hk i z * linRowB hk i y) =
            dotProduct y ((a i • ProwTerm hk i).mulVec z) := by
        intro i
        rw [dotProduct_lin_prod (linRowA hk i) (linRowB hk i) y z]
        change a i * dotProduct y ((ProwTerm hk i).mulVec z) =
          dotProduct y ((a i • ProwTerm hk i).mulVec z)
        rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      simp_rw [hterm]
      simp only [Prow, Matrix.sum_mulVec, dotProduct_sum]
    have hcol_dot :
        (∑ i : Fin k, b i * (linColA hk i y * linColB hk i z + linColA hk i z * linColB hk i y)) =
          dotProduct y (Pcol.mulVec z) := by
      have hterm : ∀ i : Fin k,
          b i * (linColA hk i y * linColB hk i z + linColA hk i z * linColB hk i y) =
            dotProduct y ((b i • PcolTerm hk i).mulVec z) := by
        intro i
        rw [dotProduct_lin_prod (linColA hk i) (linColB hk i) y z]
        change b i * dotProduct y ((PcolTerm hk i).mulVec z) =
          dotProduct y ((b i • PcolTerm hk i).mulVec z)
        rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      simp_rw [hterm]
      simp only [Pcol, Matrix.sum_mulVec, dotProduct_sum]
    rw [hrow_dot, hcol_dot, Matrix.add_mulVec, dotProduct_add]
  have hP_eq : P = Prow + Pcol := by
    ext l r
    have h0 := hpolar_F 0 (unitVec l) (unitVec r)
    simp only [zero_add] at h0
    have hdot : dotProduct (unitVec l) ((Prow + Pcol).mulVec (unitVec r)) = (Prow + Pcol) l r := by
      simp only [dotProduct, Matrix.mulVec, unitVec]
      have h1 : ∀ i : Fin k,
          (if i = l then (1 : ZMod 2) else 0) *
            ∑ j : Fin k, (Prow + Pcol) i j * (if j = r then 1 else 0) =
          if i = l then (Prow + Pcol) l r else 0 := by
        intro i
        by_cases hil : i = l
        · subst hil
          simp only [↓reduceIte, one_mul]
          have h2 : ∀ j : Fin k, (Prow + Pcol) i j * (if j = r then (1 : ZMod 2) else 0) =
              if j = r then (Prow + Pcol) i r else 0 := by
            intro j
            split_ifs with hjr
            · subst hjr; simp
            · simp
          simp_rw [h2]
          simp
        · simp [hil]
      simp_rw [h1]
      simp
    rw [hdot] at h0
    exact h0
  have hpart1 : (k - 10) * (Finset.univ.filter (fun index => b index ≠ 0)).card ≤ k * P.rank := by
    have hband : ∀ l r : Fin k, 5 < distMod l r → 5 < distMod r l → P l r = 0 := by
      intro l r h1 h2
      rw [hP_eq, Matrix.add_apply]
      have hr0 : Prow l r = 0 := by
        simp only [Prow, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [ProwTerm_band hk hk11 i l r (by omega) (by omega), mul_zero]
      have hc0 : Pcol l r = 0 := by
        simp only [Pcol, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [PcolTerm_band hk hk11 i l r h1 h2, mul_zero]
      rw [hr0, hc0, add_zero]
    have hdiag : ∀ i : Fin k,
        P (PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + (k - 4)))
          (PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + (k - 4) + 5)) = b i := by
      intro i
      rw [hP_eq, Matrix.add_apply]
      let l := PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + (k - 4))
      let r := PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + (k - 4) + 5)
      have hdlr : distMod l r = 5 := by
        have h1 : r = PEqualNP.Outside.L_meta_25681_aux.ix hk (l.val + 5) := by
          simp only [l, r]
          exact (ix_val_add hk (i.val + (k - 4)) 5).symm
        rw [h1]
        exact distMod_ix_shift hk l 5 (by omega)
      have hdrl : distMod r l = k - 5 := by
        have h1 : l = PEqualNP.Outside.L_meta_25681_aux.ix hk (l.val + 0) := by simp [ix_self]
        have h2 : r = PEqualNP.Outside.L_meta_25681_aux.ix hk (l.val + 5) := by
          simp only [l, r]
          exact (ix_val_add hk (i.val + (k - 4)) 5).symm
        conv_lhs => rw [h2]; arg 2; rw [h1]
        rw [distMod_ix_add hk l 5 0 (by omega) hk]
        simp
      have hr0 : Prow l r = 0 := by
        simp only [Prow, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
        refine Finset.sum_eq_zero fun i' _ => ?_
        rw [ProwTerm_band hk hk11 i' l r (by omega) (by omega), mul_zero]
      have hc : Pcol l r = b i := by
        simp only [Pcol, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
        have hterm : ∀ i' : Fin k, b i' * PcolTerm hk i' l r = if i' = i then b i else 0 := by
          intro i'
          rw [PcolTerm_outer hk hk11 i i']
          split_ifs with h
          · subst h; ring
          · ring
        simp_rw [hterm]
        simp
      rw [hr0, hc, zero_add]
    exact cyclic_band_rank_bound hk (by omega : 2 * 5 < k) (k - 4) P b hband hdiag
  have hpart2 :
      (k - 6) * (Finset.univ.filter (fun index => a index ≠ 0)).card ≤
        k * (P.rank + 2 * (Finset.univ.filter (fun index => b index ≠ 0)).card) := by
    have hrow_rank : (k - 6) * (Finset.univ.filter (fun index => a index ≠ 0)).card ≤
        k * Prow.rank := by
      have hband : ∀ l r : Fin k, 3 < distMod l r → 3 < distMod r l → Prow l r = 0 := by
        intro l r h1 h2
        simp only [Prow, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [ProwTerm_band hk hk11 i l r h1 h2, mul_zero]
      have hdiag : ∀ i : Fin k,
          Prow (PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + (k - 1)))
            (PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + (k - 1) + 3)) = a i := by
        intro i
        simp only [Prow, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
        have hterm : ∀ i' : Fin k,
            a i' * ProwTerm hk i'
              (PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + (k - 1)))
              (PEqualNP.Outside.L_meta_25681_aux.ix hk (i.val + (k - 1) + 3)) =
            if i' = i then a i else 0 := by
          intro i'
          rw [ProwTerm_outer hk hk11 i i']
          split_ifs with h
          · subst h; ring
          · ring
        simp_rw [hterm]
        simp
      exact cyclic_band_rank_bound hk (by omega : 2 * 3 < k) (k - 1) Prow a hband hdiag
    have hProw_eq : Prow = P + Pcol := by
      rw [hP_eq]
      ext l r
      simp only [Matrix.add_apply]
      rw [add_assoc, zmod2_add_self, add_zero]
    have hcol_rank : Pcol.rank ≤ 2 * (Finset.univ.filter (fun index => b index ≠ 0)).card := by
      have hPcol_filt : Pcol =
          ∑ i ∈ Finset.univ.filter (fun index => b index ≠ 0), PcolTerm hk i := by
        simp only [Pcol]
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun index => b index ≠ 0)]
        have hzero : (∑ i ∈ Finset.univ.filter (fun index => ¬ b index ≠ 0),
            b i • PcolTerm hk i) = 0 := by
          refine Finset.sum_eq_zero fun i hi => ?_
          have hb0 : b i = 0 := not_not.mp (Finset.mem_filter.mp hi).2
          simp [hb0]
        rw [hzero, add_zero]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hb1 : b i = 1 := zmod2_eq_one_of_ne_zero (Finset.mem_filter.mp hi).2
        simp [hb1]
      rw [hPcol_filt]
      refine le_trans (matrix_rank_sum_le _ _) ?_
      calc
        ∑ i ∈ Finset.univ.filter (fun index => b index ≠ 0), (PcolTerm hk i).rank
            ≤ ∑ _i ∈ Finset.univ.filter (fun index => b index ≠ 0), 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hcomm : PcolTerm hk i = Matrix.of fun l r =>
              linColA hk i (unitVec l) * linColB hk i (unitVec r) +
                linColB hk i (unitVec l) * linColA hk i (unitVec r) := by
            ext l r
            simp only [PcolTerm, Matrix.of_apply]
            ring
          rw [hcomm]
          exact matrix_rank_sym_outer_le_two
            (fun l => linColA hk i (unitVec l)) (fun r => linColB hk i (unitVec r))
        _ = 2 * (Finset.univ.filter (fun index => b index ≠ 0)).card := by
          simp [Nat.mul_comm]
    have hProw_le : Prow.rank ≤
        P.rank + 2 * (Finset.univ.filter (fun index => b index ≠ 0)).card := by
      rw [hProw_eq]
      exact le_trans (matrix_rank_add_le P Pcol) (Nat.add_le_add_left hcol_rank _)
    exact le_trans hrow_rank (Nat.mul_le_mul_left k hProw_le)
  refine ⟨hpart1, hpart2, ?_⟩
  intro s hs L hL base ell c
  have hpolar_P : ∀ x y z : W,
      F (x + y + z) + F (x + y) + F (x + z) + F x = dotProduct y (P.mulVec z) := by
    intro x y z
    rw [hP_eq]
    exact hpolar_F x y z
  exact walsh_quadratic_bound hs F P hpolar_P L hL base ell c

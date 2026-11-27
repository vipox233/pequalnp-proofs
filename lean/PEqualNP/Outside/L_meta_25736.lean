import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25736_aux

private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  interval_cases v
  · left; rfl
  · right; rfl

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> decide

private lemma zmod2_mul_self (x : ZMod 2) : x * x = x := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> decide

private lemma zmod2_add_eq_zero (x y : ZMod 2) : x + y = 0 ↔ x = y := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;>
  rcases zmod2_eq_zero_or_one y with rfl | rfl <;> decide

private def ix {k : ℕ} (hk : 0 < k) (z : ℕ) : Fin k :=
  ⟨z % k, Nat.mod_lt z hk⟩

private lemma ix_add_mod {k : ℕ} (hk : 0 < k) (a b : ℕ) :
    ix hk ((ix hk a).val + b) = ix hk (a + b) := by
  ext
  simp [ix, Nat.mod_add_mod]

private lemma ix_self {k : ℕ} (hk : 0 < k) (i : Fin k) : ix hk i.val = i := by
  ext
  simp [ix, Nat.mod_eq_of_lt i.isLt]

private lemma ix_add_sub_cancel {k : ℕ} (hk : 0 < k) (i : Fin k) (q : ℕ) :
    ix hk ((ix hk (i.val + q)).val + k - q % k) = i := by
  ext
  dsimp only [ix]
  have h1 : (i.val + q) % k + k - q % k = (i.val + q) % k + (k - q % k) := by
    have := Nat.mod_lt q hk; omega
  rw [h1, Nat.mod_add_mod]
  have h2 : i.val + q + (k - q % k) = i.val + (q / k * k + k) := by
    have hdm := Nat.div_add_mod q k
    have hq : q = q / k * k + q % k := by rw [mul_comm]; exact hdm.symm
    have hlt := Nat.mod_lt q hk
    omega
  rw [h2]
  have h3 : q / k * k + k = (q / k + 1) * k := by ring
  rw [h3, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]

private lemma ix_sub_add_cancel {k : ℕ} (hk : 0 < k) (i : Fin k) (q : ℕ) :
    ix hk ((ix hk (i.val + k - q % k)).val + q) = i := by
  ext
  dsimp only [ix]
  rw [Nat.mod_add_mod]
  have hlt := Nat.mod_lt q hk
  have hdm := Nat.div_add_mod q k
  have h1 : i.val + k - q % k + q = i.val + (q / k + 1) * k := by
    have : q = q / k * k + q % k := by rw [mul_comm]; exact hdm.symm
    have : (q / k + 1) * k = q / k * k + k := by ring
    omega
  rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]

private def rotLin {k : ℕ} (hk : 0 < k) (q : ℕ) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun x i := x (ix hk (i.val + k - q % k))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma rotLin_bijective {k : ℕ} (hk : 0 < k) (q : ℕ) :
    Function.Bijective (rotLin hk q) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun y i => y (ix hk (i.val + q)), ?_, ?_⟩
  · intro x
    funext i
    dsimp only [rotLin, LinearMap.coe_mk, AddHom.coe_mk]
    rw [ix_add_sub_cancel hk i q]
  · intro y
    funext i
    dsimp only [rotLin, LinearMap.coe_mk, AddHom.coe_mk]
    rw [ix_sub_add_cancel hk i q]

private def mixLin {k : ℕ} (hk : 0 < k) (spacing : ℕ) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun z j := z j + z (ix hk (j.val + spacing)) + z (ix hk (j.val + k - spacing % k))
  map_add' z₁ z₂ := by
    funext j; dsimp only [Pi.add_apply]; ring
  map_smul' c z := by
    funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private lemma mixLin_injective {k : ℕ} (hk : 0 < k) (hk3 : k % 3 ≠ 0) (spacing : ℕ) :
    Function.Injective (mixLin hk spacing) := by
  have hker : ∀ z : Fin k → ZMod 2, mixLin hk spacing z = 0 → z = 0 := by
    intro z hz
    have heq : ∀ j : Fin k,
        z j + z (ix hk (j.val + spacing)) + z (ix hk (j.val + k - spacing % k)) = 0 :=
      fun j => congrFun hz j
    have hstep3 : ∀ j : Fin k, z (ix hk (j.val + 3 * spacing)) = z j := by
      intro j
      have h1 := heq (ix hk (j.val + spacing))
      have h2 := heq (ix hk (j.val + 2 * spacing))
      have ha1 : ix hk ((ix hk (j.val + spacing)).val + spacing) = ix hk (j.val + 2 * spacing) := by
        rw [ix_add_mod]; congr 1; ring
      have hb1 : ix hk ((ix hk (j.val + spacing)).val + k - spacing % k) = j :=
        ix_add_sub_cancel hk j spacing
      have ha2 : ix hk ((ix hk (j.val + 2 * spacing)).val + spacing) = ix hk (j.val + 3 * spacing) := by
        rw [ix_add_mod]; congr 1; ring
      have hb2 : ix hk ((ix hk (j.val + 2 * spacing)).val + k - spacing % k) = ix hk (j.val + spacing) := by
        have hrew : ix hk (j.val + 2 * spacing) = ix hk ((ix hk (j.val + spacing)).val + spacing) := ha1.symm
        rw [hrew, ix_add_sub_cancel]
      rw [ha1, hb1] at h1
      rw [ha2, hb2] at h2
      generalize z j = a at h1 ⊢
      generalize z (ix hk (j.val + spacing)) = b at h1 h2
      generalize z (ix hk (j.val + 2 * spacing)) = c at h1 h2
      generalize z (ix hk (j.val + 3 * spacing)) = d at h2 ⊢
      rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
      rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
      rcases zmod2_eq_zero_or_one c with rfl | rfl <;>
      rcases zmod2_eq_zero_or_one d with rfl | rfl <;>
      first | rfl | exact absurd h1 (by decide) | exact absurd h2 (by decide)
    have hstep_mul : ∀ (m : ℕ) (j : Fin k), z (ix hk (j.val + 3 * m * spacing)) = z j := by
      intro m
      induction m with
      | zero => intro j; simpa using congrArg z (ix_self hk j)
      | succ m ih =>
        intro j
        have hrew : ix hk (j.val + 3 * (m + 1) * spacing) =
            ix hk ((ix hk (j.val + 3 * m * spacing)).val + 3 * spacing) := by
          rw [ix_add_mod]; congr 1; ring
        rw [hrew, hstep3, ih]
    have hex_m : ∃ m : ℕ, (3 * m) % k = 1 % k := by
      have hmod3 : k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases hmod3 with h1 | h2
      · refine ⟨2 * (k / 3) + 1, ?_⟩
        have hk_eq : k = 3 * (k / 3) + 1 := by omega
        have h3m : 3 * (2 * (k / 3) + 1) = 1 + 2 * k := by omega
        rw [h3m, Nat.add_mul_mod_self_right]
      · refine ⟨k / 3 + 1, ?_⟩
        have hk_eq : k = 3 * (k / 3) + 2 := by omega
        have h3m : 3 * (k / 3 + 1) = 1 + 1 * k := by omega
        rw [h3m, Nat.add_mul_mod_self_right]
    rcases hex_m with ⟨m, hm⟩
    have hstep1 : ∀ j : Fin k, z (ix hk (j.val + spacing)) = z j := by
      intro j
      have h1 := hstep_mul m j
      have hidx : ix hk (j.val + 3 * m * spacing) = ix hk (j.val + spacing) := by
        ext
        dsimp only [ix]
        rw [Nat.add_mod, Nat.mul_mod, hm, ← Nat.mul_mod, one_mul, ← Nat.add_mod]
      rwa [hidx] at h1
    have hstep_neg : ∀ j : Fin k, z (ix hk (j.val + k - spacing % k)) = z j := by
      intro j
      have h1 := hstep1 (ix hk (j.val + k - spacing % k))
      rw [ix_sub_add_cancel hk j spacing] at h1
      exact h1.symm
    funext j
    have hj := heq j
    rw [hstep1 j, hstep_neg j] at hj
    have h2 := zmod2_add_self (z j)
    calc z j = z j + (z j + z j) := by rw [h2, add_zero]
      _ = z j + z j + z j := by ring
      _ = 0 := hj
  intro z₁ z₂ heq
  have hdiff : mixLin hk spacing (z₁ + z₂) = 0 := by
    rw [map_add, heq]
    funext j; exact zmod2_add_self _
  have hz := hker (z₁ + z₂) hdiff
  funext j
  exact (zmod2_add_eq_zero _ _).mp (congrFun hz j)

private lemma mixLin_bijective {k : ℕ} (hk : 0 < k) (hk3 : k % 3 ≠ 0) (spacing : ℕ) :
    Function.Bijective (mixLin hk spacing) :=
  Finite.injective_iff_bijective.mp (mixLin_injective hk hk3 spacing)

private lemma exists_pivot_basis {k : ℕ} :
    ∀ (d : ℕ) (ℓ : Fin d → ((Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2)),
      ∃ (B : Finset (Fin k)) (w : Fin k → (Fin k → ZMod 2)),
        k ≤ B.card + d ∧
        (∀ b ∈ B, ∀ j : Fin d, ℓ j (w b) = 0) ∧
        (∀ b ∈ B, ∀ b' ∈ B, w b b' = if b = b' then 1 else 0)
  | 0, _ => by
      refine ⟨Finset.univ, fun b i => if b = i then 1 else 0, by simp, fun _ _ j => Fin.elim0 j,
        fun _ _ _ _ => rfl⟩
  | d + 1, ℓ => by
      rcases exists_pivot_basis d (fun j => ℓ j.castSucc) with ⟨B, w, hcard, hker, hdiag⟩
      let f := ℓ (Fin.last d)
      by_cases hall : ∀ b ∈ B, f (w b) = 0
      · refine ⟨B, w, by omega, ?_, hdiag⟩
        intro b hb j
        exact Fin.lastCases (hall b hb) (fun j' => hker b hb j') j
      · push Not at hall
        rcases hall with ⟨p, hpB, hfp_ne⟩
        have hfp : f (w p) = 1 := by
          rcases zmod2_eq_zero_or_one (f (w p)) with h0 | h1
          · exact absurd h0 hfp_ne
          · exact h1
        let B' := B.erase p
        let w' : Fin k → (Fin k → ZMod 2) := fun b =>
          if f (w b) = 0 then w b else w b + w p
        refine ⟨B', w', ?_, ?_, ?_⟩
        · have hce : B'.card + 1 = B.card := Finset.card_erase_add_one hpB
          omega
        · intro b hb j
          have hbB : b ∈ B := Finset.mem_of_mem_erase hb
          refine Fin.lastCases ?_ ?_ j
          · change f (w' b) = 0
            dsimp only [w']
            split_ifs with h0
            · exact h0
            · have h1 : f (w b) = 1 := by
                rcases zmod2_eq_zero_or_one (f (w b)) with hz | ho
                · exact absurd hz h0
                · exact ho
              rw [map_add, h1, hfp]
              exact zmod2_add_self 1
          · intro j'
            dsimp only [w']
            split_ifs
            · exact hker b hbB j'
            · rw [map_add, hker b hbB j', hker p hpB j', add_zero]
        · intro b hb b' hb'
          have hbB : b ∈ B := Finset.mem_of_mem_erase hb
          have hb'B : b' ∈ B := Finset.mem_of_mem_erase hb'
          have hne_p : p ≠ b' := (Finset.ne_of_mem_erase hb').symm
          have hwp : w p b' = 0 := by
            rw [hdiag p hpB b' hb'B]
            simp only [hne_p, ↓reduceIte]
          dsimp only [w']
          by_cases hf0 : f (w b) = 0
          · simp only [hf0, ↓reduceIte]
            exact hdiag b hbB b' hb'B
          · simp only [hf0, ↓reduceIte, Pi.add_apply, hwp, add_zero]
            exact hdiag b hbB b' hb'B

private lemma linear_path_cover_eq_matching :
    ∀ (n : ℕ) (A : Finset ℕ), (∀ t ∈ A, t < n) →
      ∃ (E C : Finset ℕ),
        E ⊆ A ∧ (∀ t ∈ E, t + 1 ∉ E) ∧
        (∀ t ∈ A, t ∈ C ∨ t + 1 ∈ C) ∧
        C.card ≤ E.card ∧ (∀ v ∈ C, v ≤ n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro A hA
    cases n with
    | zero =>
      have hA0 : A = ∅ := by
        ext t; simp only [Finset.notMem_empty, iff_false]
        intro ht; have := hA t ht; omega
      subst hA0
      exact ⟨∅, ∅, subset_refl _, by simp, by simp, by simp, by simp⟩
    | succ m =>
      by_cases hm : m ∈ A
      · cases m with
        | zero =>
          refine ⟨{0}, {0}, ?_, ?_, ?_, by simp, by simp⟩
          · intro t ht; simp only [Finset.mem_singleton] at ht; subst ht; exact hm
          · intro t ht; simp only [Finset.mem_singleton] at ht ⊢; omega
          · intro t ht; have := hA t ht; left; simp only [Finset.mem_singleton]; omega
        | succ m' =>
          let A' := A.filter (fun t => t < m')
          have hA' : ∀ t ∈ A', t < m' := fun t ht => (Finset.mem_filter.mp ht).2
          rcases ih m' (by omega) A' hA' with ⟨E', C', hEA', hE'ind, hC'cov, hcard, hC'le⟩
          have hm_not_E' : m' + 1 ∉ E' := by
            intro hmem
            have := hA' (m' + 1) (hEA' hmem)
            omega
          refine ⟨insert (m' + 1) E', insert (m' + 1) C', ?_, ?_, ?_, ?_, ?_⟩
          · intro t ht
            rcases Finset.mem_insert.mp ht with rfl | ht'
            · exact hm
            · exact (Finset.mem_filter.mp (hEA' ht')).1
          · intro t ht ht1
            rcases Finset.mem_insert.mp ht with rfl | ht'
            · rcases Finset.mem_insert.mp ht1 with h1 | h1
              · omega
              · have := hA' (m' + 1 + 1) (hEA' h1); omega
            · have htlt : t < m' := hA' t (hEA' ht')
              rcases Finset.mem_insert.mp ht1 with h1 | h1
              · omega
              · exact hE'ind t ht' h1
          · intro t ht
            have htlt : t < m' + 1 + 1 := hA t ht
            by_cases h1 : t < m'
            · rcases hC'cov t (Finset.mem_filter.mpr ⟨ht, h1⟩) with hc | hc
              · left; exact Finset.mem_insert_of_mem hc
              · right; exact Finset.mem_insert_of_mem hc
            · by_cases h2 : t = m'
              · right; subst h2; exact Finset.mem_insert_self _ _
              · left
                have hteq : t = m' + 1 := by omega
                rw [hteq]
                exact Finset.mem_insert_self _ _
          · rw [Finset.card_insert_of_notMem hm_not_E']
            calc (insert (m' + 1) C').card ≤ C'.card + 1 := Finset.card_insert_le _ _
              _ ≤ E'.card + 1 := Nat.add_le_add_right hcard 1
          · intro v hv
            rcases Finset.mem_insert.mp hv with rfl | hv'
            · omega
            · have := hC'le v hv'; omega
      · have hA' : ∀ t ∈ A, t < m := fun t ht => by
          have := hA t ht
          have hne : t ≠ m := fun h => hm (h ▸ ht)
          omega
        rcases ih m (by omega) A hA' with ⟨E, C, hEA, hEind, hCcov, hcard, hCle⟩
        exact ⟨E, C, hEA, hEind, hCcov, hcard, fun v hv => le_trans (hCle v hv) (by omega)⟩

private lemma ix_succ_inj {k : ℕ} (hk : 0 < k) :
    Function.Injective (fun i : Fin k => ix hk (i.val + 1)) := by
  intro i₁ i₂ heq
  dsimp only at heq
  have h1 := ix_add_sub_cancel hk i₁ 1
  have h2 := ix_add_sub_cancel hk i₂ 1
  rw [heq] at h1
  exact h1.symm.trans h2

private lemma cover_lower_bound {k : ℕ} (hk : 0 < k) (S C : Finset (Fin k))
    (hcov : ∀ i ∈ S, i ∈ C ∨ ix hk (i.val + 1) ∈ C) :
    let mu := (S.powerset.filter (fun E => ∀ i ∈ E, ix hk (i.val + 1) ∉ E)).sup Finset.card
    let cost := if S = Finset.univ ∧ 1 < k ∧ k % 2 = 1 then mu + 1 else mu
    cost ≤ C.card := by
  intro mu cost
  have hmu_le : mu ≤ C.card := by
    refine Finset.sup_le fun E hE => ?_
    simp only [Finset.mem_filter, Finset.mem_powerset] at hE
    rcases hE with ⟨hES, hind⟩
    let pick : Fin k → Fin k := fun i => if i ∈ C then i else ix hk (i.val + 1)
    refine Finset.card_le_card_of_injOn pick ?_ ?_
    · intro i hi
      have hiE : i ∈ E := hi
      dsimp only [pick]
      split_ifs with h1
      · exact Finset.mem_coe.mpr h1
      · rcases hcov i (hES hiE) with hC | hC
        · exact absurd hC h1
        · exact Finset.mem_coe.mpr hC
    · intro i₁ hi₁ i₂ hi₂ heq
      have hi₁E : i₁ ∈ E := hi₁
      have hi₂E : i₂ ∈ E := hi₂
      dsimp only [pick] at heq
      split_ifs at heq with h1 h2 h2
      · exact heq
      · exfalso; exact hind i₂ hi₂E (heq ▸ hi₁E)
      · exfalso; exact hind i₁ hi₁E (heq.symm ▸ hi₂E)
      · exact ix_succ_inj hk heq
  dsimp only [cost]
  split_ifs with hodd
  · rcases hodd with ⟨rfl, hk1, hkodd⟩
    have hind_bound : ∀ E : Finset (Fin k),
        (∀ i ∈ E, ix hk (i.val + 1) ∉ E) → 2 * E.card ≤ k := by
      intro E hind
      have hdisj : Disjoint E (E.image (fun i => ix hk (i.val + 1))) := by
        rw [Finset.disjoint_left]
        intro x hxE hxI
        rcases Finset.mem_image.mp hxI with ⟨y, hyE, rfl⟩
        exact hind y hyE hxE
      have hcard_un : (E ∪ E.image (fun i => ix hk (i.val + 1))).card = 2 * E.card := by
        rw [Finset.card_union_of_disjoint hdisj,
            Finset.card_image_of_injective _ (ix_succ_inj hk)]
        ring
      have hle : (E ∪ E.image (fun i => ix hk (i.val + 1))).card ≤ k := by
        calc (E ∪ E.image (fun i => ix hk (i.val + 1))).card
            ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_univ _
          _ = k := Fintype.card_fin k
      omega
    have hmu_half : mu ≤ k / 2 := by
      refine Finset.sup_le fun E hE => ?_
      have hind := (Finset.mem_filter.mp hE).2
      have := hind_bound E hind
      omega
    let I : Finset (Fin k) := Finset.univ \ C
    have hI_ind : ∀ i ∈ I, ix hk (i.val + 1) ∉ I := by
      intro i hi hnext
      have hiC : i ∉ C := (Finset.mem_sdiff.mp hi).2
      have hnextC : ix hk (i.val + 1) ∉ C := (Finset.mem_sdiff.mp hnext).2
      rcases hcov i (Finset.mem_univ i) with h1 | h1
      · exact hiC h1
      · exact hnextC h1
    have hI_le : 2 * I.card ≤ k := hind_bound I hI_ind
    have hIC : I.card + C.card = k := by
      have hs : (Finset.univ \ C).card = k - C.card := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      have hCle : C.card ≤ k := by
        calc C.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_univ _
          _ = k := Fintype.card_fin k
      dsimp only [I]
      omega
    omega
  · exact hmu_le

private lemma exists_optimal_cover {k : ℕ} (hk : 1 < k) (S : Finset (Fin k)) :
    let hk0 : 0 < k := by omega
    let mu := (S.powerset.filter (fun E => ∀ i ∈ E, ix hk0 (i.val + 1) ∉ E)).sup Finset.card
    let cost := if S = Finset.univ ∧ 1 < k ∧ k % 2 = 1 then mu + 1 else mu
    ∃ C : Finset (Fin k), C.card ≤ cost ∧ ∀ i ∈ S, i ∈ C ∨ ix hk0 (i.val + 1) ∈ C := by
  intro hk0 mu cost
  by_cases hS : S = Finset.univ
  · subst hS
    let E : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => i.val % 2 = 0 ∧ i.val + 1 < k)
    have hE_ind : ∀ i ∈ E, ix hk0 (i.val + 1) ∉ E := by
      intro i hi hnext
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hi hnext
      have hv : (ix hk0 (i.val + 1)).val = i.val + 1 := Nat.mod_eq_of_lt hi.2
      rw [hv] at hnext
      omega
    have hE_card : E.card = k / 2 := by
      have hbij : E.card = (Finset.univ : Finset (Fin (k / 2))).card := by
        refine (Finset.card_bij (fun t _ => (⟨2 * t.val, by omega⟩ : Fin k)) ?_ ?_ ?_).symm
        · intro t _
          simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        · intro t₁ _ t₂ _ heq
          have : 2 * t₁.val = 2 * t₂.val := congrArg Fin.val heq
          exact Fin.ext (by omega)
        · intro i hi
          simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact ⟨⟨i.val / 2, by omega⟩, Finset.mem_univ _, Fin.ext (by simp; omega)⟩
      rw [hbij, Finset.card_univ, Fintype.card_fin]
    have hhalf_le_mu : k / 2 ≤ mu := by
      rw [← hE_card]
      exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hE_ind⟩)
    let C : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => i.val % 2 = 0)
    have hC_cov : ∀ i : Fin k, i ∈ C ∨ ix hk0 (i.val + 1) ∈ C := by
      intro i
      by_cases hev : i.val % 2 = 0
      · left; simp [C, hev]
      · right
        simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hlt : i.val + 1 < k
        · have hv : (ix hk0 (i.val + 1)).val = i.val + 1 := Nat.mod_eq_of_lt hlt
          rw [hv]; omega
        · have heq : i.val + 1 = k := by have := i.isLt; omega
          have hv : (ix hk0 (i.val + 1)).val = 0 := by simp [ix, heq]
          rw [hv]
    have hC_card : C.card = (k + 1) / 2 := by
      have hbij : C.card = (Finset.univ : Finset (Fin ((k + 1) / 2))).card := by
        refine (Finset.card_bij (fun t _ => (⟨2 * t.val, by omega⟩ : Fin k)) ?_ ?_ ?_).symm
        · intro t _
          simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        · intro t₁ _ t₂ _ heq
          have : 2 * t₁.val = 2 * t₂.val := congrArg Fin.val heq
          exact Fin.ext (by omega)
        · intro i hi
          simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact ⟨⟨i.val / 2, by omega⟩, Finset.mem_univ _, Fin.ext (by simp; omega)⟩
      rw [hbij, Finset.card_univ, Fintype.card_fin]
    refine ⟨C, ?_, fun i _ => hC_cov i⟩
    dsimp only [cost]
    by_cases hodd : k % 2 = 1
    · simp only [hk, hodd, and_self, ↓reduceIte]
      omega
    · simp only [hk, hodd, and_false, ↓reduceIte]
      omega
  · have hnotall : ∃ r : Fin k, r ∉ S := by
      by_contra hall
      push Not at hall
      apply hS
      ext i; simp [hall i]
    rcases hnotall with ⟨r, hrS⟩
    let shift : ℕ → Fin k := fun t => ix hk0 (r.val + 1 + t)
    have hshift_inj : ∀ t₁ t₂ : ℕ, t₁ < k → t₂ < k → shift t₁ = shift t₂ → t₁ = t₂ := by
      intro t₁ t₂ h1 h2 heq
      have hm : (r.val + 1 + t₁) % k = (r.val + 1 + t₂) % k := congrArg Fin.val heq
      have hrm : (r.val + 1) % k < k := Nat.mod_lt _ hk0
      have hmod : ((r.val + 1) % k + t₁) % k = ((r.val + 1) % k + t₂) % k := by
        rw [Nat.mod_add_mod, Nat.mod_add_mod]
        exact hm
      have hlt2 : ∀ x : ℕ, x < 2 * k → x % k = if x < k then x else x - k := fun x hx => by
        by_cases hx1 : x < k
        · simp [hx1, Nat.mod_eq_of_lt hx1]
        · simp only [hx1, ↓reduceIte]
          have hx2 : x = (x - k) + k := by omega
          conv_lhs => rw [hx2]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hlt2 ((r.val + 1) % k + t₁) (by omega), hlt2 ((r.val + 1) % k + t₂) (by omega)] at hmod
      split_ifs at hmod <;> omega
    let A : Finset ℕ := (Finset.range (k - 1)).filter (fun t => shift t ∈ S)
    have hA_lt : ∀ t ∈ A, t < k - 1 := fun t ht => Finset.mem_range.mp (Finset.mem_filter.mp ht).1
    rcases linear_path_cover_eq_matching (k - 1) A hA_lt with ⟨E0, C0, hE0A, hE0ind, hC0cov, hcard, hC0le⟩
    let E : Finset (Fin k) := E0.image shift
    let C : Finset (Fin k) := C0.image shift
    have hES : E ⊆ S := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨t, htE, rfl⟩
      exact (Finset.mem_filter.mp (hE0A htE)).2
    have hE_ind : ∀ i ∈ E, ix hk0 (i.val + 1) ∉ E := by
      intro i hi hnext
      rcases Finset.mem_image.mp hi with ⟨t₁, ht₁, rfl⟩
      rcases Finset.mem_image.mp hnext with ⟨t₂, ht₂, hshift_eq⟩
      have ht₁_lt : t₁ < k - 1 := hA_lt t₁ (hE0A ht₁)
      have ht₂_lt : t₂ < k - 1 := hA_lt t₂ (hE0A ht₂)
      have hnext_eq : ix hk0 ((shift t₁).val + 1) = shift (t₁ + 1) := by
        dsimp only [shift]
        rw [ix_add_mod, Nat.add_assoc]
      rw [hnext_eq] at hshift_eq
      have heq_t : t₂ = t₁ + 1 := hshift_inj t₂ (t₁ + 1) (by omega) (by omega) hshift_eq
      exact hE0ind t₁ ht₁ (heq_t ▸ ht₂)
    have hE_card : E.card = E0.card := by
      refine Finset.card_image_of_injOn ?_
      intro t₁ ht₁ t₂ ht₂ heq
      exact hshift_inj t₁ t₂ (by have := hA_lt t₁ (hE0A ht₁); omega)
        (by have := hA_lt t₂ (hE0A ht₂); omega) heq
    have hE_le_mu : E0.card ≤ mu := by
      rw [← hE_card]
      exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hES, hE_ind⟩)
    have hC_card : C.card ≤ cost := by
      dsimp only [cost]
      simp only [hS, false_and, ↓reduceIte]
      calc C.card ≤ C0.card := Finset.card_image_le
        _ ≤ E0.card := hcard
        _ ≤ mu := hE_le_mu
    have hC_cov : ∀ i ∈ S, i ∈ C ∨ ix hk0 (i.val + 1) ∈ C := by
      intro i hiS
      let t := (i.val + k - (r.val + 1) % k) % k
      have ht_lt_k : t < k := Nat.mod_lt _ hk0
      have hshift_t : shift t = i := by
        dsimp only [shift, t]
        have h1 : (r.val + 1 + (i.val + k - (r.val + 1) % k) % k) % k = i.val := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have hlt := Nat.mod_lt (r.val + 1) hk0
          have hdm := Nat.div_add_mod (r.val + 1) k
          have hrew : r.val + 1 + (i.val + k - (r.val + 1) % k) =
              i.val + ((r.val + 1) / k + 1) * k := by
            have : r.val + 1 = (r.val + 1) / k * k + (r.val + 1) % k := by
              rw [mul_comm]; exact hdm.symm
            have : ((r.val + 1) / k + 1) * k = (r.val + 1) / k * k + k := by ring
            omega
          rw [hrew, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
        exact Fin.ext h1
      have ht_ne : t ≠ k - 1 := by
        intro htk
        have hsr : shift (k - 1) = r := by
          ext; dsimp only [shift, ix]
          have h1 : r.val + 1 + (k - 1) = r.val + k := by omega
          rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt r.isLt]
        rw [htk, hsr] at hshift_t
        exact hrS (hshift_t ▸ hiS)
      have htA : t ∈ A := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hshift_t.symm ▸ hiS⟩
      rcases hC0cov t htA with hc | hc
      · left; rw [← hshift_t]; exact Finset.mem_image_of_mem shift hc
      · right
        have hnext : ix hk0 (i.val + 1) = shift (t + 1) := by
          rw [← hshift_t]; dsimp only [shift]; rw [ix_add_mod, Nat.add_assoc]
        rw [hnext]
        exact Finset.mem_image_of_mem shift hc
    exact ⟨C, hC_card, hC_cov⟩

private lemma foldl_run_zero {d : ℕ} (f : Fin d → ℕ → ℕ)
    (h0 : ∀ j : Fin d, f j 0 = 0) :
    (List.finRange d).foldl (fun h j => 2 * h + f j h) 0 = 0 := by
  have hgen : ∀ (l : List (Fin d)), (∀ j ∈ l, f j 0 = 0) →
      l.foldl (fun h j => 2 * h + f j h) 0 = 0 := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a rest ih =>
      intro hall
      simp only [List.foldl_cons, Nat.mul_zero, zero_add]
      rw [hall a (by simp)]
      exact ih fun j hj => hall j (by simp [hj])
  exact hgen (List.finRange d) (fun j _ => h0 j)

private lemma foldl_bits_testBit (b : ℕ → Bool) :
    ∀ (l : List ℕ) (acc : ℕ) (pos : ℕ) (hpos : pos < l.length),
      (l.foldl (fun h a => 2 * h + if b a then 1 else 0) acc).testBit pos =
        b (l[l.length - 1 - pos]'(by omega)) := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _ pos hpos; simp at hpos
  | append_singleton l a ih =>
    intro acc pos hpos
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set prev := l.foldl (fun h x => 2 * h + if b x then 1 else 0) acc
    have hmul : 2 * prev + (if b a then 1 else 0) =
        Nat.bit (b a) prev := by
      cases b a <;> simp [Nat.bit]
    rw [hmul]
    cases pos with
    | zero =>
      simp only [Nat.testBit_bit_zero, List.length_append, List.length_singleton,
        Nat.add_sub_cancel, Nat.sub_zero]
      rw [List.getElem_append_right (le_refl _)]
      simp
    | succ pos' =>
      rw [Nat.testBit_bit_succ]
      simp only [List.length_append, List.length_singleton] at hpos ⊢
      have hpos' : pos' < l.length := by omega
      rw [ih acc pos' hpos']
      have hlt : l.length + 1 - 1 - (pos' + 1) < l.length := by omega
      rw [List.getElem_append_left hlt]
      congr 2
      omega

private lemma run_nonadaptive_testBit {d : ℕ} (b : Fin d → Bool) (j : Fin d) :
    ((List.finRange d).foldl (fun h i => 2 * h + if b i then 1 else 0) 0).testBit
      (d - 1 - j.val) = b j := by
  let b' : ℕ → Bool := fun n => if h : n < d then b ⟨n, h⟩ else false
  have hmap : (List.finRange d).foldl (fun h i => 2 * h + if b i then 1 else 0) 0 =
      (List.range d).foldl (fun h n => 2 * h + if b' n then 1 else 0) 0 := by
    have hfr : List.finRange d = (List.range d).pmap (fun n hn => ⟨n, hn⟩)
        (fun _ hn => List.mem_range.mp hn) := by
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp
    have hgen : ∀ (l : List (Fin d)) (acc : ℕ),
        l.foldl (fun h i => 2 * h + if b i then 1 else 0) acc =
        (l.map Fin.val).foldl (fun h n => 2 * h + if b' n then 1 else 0) acc := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons a rest ih =>
        intro acc
        simp only [List.map_cons, List.foldl_cons, b', a.isLt, ↓reduceDIte]
        exact ih _
    rw [hgen]
    have hmv : (List.finRange d).map Fin.val = List.range d := by
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp
    rw [hmv]
  rw [hmap]
  have hpos : d - 1 - j.val < (List.range d).length := by simp; omega
  rw [foldl_bits_testBit b' (List.range d) 0 (d - 1 - j.val) hpos]
  have hlen : (List.range d).length = d := List.length_range
  have hidx : (List.range d)[(List.range d).length - 1 - (d - 1 - j.val)]'(by omega) = j.val := by
    rw [List.getElem_range]
    omega
  rw [hidx]
  simp [b', j.isLt]

private lemma prove_25736 (k : ℕ) (hk : 0 < k) (hk3 : k % 3 ≠ 0)
    (spacing s t : ℕ) (name c : Fin k → ZMod 2) (S : Finset (Fin k)) (d : ℕ) :
    let F := ZMod 2
    let W := Fin k → F
    let D := W →ₗ[F] F
    let out := fun (x : W) (i : Fin k) =>
      let z := rotLin hk s x + name
      let y := fun j : Fin k =>
        z j + z (ix hk (j.val + spacing)) + z (ix hk (j.val + k - spacing % k))
      y i + (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2)) + rotLin hk t x i + c i
    let mu := (S.powerset.filter (fun E => ∀ i ∈ E, ix hk (i.val + 1) ∉ E)).sup Finset.card
    let run := fun (ask : Fin d → ℕ → D) (x : W) =>
      (List.finRange d).foldl (fun h j =>
        2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
    let cost := if S = Finset.univ ∧ 1 < k ∧ k % 2 = 1 then mu + 1 else mu
    (∃ (ask : Fin d → ℕ → D) (readout : ℕ → Fin k → D) (bias : ℕ → Fin k → F),
      ∀ x, ∀ i ∈ S, out x i = readout (run ask x) i x + bias (run ask x) i) ↔
      cost ≤ d := by
  intro F W D out mu run cost
  let L : W →ₗ[F] W := (mixLin hk spacing).comp (rotLin hk s)
  have hL_bij : Function.Bijective L :=
    (mixLin_bijective hk hk3 spacing).comp (rotLin_bijective hk s)
  let eL : W ≃ W := Equiv.ofBijective L hL_bij
  let Linv : W →ₗ[F] W :=
    { toFun := eL.symm
      map_add' := fun u v => by
        apply hL_bij.1
        change L (eL.symm (u + v)) = L (eL.symm u + eL.symm v)
        rw [L.map_add]
        exact (eL.apply_symm_apply (u + v)).trans
          (congrArg₂ (· + ·) (eL.apply_symm_apply u).symm (eL.apply_symm_apply v).symm)
      map_smul' := fun r u => by
        apply hL_bij.1
        simp only [RingHom.id_apply]
        change L (eL.symm (r • u)) = L (r • eL.symm u)
        rw [L.map_smul]
        exact (eL.apply_symm_apply (r • u)).trans
          (congrArg (r • ·) (eL.apply_symm_apply u).symm) }
  have hL_Linv : ∀ u : W, L (Linv u) = u := fun u => eL.apply_symm_apply u
  let y0 : W := mixLin hk spacing name
  let Lcoord : Fin k → (W →ₗ[F] F) := fun j =>
    { toFun := fun x => L x j
      map_add' := fun x₁ x₂ => congrFun (map_add L x₁ x₂) j
      map_smul' := fun r x => congrFun (map_smul L r x) j }
  let rotCoord : Fin k → (W →ₗ[F] F) := fun i =>
    { toFun := fun x => rotLin hk t x i
      map_add' := fun x₁ x₂ => congrFun (map_add (rotLin hk t) x₁ x₂) i
      map_smul' := fun r x => congrFun (map_smul (rotLin hk t) r x) i }
  let affLin : Fin k → (W →ₗ[F] F) := fun i =>
    Lcoord i + y0 (ix hk (i.val + 2)) • Lcoord (ix hk (i.val + 1)) +
    (1 + y0 (ix hk (i.val + 1))) • Lcoord (ix hk (i.val + 2)) + rotCoord i
  let affConst : Fin k → F := fun i =>
    y0 i + (1 + y0 (ix hk (i.val + 1))) * y0 (ix hk (i.val + 2)) + c i
  have hout_decomp : ∀ (x : W) (i : Fin k),
      out x i = L x (ix hk (i.val + 1)) * L x (ix hk (i.val + 2)) + affLin i x + affConst i := by
    intro x i
    have hy : ∀ j : Fin k,
        (rotLin hk s x + name) j + (rotLin hk s x + name) (ix hk (j.val + spacing)) +
          (rotLin hk s x + name) (ix hk (j.val + k - spacing % k)) = L x j + y0 j := by
      intro j
      change mixLin hk spacing (rotLin hk s x + name) j = L x j + y0 j
      rw [map_add]; rfl
    dsimp only [out]
    simp_rw [hy]
    simp only [affLin, affConst, Lcoord, rotCoord, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    ring
  constructor
  · rintro ⟨ask, readout, bias, hread⟩
    by_cases hk1 : k = 1
    · subst hk1
      have hmu0 : mu = 0 := by
        apply Nat.eq_zero_of_le_zero
        refine Finset.sup_le fun E hE => ?_
        have hind := (Finset.mem_filter.mp hE).2
        have hE0 : E = ∅ := by
          ext i
          simp only [Finset.notMem_empty, iff_false]
          intro hi
          have hix : ix hk (i.val + 1) = i := by
            ext; simp [ix]
          exact hind i hi (hix.symm ▸ hi)
        rw [hE0]; simp
      dsimp only [cost]
      simp [hmu0]
    · have hk2 : 1 < k := by omega
      let ℓ : Fin d → D := fun j => (ask j 0).comp Linv
      rcases exists_pivot_basis d ℓ with ⟨B, w, hBcard, hBker, hBdiag⟩
      have hrun_zero : ∀ u : W, (∀ j : Fin d, ℓ j u = 0) → run ask (Linv u) = 0 := by
        intro u hu
        dsimp only [run]
        refine foldl_run_zero (fun j h => if ask j h (Linv u) = 0 then 0 else 1) ?_
        intro j
        have h0 : ask j 0 (Linv u) = 0 := hu j
        simp [h0]
      have hno_edge : ∀ i ∈ S, ¬ (ix hk (i.val + 1) ∈ B ∧ ix hk (i.val + 2) ∈ B) := by
        intro i hiS ⟨hp1, hp2⟩
        let p₁ := ix hk (i.val + 1)
        let p₂ := ix hk (i.val + 2)
        have hne : p₁ ≠ p₂ := by
          intro heq
          have h2 : ix hk ((ix hk (i.val + 1)).val + 1) = ix hk (i.val + 2) := by
            rw [ix_add_mod]
          have h3 : ix hk (i.val + 1) = ix hk ((ix hk (i.val + 1)).val + 1) := by
            rw [h2]; exact heq
          have h4 := congrArg Fin.val h3
          dsimp only [ix] at h4
          have hlt : (i.val + 1) % k < k := Nat.mod_lt _ hk
          by_cases hlt1 : (i.val + 1) % k + 1 < k
          · rw [Nat.mod_eq_of_lt hlt1] at h4; omega
          · have hkeq : (i.val + 1) % k + 1 = k := by omega
            rw [hkeq, Nat.mod_self] at h4; omega
        have hu0 : run ask (Linv 0) = 0 := hrun_zero 0 (fun j => by simp)
        have hu1 : run ask (Linv (w p₁)) = 0 := hrun_zero (w p₁) (hBker p₁ hp1)
        have hu2 : run ask (Linv (w p₂)) = 0 := hrun_zero (w p₂) (hBker p₂ hp2)
        have hu12 : run ask (Linv (w p₁ + w p₂)) = 0 :=
          hrun_zero (w p₁ + w p₂) (fun j => by rw [map_add, hBker p₁ hp1 j, hBker p₂ hp2 j, add_zero])
        have heq0 := hread (Linv 0) i hiS
        have heq1 := hread (Linv (w p₁)) i hiS
        have heq2 := hread (Linv (w p₂)) i hiS
        have heq12 := hread (Linv (w p₁ + w p₂)) i hiS
        rw [hu0, hout_decomp, hL_Linv] at heq0
        rw [hu1, hout_decomp, hL_Linv] at heq1
        rw [hu2, hout_decomp, hL_Linv] at heq2
        rw [hu12, hout_decomp, hL_Linv] at heq12
        have hsum := congrArg₂ (· + ·) (congrArg₂ (· + ·) heq0 heq1) (congrArg₂ (· + ·) heq2 heq12)
        have hlin_zero : ∀ (g : D) (b : F),
            (g (Linv 0) + b) + (g (Linv (w p₁)) + b) +
            ((g (Linv (w p₂)) + b) + (g (Linv (w p₁ + w p₂)) + b)) = 0 := by
          intro g b
          rw [map_zero, map_zero, map_add, map_add]
          have hs1 := zmod2_add_self (g (Linv (w p₁)))
          have hs2 := zmod2_add_self (g (Linv (w p₂)))
          have hsb := zmod2_add_self b
          calc (0 + b) + (g (Linv (w p₁)) + b) +
                ((g (Linv (w p₂)) + b) + (g (Linv (w p₁)) + g (Linv (w p₂)) + b))
              = (g (Linv (w p₁)) + g (Linv (w p₁))) + (g (Linv (w p₂)) + g (Linv (w p₂))) +
                (b + b) + (b + b) := by ring
            _ = 0 := by rw [hs1, hs2, hsb]; simp
        have hlin_aff := hlin_zero (affLin i) (affConst i)
        have hlin_rd := hlin_zero (readout 0 i) (bias 0 i)
        have hquad : (0 : W) p₁ * (0 : W) p₂ + w p₁ p₁ * w p₁ p₂ +
            (w p₂ p₁ * w p₂ p₂ + (w p₁ + w p₂) p₁ * (w p₁ + w p₂) p₂) = 1 := by
          have h01 : (0 : W) p₁ = 0 := rfl
          have h11 : w p₁ p₁ = 1 := by rw [hBdiag p₁ hp1 p₁ hp1]; simp
          have h12 : w p₁ p₂ = 0 := by rw [hBdiag p₁ hp1 p₂ hp2]; simp only [hne, ↓reduceIte]
          have h21 : w p₂ p₁ = 0 := by rw [hBdiag p₂ hp2 p₁ hp1]; simp only [hne.symm, ↓reduceIte]
          have h22 : w p₂ p₂ = 1 := by rw [hBdiag p₂ hp2 p₂ hp2]; simp
          rw [h01]
          simp [Pi.add_apply, h11, h12, h21, h22]
        have h10 : (1 : ZMod 2) = 0 := by
          calc (1 : ZMod 2)
              = ((0 : W) p₁ * (0 : W) p₂ + w p₁ p₁ * w p₁ p₂ +
                  (w p₂ p₁ * w p₂ p₂ + (w p₁ + w p₂) p₁ * (w p₁ + w p₂) p₂)) +
                ((affLin i (Linv 0) + affConst i) + (affLin i (Linv (w p₁)) + affConst i) +
                  ((affLin i (Linv (w p₂)) + affConst i) +
                    (affLin i (Linv (w p₁ + w p₂)) + affConst i))) := by
                rw [hquad, hlin_aff, add_zero]
            _ = ((0 : W) p₁ * (0 : W) p₂ + affLin i (Linv 0) + affConst i) +
                (w p₁ p₁ * w p₁ p₂ + affLin i (Linv (w p₁)) + affConst i) +
                ((w p₂ p₁ * w p₂ p₂ + affLin i (Linv (w p₂)) + affConst i) +
                  ((w p₁ + w p₂) p₁ * (w p₁ + w p₂) p₂ +
                    affLin i (Linv (w p₁ + w p₂)) + affConst i)) := by ring
            _ = (readout 0 i (Linv 0) + bias 0 i) + (readout 0 i (Linv (w p₁)) + bias 0 i) +
                ((readout 0 i (Linv (w p₂)) + bias 0 i) +
                  (readout 0 i (Linv (w p₁ + w p₂)) + bias 0 i)) := hsum
            _ = 0 := hlin_rd
        exact absurd h10 (by decide)
      let C : Finset (Fin k) := (Finset.univ \ B).image (fun v => ix hk (v.val + k - 1 % k))
      have hC_cov : ∀ i ∈ S, i ∈ C ∨ ix hk (i.val + 1) ∈ C := by
        intro i hiS
        have hne := hno_edge i hiS
        by_cases h1 : ix hk (i.val + 1) ∈ B
        · have h2 : ix hk (i.val + 2) ∉ B := fun h => hne ⟨h1, h⟩
          right
          refine Finset.mem_image.mpr ⟨ix hk (i.val + 2), Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h2⟩, ?_⟩
          have hrew : ix hk (i.val + 2) = ix hk ((ix hk (i.val + 1)).val + 1) := by
            rw [ix_add_mod]
          rw [hrew]
          exact ix_add_sub_cancel hk (ix hk (i.val + 1)) 1
        · left
          refine Finset.mem_image.mpr ⟨ix hk (i.val + 1), Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h1⟩, ?_⟩
          exact ix_add_sub_cancel hk i 1
      have hC_card : C.card ≤ d := by
        have hsdiff : (Finset.univ \ B).card = k - B.card := by
          rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
        calc C.card ≤ (Finset.univ \ B).card := Finset.card_image_le
          _ = k - B.card := hsdiff
          _ ≤ d := by omega
      exact le_trans (cover_lower_bound hk S C hC_cov) hC_card
  · intro hcost
    by_cases hk1 : k = 1
    · subst hk1
      refine ⟨fun _ _ => 0, fun _ i => affLin i + Lcoord i, fun _ i => affConst i, ?_⟩
      intro x i _
      rw [hout_decomp x i]
      have h1 : ix hk (i.val + 1) = i := by ext; simp [ix]
      have h2 : ix hk (i.val + 2) = i := by ext; simp [ix]
      rw [h1, h2, zmod2_mul_self]
      change L x i + affLin i x + affConst i = (affLin i x + L x i) + affConst i
      ring
    · have hk2 : 1 < k := by omega
      rcases exists_optimal_cover hk2 S with ⟨C', hC'card, hC'cov⟩
      let C : Finset (Fin k) := C'.image (fun v => ix hk (v.val + 1))
      have hC_card : C.card ≤ d := by
        calc C.card ≤ C'.card := Finset.card_image_le
          _ ≤ cost := hC'card
          _ ≤ d := hcost
      have hC_cov : ∀ i ∈ S, ix hk (i.val + 1) ∈ C ∨ ix hk (i.val + 2) ∈ C := by
        intro i hiS
        rcases hC'cov i hiS with hc | hc
        · left; exact Finset.mem_image_of_mem _ hc
        · right
          have hrew : ix hk (i.val + 2) = ix hk ((ix hk (i.val + 1)).val + 1) := by
            rw [ix_add_mod]
          rw [hrew]
          exact Finset.mem_image_of_mem _ hc
      let eC : Fin C.card ≃ C := (Fintype.equivFinOfCardEq (by simp)).symm
      let ask : Fin d → ℕ → D := fun j _ =>
        if h : j.val < C.card then Lcoord (eC ⟨j.val, h⟩).val else 0
      let valOf : ℕ → Fin k → F := fun h v =>
        if hv : v ∈ C then
          if h.testBit (d - 1 - (eC.symm ⟨v, hv⟩).val) then 1 else 0
        else 0
      have hvalOf_eq : ∀ (x : W) (v : Fin k), v ∈ C → valOf (run ask x) v = L x v := by
        intro x v hv
        let j0 : Fin d := ⟨(eC.symm ⟨v, hv⟩).val, lt_of_lt_of_le (eC.symm ⟨v, hv⟩).isLt hC_card⟩
        let b : Fin d → Bool := fun j => decide (ask j 0 x ≠ 0)
        have hrun_eq : run ask x =
            (List.finRange d).foldl (fun h j => 2 * h + if b j then 1 else 0) 0 := by
          dsimp only [run]
          congr 1
          funext h j
          have hconst : ask j h x = ask j 0 x := rfl
          rw [hconst]
          dsimp only [b]
          by_cases hz : ask j 0 x = 0 <;> simp [hz]
        dsimp only [valOf]
        simp only [hv, ↓reduceDIte]
        rw [hrun_eq]
        have htb := run_nonadaptive_testBit b j0
        change (if ((List.finRange d).foldl (fun h i => 2 * h + if b i then 1 else 0) 0).testBit
            (d - 1 - j0.val) then 1 else 0) = L x v
        rw [htb]
        dsimp only [b, ask, j0]
        have hlt : (eC.symm ⟨v, hv⟩).val < C.card := (eC.symm ⟨v, hv⟩).isLt
        simp only [hlt, ↓reduceDIte, Fin.eta, Equiv.apply_symm_apply]
        change (if decide (L x v ≠ 0) = true then (1 : ZMod 2) else 0) = L x v
        rcases zmod2_eq_zero_or_one (L x v) with h0 | h1
        · rw [h0]; decide
        · rw [h1]; decide
      let readout : ℕ → Fin k → (W →ₗ[F] F) := fun h i =>
        let p₁ := ix hk (i.val + 1)
        let p₂ := ix hk (i.val + 2)
        (if p₁ ∈ C then valOf h p₁ • Lcoord p₂ else valOf h p₂ • Lcoord p₁) + affLin i
      refine ⟨ask, readout, fun _ i => affConst i, ?_⟩
      intro x i hiS
      rw [hout_decomp x i]
      by_cases h1 : ix hk (i.val + 1) ∈ C
      · have hval : valOf (run ask x) (ix hk (i.val + 1)) = L x (ix hk (i.val + 1)) :=
          hvalOf_eq x _ h1
        have hrhs : readout (run ask x) i x =
            valOf (run ask x) (ix hk (i.val + 1)) * L x (ix hk (i.val + 2)) + affLin i x := by
          dsimp only [readout]
          simp only [h1, ↓reduceIte]
          rfl
        rw [hrhs, hval]
      · have h2 : ix hk (i.val + 2) ∈ C := (hC_cov i hiS).resolve_left h1
        have hval : valOf (run ask x) (ix hk (i.val + 2)) = L x (ix hk (i.val + 2)) :=
          hvalOf_eq x _ h2
        have hrhs : readout (run ask x) i x =
            valOf (run ask x) (ix hk (i.val + 2)) * L x (ix hk (i.val + 1)) + affLin i x := by
          dsimp only [readout]
          simp only [h1, ↓reduceIte]
          rfl
        rw [hrhs, hval, mul_comm]

end PEqualNP.Outside.L_meta_25736_aux

theorem PEqualNP.Outside.L_meta_25736 : (∀ (k : ℕ) (hk : 0 < k), k % 3 ≠ 0 →
  let F := ZMod 2
  let W := Fin k → F
  let D := W →ₗ[F] F
  let ix := fun z : ℕ => (⟨z % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (q : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - q % k))
  ∀ (spacing s t : ℕ) (name c : W) (S : Finset (Fin k)) (d : ℕ),
    let out := fun (x : W) (i : Fin k) =>
      let z := rot s x + name
      let y := fun j : Fin k =>
        z j + z (ix (j.val + spacing)) + z (ix (j.val + k - spacing % k))
      y i + (1 + y (ix (i.val + 1))) * y (ix (i.val + 2)) + rot t x i + c i
    let mu := (S.powerset.filter (fun E => ∀ i ∈ E, ix (i.val + 1) ∉ E)).sup Finset.card
    let run := fun (ask : Fin d → ℕ → D) (x : W) =>
      (List.finRange d).foldl (fun h j =>
        2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
    let cost := if S = Finset.univ ∧ 1 < k ∧ k % 2 = 1 then mu + 1 else mu
    (∃ (ask : Fin d → ℕ → D) (readout : ℕ → Fin k → D) (bias : ℕ → Fin k → F),
      ∀ x, ∀ i ∈ S, out x i = readout (run ask x) i x + bias (run ask x) i) ↔
      cost ≤ d) := by
  intro k hk hk3
  dsimp only
  intro spacing s t name c S d
  exact PEqualNP.Outside.L_meta_25736_aux.prove_25736 k hk hk3 spacing s t name c S d

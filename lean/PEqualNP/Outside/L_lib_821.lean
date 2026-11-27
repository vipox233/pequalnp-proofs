import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_821

def sgnZ (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

lemma sgnZ_zero : sgnZ 0 = 1 := rfl

lemma sgnZ_one : sgnZ 1 = -1 := rfl

lemma sgnZ_add (x y : ZMod 2) : sgnZ (x + y) = sgnZ x * sgnZ y := by
  fin_cases x <;> fin_cases y <;> decide

lemma sgnZ_sub_one_even (x : ZMod 2) : Even (sgnZ x - 1) := by
  fin_cases x
  · exact ⟨0, by decide⟩
  · exact ⟨-1, by decide⟩

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by fin_cases x <;> decide

lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma card_even_of_fpf_involution {α : Type} [DecidableEq α] (S : Finset α) (f : α → α)
    (hmem : ∀ x ∈ S, f x ∈ S) (hinv : ∀ x ∈ S, f (f x) = x) (hne : ∀ x ∈ S, f x ≠ x) :
    Even S.card := by
  classical
  induction hN : S.card using Nat.strong_induction_on generalizing S with
  | ind n ih =>
    by_cases hE : S = ∅
    · subst hE; subst hN; exact ⟨0, by simp⟩
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hE
      have hfx : f x ∈ S := hmem x hx
      have hne_x : f x ≠ x := hne x hx
      let S' := (S.erase x).erase (f x)
      have hfx_er : f x ∈ S.erase x := Finset.mem_erase.mpr ⟨hne_x, hfx⟩
      have hcard' : S'.card + 2 = S.card := by
        have h1 : (S.erase x).card + 1 = S.card := Finset.card_erase_add_one hx
        have h2 : S'.card + 1 = (S.erase x).card := Finset.card_erase_add_one hfx_er
        omega
      have hsub : S' ⊆ S := fun y hy =>
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
      have hmem' : ∀ y ∈ S', f y ∈ S' := by
        intro y hy
        have hy1 : y ≠ f x := (Finset.mem_erase.mp hy).1
        have hy2 : y ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
        have hyS : y ∈ S := hsub hy
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hmem y hyS⟩⟩
        · intro heq
          have : y = x := by rw [← hinv y hyS, heq, hinv x hx]
          exact hy2 this
        · intro heq
          have : y = f x := by rw [← hinv y hyS, heq]
          exact hy1 this
      have heven' : Even S'.card :=
        ih S'.card (by omega) S' hmem' (fun y hy => hinv y (hsub hy))
          (fun y hy => hne y (hsub hy)) rfl
      rcases heven' with ⟨k, hk⟩
      exact ⟨k + 1, by omega⟩

lemma sum_sgnZ_subspace {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [DecidableEq V]
    (S : Finset V) (hadd : ∀ u ∈ S, ∀ v ∈ S, u + v ∈ S)
    (φ : V → ZMod 2) (hφ : ∀ u v, φ (u + v) = φ u + φ v) :
    ∑ v ∈ S, sgnZ (φ v) = if ∀ v ∈ S, φ v = 0 then (S.card : ℤ) else 0 := by
  classical
  by_cases hall : ∀ v ∈ S, φ v = 0
  · rw [if_pos hall]
    have h1 : ∀ v ∈ S, sgnZ (φ v) = 1 := fun v hv => by rw [hall v hv]; rfl
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  · rw [if_neg hall]
    push_neg at hall
    obtain ⟨u, huS, hu_ne⟩ := hall
    have hu1 : φ u = 1 := by
      rcases zmod2_eq_zero_or_one (φ u) with h0 | h1
      · exact False.elim (hu_ne h0)
      · exact h1
    have hself : ∀ v : V, v + v = 0 := by
      intro v
      have h2 : (1 + 1 : ZMod 2) = 0 := by decide
      calc v + v = (1 : ZMod 2) • v + (1 : ZMod 2) • v := by simp
        _ = ((1 : ZMod 2) + 1) • v := (add_smul 1 1 v).symm
        _ = (0 : ZMod 2) • v := by rw [h2]
        _ = 0 := zero_smul _ _
    have hflip : ∑ v ∈ S, sgnZ (φ v) = -(∑ v ∈ S, sgnZ (φ v)) := by
      have hbij : ∑ v ∈ S, sgnZ (φ v) = ∑ v ∈ S, sgnZ (φ (v + u)) := by
        refine Finset.sum_bij (fun v _ => v + u) ?_ ?_ ?_ ?_
        · intro v hv; exact hadd v hv u huS
        · intro v1 _ v2 _ heq
          have : (v1 + u) + u = (v2 + u) + u := congrArg (· + u) heq
          simpa [add_assoc, hself u] using this
        · intro w hw
          refine ⟨w + u, hadd w hw u huS, ?_⟩
          simp [add_assoc, hself u]
        · intro v _; simp [add_assoc, hself u]
      have hneg : ∀ v ∈ S, sgnZ (φ (v + u)) = -sgnZ (φ v) := by
        intro v _
        rw [hφ, hu1, sgnZ_add, sgnZ_one]; ring
      calc ∑ v ∈ S, sgnZ (φ v)
          = ∑ v ∈ S, sgnZ (φ (v + u)) := hbij
        _ = ∑ v ∈ S, -sgnZ (φ v) := Finset.sum_congr rfl hneg
        _ = -(∑ v ∈ S, sgnZ (φ v)) := by rw [Finset.sum_neg_distrib]
    omega

def mv' {m j : ℕ} (M : Matrix (Fin m) (Fin j) (ZMod 2)) (c : Fin j → ZMod 2) (a : Fin m) : ZMod 2 :=
  ∑ b : Fin j, M a b * c b

def pairing' {m j : ℕ} (M Y : Matrix (Fin m) (Fin j) (ZMod 2)) : ZMod 2 :=
  ∑ a : Fin m, ∑ b : Fin j, M a b * Y a b

lemma mv'_zero {m j : ℕ} (M : Matrix (Fin m) (Fin j) (ZMod 2)) : mv' M 0 = 0 := by
  funext a; simp [mv']

lemma mv'_add {m j : ℕ} (M : Matrix (Fin m) (Fin j) (ZMod 2)) (c1 c2 : Fin j → ZMod 2) :
    mv' M (c1 + c2) = mv' M c1 + mv' M c2 := by
  funext a; simp only [mv', Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma mv'_add_mat {m j : ℕ} (M1 M2 : Matrix (Fin m) (Fin j) (ZMod 2)) (c : Fin j → ZMod 2) :
    mv' (M1 + M2) c = mv' M1 c + mv' M2 c := by
  funext a; simp only [mv', Matrix.add_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma pairing'_add {m j : ℕ} (M1 M2 Y : Matrix (Fin m) (Fin j) (ZMod 2)) :
    pairing' (M1 + M2) Y = pairing' M1 Y + pairing' M2 Y := by
  simp only [pairing', Matrix.add_apply, add_mul, Finset.sum_add_distrib]

lemma vec_add_self {k : ℕ} (v : Fin k → ZMod 2) : v + v = 0 := by
  funext i; exact zmod2_add_self (v i)

lemma card_ker_even_of_ne_zero {m j : ℕ} (M : Matrix (Fin m) (Fin j) (ZMod 2))
    (c1 : Fin j → ZMod 2) (hc1_ne : c1 ≠ 0) (hc1_ker : mv' M c1 = 0) :
    Even (Finset.univ.filter (fun c : Fin j → ZMod 2 => mv' M c = 0)).card := by
  refine card_even_of_fpf_involution _ (fun c => c + c1) ?_ ?_ ?_
  · intro c hc
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨Finset.mem_univ _, by rw [mv'_add, hc.2, hc1_ker, add_zero]⟩
  · intro c _
    simp [add_assoc, vec_add_self c1]
  · intro c _ heq
    apply hc1_ne
    have h0 : c + (c + c1) = c + c := congrArg (c + ·) heq
    simpa [← add_assoc, vec_add_self c] using h0

lemma card_preim_eq_ker {m j : ℕ} (M : Matrix (Fin m) (Fin j) (ZMod 2))
    (h : Fin m → ZMod 2) (c0 : Fin j → ZMod 2) (hc0 : mv' M c0 = h) :
    (Finset.univ.filter (fun c : Fin j → ZMod 2 => mv' M c = h)).card =
      (Finset.univ.filter (fun c : Fin j → ZMod 2 => mv' M c = 0)).card := by
  refine Finset.card_bij (fun c _ => c + c0) ?_ ?_ ?_
  · intro c hc
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨Finset.mem_univ _, by rw [mv'_add, hc.2, hc0, vec_add_self h]⟩
  · intro c1 _ c2 _ heq
    have : (c1 + c0) + c0 = (c2 + c0) + c0 := congrArg (· + c0) heq
    simpa [add_assoc, vec_add_self c0] using this
  · intro d hd
    rw [Finset.mem_filter] at hd
    refine ⟨d + c0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [mv'_add, hd.2, hc0, zero_add]
    · simp [add_assoc, vec_add_self c0]

lemma preim_sub_one_mod_two {m j : ℕ} (M : Matrix (Fin m) (Fin j) (ZMod 2))
    (h : Fin m → ZMod 2) (hh : h ≠ 0) :
    ((Finset.univ.filter (fun c : Fin j → ZMod 2 => c ≠ 0 ∧ mv' M c = h)).card - 1) % 2 =
      if (∃ c, mv' M c = h) ∧ (∃ c, c ≠ 0 ∧ mv' M c = 0) then 1 else 0 := by
  classical
  have hfilt : Finset.univ.filter (fun c : Fin j → ZMod 2 => c ≠ 0 ∧ mv' M c = h) =
      Finset.univ.filter (fun c : Fin j → ZMod 2 => mv' M c = h) := by
    ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    intro hmc hc0; subst hc0; rw [mv'_zero] at hmc; exact hh hmc.symm
  rw [hfilt]
  by_cases hex : ∃ c, mv' M c = h
  · obtain ⟨c0, hc0⟩ := hex
    rw [card_preim_eq_ker M h c0 hc0]
    by_cases hker : ∃ c, c ≠ 0 ∧ mv' M c = 0
    · rw [if_pos ⟨⟨c0, hc0⟩, hker⟩]
      obtain ⟨c1, hc1_ne, hc1_ker⟩ := hker
      have heven := card_ker_even_of_ne_zero M c1 hc1_ne hc1_ker
      have hge2 : 2 ≤ (Finset.univ.filter (fun c : Fin j → ZMod 2 => mv' M c = 0)).card := by
        have hsub : ({0, c1} : Finset (Fin j → ZMod 2)) ⊆
            Finset.univ.filter (fun c : Fin j → ZMod 2 => mv' M c = 0) := by
          intro c hc
          rw [Finset.mem_insert, Finset.mem_singleton] at hc
          rw [Finset.mem_filter]
          rcases hc with rfl | rfl
          · exact ⟨Finset.mem_univ _, mv'_zero M⟩
          · exact ⟨Finset.mem_univ _, hc1_ker⟩
        have h2 : ({0, c1} : Finset (Fin j → ZMod 2)).card = 2 := Finset.card_pair hc1_ne.symm
        have := Finset.card_le_card hsub
        omega
      rcases heven with ⟨k, hk⟩
      omega
    · rw [if_neg (fun h' => hker h'.2)]
      have hker1 : Finset.univ.filter (fun c : Fin j → ZMod 2 => mv' M c = 0) = {0} := by
        ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hc; by_contra hne; exact hker ⟨c, hne, hc⟩
        · rintro rfl; exact mv'_zero M
      rw [hker1, Finset.card_singleton]
  · rw [if_neg (fun h' => hex h'.1)]
    have hempty : Finset.univ.filter (fun c : Fin j → ZMod 2 => mv' M c = h) = ∅ := by
      ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hc; exact hex ⟨c, hc⟩
    rw [hempty, Finset.card_empty]

lemma odd_good_mats {m j : ℕ} (hj : 2 ≤ j) (h : Fin m → ZMod 2) (hh : h ≠ 0) :
    Odd (Finset.univ.filter (fun M : Matrix (Fin m) (Fin j) (ZMod 2) =>
      (∃ c, mv' M c = h) ∧ (∃ c, c ≠ 0 ∧ mv' M c = 0))).card := by
  classical
  let Mat := Matrix (Fin m) (Fin j) (ZMod 2)
  let col : Mat → Fin j → (Fin m → ZMod 2) := fun M b a => M a b
  let S_good : Finset Mat := Finset.univ.filter (fun M =>
    (∃ c, mv' M c = h) ∧ (∃ c, c ≠ 0 ∧ mv' M c = 0))
  let S_rk1 : Finset Mat := Finset.univ.filter (fun M =>
    (∀ b : Fin j, col M b = 0 ∨ col M b = h) ∧ (∃ b : Fin j, col M b = h))
  have hrk1_sub : S_rk1 ⊆ S_good := by
    intro M hM
    rw [Finset.mem_filter] at hM ⊢
    obtain ⟨_, hall, ⟨b0, hb0⟩⟩ := hM
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · refine ⟨Pi.single b0 1, ?_⟩
      funext a
      simp only [mv', Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
      exact congrFun hb0 a
    · have hb1_ex : ∃ b1 : Fin j, b1 ≠ b0 := by
        by_cases hb00 : b0 = ⟨0, by omega⟩
        · exact ⟨⟨1, by omega⟩, by rw [hb00]; intro heq; simp [Fin.ext_iff] at heq⟩
        · exact ⟨⟨0, by omega⟩, Ne.symm hb00⟩
      obtain ⟨b1, hb1⟩ := hb1_ex
      rcases hall b1 with h0 | h1
      · refine ⟨Pi.single b1 1, ?_, ?_⟩
        · intro heq
          have : (Pi.single b1 (1 : ZMod 2) : Fin j → ZMod 2) b1 = 0 := congrFun heq b1
          simp at this
        · funext a
          simp only [mv', Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, ↓reduceIte, Pi.zero_apply]
          exact congrFun h0 a
      · refine ⟨Pi.single b0 1 + Pi.single b1 1, ?_, ?_⟩
        · intro heq
          have : (Pi.single b0 (1 : ZMod 2) + Pi.single b1 1 : Fin j → ZMod 2) b0 = 0 :=
            congrFun heq b0
          simp [Pi.single_apply, hb1.symm] at this
        · funext a
          have hsum : mv' M (Pi.single b0 1 + Pi.single b1 1) a = col M b0 a + col M b1 a := by
            rw [mv'_add, Pi.add_apply]
            simp only [mv', col, Pi.single_apply, mul_ite, mul_one, mul_zero,
              Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
          rw [hsum, hb0, h1, Pi.zero_apply]; exact zmod2_add_self (h a)
  have hrk1_card : S_rk1.card = 2 ^ j - 1 := by
    let T : Finset (Fin j → Bool) := Finset.univ.erase (fun _ => false)
    have hbij : S_rk1.card = T.card := by
      refine Finset.card_bij (fun M _ b => decide (col M b = h)) ?_ ?_ ?_
      · intro M hM
        rw [Finset.mem_filter] at hM
        obtain ⟨_, _, ⟨b0, hb0⟩⟩ := hM
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
        intro heq
        have : decide (col M b0 = h) = false := congrFun heq b0
        simp [hb0] at this
      · intro M1 hM1 M2 hM2 heq
        rw [Finset.mem_filter] at hM1 hM2
        ext a b
        have hb := congrFun heq b
        rcases hM1.2.1 b with h10 | h1h <;> rcases hM2.2.1 b with h20 | h2h
        · exact (congrFun h10 a).trans (congrFun h20 a).symm
        · simp [h10, h2h, hh.symm] at hb
        · simp [h1h, h20, hh.symm] at hb
        · exact (congrFun h1h a).trans (congrFun h2h a).symm
      · intro s hs
        rw [Finset.mem_erase] at hs
        have hex : ∃ b : Fin j, s b = true := by
          by_contra hno; apply hs.1; funext b; by_contra hne
          have : s b = true := by cases hsb : s b <;> simp_all
          exact hno ⟨b, this⟩
        let M : Mat := Matrix.of (fun a b => if s b then h a else 0)
        refine ⟨M, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, fun b => ?_, ?_⟩
          · cases hsb : s b
            · left; funext a; simp [col, M, hsb]
            · right; funext a; simp [col, M, hsb]
          · obtain ⟨b0, hb0⟩ := hex
            exact ⟨b0, by funext a; simp [col, M, hb0]⟩
        · funext b
          cases hsb : s b
          · have : col M b = 0 := by funext a; simp [col, M, hsb]
            simp [this, hh.symm]
          · have : col M b = h := by funext a; simp [col, M, hsb]
            simp [this]
    rw [hbij, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hrest_even : Even (S_good \ S_rk1).card := by
    let colNZ : Mat → Finset (Fin j) := fun M => Finset.univ.filter (fun b => col M b ≠ 0)
    have hrest_props : ∀ M ∈ S_good \ S_rk1,
        (colNZ M).Nonempty ∧
          ∀ (hne : (colNZ M).Nonempty),
            (Finset.univ.filter (fun b => col M b ≠ 0 ∧ col M b ≠ col M ((colNZ M).min' hne))).Nonempty := by
      intro M hM
      rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hM
      obtain ⟨⟨_, ⟨c0, hc0⟩, _⟩, hnot_rk1⟩ := hM
      have hnz : (colNZ M).Nonempty := by
        by_contra hem
        rw [Finset.not_nonempty_iff_eq_empty] at hem
        have hM0 : M = 0 := by
          ext a b
          have : b ∉ colNZ M := by rw [hem]; simp
          simp only [colNZ, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at this
          exact congrFun this a
        subst hM0
        have : mv' (0 : Mat) c0 = 0 := by
          funext a; exact Finset.sum_eq_zero fun b _ => by
            change (0 : ZMod 2) * c0 b = 0; exact zero_mul _
        rw [this] at hc0
        exact hh hc0.symm
      refine ⟨hnz, fun hne => ?_⟩
      set a := (colNZ M).min' hne
      have ha_nz : col M a ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
      by_contra hem2
      rw [Finset.not_nonempty_iff_eq_empty] at hem2
      have hall_a : ∀ b : Fin j, col M b = 0 ∨ col M b = col M a := by
        intro b
        have : b ∉ Finset.univ.filter (fun b => col M b ≠ 0 ∧ col M b ≠ col M a) := by
          rw [hem2]; simp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not] at this
        exact this
      have hha : h = col M a := by
        have hmul : mv' M c0 = (∑ b ∈ Finset.univ.filter (fun b => col M b = col M a), c0 b) • col M a := by
          funext r
          simp only [mv', Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b => col M b = col M a)]
          have hzero : ∑ b ∈ Finset.univ.filter (fun b => ¬col M b = col M a), M r b * c0 b = 0 := by
            refine Finset.sum_eq_zero fun b hb => ?_
            have hne' : col M b ≠ col M a := (Finset.mem_filter.mp hb).2
            rcases hall_a b with h0 | h1
            · rw [show M r b = 0 from congrFun h0 r, zero_mul]
            · exact False.elim (hne' h1)
          rw [hzero, add_zero]
          refine Finset.sum_congr rfl fun b hb => ?_
          have heq' : col M b = col M a := (Finset.mem_filter.mp hb).2
          rw [show M r b = col M a r from congrFun heq' r, mul_comm]
        rw [hc0] at hmul
        rcases zmod2_eq_zero_or_one (∑ b ∈ Finset.univ.filter (fun b => col M b = col M a), c0 b) with hs0 | hs1
        · rw [hs0, zero_smul] at hmul; exact False.elim (hh hmul)
        · rw [hs1, one_smul] at hmul; exact hmul
      apply hnot_rk1
      refine ⟨Finset.mem_univ _, fun b => by rw [hha]; exact hall_a b, ⟨a, hha.symm⟩⟩
    let τ : Mat → Mat := fun M =>
      if hnz : (colNZ M).Nonempty then
        let a := (colNZ M).min' hnz
        let S2 := Finset.univ.filter (fun b => col M b ≠ 0 ∧ col M b ≠ col M a)
        if h2 : S2.Nonempty then
          let b := S2.min' h2
          Matrix.of (fun r c => if c = b then M r b + M r a else M r c)
        else M
      else M
    have hτ_spec : ∀ M ∈ S_good \ S_rk1,
        ∃ (a b : Fin j),
          a < b ∧ col M a ≠ 0 ∧ col M b ≠ 0 ∧ col M b ≠ col M a ∧
          (∀ c < a, col M c = 0) ∧
          (∀ c < b, col M c = 0 ∨ col M c = col M a) ∧
          τ M = Matrix.of (fun r c => if c = b then M r b + M r a else M r c) := by
      intro M hM
      obtain ⟨hnz, h2_fn⟩ := hrest_props M hM
      have h2 := h2_fn hnz
      set a := (colNZ M).min' hnz
      set S2 := Finset.univ.filter (fun b => col M b ≠ 0 ∧ col M b ≠ col M a)
      set b := S2.min' h2
      have ha_mem : a ∈ colNZ M := Finset.min'_mem _ hnz
      have hb_mem : b ∈ S2 := Finset.min'_mem _ h2
      have ha_nz : col M a ≠ 0 := (Finset.mem_filter.mp ha_mem).2
      have hb_nz : col M b ≠ 0 := (Finset.mem_filter.mp hb_mem).2.1
      have hb_nea : col M b ≠ col M a := (Finset.mem_filter.mp hb_mem).2.2
      have hab_le : a ≤ b := Finset.min'_le (colNZ M) b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb_nz⟩)
      have hab_ne : a ≠ b := fun heq => hb_nea (by rw [heq])
      have hab_lt : a < b := lt_of_le_of_ne hab_le hab_ne
      refine ⟨a, b, hab_lt, ha_nz, hb_nz, hb_nea, ?_, ?_, ?_⟩
      · intro c hc
        by_contra hcnz
        have := Finset.min'_le (colNZ M) c (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcnz⟩)
        exact not_le_of_gt hc this
      · intro c hc
        by_contra hnot
        push_neg at hnot
        have := Finset.min'_le S2 c (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩)
        exact not_le_of_gt hc this
      · dsimp only [τ]; rw [dif_pos hnz, dif_pos h2]
    have hτ_mv : ∀ (M : Mat) (a b : Fin j), a ≠ b →
        let M' : Mat := Matrix.of (fun r c => if c = b then M r b + M r a else M r c)
        let φ : (Fin j → ZMod 2) → (Fin j → ZMod 2) := fun x i => if i = a then x a + x b else x i
        (∀ x, mv' M' x = mv' M (φ x)) ∧ (∀ x, φ (φ x) = x) ∧ φ 0 = 0 := by
      intro M a b hab M' φ
      refine ⟨?_, ?_, ?_⟩
      · intro x; funext r
        simp only [mv', M', φ, Matrix.of_apply]
        have hba : b ≠ a := hab.symm
        have hb_mem : b ∈ (Finset.univ : Finset (Fin j)).erase a :=
          Finset.mem_erase.mpr ⟨hba, Finset.mem_univ b⟩
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a),
            ← Finset.add_sum_erase ((Finset.univ : Finset (Fin j)).erase a) _ hb_mem]
        symm
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a),
            ← Finset.add_sum_erase ((Finset.univ : Finset (Fin j)).erase a) _ hb_mem]
        have hrest : ∑ i ∈ ((Finset.univ : Finset (Fin j)).erase a).erase b,
              M r i * (if i = a then x a + x b else x i) =
            ∑ i ∈ ((Finset.univ : Finset (Fin j)).erase a).erase b,
              (if i = b then M r b + M r a else M r i) * x i := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_erase, Finset.mem_erase] at hi
          simp [hi.1, hi.2.1]
        rw [hrest, if_pos rfl, if_neg hba, if_neg hab, if_pos rfl]
        ring
      · intro x; funext i
        dsimp only [φ]
        by_cases hia : i = a
        · subst hia; simp [hab.symm, add_assoc, zmod2_add_self]
        · simp [hia]
      · funext i; simp [φ]
    have hτ_mem : ∀ M ∈ S_good \ S_rk1, τ M ∈ S_good \ S_rk1 := by
      intro M hM
      obtain ⟨a, b, hab, ha_nz, hb_nz, hb_nea, _, _, hτeq⟩ := hτ_spec M hM
      obtain ⟨hmv, hφinv, hφ0⟩ := hτ_mv M a b (ne_of_lt hab)
      let φ : (Fin j → ZMod 2) → (Fin j → ZMod 2) := fun x i => if i = a then x a + x b else x i
      rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hM ⊢
      obtain ⟨⟨_, ⟨c0, hc0⟩, ⟨c1, hc1_ne, hc1_ker⟩⟩, hnot_rk1⟩ := hM
      rw [hτeq]
      refine ⟨⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
      · refine ⟨φ c0, ?_⟩
        rw [hmv, hφinv, hc0]
      · refine ⟨φ c1, ?_, ?_⟩
        · intro heq
          have h1 : (fun (x : Fin j → ZMod 2) (i : Fin j) => if i = a then x a + x b else x i)
              ((fun (x : Fin j → ZMod 2) (i : Fin j) => if i = a then x a + x b else x i) c1) =
              (fun (x : Fin j → ZMod 2) (i : Fin j) => if i = a then x a + x b else x i) 0 :=
            congrArg (fun (x : Fin j → ZMod 2) (i : Fin j) => if i = a then x a + x b else x i) heq
          rw [hφinv c1, hφ0] at h1
          exact hc1_ne h1
        · rw [hmv, hφinv, hc1_ker]
      · intro hrk
        obtain ⟨_, hall', _⟩ := hrk
        have hcola : col M a = 0 ∨ col M a = h := by
          have := hall' a
          have heqa : col (Matrix.of (fun r c => if c = b then M r b + M r a else M r c)) a = col M a := by
            funext r; simp [col, ne_of_lt hab]
          rwa [heqa] at this
        have hcolah : col M a = h := hcola.resolve_left ha_nz
        have hcolb' : col M b + col M a = 0 ∨ col M b + col M a = h := by
          have := hall' b
          have heqb : col (Matrix.of (fun r c => if c = b then M r b + M r a else M r c)) b = col M b + col M a := by
            funext r; simp [col]
          rwa [heqb] at this
        rcases hcolb' with h0 | h1
        · apply hb_nea
          have : col M b + col M a + col M a = 0 + col M a := congrArg (· + col M a) h0
          simpa [add_assoc, vec_add_self (col M a)] using this
        · apply hb_nz
          rw [← hcolah] at h1
          have : col M b + col M a + col M a = col M a + col M a := congrArg (· + col M a) h1
          simpa [add_assoc, vec_add_self (col M a)] using this
    have hτ_inv : ∀ M ∈ S_good \ S_rk1, τ (τ M) = M := by
      intro M hM
      obtain ⟨a, b, hab, ha_nz, hb_nz, hb_nea, hlt_a, hlt_b, hτeq⟩ := hτ_spec M hM
      have hτM_mem : τ M ∈ S_good \ S_rk1 := hτ_mem M hM
      obtain ⟨a', b', hab', ha'_nz, hb'_nz, hb'_nea, hlt_a', hlt_b', hτ2eq⟩ := hτ_spec (τ M) hτM_mem
      have hcol_ne : ∀ c : Fin j, c ≠ b → col (τ M) c = col M c := by
        intro c hcb; funext r; rw [hτeq]; simp [col, hcb]
      have hcol_b : col (τ M) b = col M b + col M a := by
        funext r; rw [hτeq]; simp [col]
      have ha_eq : a' = a := by
        rcases lt_trichotomy a' a with hlt | heq | hgt
        · exfalso; apply ha'_nz
          rw [hcol_ne a' (ne_of_lt (lt_trans hlt hab))]; exact hlt_a a' hlt
        · exact heq
        · exfalso
          have := hlt_a' a hgt
          rw [hcol_ne a (ne_of_lt hab)] at this
          exact ha_nz this
      subst a'
      have hcol_a' : col (τ M) a = col M a := hcol_ne a (ne_of_lt hab)
      have hb_eq : b' = b := by
        rcases lt_trichotomy b' b with hlt | heq | hgt
        · exfalso
          have h1 := hlt_b b' hlt
          rw [hcol_ne b' (ne_of_lt hlt)] at hb'_nz hb'_nea
          rw [hcol_a'] at hb'_nea
          rcases h1 with h0 | h2
          · exact hb'_nz h0
          · exact hb'_nea h2
        · exact heq
        · exfalso
          have h1 := hlt_b' b hgt
          rw [hcol_b, hcol_a'] at h1
          rcases h1 with h0 | h2
          · apply hb_nea
            have : col M b + col M a + col M a = 0 + col M a := congrArg (· + col M a) h0
            simpa [add_assoc, vec_add_self (col M a)] using this
          · apply hb_nz
            have : col M b + col M a + col M a = col M a + col M a := congrArg (· + col M a) h2
            simpa [add_assoc, vec_add_self (col M a)] using this
      subst b'
      rw [hτ2eq]
      ext r c
      simp only [Matrix.of_apply]
      by_cases hcb : c = b
      · subst hcb
        rw [if_pos rfl, hτeq]
        simp [ne_of_lt hab, add_assoc, zmod2_add_self]
      · rw [if_neg hcb, hτeq]; simp [hcb]
    have hτ_ne : ∀ M ∈ S_good \ S_rk1, τ M ≠ M := by
      intro M hM heq
      obtain ⟨a, b, _, ha_nz, _, _, _, _, hτeq⟩ := hτ_spec M hM
      apply ha_nz; funext r
      have hr := congrFun (congrFun (hτeq.symm.trans heq) r) b
      simp only [Matrix.of_apply, ↓reduceIte] at hr
      have : M r b + (M r b + M r a) = M r b + M r b := congrArg (M r b + ·) hr
      simpa [← add_assoc, zmod2_add_self] using this
    exact card_even_of_fpf_involution (S_good \ S_rk1) τ hτ_mem hτ_inv hτ_ne
  have hsplit : S_good.card = S_rk1.card + (S_good \ S_rk1).card := by
    have := Finset.card_sdiff_add_card_eq_card hrk1_sub
    omega
  have hrk1_odd : Odd S_rk1.card := by
    rw [hrk1_card]
    have hpow : 2 ≤ 2 ^ j := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    have hev : Even (2 ^ j) := by
      obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      exact ⟨2 ^ j', by rw [pow_succ]; ring⟩
    rcases hev with ⟨k, hk⟩
    exact ⟨k - 1, by omega⟩
  rw [hsplit]
  exact hrk1_odd.add_even hrest_even

lemma odd_coeff_nonzero {m j : ℕ} (hj : 2 ≤ j) (Y : Matrix (Fin m) (Fin j) (ZMod 2))
    (h : Fin m → ZMod 2) (hh : h ≠ 0) :
    Odd (∑ M : Matrix (Fin m) (Fin j) (ZMod 2),
      sgnZ (pairing' M Y) *
        (((Finset.univ.filter (fun c : Fin j → ZMod 2 => c ≠ 0 ∧ mv' M c = h)).card - 1 : ℕ) : ℤ)) := by
  classical
  let Mat := Matrix (Fin m) (Fin j) (ZMod 2)
  let f : Mat → ℕ := fun M =>
    (Finset.univ.filter (fun c : Fin j → ZMod 2 => c ≠ 0 ∧ mv' M c = h)).card - 1
  have hsplit : (∑ M : Mat, sgnZ (pairing' M Y) * (f M : ℤ)) =
      (∑ M : Mat, (f M : ℤ)) + ∑ M : Mat, (sgnZ (pairing' M Y) - 1) * (f M : ℤ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun M _ => by ring
  rw [hsplit]
  have hev2 : Even (∑ M : Mat, (sgnZ (pairing' M Y) - 1) * (f M : ℤ)) := by
    have hterm : ∀ M ∈ (Finset.univ : Finset Mat), Even ((sgnZ (pairing' M Y) - 1) * (f M : ℤ)) :=
      fun M _ => (sgnZ_sub_one_even _).mul_right _
    clear hsplit
    generalize (Finset.univ : Finset Mat) = S at hterm ⊢
    induction S using Finset.induction_on with
    | empty => simp
    | insert M S hM ih =>
      rw [Finset.sum_insert hM]
      exact (hterm M (Finset.mem_insert_self _ _)).add
        (ih fun M' hM' => hterm M' (Finset.mem_insert_of_mem hM'))
  have hodd1 : Odd (∑ M : Mat, (f M : ℤ)) := by
    have hnat : Odd (∑ M : Mat, f M) := by
      have hmod : (∑ M : Mat, f M) % 2 =
          (Finset.univ.filter (fun M : Mat =>
            (∃ c, mv' M c = h) ∧ (∃ c, c ≠ 0 ∧ mv' M c = 0))).card % 2 := by
        rw [Finset.sum_nat_mod]
        have hcongr : ∑ M : Mat, f M % 2 =
            ∑ M : Mat, if (∃ c, mv' M c = h) ∧ (∃ c, c ≠ 0 ∧ mv' M c = 0) then 1 else 0 := by
          refine Finset.sum_congr rfl fun M _ => preim_sub_one_mod_two M h hh
        rw [hcongr, ← Finset.card_filter]
      have ho := Nat.odd_iff.mp (odd_good_mats hj h hh)
      rw [Nat.odd_iff, hmod]
      convert ho
    rcases hnat with ⟨k, hk⟩
    refine ⟨(k : ℤ), ?_⟩
    have : (∑ M : Mat, (f M : ℤ)) = ((∑ M : Mat, f M : ℕ) : ℤ) := by push_cast; rfl
    rw [this, hk]; push_cast; ring
  exact hodd1.add_even hev2

lemma card_mat_ker_c {m j : ℕ} (c : Fin j → ZMod 2) (hc : c ≠ 0) :
    (Finset.univ.filter (fun M : Matrix (Fin m) (Fin j) (ZMod 2) => mv' M c = 0)).card =
      2 ^ (m * (j - 1)) := by
  classical
  have hex : ∃ b0 : Fin j, c b0 = 1 := by
    by_contra hno
    apply hc; funext b
    rcases zmod2_eq_zero_or_one (c b) with h0 | h1
    · exact h0
    · exact False.elim (hno ⟨b, h1⟩)
  obtain ⟨b0, hb0⟩ := hex
  let Rest := {b : Fin j // b ≠ b0}
  have hbij : (Finset.univ.filter (fun M : Matrix (Fin m) (Fin j) (ZMod 2) => mv' M c = 0)).card =
      (Finset.univ : Finset (Fin m → Rest → ZMod 2)).card := by
    refine Finset.card_bij (fun M _ a b => M a b.1) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro M1 hM1 M2 hM2 heq
      rw [Finset.mem_filter] at hM1 hM2
      ext a b
      by_cases hbb0 : b = b0
      · subst b
        have h1 : M1 a b0 = ∑ b' ∈ (Finset.univ : Finset (Fin j)).erase b0, M1 a b' * c b' := by
          have ha := congrFun hM1.2 a
          simp only [mv', Pi.zero_apply] at ha
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ b0), hb0, mul_one] at ha
          have : M1 a b0 + (M1 a b0 + ∑ b' ∈ Finset.univ.erase b0, M1 a b' * c b') = M1 a b0 + 0 :=
            congrArg (M1 a b0 + ·) ha
          simpa [← add_assoc, zmod2_add_self] using this.symm
        have h2 : M2 a b0 = ∑ b' ∈ (Finset.univ : Finset (Fin j)).erase b0, M2 a b' * c b' := by
          have ha := congrFun hM2.2 a
          simp only [mv', Pi.zero_apply] at ha
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ b0), hb0, mul_one] at ha
          have : M2 a b0 + (M2 a b0 + ∑ b' ∈ Finset.univ.erase b0, M2 a b' * c b') = M2 a b0 + 0 :=
            congrArg (M2 a b0 + ·) ha
          simpa [← add_assoc, zmod2_add_self] using this.symm
        rw [h1, h2]
        refine Finset.sum_congr rfl fun b' hb' => ?_
        have hne : b' ≠ b0 := (Finset.mem_erase.mp hb').1
        have hval := congrFun (congrFun heq a) ⟨b', hne⟩
        rw [hval]
      · exact congrFun (congrFun heq a) ⟨b, hbb0⟩
    · intro f _
      let M : Matrix (Fin m) (Fin j) (ZMod 2) := Matrix.of (fun a b =>
        if hbb0 : b = b0 then ∑ b' : Rest, f a b' * c b'.1 else f a ⟨b, hbb0⟩)
      refine ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · funext a
        simp only [mv', Pi.zero_apply]
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ b0), hb0, mul_one]
        have hM0 : M a b0 = ∑ b' : Rest, f a b' * c b'.1 := by simp [M]
        have hrest : ∑ b' ∈ (Finset.univ : Finset (Fin j)).erase b0, M a b' * c b' =
            ∑ b' : Rest, f a b' * c b'.1 := by
          refine Finset.sum_bij (fun b' hb' => ⟨b', (Finset.mem_erase.mp hb').1⟩) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro x1 _ x2 _ h; exact congrArg Subtype.val h
          · intro y _; exact ⟨y.1, Finset.mem_erase.mpr ⟨y.2, Finset.mem_univ _⟩, rfl⟩
          · intro b' hb'
            have hne : b' ≠ b0 := (Finset.mem_erase.mp hb').1
            simp [M, hne]
        rw [hM0, hrest, zmod2_add_self]
      · funext a ⟨b, hb⟩; simp [M, hb]
  rw [hbij, Finset.card_univ, Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hcardR : Fintype.card Rest = j - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  rw [hcardR, ← pow_mul, mul_comm]

lemma ker_c_pairing_zero_iff {m j : ℕ} (Y : Matrix (Fin m) (Fin j) (ZMod 2))
    (c : Fin j → ZMod 2) (b0 : Fin j) (hb0 : c b0 = 1) :
    (∀ M : Matrix (Fin m) (Fin j) (ZMod 2), mv' M c = 0 → pairing' M Y = 0) ↔
      (∀ a : Fin m, ∀ b : Fin j, Y a b = Y a b0 * c b) := by
  constructor
  · intro hall a b
    by_cases hbb0 : b = b0
    · subst hbb0; rw [hb0, mul_one]
    · let M : Matrix (Fin m) (Fin j) (ZMod 2) := Matrix.of (fun r s =>
        if r = a ∧ s = b then 1 else if r = a ∧ s = b0 then c b else 0)
      have hker : mv' M c = 0 := by
        funext r
        simp only [mv', Pi.zero_apply]
        by_cases hra : r = a
        · subst hra
          have hb_mem : b ∈ (Finset.univ : Finset (Fin j)).erase b0 :=
            Finset.mem_erase.mpr ⟨hbb0, Finset.mem_univ _⟩
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ b0),
              ← Finset.add_sum_erase ((Finset.univ : Finset (Fin j)).erase b0) _ hb_mem]
          have hrest : ∑ s ∈ ((Finset.univ : Finset (Fin j)).erase b0).erase b, M r s * c s = 0 := by
            refine Finset.sum_eq_zero fun s hs => ?_
            rw [Finset.mem_erase, Finset.mem_erase] at hs
            simp [M, hs.1, hs.2.1]
          rw [hrest, add_zero]
          simp [M, hbb0, Ne.symm hbb0, hb0, zmod2_add_self]
        · refine Finset.sum_eq_zero fun s _ => ?_
          simp [M, hra]
      have hp := hall M hker
      simp only [pairing'] at hp
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)] at hp
      have hother_r : ∑ r ∈ (Finset.univ : Finset (Fin m)).erase a, ∑ s : Fin j, M r s * Y r s = 0 := by
        refine Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun s _ => ?_
        simp [M, (Finset.mem_erase.mp hr).1]
      rw [hother_r, add_zero] at hp
      have hb_mem : b ∈ (Finset.univ : Finset (Fin j)).erase b0 :=
        Finset.mem_erase.mpr ⟨hbb0, Finset.mem_univ _⟩
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ b0),
          ← Finset.add_sum_erase ((Finset.univ : Finset (Fin j)).erase b0) _ hb_mem] at hp
      have hother_s : ∑ s ∈ ((Finset.univ : Finset (Fin j)).erase b0).erase b, M a s * Y a s = 0 := by
        refine Finset.sum_eq_zero fun s hs => ?_
        rw [Finset.mem_erase, Finset.mem_erase] at hs
        simp [M, hs.1, hs.2.1]
      rw [hother_s, add_zero] at hp
      simp only [M, Matrix.of_apply, true_and, hbb0, Ne.symm hbb0, ↓reduceIte, one_mul] at hp
      have : c b * Y a b0 + (c b * Y a b0 + Y a b) = c b * Y a b0 + 0 :=
        congrArg (c b * Y a b0 + ·) hp
      simpa [← add_assoc, zmod2_add_self, mul_comm] using this
  · intro hY M hker
    simp only [pairing']
    refine Finset.sum_eq_zero fun a _ => ?_
    have hrow : ∑ b : Fin j, M a b * Y a b = Y a b0 * (∑ b : Fin j, M a b * c b) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hY a b]; ring
    rw [hrow]
    have ha := congrFun hker a
    simp only [mv', Pi.zero_apply] at ha
    rw [ha, mul_zero]

lemma T1_eval {m j : ℕ} (Y : Matrix (Fin m) (Fin j) (ZMod 2))
    (ht : 1 ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
      (Set.range (fun b : Fin j => fun a : Fin m => Y a b)))) :
    ∑ M : Matrix (Fin m) (Fin j) (ZMod 2),
      sgnZ (pairing' M Y) *
        ((Finset.univ.filter (fun c : Fin j → ZMod 2 => mv' M c = 0)).card : ℤ) =
      if Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        (Set.range (fun b : Fin j => fun a : Fin m => Y a b))) = 1
      then (2 ^ (m * (j - 1)) : ℤ) else 0 := by
  classical
  let Mat := Matrix (Fin m) (Fin j) (ZMod 2)
  let F := ZMod 2
  let S := Submodule.span F (Set.range (fun b : Fin j => fun a : Fin m => Y a b))
  change 1 ≤ Module.finrank F S at ht
  have hYne : Y ≠ 0 := by
    intro h0; subst h0
    have hS0 : S = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro v ⟨b, rfl⟩; funext a; rfl
    have : Module.finrank F S = 0 := by rw [hS0, finrank_bot]
    omega
  have hT2 : ∑ M : Mat, sgnZ (pairing' M Y) = 0 := by
    rw [sum_sgnZ_subspace Finset.univ (fun _ _ _ _ => Finset.mem_univ _)
        (fun M => pairing' M Y) (fun M1 M2 => pairing'_add M1 M2 Y)]
    rw [if_neg]
    intro hall
    apply hYne; ext a b
    let E : Mat := Matrix.of (fun r s => if r = a ∧ s = b then 1 else 0)
    have hE := hall E (Finset.mem_univ _)
    have hp : pairing' E Y = Y a b := by
      simp only [pairing', E, Matrix.of_apply]
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
      have hr : ∑ r ∈ (Finset.univ : Finset (Fin m)).erase a,
          ∑ s : Fin j, (if r = a ∧ s = b then (1 : ZMod 2) else 0) * Y r s = 0 := by
        refine Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun s _ => ?_
        simp [(Finset.mem_erase.mp hr).1]
      rw [hr, add_zero, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ b)]
      have hs : ∑ s ∈ (Finset.univ : Finset (Fin j)).erase b,
          (if a = a ∧ s = b then (1 : ZMod 2) else 0) * Y a s = 0 := by
        refine Finset.sum_eq_zero fun s hs => ?_
        simp [(Finset.mem_erase.mp hs).1]
      rw [hs, add_zero]; simp
    rw [hp] at hE; exact hE
  have hswap : (∑ M : Mat, sgnZ (pairing' M Y) *
        ((Finset.univ.filter (fun c : Fin j → F => mv' M c = 0)).card : ℤ)) =
      ∑ c : Fin j → F, ∑ M ∈ Finset.univ.filter (fun M : Mat => mv' M c = 0),
        sgnZ (pairing' M Y) := by
    have h1 : ∀ M : Mat, sgnZ (pairing' M Y) *
          ((Finset.univ.filter (fun c : Fin j → F => mv' M c = 0)).card : ℤ) =
        ∑ c : Fin j → F, if mv' M c = 0 then sgnZ (pairing' M Y) else 0 := by
      intro M
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_filter]
  rw [hswap]
  have hterm : ∀ c : Fin j → F,
      ∑ M ∈ Finset.univ.filter (fun M : Mat => mv' M c = 0), sgnZ (pairing' M Y) =
        if c ≠ 0 ∧ (∀ M : Mat, mv' M c = 0 → pairing' M Y = 0)
        then (2 ^ (m * (j - 1)) : ℤ) else 0 := by
    intro c
    by_cases hc0 : c = 0
    · subst hc0
      rw [if_neg (fun h => h.1 rfl)]
      have huniv : Finset.univ.filter (fun M : Mat => mv' M 0 = 0) = Finset.univ := by
        ext M; simp [mv'_zero]
      rw [huniv]; exact hT2
    · have hadd : ∀ M1 ∈ Finset.univ.filter (fun M : Mat => mv' M c = 0),
          ∀ M2 ∈ Finset.univ.filter (fun M : Mat => mv' M c = 0),
          M1 + M2 ∈ Finset.univ.filter (fun M : Mat => mv' M c = 0) := by
        intro M1 h1 M2 h2
        rw [Finset.mem_filter] at h1 h2 ⊢
        exact ⟨Finset.mem_univ _, by rw [mv'_add_mat, h1.2, h2.2, add_zero]⟩
      rw [sum_sgnZ_subspace _ hadd (fun M => pairing' M Y) (fun M1 M2 => pairing'_add M1 M2 Y)]
      by_cases hall : ∀ M : Mat, mv' M c = 0 → pairing' M Y = 0
      · have hall' : ∀ M ∈ Finset.univ.filter (fun M : Mat => mv' M c = 0), pairing' M Y = 0 :=
          fun M hM => hall M (Finset.mem_filter.mp hM).2
        rw [if_pos hall', if_pos ⟨hc0, hall⟩, card_mat_ker_c c hc0]; push_cast; rfl
      · have hall' : ¬∀ M ∈ Finset.univ.filter (fun M : Mat => mv' M c = 0), pairing' M Y = 0 :=
          fun h => hall (fun M hM => h M (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM⟩))
        rw [if_neg hall', if_neg (fun h => hall h.2)]
  simp_rw [hterm]
  by_cases ht1 : Module.finrank F S = 1
  · rw [if_pos ht1]
    have hcol_ex : ∃ b1 : Fin j, (fun a : Fin m => Y a b1) ≠ 0 := by
      by_contra hno; push_neg at hno
      apply hYne; ext a b; exact congrFun (hno b) a
    obtain ⟨b1, hb1⟩ := hcol_ex
    let u : Fin m → F := fun a => Y a b1
    have hS_eq : S = Submodule.span F ({u} : Set (Fin m → F)) := by
      have hle : Submodule.span F ({u} : Set (Fin m → F)) ≤ S := by
        rw [Submodule.span_le]
        rintro _ rfl; exact Submodule.subset_span ⟨b1, rfl⟩
      have hfin_u : Module.finrank F (Submodule.span F ({u} : Set (Fin m → F))) = 1 :=
        finrank_span_singleton hb1
      exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin_u, ht1])).symm
    have hcol_mult : ∀ b : Fin j, ∃ α : F, (fun a : Fin m => Y a b) = α • u := by
      intro b
      have hmem : (fun a : Fin m => Y a b) ∈ Submodule.span F ({u} : Set (Fin m → F)) := by
        rw [← hS_eq]; exact Submodule.subset_span ⟨b, rfl⟩
      obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp hmem
      exact ⟨α, hα.symm⟩
    let c0 : Fin j → F := fun b => (hcol_mult b).choose
    have hY_fact : ∀ a : Fin m, ∀ b : Fin j, Y a b = u a * c0 b := by
      intro a b
      have h := congrFun (hcol_mult b).choose_spec a
      simp only [Pi.smul_apply, smul_eq_mul] at h
      rw [h, mul_comm]
    have hc0_b1 : c0 b1 = 1 := by
      have ha_ex : ∃ a0 : Fin m, u a0 = 1 := by
        by_contra hno; apply hb1; funext a
        rcases zmod2_eq_zero_or_one (u a) with h0 | h1
        · exact h0
        · exact False.elim (hno ⟨a, h1⟩)
      obtain ⟨a0, ha0⟩ := ha_ex
      have h := hY_fact a0 b1
      change u a0 = u a0 * c0 b1 at h
      rw [ha0, one_mul] at h; exact h.symm
    have hc0_ne : c0 ≠ 0 := fun h0 => by have := congrFun h0 b1; rw [hc0_b1] at this; exact one_ne_zero this
    have huniq : ∀ c : Fin j → F,
        (c ≠ 0 ∧ (∀ M : Mat, mv' M c = 0 → pairing' M Y = 0)) ↔ c = c0 := by
      intro c
      constructor
      · rintro ⟨hcne, hall⟩
        have hb_ex : ∃ b0 : Fin j, c b0 = 1 := by
          by_contra hno; apply hcne; funext b
          rcases zmod2_eq_zero_or_one (c b) with h0 | h1
          · exact h0
          · exact False.elim (hno ⟨b, h1⟩)
        obtain ⟨b0, hb0⟩ := hb_ex
        have hYeq := (ker_c_pairing_zero_iff Y c b0 hb0).mp hall
        have ha_ex : ∃ a0 : Fin m, u a0 = 1 := by
          by_contra hno; apply hb1; funext a
          rcases zmod2_eq_zero_or_one (u a) with h0 | h1
          · exact h0
          · exact False.elim (hno ⟨a, h1⟩)
        obtain ⟨a0, ha0⟩ := ha_ex
        have hcb0 : c0 b0 = 1 := by
          have hb1' := hYeq a0 b1
          rw [hY_fact a0 b1, hY_fact a0 b0, ha0, one_mul, one_mul, hc0_b1] at hb1'
          rcases zmod2_eq_zero_or_one (c0 b0) with h0 | h1
          · rw [h0, zero_mul] at hb1'; exact False.elim (one_ne_zero hb1')
          · exact h1
        funext b
        have hb' := hYeq a0 b
        rw [hY_fact a0 b, hY_fact a0 b0, ha0, one_mul, one_mul, hcb0, one_mul] at hb'
        exact hb'.symm
      · rintro rfl
        refine ⟨hc0_ne, (ker_c_pairing_zero_iff Y c0 b1 hc0_b1).mpr ?_⟩
        intro a b
        rw [hY_fact a b, hY_fact a b1, hc0_b1, mul_one]
    have hcongr : ∀ c : Fin j → F,
        (if c ≠ 0 ∧ (∀ M : Mat, mv' M c = 0 → pairing' M Y = 0) then (2 ^ (m * (j - 1)) : ℤ) else 0) =
        if c = c0 then (2 ^ (m * (j - 1)) : ℤ) else 0 := by
      intro c; by_cases h : c = c0
      · rw [if_pos h, if_pos ((huniq c).mpr h)]
      · rw [if_neg h, if_neg (fun h' => h ((huniq c).mp h'))]
    simp_rw [hcongr]; simp
  · rw [if_neg ht1]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg]
    rintro ⟨hcne, hall⟩
    have hb_ex : ∃ b0 : Fin j, c b0 = 1 := by
      by_contra hno; apply hcne; funext b
      rcases zmod2_eq_zero_or_one (c b) with h0 | h1
      · exact h0
      · exact False.elim (hno ⟨b, h1⟩)
    obtain ⟨b0, hb0⟩ := hb_ex
    have hYeq := (ker_c_pairing_zero_iff Y c b0 hb0).mp hall
    have hle : S ≤ Submodule.span F ({fun a : Fin m => Y a b0} : Set (Fin m → F)) := by
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      show (fun a : Fin m => Y a b) ∈ Submodule.span F ({fun a : Fin m => Y a b0} : Set (Fin m → F))
      rw [Submodule.mem_span_singleton]
      refine ⟨c b, ?_⟩
      funext a; simp only [Pi.smul_apply, smul_eq_mul]; rw [hYeq a b, mul_comm]
    have hfin_le := Submodule.finrank_mono hle
    have hfin_1 : Module.finrank F (Submodule.span F ({fun a : Fin m => Y a b0} : Set (Fin m → F))) ≤ 1 := by
      by_cases h0 : (fun a : Fin m => Y a b0) = 0
      · rw [h0, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]; omega
      · rw [finrank_span_singleton h0]
    exact ht1 (le_antisymm (le_trans hfin_le hfin_1) ht)

def dotV {m : ℕ} (u v : Fin m → ZMod 2) : ZMod 2 := ∑ a : Fin m, u a * v a

lemma dotV_add_left {m : ℕ} (u1 u2 v : Fin m → ZMod 2) :
    dotV (u1 + u2) v = dotV u1 v + dotV u2 v := by
  simp only [dotV, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma card_submodule_eq_pow {m : ℕ} (U : Submodule (ZMod 2) (Fin m → ZMod 2))
    [DecidablePred (fun v : Fin m → ZMod 2 => v ∈ U)] :
    (Finset.univ.filter (fun v : Fin m → ZMod 2 => v ∈ U)).card = 2 ^ (Module.finrank (ZMod 2) U) := by
  classical
  have h1 : (Finset.univ.filter (fun v : Fin m → ZMod 2 => v ∈ U)).card = Fintype.card U := by
    refine Finset.card_bij (fun v hv => ⟨v, (Finset.mem_filter.mp hv).2⟩) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro _ _ _ _ h; exact congrArg Subtype.val h
    · intro u _; exact ⟨u.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.2⟩, rfl⟩
  rw [h1]
  have h2 := Module.card_eq_pow_finrank (K := ZMod 2) (V := U)
  rw [ZMod.card] at h2
  exact h2

lemma sum_indep_J {m : ℕ} : ∀ (t : ℕ) (W : Submodule (ZMod 2) (Fin m → ZMod 2))
    (y : Fin t → Fin m → ZMod 2)
    [DecidablePred (fun v : Fin t → Fin m → ZMod 2 => (∀ r, v r ∈ W) ∧ LinearIndependent (ZMod 2) v)],
    Function.Surjective (fun v : W => fun r : Fin t => dotV v.1 (y r)) →
    ∑ v ∈ Finset.univ.filter (fun v : Fin t → Fin m → ZMod 2 =>
        (∀ r, v r ∈ W) ∧ LinearIndependent (ZMod 2) v),
      sgnZ (∑ r : Fin t, dotV (v r) (y r)) =
    (-1 : ℤ) ^ t * (2 : ℤ) ^ (t * (t - 1) / 2) := by
  intro t
  induction t with
  | zero =>
    intro W y _ _
    have hfilt : Finset.univ.filter (fun v : Fin 0 → Fin m → ZMod 2 =>
        (∀ r, v r ∈ W) ∧ LinearIndependent (ZMod 2) v) = {Fin.elim0} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro _; funext r; exact Fin.elim0 r
      · rintro rfl; exact ⟨fun r => Fin.elim0 r, linearIndependent_empty_type⟩
    rw [hfilt, Finset.sum_singleton]; simp [sgnZ]
  | succ t ih =>
    intro W y instDec hsurj
    classical
    let F := ZMod 2
    let A := Fin m → F
    let yInit : Fin t → A := fun r => y r.castSucc
    let yLast : A := y (Fin.last t)
    let fLast : A →ₗ[F] F :=
      { toFun := fun v => dotV v yLast
        map_add' := fun u v => dotV_add_left u v yLast
        map_smul' := fun α v => by
          change dotV (α • v) yLast = α * dotV v yLast
          simp only [dotV, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          change α * v a * yLast a = α * (v a * yLast a); ring }
    let W' : Submodule F A := W ⊓ LinearMap.ker fLast
    have hsurj' : Function.Surjective (fun v : W' => fun r : Fin t => dotV v.1 (yInit r)) := by
      intro target
      let target' : Fin (t + 1) → F := Fin.snoc target 0
      obtain ⟨⟨v, hvW⟩, hv⟩ := hsurj target'
      have hvLast : dotV v yLast = 0 := by
        have := congrFun hv (Fin.last t)
        simpa [yLast, target'] using this
      refine ⟨⟨v, ⟨hvW, hvLast⟩⟩, ?_⟩
      funext r
      have := congrFun hv r.castSucc
      simpa [yInit, target'] using this
    let S_big := Finset.univ.filter (fun v : Fin (t + 1) → A =>
      (∀ r, v r ∈ W) ∧ LinearIndependent F v)
    let S_init := Finset.univ.filter (fun v : Fin t → A =>
      (∀ r, v r ∈ W) ∧ LinearIndependent F v)
    let S_init' := Finset.univ.filter (fun v : Fin t → A =>
      (∀ r, v r ∈ W') ∧ LinearIndependent F v)
    have hsnoc_split : ∑ v ∈ S_big, sgnZ (∑ r : Fin (t + 1), dotV (v r) (y r)) =
        ∑ v ∈ S_init, sgnZ (∑ r : Fin t, dotV (v r) (yInit r)) *
          ∑ w ∈ Finset.univ.filter (fun w : A => w ∈ W ∧ w ∉ Submodule.span F (Set.range v)),
            sgnZ (dotV w yLast) := by
      have hpair : ∑ v ∈ S_big, sgnZ (∑ r : Fin (t + 1), dotV (v r) (y r)) =
          ∑ p ∈ S_init.sigma (fun v =>
              Finset.univ.filter (fun w : A => w ∈ W ∧ w ∉ Submodule.span F (Set.range v))),
            sgnZ (∑ r : Fin t, dotV (p.1 r) (yInit r)) * sgnZ (dotV p.2 yLast) := by
        refine Finset.sum_bij (fun v _ => ⟨fun r => v r.castSucc, v (Fin.last t)⟩) ?_ ?_ ?_ ?_
        · intro v hv
          rw [Finset.mem_filter] at hv
          obtain ⟨_, hvW, hvLI⟩ := hv
          rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter]
          refine ⟨⟨Finset.mem_univ _, fun r => hvW r.castSucc,
              hvLI.comp Fin.castSucc (Fin.castSucc_injective t)⟩,
            Finset.mem_univ _, hvW (Fin.last t), ?_⟩
          intro hmem
          rw [Submodule.mem_span_range_iff_exists_fun F] at hmem
          obtain ⟨c, hc⟩ := hmem
          let c' : Fin (t + 1) → F := Fin.snoc c 1
          have hsum0 : ∑ r : Fin (t + 1), c' r • v r = 0 := by
            rw [Fin.sum_univ_castSucc]
            simp only [c', Fin.snoc_castSucc, Fin.snoc_last, one_smul]
            rw [hc, vec_add_self]
          have h0 := Fintype.linearIndependent_iff.mp hvLI c' hsum0 (Fin.last t)
          simp [c'] at h0
        · intro v1 _ v2 _ heq
          have h1 : (fun r : Fin t => v1 r.castSucc) = (fun r : Fin t => v2 r.castSucc) :=
            congrArg Sigma.fst heq
          have h2 : v1 (Fin.last t) = v2 (Fin.last t) := by
            have := congrArg Sigma.snd heq; simpa using this
          funext r
          refine Fin.lastCases h2 (fun r' => congrFun h1 r') r
        · rintro ⟨v, w⟩ hp
          rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter] at hp
          obtain ⟨⟨_, hvW, hvLI⟩, _, hwW, hw_not⟩ := hp
          refine ⟨Fin.snoc v w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
          · intro r; refine Fin.lastCases (by simpa using hwW) (fun r' => by simpa using hvW r') r
          · rw [Fintype.linearIndependent_iff]
            intro c hc
            rw [Fin.sum_univ_castSucc] at hc
            simp only [Fin.snoc_castSucc, Fin.snoc_last] at hc
            have hclast : c (Fin.last t) = 0 := by
              by_contra hne
              have h1 : c (Fin.last t) = 1 := (zmod2_eq_zero_or_one _).resolve_left hne
              rw [h1, one_smul] at hc
              have hw_eq : w = ∑ r : Fin t, c r.castSucc • v r := by
                have := congrArg (· + w) hc
                simpa [add_assoc, vec_add_self w] using this.symm
              apply hw_not
              dsimp only
              rw [hw_eq]
              exact Submodule.sum_mem (Submodule.span F (Set.range v)) fun r _ =>
                Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range.mpr ⟨r, rfl⟩))
            rw [hclast, zero_smul, add_zero] at hc
            have hinit := Fintype.linearIndependent_iff.mp hvLI (fun r => c r.castSucc) hc
            intro r
            exact Fin.lastCases hclast hinit r
          · ext1
            · funext r; simp
            · simp
        · intro v _
          rw [Fin.sum_univ_castSucc, sgnZ_add]
      rw [hpair, Finset.sum_sigma]
      refine Finset.sum_congr rfl fun v _ => ?_
      dsimp only
      rw [Finset.mul_sum]
    rw [hsnoc_split]
    have hW_sum : ∑ w ∈ Finset.univ.filter (fun w : A => w ∈ W), sgnZ (dotV w yLast) = 0 := by
      have hadd : ∀ u ∈ Finset.univ.filter (fun w : A => w ∈ W),
          ∀ v ∈ Finset.univ.filter (fun w : A => w ∈ W),
          u + v ∈ Finset.univ.filter (fun w : A => w ∈ W) := by
        intro u hu v hv
        rw [Finset.mem_filter] at hu hv ⊢
        exact ⟨Finset.mem_univ _, W.add_mem hu.2 hv.2⟩
      rw [sum_sgnZ_subspace _ hadd (fun w => dotV w yLast) (fun u v => dotV_add_left u v yLast)]
      rw [if_neg]
      intro hall
      obtain ⟨⟨w0, hw0W⟩, hw0⟩ := hsurj (Pi.single (Fin.last t) 1)
      have h0 := hall w0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw0W⟩)
      have h1 : dotV w0 yLast = 1 := by
        have := congrFun hw0 (Fin.last t); simpa [yLast] using this
      rw [h0] at h1; exact zero_ne_one h1
    have hinner : ∀ v ∈ S_init,
        ∑ w ∈ Finset.univ.filter (fun w : A => w ∈ W ∧ w ∉ Submodule.span F (Set.range v)),
          sgnZ (dotV w yLast) =
        if ∀ r : Fin t, v r ∈ W' then -((2 : ℤ) ^ t) else 0 := by
      intro v hv
      rw [Finset.mem_filter] at hv
      obtain ⟨_, hvW, hvLI⟩ := hv
      let U := Submodule.span F (Set.range v)
      have hUW : U ≤ W := by
        rw [Submodule.span_le]; rintro _ ⟨r, rfl⟩; exact hvW r
      have hsplitW : (∑ w ∈ Finset.univ.filter (fun w : A => w ∈ W), sgnZ (dotV w yLast)) =
          (∑ w ∈ Finset.univ.filter (fun w : A => w ∈ W ∧ w ∈ U), sgnZ (dotV w yLast)) +
          (∑ w ∈ Finset.univ.filter (fun w : A => w ∈ W ∧ w ∉ U), sgnZ (dotV w yLast)) := by
        have hdisj : Disjoint (Finset.univ.filter (fun w : A => w ∈ W ∧ w ∈ U))
            (Finset.univ.filter (fun w : A => w ∈ W ∧ w ∉ U)) := by
          rw [Finset.disjoint_left]; intro w h1 h2
          exact (Finset.mem_filter.mp h2).2.2 (Finset.mem_filter.mp h1).2.2
        rw [← Finset.sum_union hdisj]
        congr 1; ext w; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      have hWU_eq : Finset.univ.filter (fun w : A => w ∈ W ∧ w ∈ U) =
          Finset.univ.filter (fun w : A => w ∈ U) := by
        ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
        exact fun hw => hUW hw
      rw [hW_sum, hWU_eq] at hsplitW
      have hU_add : ∀ u ∈ Finset.univ.filter (fun w : A => w ∈ U),
          ∀ u' ∈ Finset.univ.filter (fun w : A => w ∈ U),
          u + u' ∈ Finset.univ.filter (fun w : A => w ∈ U) := by
        intro u hu u' hu'
        rw [Finset.mem_filter] at hu hu' ⊢
        exact ⟨Finset.mem_univ _, U.add_mem hu.2 hu'.2⟩
      have hU_sum := sum_sgnZ_subspace (Finset.univ.filter (fun w : A => w ∈ U)) hU_add
        (fun w => dotV w yLast) (fun u u' => dotV_add_left u u' yLast)
      have hU_card : (Finset.univ.filter (fun w : A => w ∈ U)).card = 2 ^ t := by
        rw [card_submodule_eq_pow U, finrank_span_eq_card hvLI, Fintype.card_fin]
      have hiff : (∀ w ∈ Finset.univ.filter (fun w : A => w ∈ U), dotV w yLast = 0) ↔
          (∀ r : Fin t, v r ∈ W') := by
        constructor
        · intro hall r
          exact ⟨hvW r, hall (v r) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Submodule.subset_span ⟨r, rfl⟩⟩)⟩
        · intro hall w hw
          have hwU : w ∈ U := (Finset.mem_filter.mp hw).2
          rw [Submodule.mem_span_range_iff_exists_fun F] at hwU
          obtain ⟨c, rfl⟩ := hwU
          have hlin : dotV (∑ r : Fin t, c r • v r) yLast = ∑ r : Fin t, c r * dotV (v r) yLast := by
            simp only [dotV, Finset.sum_apply, Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ => ?_
            change c r * v r a * yLast a = c r * (v r a * yLast a); ring
          rw [hlin]
          exact Finset.sum_eq_zero fun r _ => by
            have h0 : dotV (v r) yLast = 0 := (hall r).2
            rw [h0, mul_zero]
      rw [hU_sum, hU_card] at hsplitW
      by_cases hcond : ∀ r : Fin t, v r ∈ W'
      · rw [if_pos hcond]
        rw [if_pos (hiff.mpr hcond)] at hsplitW
        push_cast at hsplitW; linarith
      · rw [if_neg hcond]
        rw [if_neg (fun h => hcond (hiff.mp h))] at hsplitW
        linarith
    rw [Finset.sum_congr rfl fun v hv => by rw [hinner v hv]]
    have hfilt_eq : ∑ v ∈ S_init,
          sgnZ (∑ r : Fin t, dotV (v r) (yInit r)) * (if ∀ r : Fin t, v r ∈ W' then -((2 : ℤ) ^ t) else 0) =
        -((2 : ℤ) ^ t) * ∑ v ∈ S_init', sgnZ (∑ r : Fin t, dotV (v r) (yInit r)) := by
      have hterm' : ∀ v ∈ S_init,
          sgnZ (∑ r : Fin t, dotV (v r) (yInit r)) * (if ∀ r : Fin t, v r ∈ W' then -((2 : ℤ) ^ t) else 0) =
          if ∀ r : Fin t, v r ∈ W' then -((2 : ℤ) ^ t) * sgnZ (∑ r : Fin t, dotV (v r) (yInit r)) else 0 := by
        intro v _; split_ifs <;> ring
      rw [Finset.sum_congr rfl hterm', ← Finset.sum_filter, ← Finset.mul_sum]
      refine congrArg (-((2 : ℤ) ^ t) * ·) (Finset.sum_congr ?_ fun _ _ => rfl)
      ext v
      simp only [S_init, S_init', Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨_, hLI⟩, hW'⟩; exact ⟨hW', hLI⟩
      · rintro ⟨hW', hLI⟩; exact ⟨⟨fun r => (hW' r).1, hLI⟩, hW'⟩
    rw [hfilt_eq, ih W' yInit hsurj']
    have hexp : t + t * (t - 1) / 2 = (t + 1) * t / 2 := by
      have h1 : (t + 1) * t = t * (t - 1) + 2 * t := by
        cases t with
        | zero => simp
        | succ t' => simp; ring
      rw [h1, Nat.add_mul_div_left _ _ (by omega)]; ring
    calc -((2 : ℤ) ^ t) * ((-1 : ℤ) ^ t * (2 : ℤ) ^ (t * (t - 1) / 2))
        = ((-1 : ℤ) * (-1 : ℤ) ^ t) * ((2 : ℤ) ^ t * (2 : ℤ) ^ (t * (t - 1) / 2)) := by ring
      _ = (-1 : ℤ) ^ (t + 1) * (2 : ℤ) ^ (t + t * (t - 1) / 2) := by
          rw [← pow_succ', ← pow_add]
      _ = (-1 : ℤ) ^ (t + 1) * (2 : ℤ) ^ ((t + 1) * t / 2) := by rw [hexp]
      _ = (-1 : ℤ) ^ (t + 1) * (2 : ℤ) ^ ((t + 1) * (t + 1 - 1) / 2) := by simp

lemma sum_indep_peel {m t : ℕ} (y : Fin t → Fin m → ZMod 2)
    (hsurj : Function.Surjective (fun v : (⊤ : Submodule (ZMod 2) (Fin m → ZMod 2)) =>
      fun r : Fin t => dotV v.1 (y r))) :
    ∀ (s : ℕ) (hs : t ≤ s)
      [DecidablePred (fun v : Fin s → Fin m → ZMod 2 => LinearIndependent (ZMod 2) v)],
      ∑ v ∈ Finset.univ.filter (fun v : Fin s → Fin m → ZMod 2 => LinearIndependent (ZMod 2) v),
        sgnZ (∑ r : Fin t, dotV (v ⟨r.val, by omega⟩) (y r)) =
      (-1 : ℤ) ^ t * (2 : ℤ) ^ (t * (t - 1) / 2) *
        ∏ i ∈ Finset.Ico t s, ((2 ^ m : ℤ) - (2 ^ i : ℤ)) := by
  intro s
  induction s with
  | zero =>
    intro hs instDec
    classical
    have ht0 : t = 0 := by omega
    subst ht0
    have h0 := sum_indep_J 0 ⊤ y hsurj
    have hfilt : Finset.univ.filter (fun v : Fin 0 → Fin m → ZMod 2 => LinearIndependent (ZMod 2) v) =
        Finset.univ.filter (fun v : Fin 0 → Fin m → ZMod 2 =>
          (∀ r, v r ∈ (⊤ : Submodule (ZMod 2) (Fin m → ZMod 2))) ∧ LinearIndependent (ZMod 2) v) := by
      ext v; simp
    rw [hfilt, h0]; simp
  | succ s ih =>
    intro hs instDec
    classical
    by_cases hts : t = s + 1
    · subst hts
      have h0 := sum_indep_J (s + 1) ⊤ y hsurj
      have hfilt : Finset.univ.filter (fun v : Fin (s + 1) → Fin m → ZMod 2 => LinearIndependent (ZMod 2) v) =
          Finset.univ.filter (fun v : Fin (s + 1) → Fin m → ZMod 2 =>
            (∀ r, v r ∈ (⊤ : Submodule (ZMod 2) (Fin m → ZMod 2))) ∧ LinearIndependent (ZMod 2) v) := by
        ext v; simp
      rw [hfilt, h0]; simp
    · have hts' : t ≤ s := by omega
      let F := ZMod 2
      let A := Fin m → F
      let S_big := Finset.univ.filter (fun v : Fin (s + 1) → A => LinearIndependent F v)
      let S_init := Finset.univ.filter (fun v : Fin s → A => LinearIndependent F v)
      have hsplit : ∑ v ∈ S_big, sgnZ (∑ r : Fin t, dotV (v ⟨r.val, by omega⟩) (y r)) =
          ∑ v ∈ S_init, sgnZ (∑ r : Fin t, dotV (v ⟨r.val, by omega⟩) (y r)) *
            ((Finset.univ.filter (fun w : A => w ∉ Submodule.span F (Set.range v))).card : ℤ) := by
        have hpair : ∑ v ∈ S_big, sgnZ (∑ r : Fin t, dotV (v ⟨r.val, by omega⟩) (y r)) =
            ∑ p ∈ S_init.sigma (fun v => Finset.univ.filter (fun w : A => w ∉ Submodule.span F (Set.range v))),
              sgnZ (∑ r : Fin t, dotV (p.1 ⟨r.val, by omega⟩) (y r)) := by
          refine Finset.sum_bij (fun v _ => ⟨fun r => v r.castSucc, v (Fin.last s)⟩) ?_ ?_ ?_ ?_
          · intro v hv
            rw [Finset.mem_filter] at hv
            rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter]
            refine ⟨⟨Finset.mem_univ _, hv.2.comp Fin.castSucc (Fin.castSucc_injective s)⟩,
              Finset.mem_univ _, ?_⟩
            intro hmem
            rw [Submodule.mem_span_range_iff_exists_fun F] at hmem
            obtain ⟨c, hc⟩ := hmem
            let c' : Fin (s + 1) → F := Fin.snoc c 1
            have hsum0 : ∑ r : Fin (s + 1), c' r • v r = 0 := by
              rw [Fin.sum_univ_castSucc]
              simp only [c', Fin.snoc_castSucc, Fin.snoc_last, one_smul]
              rw [hc, vec_add_self]
            have h0 := Fintype.linearIndependent_iff.mp hv.2 c' hsum0 (Fin.last s)
            simp [c'] at h0
          · intro v1 _ v2 _ heq
            have h1 : (fun r : Fin s => v1 r.castSucc) = (fun r : Fin s => v2 r.castSucc) :=
              congrArg Sigma.fst heq
            have h2 : v1 (Fin.last s) = v2 (Fin.last s) := by
              have := congrArg Sigma.snd heq; simpa using this
            funext r; exact Fin.lastCases h2 (fun r' => congrFun h1 r') r
          · rintro ⟨v, w⟩ hp
            rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter] at hp
            obtain ⟨⟨_, hvLI⟩, _, hw_not⟩ := hp
            refine ⟨Fin.snoc v w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
            · rw [Fintype.linearIndependent_iff]
              intro c hc
              rw [Fin.sum_univ_castSucc] at hc
              simp only [Fin.snoc_castSucc, Fin.snoc_last] at hc
              have hclast : c (Fin.last s) = 0 := by
                by_contra hne
                have h1 : c (Fin.last s) = 1 := (zmod2_eq_zero_or_one _).resolve_left hne
                rw [h1, one_smul] at hc
                have hw_eq : w = ∑ r : Fin s, c r.castSucc • v r := by
                  have := congrArg (· + w) hc
                  simpa [add_assoc, vec_add_self w] using this.symm
                apply hw_not
                dsimp only
                rw [hw_eq]
                exact Submodule.sum_mem (Submodule.span F (Set.range v)) fun r _ =>
                  Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range.mpr ⟨r, rfl⟩))
              rw [hclast, zero_smul, add_zero] at hc
              have hinit := Fintype.linearIndependent_iff.mp hvLI (fun r => c r.castSucc) hc
              intro r; exact Fin.lastCases hclast hinit r
            · ext1
              · funext r; simp
              · simp
          · intro v _; rfl
        rw [hpair, Finset.sum_sigma]
        refine Finset.sum_congr rfl fun v _ => ?_
        dsimp only
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      have hcard_out : ∀ v ∈ S_init,
          ((Finset.univ.filter (fun w : A => w ∉ Submodule.span F (Set.range v))).card : ℤ) =
            (2 ^ m : ℤ) - (2 ^ s : ℤ) := by
        intro v hv
        have hvLI : LinearIndependent F v := (Finset.mem_filter.mp hv).2
        have hin : (Finset.univ.filter (fun w : A => w ∈ Submodule.span F (Set.range v))).card = 2 ^ s := by
          rw [card_submodule_eq_pow, finrank_span_eq_card hvLI, Fintype.card_fin]
        have htot : (Finset.univ.filter (fun w : A => w ∈ Submodule.span F (Set.range v))).card +
            (Finset.univ.filter (fun w : A => w ∉ Submodule.span F (Set.range v))).card = 2 ^ m := by
          have hdisj : Disjoint (Finset.univ.filter (fun w : A => w ∈ Submodule.span F (Set.range v)))
              (Finset.univ.filter (fun w : A => w ∉ Submodule.span F (Set.range v))) := by
            rw [Finset.disjoint_left]; intro w h1 h2
            exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
          have hun : Finset.univ.filter (fun w : A => w ∈ Submodule.span F (Set.range v)) ∪
              Finset.univ.filter (fun w : A => w ∉ Submodule.span F (Set.range v)) = Finset.univ := by
            ext w; simp [em]
          rw [← Finset.card_union_of_disjoint hdisj, hun, Finset.card_univ,
              Fintype.card_fun, ZMod.card, Fintype.card_fin]
        have hle : 2 ^ s ≤ 2 ^ m := by omega
        have hout : (Finset.univ.filter (fun w : A => w ∉ Submodule.span F (Set.range v))).card =
            2 ^ m - 2 ^ s := by omega
        rw [hout, Nat.cast_sub hle]; push_cast; rfl
      rw [hsplit, Finset.sum_congr rfl fun v hv => by rw [hcard_out v hv],
          ← Finset.sum_mul, ih hts', Finset.prod_Ico_succ_top hts']
      ring

lemma surj_dot_of_linearIndependent {m t : ℕ} (y : Fin t → Fin m → ZMod 2)
    (hy : LinearIndependent (ZMod 2) y) :
    Function.Surjective (fun v : (⊤ : Submodule (ZMod 2) (Fin m → ZMod 2)) =>
      fun r : Fin t => dotV v.1 (y r)) := by
  let F := ZMod 2
  let A : Matrix (Fin m) (Fin t) F := Matrix.of (fun a r => y r a)
  have hkerA : LinearMap.ker (Matrix.mulVecLin A) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    funext i
    refine Fintype.linearIndependent_iff.mp hy c ?_ i
    funext a
    have ha := congrFun hc a
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, A, Matrix.of_apply,
      Pi.zero_apply] at ha
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using ha
  have hrankA : A.rank = t := by
    have hrk := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin A)
    rw [hkerA, finrank_bot, add_zero, Module.finrank_fin_fun] at hrk
    exact hrk
  have hrankAT : A.transpose.rank = t := by rw [Matrix.rank_transpose, hrankA]
  have hrangeAT : LinearMap.range (Matrix.mulVecLin A.transpose) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact hrankAT)
  intro target
  have hmem : target ∈ LinearMap.range (Matrix.mulVecLin A.transpose) := by rw [hrangeAT]; trivial
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hmem
  refine ⟨⟨v, trivial⟩, ?_⟩
  funext r
  have hr := congrFun hv r
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    A, Matrix.of_apply] at hr
  simpa [dotV, mul_comm] using hr

lemma I_eval_of_le {m j : ℕ} (hmj : j ≤ m) (Y : Matrix (Fin m) (Fin j) (ZMod 2)) :
    let t := Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
      (Set.range (fun b : Fin j => fun a : Fin m => Y a b)))
    ∑ M ∈ Finset.univ.filter (fun M : Matrix (Fin m) (Fin j) (ZMod 2) =>
        ∀ c : Fin j → ZMod 2, mv' M c = 0 → c = 0), sgnZ (pairing' M Y) =
      (-1 : ℤ) ^ t * (2 : ℤ) ^ (t * (t - 1) / 2) *
        ∏ i ∈ Finset.Ico t j, ((2 ^ m : ℤ) - (2 ^ i : ℤ)) := by
  classical
  let F := ZMod 2
  let Mat := Matrix (Fin m) (Fin j) F
  let L : (Fin j → F) →ₗ[F] (Fin m → F) := Matrix.mulVecLin Y
  have hrangeL : LinearMap.range L = Submodule.span F (Set.range (fun b : Fin j => fun a : Fin m => Y a b)) := by
    ext v
    simp only [LinearMap.mem_range, Submodule.mem_span_range_iff_exists_fun F, L,
      Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨c, ?_⟩
      funext a; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    · rintro ⟨c, rfl⟩
      refine ⟨c, ?_⟩
      funext a; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  set t := Module.finrank F (Submodule.span F (Set.range (fun b : Fin j => fun a : Fin m => Y a b)))
  let K := LinearMap.ker L
  obtain ⟨P, hKP⟩ := Submodule.exists_isCompl K
  have hrank_null : t + Module.finrank F K = j := by
    have h := LinearMap.finrank_range_add_finrank_ker L
    rw [hrangeL, Module.finrank_fin_fun] at h
    exact h
  have ht_le_j : t ≤ j := by omega
  have hKP_fin : Module.finrank F K + Module.finrank F P = j := by
    have h := Submodule.finrank_add_eq_of_isCompl hKP
    rw [Module.finrank_fin_fun] at h
    exact h
  have hfinP : Module.finrank F P = t := by omega
  have hfinK : Module.finrank F K = j - t := by omega
  let bP : Module.Basis (Fin t) F P := Module.finBasisOfFinrankEq F P hfinP
  let bK : Module.Basis (Fin (j - t)) F K := Module.finBasisOfFinrankEq F K hfinK
  let vC : Fin j → (Fin j → F) := fun i =>
    if hi : i.val < t then (bP ⟨i.val, hi⟩).1 else (bK ⟨i.val - t, by omega⟩).1
  have hvC_LI : LinearIndependent F vC := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsplit : (∑ i : Fin j, c i • vC i) =
        (∑ i ∈ Finset.univ.filter (fun i : Fin j => i.val < t), c i • vC i) +
        (∑ i ∈ Finset.univ.filter (fun i : Fin j => ¬i.val < t), c i • vC i) :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin j => i.val < t) _).symm
    let pSum : Fin j → F := ∑ i ∈ Finset.univ.filter (fun i : Fin j => i.val < t), c i • vC i
    let kSum : Fin j → F := ∑ i ∈ Finset.univ.filter (fun i : Fin j => ¬i.val < t), c i • vC i
    have hpMem : pSum ∈ P := Submodule.sum_mem P fun i hi => by
      have hlt : i.val < t := (Finset.mem_filter.mp hi).2
      dsimp only [vC]; rw [dif_pos hlt]
      exact P.smul_mem _ (bP ⟨i.val, hlt⟩).2
    have hkMem : kSum ∈ K := Submodule.sum_mem K fun i hi => by
      have hge : ¬i.val < t := (Finset.mem_filter.mp hi).2
      dsimp only [vC]; rw [dif_neg hge]
      exact K.smul_mem _ (bK ⟨i.val - t, by omega⟩).2
    have hpk0 : pSum + kSum = 0 := by rw [← hsplit]; exact hc
    have hp_eq_k : pSum = kSum := by
      have := congrArg (pSum + ·) hpk0
      simpa [← add_assoc, vec_add_self pSum] using this.symm
    have hp0 : pSum = 0 := by
      have hmem : pSum ∈ K ⊓ P := ⟨hp_eq_k ▸ hkMem, hpMem⟩
      rw [hKP.disjoint.eq_bot] at hmem
      exact hmem
    have hk0 : kSum = 0 := by rw [← hp_eq_k, hp0]
    have hcP : ∀ r : Fin t, c ⟨r.val, by omega⟩ = 0 := by
      have hsumP : ∑ r : Fin t, c ⟨r.val, by omega⟩ • bP r = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        have hbij : ∑ r : Fin t, (c ⟨r.val, by omega⟩ • bP r : P).1 = pSum := by
          refine Finset.sum_bij (fun r _ => (⟨r.val, by omega⟩ : Fin j)) ?_ ?_ ?_ ?_
          · intro r _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.isLt⟩
          · intro r1 _ r2 _ h; exact Fin.ext (congrArg (Fin.val : Fin j → ℕ) h)
          · intro i hi
            have hlt : i.val < t := (Finset.mem_filter.mp hi).2
            exact ⟨⟨i.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
          · intro r _
            dsimp only [vC]; rw [dif_pos r.isLt]; rfl
        rw [hbij, hp0]; rfl
      exact Fintype.linearIndependent_iff.mp bP.linearIndependent _ hsumP
    have hcK : ∀ r : Fin (j - t), c ⟨t + r.val, by omega⟩ = 0 := by
      have hsumK : ∑ r : Fin (j - t), c ⟨t + r.val, by omega⟩ • bK r = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        have hbij : ∑ r : Fin (j - t), (c ⟨t + r.val, by omega⟩ • bK r : K).1 = kSum := by
          refine Finset.sum_bij (fun r _ => (⟨t + r.val, by omega⟩ : Fin j)) ?_ ?_ ?_ ?_
          · intro r _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp only [Fin.val_mk]; omega⟩
          · intro r1 _ r2 _ h
            have : t + r1.val = t + r2.val := congrArg (Fin.val : Fin j → ℕ) h
            exact Fin.ext (by omega)
          · intro i hi
            have hge : ¬i.val < t := (Finset.mem_filter.mp hi).2
            refine ⟨⟨i.val - t, by omega⟩, Finset.mem_univ _, Fin.ext (by simp only [Fin.val_mk]; omega)⟩
          · intro r _
            dsimp only [vC]; rw [dif_neg (by omega)]
            have hsub : t + r.val - t = r.val := by omega
            simp [hsub]
        rw [hbij, hk0]; rfl
      exact Fintype.linearIndependent_iff.mp bK.linearIndependent _ hsumK
    intro i
    by_cases hi : i.val < t
    · exact hcP ⟨i.val, hi⟩
    · have := hcK ⟨i.val - t, by omega⟩
      have heq : (⟨t + (i.val - t), by omega⟩ : Fin j) = i := Fin.ext (by simp only [Fin.val_mk]; omega)
      rwa [heq] at this
  let E : Matrix (Fin j) (Fin j) F := Matrix.of (fun r s => vC s r)
  have hE_inj : Function.Injective (Matrix.mulVecLin E) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    funext i
    refine Fintype.linearIndependent_iff.mp hvC_LI c ?_ i
    funext r
    have hr := congrFun hc r
    change ∑ s : Fin j, vC s r * c s = 0 at hr
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hr]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  have hET_bij : Function.Bijective (Matrix.mulVecLin E.transpose) := by
    have hrankE : E.rank = j := by
      have hker : LinearMap.ker (Matrix.mulVecLin E) = ⊥ := LinearMap.ker_eq_bot.mpr hE_inj
      have hrk := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin E)
      rw [hker, finrank_bot, add_zero, Module.finrank_fin_fun] at hrk
      exact hrk
    have hrankET : E.transpose.rank = j := by rw [Matrix.rank_transpose, hrankE]
    have hsurj : Function.Surjective (Matrix.mulVecLin E.transpose) := by
      have htop : LinearMap.range (Matrix.mulVecLin E.transpose) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact hrankET)
      intro w; have : w ∈ LinearMap.range (Matrix.mulVecLin E.transpose) := by rw [htop]; trivial
      exact LinearMap.mem_range.mp this
    exact ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  have hmul_inj : Function.Injective (fun M : Mat => M * E.transpose) := by
    intro M1 M2 heq
    ext a b
    have ha : Matrix.mulVecLin E (fun s => M1 a s) = Matrix.mulVecLin E (fun s => M2 a s) := by
      funext r
      have h := congrFun (congrFun heq a) r
      change ∑ s : Fin j, M1 a s * E r s = ∑ s : Fin j, M2 a s * E r s at h
      change ∑ s : Fin j, E r s * M1 a s = ∑ s : Fin j, E r s * M2 a s
      calc ∑ s : Fin j, E r s * M1 a s
          = ∑ s : Fin j, M1 a s * E r s := Finset.sum_congr rfl fun s _ => mul_comm _ _
        _ = ∑ s : Fin j, M2 a s * E r s := h
        _ = ∑ s : Fin j, E r s * M2 a s := Finset.sum_congr rfl fun s _ => mul_comm _ _
    exact congrFun (hE_inj ha) b
  have hmul_bij : Function.Bijective (fun M : Mat => M * E.transpose) :=
    ⟨hmul_inj, Finite.injective_iff_surjective.mp hmul_inj⟩
  have hmv_mul : ∀ (M : Mat) (c : Fin j → F), mv' (M * E.transpose) c = mv' M (Matrix.mulVecLin E.transpose c) := by
    intro M c; funext a
    dsimp only [mv', Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    have h1 : ∀ b : Fin j, (M * E.transpose) a b * c b = ∑ k : Fin j, M a k * (E.transpose k b * c b) := by
      intro b
      change (∑ k : Fin j, M a k * E.transpose k b) * c b = _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => by ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
  have hpair_mul : ∀ M : Mat, pairing' (M * E.transpose) Y = pairing' M (Y * E) := by
    intro M
    dsimp only [pairing']
    refine Finset.sum_congr rfl fun a _ => ?_
    have h1 : ∀ b : Fin j, (M * E.transpose) a b * Y a b = ∑ k : Fin j, M a k * (Y a b * E b k) := by
      intro b
      change (∑ k : Fin j, M a k * E b k) * Y a b = _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => by ring
    have h2 : ∀ k : Fin j, M a k * (Y * E) a k = ∑ b : Fin j, M a k * (Y a b * E b k) := by
      intro k
      change M a k * (∑ b : Fin j, Y a b * E b k) = _
      rw [Finset.mul_sum]
    simp_rw [h1, h2]
    exact Finset.sum_comm
  let Y' : Mat := Y * E
  have hI_eq : ∑ M ∈ Finset.univ.filter (fun M : Mat => ∀ c : Fin j → F, mv' M c = 0 → c = 0),
        sgnZ (pairing' M Y) =
      ∑ M ∈ Finset.univ.filter (fun M : Mat => ∀ c : Fin j → F, mv' M c = 0 → c = 0),
        sgnZ (pairing' M Y') := by
    symm
    refine Finset.sum_bij (fun M _ => M * E.transpose) ?_ ?_ ?_ ?_
    · intro M hM
      rw [Finset.mem_filter] at hM ⊢
      refine ⟨Finset.mem_univ _, fun c hc => ?_⟩
      rw [hmv_mul] at hc
      have h0 := hM.2 (Matrix.mulVecLin E.transpose c) hc
      exact hET_bij.1 (by rw [h0, map_zero])
    · intro M1 _ M2 _ h; exact hmul_bij.1 h
    · intro M hM
      obtain ⟨M0, rfl⟩ := hmul_bij.2 M
      refine ⟨M0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun c hc => ?_⟩, rfl⟩
      obtain ⟨c', rfl⟩ := hET_bij.2 c
      have h0 := (Finset.mem_filter.mp hM).2 c' (by rw [hmv_mul]; exact hc)
      rw [h0, map_zero]
    · intro M _; rw [hpair_mul]
  rw [hI_eq]
  have hY'_col : ∀ s : Fin j, (fun a : Fin m => Y' a s) = L (vC s) := by
    intro s; funext a
    simp only [Y', L, E, Matrix.mul_apply, Matrix.of_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct]
  let y : Fin t → Fin m → F := fun r => L (bP r).1
  have hy_LI : LinearIndependent F y := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hker : (∑ r : Fin t, c r • (bP r).1) ∈ K := by
      show L (∑ r : Fin t, c r • (bP r).1) = 0
      rw [map_sum]
      simp_rw [map_smul]
      exact hc
    have hP : (∑ r : Fin t, c r • (bP r).1) ∈ P :=
      Submodule.sum_mem P fun r _ => P.smul_mem _ (bP r).2
    have h0 : (∑ r : Fin t, c r • (bP r).1) = 0 := by
      have hmem : (∑ r : Fin t, c r • (bP r).1) ∈ K ⊓ P := ⟨hker, hP⟩
      rw [hKP.disjoint.eq_bot] at hmem; exact hmem
    have hsumP : ∑ r : Fin t, c r • bP r = 0 := by
      apply Subtype.ext; rw [Submodule.coe_sum]; exact h0
    exact Fintype.linearIndependent_iff.mp bP.linearIndependent c hsumP
  have hpair_Y' : ∀ M : Mat,
      pairing' M Y' = ∑ r : Fin t, dotV (fun a => M a ⟨r.val, by omega⟩) (y r) := by
    intro M
    simp only [pairing', dotV]
    rw [Finset.sum_comm]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s : Fin j => s.val < t)]
    have hzero : ∑ s ∈ Finset.univ.filter (fun s : Fin j => ¬s.val < t),
        ∑ a : Fin m, M a s * Y' a s = 0 := by
      refine Finset.sum_eq_zero fun s hs => Finset.sum_eq_zero fun a _ => ?_
      have hge : ¬s.val < t := (Finset.mem_filter.mp hs).2
      have hcol0 : (fun r => Y' r s) = 0 := by
        rw [hY'_col s]; dsimp only [vC]; rw [dif_neg hge]
        exact (bK ⟨s.val - t, by omega⟩).2
      rw [show Y' a s = 0 from congrFun hcol0 a, mul_zero]
    rw [hzero, add_zero]
    symm
    refine Finset.sum_bij (fun r _ => (⟨r.val, by omega⟩ : Fin j)) ?_ ?_ ?_ ?_
    · intro r _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.isLt⟩
    · intro r1 _ r2 _ h; exact Fin.ext (congrArg (Fin.val : Fin j → ℕ) h)
    · intro s hs
      have hlt : s.val < t := (Finset.mem_filter.mp hs).2
      exact ⟨⟨s.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · intro r _
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 1
      have hc := congrFun (hY'_col ⟨r.val, by omega⟩) a
      dsimp only [vC] at hc
      rw [dif_pos r.isLt] at hc
      exact hc.symm
  have hbij_cols : ∑ M ∈ Finset.univ.filter (fun M : Mat => ∀ c : Fin j → F, mv' M c = 0 → c = 0),
        sgnZ (pairing' M Y') =
      ∑ v ∈ Finset.univ.filter (fun v : Fin j → Fin m → F => LinearIndependent F v),
        sgnZ (∑ r : Fin t, dotV (v ⟨r.val, by omega⟩) (y r)) := by
    refine Finset.sum_bij (fun M _ b a => M a b) ?_ ?_ ?_ ?_
    · intro M hM
      rw [Finset.mem_filter] at hM ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hmv0 : mv' M c = 0 := by
        funext a
        have ha := congrFun hc a
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ha
        change ∑ b : Fin j, M a b * c b = 0
        rw [← ha]; exact Finset.sum_congr rfl fun b _ => mul_comm _ _
      have hc0 := hM.2 c hmv0
      intro i; exact congrFun hc0 i
    · intro M1 _ M2 _ h
      ext a b; exact congrFun (congrFun h b) a
    · intro v hv
      rw [Finset.mem_filter] at hv
      let M : Mat := Matrix.of (fun a b => v b a)
      refine ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun c hc => ?_⟩, rfl⟩
      have hsum : ∑ b : Fin j, c b • v b = 0 := by
        funext a
        have ha := congrFun hc a
        change ∑ b : Fin j, v b a * c b = 0 at ha
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← ha]; exact Finset.sum_congr rfl fun b _ => mul_comm _ _
      funext b; exact Fintype.linearIndependent_iff.mp hv.2 c hsum b
    · intro M _; rw [hpair_Y' M]
  rw [hbij_cols]
  exact sum_indep_peel y (surj_dot_of_linearIndependent y hy_LI) j ht_le_j

lemma no_inj_of_lt {m j : ℕ} (hmj : m < j) (M : Matrix (Fin m) (Fin j) (ZMod 2)) :
    ¬(∀ c : Fin j → ZMod 2, mv' M c = 0 → c = 0) := by
  intro hinj
  let L := Matrix.mulVecLin M
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc; exact hinj c hc
  have hrk := LinearMap.finrank_range_add_finrank_ker L
  rw [hker, finrank_bot, add_zero, Module.finrank_fin_fun] at hrk
  have hle : Module.finrank (ZMod 2) (LinearMap.range L) ≤ m := by
    calc Module.finrank (ZMod 2) (LinearMap.range L)
        ≤ Module.finrank (ZMod 2) (Fin m → ZMod 2) := Submodule.finrank_le _
      _ = m := Module.finrank_fin_fun _
  omega

end PEqualNP.Outside.L_lib_821

open PEqualNP.Outside.L_lib_821 in
theorem PEqualNP.Outside.L_lib_821 : ∀ (m j : ℕ), 2 ≤ j →
  let F := ZMod 2
  let A := Fin m → F
  let C := Fin j → F
  let Mat := Matrix (Fin m) (Fin j) F
  let mv := fun (M : Mat) (c : C) (a : Fin m) => ∑ b, M a b * c b
  let pairing := fun (M Y : Mat) => ∑ a, ∑ b, M a b * Y a b
  let coeff := fun (Y : Mat) (h : A) =>
    ∑ M : Mat, (if pairing M Y = 0 then (1 : ℤ) else -1) *
      (((Finset.univ.filter (fun c : C => c ≠ 0 ∧ mv M c = h)).card - 1 : ℕ) : ℤ)
  ∀ Y : Mat,
    let t := Module.finrank F (Submodule.span F (Set.range (fun b : Fin j => fun a : Fin m => Y a b)))
    (∀ h : A, h ≠ 0 → Odd (coeff Y h)) ∧
      (coeff Y 0 = 0 ↔ m < j ∧ 2 ≤ t) := by
  classical
  intro m j hj F A C Mat mv pairing coeff Y t
  constructor
  · intro h hh
    exact odd_coeff_nonzero hj Y h hh
  · by_cases ht0 : t = 0
    · have hY0 : Y = 0 := by
        have hS0 : Submodule.span F (Set.range (fun b : Fin j => fun a : Fin m => Y a b)) = ⊥ :=
          Submodule.finrank_eq_zero.mp ht0
        ext a b
        have hmem : (fun r : Fin m => Y r b) ∈ (⊥ : Submodule F (Fin m → F)) := by
          rw [← hS0]; exact Submodule.subset_span ⟨b, rfl⟩
        exact congrFun hmem a
      have hpos : (0 : ℤ) < coeff Y 0 := by
        have hterm_nonneg : ∀ M : Mat, (0 : ℤ) ≤
            (if pairing M Y = 0 then (1 : ℤ) else -1) *
              (((Finset.univ.filter (fun c : C => c ≠ 0 ∧ mv M c = 0)).card - 1 : ℕ) : ℤ) := by
          intro M
          have hp0 : pairing M Y = 0 := by
            rw [hY0]
            exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => by
              change M a b * (0 : ZMod 2) = 0; exact mul_zero _
          rw [if_pos hp0, one_mul]; exact Nat.cast_nonneg _
        have hM0_ge : (2 : ℤ) ≤
            (if pairing 0 Y = 0 then (1 : ℤ) else -1) *
              (((Finset.univ.filter (fun c : C => c ≠ 0 ∧ mv 0 c = 0)).card - 1 : ℕ) : ℤ) := by
          have hp0 : pairing 0 Y = 0 :=
            Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => by
              change (0 : ZMod 2) * Y a b = 0; exact zero_mul _
          rw [if_pos hp0, one_mul]
          have hmv0 : ∀ c : C, mv 0 c = 0 := fun c => by
            funext a; exact Finset.sum_eq_zero fun b _ => by
              change (0 : ZMod 2) * c b = 0; exact zero_mul _
          have hfilt : Finset.univ.filter (fun c : C => c ≠ 0 ∧ mv 0 c = 0) =
              (Finset.univ : Finset C).erase 0 := by
            ext c
            simp [hmv0 c]
          rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
              Fintype.card_fun, ZMod.card, Fintype.card_fin]
          have h4 : 4 ≤ 2 ^ j := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
          omega
        have hle := Finset.single_le_sum (f := fun M : Mat =>
            (if pairing M Y = 0 then (1 : ℤ) else -1) *
              (((Finset.univ.filter (fun c : C => c ≠ 0 ∧ mv M c = 0)).card - 1 : ℕ) : ℤ))
          (fun M _ => hterm_nonneg M) (Finset.mem_univ (0 : Mat))
        dsimp only [coeff]
        linarith
      constructor
      · intro heq; linarith
      · rintro ⟨_, h2⟩; omega
    · have ht1_ge : 1 ≤ t := by omega
      have hdecomp : coeff Y 0 =
          (∑ M : Mat, sgnZ (pairing' M Y) *
            ((Finset.univ.filter (fun c : C => mv' M c = 0)).card : ℤ)) -
          2 * (∑ M : Mat, sgnZ (pairing' M Y)) +
          (∑ M ∈ Finset.univ.filter (fun M : Mat => ∀ c : C, mv' M c = 0 → c = 0),
            sgnZ (pairing' M Y)) := by
        have hpt : ∀ M : Mat,
            (((Finset.univ.filter (fun c : C => c ≠ 0 ∧ mv' M c = 0)).card - 1 : ℕ) : ℤ) =
            ((Finset.univ.filter (fun c : C => mv' M c = 0)).card : ℤ) - 2 +
              (if ∀ c : C, mv' M c = 0 → c = 0 then (1 : ℤ) else 0) := by
          intro M
          have hcard_ins : (Finset.univ.filter (fun c : C => mv' M c = 0)).card =
              (Finset.univ.filter (fun c : C => c ≠ 0 ∧ mv' M c = 0)).card + 1 := by
            have heq : Finset.univ.filter (fun c : C => mv' M c = 0) =
                insert 0 (Finset.univ.filter (fun c : C => c ≠ 0 ∧ mv' M c = 0)) := by
              ext c
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
              by_cases hc : c = 0
              · subst hc; simp [mv'_zero]
              · simp [hc]
            rw [heq, Finset.card_insert_of_notMem (by simp)]
          by_cases hinj : ∀ c : C, mv' M c = 0 → c = 0
          · rw [if_pos hinj]
            have h0 : Finset.univ.filter (fun c : C => c ≠ 0 ∧ mv' M c = 0) = ∅ := by
              ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
              rintro ⟨hne, hmc⟩; exact hne (hinj c hmc)
            rw [hcard_ins, h0, Finset.card_empty]; norm_num
          · rw [if_neg hinj]
            push_neg at hinj
            obtain ⟨c1, hc1_ker, hc1_ne⟩ := hinj
            have hpos : 1 ≤ (Finset.univ.filter (fun c : C => c ≠ 0 ∧ mv' M c = 0)).card :=
              Finset.card_pos.mpr ⟨c1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc1_ne, hc1_ker⟩⟩
            rw [hcard_ins]
            omega
        have hstep1 : coeff Y 0 = ∑ M : Mat, sgnZ (pairing' M Y) *
            (((Finset.univ.filter (fun c : C => mv' M c = 0)).card : ℤ) - 2 +
              (if ∀ c : C, mv' M c = 0 → c = 0 then (1 : ℤ) else 0)) := by
          dsimp only [coeff]
          refine Finset.sum_congr rfl fun M _ => ?_
          rw [← hpt M]; rfl
        rw [hstep1]
        have hsplit : ∑ M : Mat, sgnZ (pairing' M Y) *
              (((Finset.univ.filter (fun c : C => mv' M c = 0)).card : ℤ) - 2 +
                (if ∀ c : C, mv' M c = 0 → c = 0 then (1 : ℤ) else 0)) =
            (∑ M : Mat, sgnZ (pairing' M Y) * ((Finset.univ.filter (fun c : C => mv' M c = 0)).card : ℤ)) -
            (∑ M : Mat, 2 * sgnZ (pairing' M Y)) +
            (∑ M : Mat, if ∀ c : C, mv' M c = 0 → c = 0 then sgnZ (pairing' M Y) else 0) := by
          rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun M _ => ?_
          split_ifs <;> ring
        rw [hsplit, ← Finset.mul_sum, ← Finset.sum_filter]
      have hT2_zero : ∑ M : Mat, sgnZ (pairing' M Y) = 0 := by
        have hYne : Y ≠ 0 := by
          intro h0; subst h0
          have hS0 : Submodule.span F (Set.range (fun b : Fin j => fun a : Fin m => (0 : Mat) a b)) = ⊥ := by
            rw [Submodule.span_eq_bot]; rintro _ ⟨_, rfl⟩; rfl
          have : t = 0 := by dsimp only [t]; rw [hS0, finrank_bot]
          omega
        rw [sum_sgnZ_subspace Finset.univ (fun _ _ _ _ => Finset.mem_univ _)
            (fun M => pairing' M Y) (fun M1 M2 => pairing'_add M1 M2 Y), if_neg]
        intro hall; apply hYne; ext a b
        let E : Mat := Matrix.of (fun r s => if r = a ∧ s = b then 1 else 0)
        have hE := hall E (Finset.mem_univ _)
        have hp : pairing' E Y = Y a b := by
          simp only [pairing', E, Matrix.of_apply]
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
          have hr : ∑ r ∈ (Finset.univ : Finset (Fin m)).erase a,
              ∑ s : Fin j, (if r = a ∧ s = b then (1 : ZMod 2) else 0) * Y r s = 0 := by
            refine Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun s _ => ?_
            simp [(Finset.mem_erase.mp hr).1]
          rw [hr, add_zero, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ b)]
          have hs : ∑ s ∈ (Finset.univ : Finset (Fin j)).erase b,
              (if a = a ∧ s = b then (1 : ZMod 2) else 0) * Y a s = 0 := by
            refine Finset.sum_eq_zero fun s hs => ?_
            simp [(Finset.mem_erase.mp hs).1]
          rw [hs, add_zero]; simp
        rw [hp] at hE; exact hE
      rw [hT2_zero, mul_zero, sub_zero, T1_eval Y ht1_ge] at hdecomp
      by_cases hmj : m < j
      · have hI0 : ∑ M ∈ Finset.univ.filter (fun M : Mat => ∀ c : C, mv' M c = 0 → c = 0),
            sgnZ (pairing' M Y) = 0 := by
          have hem : Finset.univ.filter (fun M : Mat => ∀ c : C, mv' M c = 0 → c = 0) = ∅ := by
            ext M; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            exact no_inj_of_lt hmj M
          rw [hem, Finset.sum_empty]
        rw [hI0, add_zero] at hdecomp
        by_cases ht1 : t = 1
        · rw [if_pos ht1] at hdecomp
          have hpos : (0 : ℤ) < (2 ^ (m * (j - 1)) : ℤ) := by positivity
          constructor
          · intro heq; linarith
          · rintro ⟨_, h2⟩; omega
        · rw [if_neg ht1] at hdecomp
          exact ⟨fun _ => ⟨hmj, by omega⟩, fun _ => hdecomp⟩
      · have hjm : j ≤ m := by omega
        have hI := I_eval_of_le hjm Y
        change ∑ M ∈ Finset.univ.filter (fun M : Mat => ∀ c : C, mv' M c = 0 → c = 0),
            sgnZ (pairing' M Y) =
          (-1 : ℤ) ^ t * (2 : ℤ) ^ (t * (t - 1) / 2) *
            ∏ i ∈ Finset.Ico t j, ((2 ^ m : ℤ) - (2 ^ i : ℤ)) at hI
        rw [hI] at hdecomp
        have hne0 : coeff Y 0 ≠ 0 := by
          by_cases ht1 : t = 1
          · rw [if_pos ht1, ht1] at hdecomp
            simp only [pow_one, Nat.sub_self, mul_zero, Nat.zero_div, pow_zero, mul_one,
              neg_one_mul] at hdecomp
            have hprod_lt : ∏ i ∈ Finset.Ico 1 j, ((2 ^ m : ℤ) - (2 ^ i : ℤ)) < (2 ^ (m * (j - 1)) : ℤ) := by
              have h1mem : (1 : ℕ) ∈ Finset.Ico 1 j := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
              have hpos_rest : (0 : ℤ) < ∏ i ∈ (Finset.Ico 1 j).erase 1, ((2 ^ m : ℤ) - (2 ^ i : ℤ)) := by
                refine Finset.prod_pos fun i hi => ?_
                have hmem := Finset.mem_Ico.mp (Finset.mem_of_mem_erase hi)
                have hlt : (2 : ℤ) ^ i < (2 : ℤ) ^ m := by
                  exact_mod_cast Nat.pow_lt_pow_right (by omega) (by omega)
                linarith
              have hle_rest : ∏ i ∈ (Finset.Ico 1 j).erase 1, ((2 ^ m : ℤ) - (2 ^ i : ℤ)) ≤
                  ∏ _i ∈ (Finset.Ico 1 j).erase 1, (2 ^ m : ℤ) := by
                have hgen : ∀ S : Finset ℕ, (∀ i ∈ S, i < m) →
                    ∏ i ∈ S, ((2 ^ m : ℤ) - (2 ^ i : ℤ)) ≤ ∏ _i ∈ S, (2 ^ m : ℤ) := by
                  intro S
                  induction S using Finset.induction_on with
                  | empty => intro _; simp
                  | insert a S ha ih =>
                    intro hltS
                    rw [Finset.prod_insert ha, Finset.prod_insert ha]
                    have ha_lt : a < m := hltS a (Finset.mem_insert_self _ _)
                    have h2a_lt : (2 : ℤ) ^ a < (2 : ℤ) ^ m := by
                      exact_mod_cast Nat.pow_lt_pow_right (by omega) ha_lt
                    have h2a_pos : (0 : ℤ) < (2 : ℤ) ^ a := by positivity
                    have hnonneg_S : (0 : ℤ) ≤ ∏ i ∈ S, ((2 ^ m : ℤ) - (2 ^ i : ℤ)) := by
                      refine Finset.prod_nonneg fun i hi => ?_
                      have hi_lt : i < m := hltS i (Finset.mem_insert_of_mem hi)
                      have : (2 : ℤ) ^ i < (2 : ℤ) ^ m := by
                        exact_mod_cast Nat.pow_lt_pow_right (by omega) hi_lt
                      linarith
                    exact mul_le_mul (by linarith) (ih fun i hi => hltS i (Finset.mem_insert_of_mem hi))
                      hnonneg_S (by positivity)
                refine hgen _ fun i hi => ?_
                have hmem := Finset.mem_Ico.mp (Finset.mem_of_mem_erase hi)
                omega
              have hlt1 : (2 ^ m : ℤ) - (2 ^ 1 : ℤ) < (2 ^ m : ℤ) := by norm_num
              have h2m_pos : (0 : ℤ) < (2 ^ m : ℤ) := by positivity
              calc ∏ i ∈ Finset.Ico 1 j, ((2 ^ m : ℤ) - (2 ^ i : ℤ))
                  = ((2 ^ m : ℤ) - (2 ^ 1 : ℤ)) * ∏ i ∈ (Finset.Ico 1 j).erase 1, ((2 ^ m : ℤ) - (2 ^ i : ℤ)) :=
                    (Finset.mul_prod_erase (Finset.Ico 1 j) (fun i => (2 ^ m : ℤ) - (2 ^ i : ℤ)) h1mem).symm
                _ < (2 ^ m : ℤ) * ∏ i ∈ (Finset.Ico 1 j).erase 1, ((2 ^ m : ℤ) - (2 ^ i : ℤ)) :=
                    mul_lt_mul_of_pos_right hlt1 hpos_rest
                _ ≤ (2 ^ m : ℤ) * ∏ _i ∈ (Finset.Ico 1 j).erase 1, (2 ^ m : ℤ) :=
                    mul_le_mul_of_nonneg_left hle_rest (le_of_lt h2m_pos)
                _ = ∏ _i ∈ Finset.Ico 1 j, (2 ^ m : ℤ) :=
                    Finset.mul_prod_erase (Finset.Ico 1 j) (fun _ => (2 ^ m : ℤ)) h1mem
                _ = (2 ^ (m * (j - 1)) : ℤ) := by rw [Finset.prod_const, Nat.card_Ico, ← pow_mul]
            linarith
          · rw [if_neg ht1, zero_add] at hdecomp
            rw [hdecomp]
            have h1 : (-1 : ℤ) ^ t ≠ 0 := pow_ne_zero t (by norm_num)
            have h2 : (2 : ℤ) ^ (t * (t - 1) / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
            have h3 : ∏ i ∈ Finset.Ico t j, ((2 ^ m : ℤ) - (2 ^ i : ℤ)) ≠ 0 := by
              rw [Finset.prod_ne_zero_iff]
              intro i hi
              rw [Finset.mem_Ico] at hi
              have hlt : (2 : ℤ) ^ i < (2 : ℤ) ^ m := by
                exact_mod_cast Nat.pow_lt_pow_right (by omega) (by omega)
              linarith
            exact mul_ne_zero (mul_ne_zero h1 h2) h3
        exact ⟨fun heq => False.elim (hne0 heq), fun ⟨hlt, _⟩ => False.elim (hmj hlt)⟩

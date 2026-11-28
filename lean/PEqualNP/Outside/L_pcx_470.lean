import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_470_aux

private abbrev X (m : ℕ) := (Fin m → ZMod 2) × (Fin m → ZMod 2)

private def B (m : ℕ) (x y : X m) : ZMod 2 :=
  dotProduct x.1 y.2 + dotProduct x.2 y.1

private def J {m : ℕ} (x : X m) : X m := (x.2, x.1 + x.2)

private def Jinv {m : ℕ} (x : X m) : X m := (x.1 + x.2, x.1)

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

private lemma zmod2_vec_add_self {m : ℕ} (v : Fin m → ZMod 2) : v + v = 0 := by
  ext i
  exact zmod2_add_self (v i)

private lemma x_add_self {m : ℕ} (x : X m) : x + x = 0 := by
  ext i
  · exact zmod2_add_self (x.1 i)
  · exact zmod2_add_self (x.2 i)

private lemma J_add {m : ℕ} (x y : X m) : J (x + y) = J x + J y := by
  ext i
  · rfl
  · simp [J]; ring

private lemma J_Jinv {m : ℕ} (x : X m) : J (Jinv x) = x := by
  ext i
  · rfl
  · simp only [J, Jinv, Prod.fst, Prod.snd, Pi.add_apply]
    have h := zmod2_add_self (x.1 i)
    calc
      (x.1 i + x.2 i) + x.1 i = (x.1 i + x.1 i) + x.2 i := by ring
      _ = 0 + x.2 i := by rw [h]
      _ = x.2 i := zero_add _

private lemma Jinv_J {m : ℕ} (x : X m) : Jinv (J x) = x := by
  ext i
  · simp only [J, Jinv, Prod.fst, Prod.snd, Pi.add_apply]
    have h := zmod2_add_self (x.2 i)
    calc
      x.2 i + (x.1 i + x.2 i) = x.1 i + (x.2 i + x.2 i) := by ring
      _ = x.1 i + 0 := by rw [h]
      _ = x.1 i := add_zero _
  · rfl

private lemma add_J_eq_Jinv {m : ℕ} (x : X m) : x + J x = Jinv x := by
  ext i
  · rfl
  · simp only [J, Jinv, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    have h := zmod2_add_self (x.2 i)
    calc
      x.2 i + (x.1 i + x.2 i) = x.1 i + (x.2 i + x.2 i) := by ring
      _ = x.1 i + 0 := by rw [h]
      _ = x.1 i := add_zero _

private lemma B_add_left {m : ℕ} (x y z : X m) : B m (x + y) z = B m x z + B m y z := by
  simp only [B, Prod.fst_add, Prod.snd_add, add_dotProduct]
  ring

private lemma B_add_right {m : ℕ} (x y z : X m) : B m x (y + z) = B m x y + B m x z := by
  simp only [B, Prod.fst_add, Prod.snd_add, dotProduct_add]
  ring

private lemma B_self {m : ℕ} (x : X m) : B m x x = 0 := by
  simp only [B, dotProduct_comm x.2 x.1]
  exact zmod2_add_self _

private lemma B_J_polar {m : ℕ} (x y : X m) :
    B m x (J y) + B m y (J x) = B m x y := by
  simp only [B, J, dotProduct]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 := zmod2_add_self (x.1 i * y.1 i)
  have h2 := zmod2_add_self (x.2 i * y.2 i)
  calc
    (x.1 i * (y.1 i + y.2 i) + x.2 i * y.2 i) + (y.1 i * (x.1 i + x.2 i) + y.2 i * x.2 i)
      = (x.1 i * y.1 i + x.1 i * y.1 i) + (x.2 i * y.2 i + x.2 i * y.2 i) +
        (x.1 i * y.2 i + x.2 i * y.1 i) := by ring
    _ = 0 + 0 + (x.1 i * y.2 i + x.2 i * y.1 i) := by rw [h1, h2]
    _ = x.1 i * y.2 i + x.2 i * y.1 i := by simp

private lemma B_J_add {m : ℕ} (x y : X m) :
    B m (x + y) (J (x + y)) = B m x (J x) + B m y (J y) + B m x y := by
  rw [J_add, B_add_left, B_add_right, B_add_right]
  have hp := B_J_polar x y
  calc
    B m x (J x) + B m x (J y) + (B m y (J x) + B m y (J y))
      = B m x (J x) + B m y (J y) + (B m x (J y) + B m y (J x)) := by ring
    _ = B m x (J x) + B m y (J y) + B m x y := by rw [hp]

private def snocX {m : ℕ} (x : X m) (p q : ZMod 2) : X (m + 1) :=
  (Fin.snoc x.1 p, Fin.snoc x.2 q)

private def initX {m : ℕ} (a : X (m + 1)) : X m :=
  (Fin.init a.1, Fin.init a.2)

private lemma snocX_eq_iff {m : ℕ} (x : X m) (p q : ZMod 2) (a : X (m + 1)) :
    snocX x p q = a ↔ x = initX a ∧ p = a.1 (Fin.last m) ∧ q = a.2 (Fin.last m) := by
  constructor
  · intro h
    have h1 : Fin.snoc x.1 p = a.1 := congrArg Prod.fst h
    have h2 : Fin.snoc x.2 q = a.2 := congrArg Prod.snd h
    refine ⟨?_, ?_, ?_⟩
    · ext i
      · have hi := congrFun h1 i.castSucc
        simpa [initX, Fin.init, Fin.snoc_castSucc] using hi
      · have hi := congrFun h2 i.castSucc
        simpa [initX, Fin.init, Fin.snoc_castSucc] using hi
    · have hl := congrFun h1 (Fin.last m)
      simpa [Fin.snoc_last] using hl
    · have hl := congrFun h2 (Fin.last m)
      simpa [Fin.snoc_last] using hl
  · rintro ⟨hx, hp, hq⟩
    ext i
    · refine Fin.lastCases ?_ ?_ i
      · simp [snocX, Fin.snoc_last, hp]
      · intro j
        have hj := congrFun (congrArg Prod.fst hx) j
        simpa [snocX, initX, Fin.init, Fin.snoc_castSucc] using hj
    · refine Fin.lastCases ?_ ?_ i
      · simp [snocX, Fin.snoc_last, hq]
      · intro j
        have hj := congrFun (congrArg Prod.snd hx) j
        simpa [snocX, initX, Fin.init, Fin.snoc_castSucc] using hj

private lemma snocX_add {m : ℕ} (x y : X m) (p q r s : ZMod 2) :
    snocX x p q + snocX y r s = snocX (x + y) (p + r) (q + s) := by
  ext i
  · refine Fin.lastCases ?_ ?_ i
    · simp [snocX, Fin.snoc_last]
    · intro j; simp [snocX, Fin.snoc_castSucc]
  · refine Fin.lastCases ?_ ?_ i
    · simp [snocX, Fin.snoc_last]
    · intro j; simp [snocX, Fin.snoc_castSucc]

private lemma snocX_zero {m : ℕ} : snocX (0 : X m) 0 0 = 0 := by
  ext i
  · refine Fin.lastCases ?_ ?_ i
    · simp [snocX, Fin.snoc_last]
    · intro j; simp [snocX, Fin.snoc_castSucc]
  · refine Fin.lastCases ?_ ?_ i
    · simp [snocX, Fin.snoc_last]
    · intro j; simp [snocX, Fin.snoc_castSucc]

private lemma snocX_inj {m : ℕ} {x y : X m} {p q r s : ZMod 2}
    (h : snocX x p q = snocX y r s) : x = y ∧ p = r ∧ q = s := by
  have hiff := (snocX_eq_iff x p q (snocX y r s)).mp h
  refine ⟨?_, ?_, ?_⟩
  · ext i
    · have hi := congrFun (congrArg Prod.fst hiff.1) i
      simpa [initX, Fin.init, snocX, Fin.snoc_castSucc] using hi
    · have hi := congrFun (congrArg Prod.snd hiff.1) i
      simpa [initX, Fin.init, snocX, Fin.snoc_castSucc] using hi
  · simpa [snocX, Fin.snoc_last] using hiff.2.1
  · simpa [snocX, Fin.snoc_last] using hiff.2.2

private lemma B_snocX {m : ℕ} (x y : X m) (p q r s : ZMod 2) :
    B (m + 1) (snocX x p q) (snocX y r s) = B m x y + (p * s + q * r) := by
  simp only [B, snocX, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  ring

private lemma dvd_four_pow_sub_one (m : ℕ) : 3 ∣ 4 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rcases ih with ⟨c, hc⟩
    refine ⟨4 * c + 1, ?_⟩
    have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by decide)
    have h4 : 4 ^ (k + 1) = 4 * 4 ^ k := by rw [pow_succ']
    omega

private lemma card_T_succ (m : ℕ) :
    2 * ((4 ^ (m + 1) - 1) / 3) = 2 * ((4 ^ m - 1) / 3) + 2 * 4 ^ m := by
  obtain ⟨c, hc⟩ := dvd_four_pow_sub_one m
  have h1 : 1 ≤ 4 ^ m := Nat.one_le_pow m 4 (by decide)
  have h4 : 4 ^ (m + 1) = 4 * 4 ^ m := by rw [pow_succ']
  have hsub : 4 ^ (m + 1) - 1 = 3 * (c + 4 ^ m) := by omega
  rw [hc, hsub, Nat.mul_div_cancel_left _ (by decide), Nat.mul_div_cancel_left _ (by decide)]
  ring

private lemma card_X (m : ℕ) : Fintype.card (X m) = 4 ^ m := by
  simp only [X, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  rw [← mul_pow]
  norm_num

private lemma exists_cover : ∀ m : ℕ, 0 < m →
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι),
      Fintype.card ι = 2 * ((4 ^ m - 1) / 3) ∧
      ∃ u v : ι → X m,
        (∀ i, u i ≠ 0 ∧ v i ≠ 0 ∧ u i ≠ v i) ∧
        (∀ a : X m, a ≠ 0 →
          Fintype.card {i : ι // a = u i ∨ a = v i ∨ a = u i + v i} = 2) ∧
        Fintype.card {i : ι // B m (u i) (v i) = 1} =
          Fintype.card {i : ι // B m (u i) (v i) = 0} + 2 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    refine ⟨Fin 2, inferInstance, inferInstance, by decide,
      fun _ => (fun _ => 1, fun _ => 0),
      fun _ => (fun _ => 0, fun _ => 1),
      ?_, ?_, ?_⟩
    · intro i
      refine ⟨?_, ?_, ?_⟩
      · intro h
        have h0 := congrFun (congrArg Prod.fst h) 0
        exact (by decide : (1 : ZMod 2) ≠ 0) h0
      · intro h
        have h0 := congrFun (congrArg Prod.snd h) 0
        exact (by decide : (1 : ZMod 2) ≠ 0) h0
      · intro h
        have h0 := congrFun (congrArg Prod.fst h) 0
        exact (by decide : (1 : ZMod 2) ≠ 0) h0
    · intro a ha
      have hall : ∀ i : Fin 2,
          a = (fun _ => 1, fun _ => 0) ∨
          a = (fun _ => 0, fun _ => 1) ∨
          a = (fun _ => 1, fun _ => 0) + (fun _ => 0, fun _ => 1) := by
        intro _
        rcases zmod2_cases (a.1 0) with h1 | h1 <;> rcases zmod2_cases (a.2 0) with h2 | h2
        · exfalso
          apply ha
          ext j
          · fin_cases j; exact h1
          · fin_cases j; exact h2
        · right; left
          ext j
          · fin_cases j; exact h1
          · fin_cases j; exact h2
        · left
          ext j
          · fin_cases j; exact h1
          · fin_cases j; exact h2
        · right; right
          ext j
          · fin_cases j; simp [h1]
          · fin_cases j; simp [h2]
      have heq : {i : Fin 2 // a = (fun _ => 1, fun _ => 0) ∨
          a = (fun _ => 0, fun _ => 1) ∨
          a = (fun _ => 1, fun _ => 0) + (fun _ => 0, fun _ => 1)} ≃ Fin 2 :=
        { toFun := Subtype.val
          invFun := fun i => ⟨i, hall i⟩
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun _ => rfl }
      rw [Fintype.card_congr heq, Fintype.card_fin]
    · have hB1 : ∀ i : Fin 2,
          B 1 ((fun _ => 1, fun _ => 0) : X 1) ((fun _ => 0, fun _ => 1) : X 1) = 1 := by
        intro _; simp [B, dotProduct]
      have e1 : {i : Fin 2 // B 1 (fun _ => 1, fun _ => 0) (fun _ => 0, fun _ => 1) = 1} ≃ Fin 2 :=
        { toFun := Subtype.val
          invFun := fun i => ⟨i, hB1 i⟩
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun _ => rfl }
      have e0 : IsEmpty {i : Fin 2 // B 1 (fun _ => 1, fun _ => 0) (fun _ => 0, fun _ => 1) = 0} :=
        ⟨fun ⟨i, hi⟩ => (by decide : (1 : ZMod 2) ≠ 0) ((hB1 i).symm.trans hi)⟩
      rw [Fintype.card_congr e1, Fintype.card_fin, Fintype.card_eq_zero]
  | succ m hm ih =>
    rcases ih with ⟨ι, hFin, hDec, hcard, u, v, hne, hcov, hbal⟩
    letI : Fintype ι := hFin
    letI : DecidableEq ι := hDec
    let t0 : X m := (Pi.single ⟨0, hm⟩ (1 : ZMod 2), 0)
    let u' : ι ⊕ (Bool × X m) → X (m + 1) := fun idx =>
      match idx with
      | Sum.inl i => snocX (u i) 0 0
      | Sum.inr (_, x) => snocX x 1 0
    let v' : ι ⊕ (Bool × X m) → X (m + 1) := fun idx =>
      match idx with
      | Sum.inl i => snocX (v i) 0 0
      | Sum.inr (false, x) => snocX (J x) 0 1
      | Sum.inr (true, x) => snocX (J x + t0) 0 1
    refine ⟨ι ⊕ (Bool × X m), inferInstance, inferInstance, ?_, u', v', ?_, ?_, ?_⟩
    · rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, card_X, hcard, card_T_succ]
    · intro idx
      rcases idx with i | ⟨b, x⟩
      · rcases hne i with ⟨hu, hv, huv⟩
        refine ⟨?_, ?_, ?_⟩
        · intro h
          rw [← snocX_zero] at h
          exact hu (snocX_inj h).1
        · intro h
          rw [← snocX_zero] at h
          exact hv (snocX_inj h).1
        · intro h
          exact huv (snocX_inj h).1
      · cases b
        · refine ⟨?_, ?_, ?_⟩
          · intro h
            have hl := congrFun (congrArg Prod.fst h) (Fin.last m)
            simp [u', snocX, Fin.snoc_last] at hl
          · intro h
            have hl := congrFun (congrArg Prod.snd h) (Fin.last m)
            simp [v', snocX, Fin.snoc_last] at hl
          · intro h
            have hl := congrFun (congrArg Prod.fst h) (Fin.last m)
            simp [u', v', snocX, Fin.snoc_last] at hl
        · refine ⟨?_, ?_, ?_⟩
          · intro h
            have hl := congrFun (congrArg Prod.fst h) (Fin.last m)
            simp [u', snocX, Fin.snoc_last] at hl
          · intro h
            have hl := congrFun (congrArg Prod.snd h) (Fin.last m)
            simp [v', snocX, Fin.snoc_last] at hl
          · intro h
            have hl := congrFun (congrArg Prod.fst h) (Fin.last m)
            simp [u', v', snocX, Fin.snoc_last] at hl
    · intro a ha
      rcases zmod2_cases (a.1 (Fin.last m)) with h1 | h1 <;>
        rcases zmod2_cases (a.2 (Fin.last m)) with h2 | h2
      · have hinit_ne : initX a ≠ 0 := by
          intro h0
          apply ha
          have ha_eq : snocX (0 : X m) 0 0 = a :=
            (snocX_eq_iff 0 0 0 a).mpr ⟨h0.symm, h1.symm, h2.symm⟩
          rw [← ha_eq, snocX_zero]
        have hiff_inl : ∀ i : ι,
            (a = u' (Sum.inl i) ∨ a = v' (Sum.inl i) ∨ a = u' (Sum.inl i) + v' (Sum.inl i)) ↔
            (initX a = u i ∨ initX a = v i ∨ initX a = u i + v i) := by
          intro i
          simp only [u', v', snocX_add, add_zero]
          constructor
          · rintro (h | h | h)
            · left; exact ((snocX_eq_iff (u i) 0 0 a).mp h.symm).1.symm
            · right; left; exact ((snocX_eq_iff (v i) 0 0 a).mp h.symm).1.symm
            · right; right; exact ((snocX_eq_iff (u i + v i) 0 0 a).mp h.symm).1.symm
          · rintro (h | h | h)
            · left; exact ((snocX_eq_iff (u i) 0 0 a).mpr ⟨h.symm, h1.symm, h2.symm⟩).symm
            · right; left; exact ((snocX_eq_iff (v i) 0 0 a).mpr ⟨h.symm, h1.symm, h2.symm⟩).symm
            · right; right; exact ((snocX_eq_iff (u i + v i) 0 0 a).mpr ⟨h.symm, h1.symm, h2.symm⟩).symm
        have hno_inr : ∀ p : Bool × X m,
            ¬ (a = u' (Sum.inr p) ∨ a = v' (Sum.inr p) ∨ a = u' (Sum.inr p) + v' (Sum.inr p)) := by
          rintro ⟨b, x⟩ h
          cases b
          · rcases h with h | h | h
            · have hlast := ((snocX_eq_iff x 1 0 a).mp h.symm).2.1
              exact (by decide : (1 : ZMod 2) ≠ 0) (hlast.trans h1)
            · have hlast := ((snocX_eq_iff (J x) 0 1 a).mp h.symm).2.2
              exact (by decide : (1 : ZMod 2) ≠ 0) (hlast.trans h2)
            · simp only [u', v', snocX_add, add_zero, zero_add] at h
              have hlast := ((snocX_eq_iff (x + J x) 1 1 a).mp h.symm).2.1
              exact (by decide : (1 : ZMod 2) ≠ 0) (hlast.trans h1)
          · rcases h with h | h | h
            · have hlast := ((snocX_eq_iff x 1 0 a).mp h.symm).2.1
              exact (by decide : (1 : ZMod 2) ≠ 0) (hlast.trans h1)
            · have hlast := ((snocX_eq_iff (J x + t0) 0 1 a).mp h.symm).2.2
              exact (by decide : (1 : ZMod 2) ≠ 0) (hlast.trans h2)
            · simp only [u', v', snocX_add, add_zero, zero_add] at h
              have hlast := ((snocX_eq_iff (x + (J x + t0)) 1 1 a).mp h.symm).2.1
              exact (by decide : (1 : ZMod 2) ≠ 0) (hlast.trans h1)
        let e : {idx : ι ⊕ (Bool × X m) // a = u' idx ∨ a = v' idx ∨ a = u' idx + v' idx} ≃
            {i : ι // initX a = u i ∨ initX a = v i ∨ initX a = u i + v i} :=
          { toFun := fun ⟨idx, hidx⟩ =>
              match idx, hidx with
              | Sum.inl i, hi => ⟨i, (hiff_inl i).mp hi⟩
              | Sum.inr p, hp => absurd hp (hno_inr p)
            invFun := fun ⟨i, hi⟩ => ⟨Sum.inl i, (hiff_inl i).mpr hi⟩
            left_inv := fun ⟨idx, hidx⟩ => by
              cases idx with
              | inl i => rfl
              | inr p => exact absurd hidx (hno_inr p)
            right_inv := fun ⟨i, _⟩ => rfl }
        rw [Fintype.card_congr e]
        exact hcov (initX a) hinit_ne
      · have hno_inl : ∀ i : ι,
            ¬ (a = u' (Sum.inl i) ∨ a = v' (Sum.inl i) ∨ a = u' (Sum.inl i) + v' (Sum.inl i)) := by
          intro i h
          simp only [u', v', snocX_add, add_zero] at h
          rcases h with h | h | h
          · have hlast := ((snocX_eq_iff (u i) 0 0 a).mp h.symm).2.2
            exact (by decide : (0 : ZMod 2) ≠ 1) (hlast.trans h2)
          · have hlast := ((snocX_eq_iff (v i) 0 0 a).mp h.symm).2.2
            exact (by decide : (0 : ZMod 2) ≠ 1) (hlast.trans h2)
          · have hlast := ((snocX_eq_iff (u i + v i) 0 0 a).mp h.symm).2.2
            exact (by decide : (0 : ZMod 2) ≠ 1) (hlast.trans h2)
        have hchar : ∀ (b : Bool) (x : X m),
            (a = u' (Sum.inr (b, x)) ∨ a = v' (Sum.inr (b, x)) ∨
              a = u' (Sum.inr (b, x)) + v' (Sum.inr (b, x))) ↔
            x = if b then Jinv (initX a + t0) else Jinv (initX a) := by
          intro b x
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte]
            constructor
            · rintro (h | h | h)
              · exfalso
                have hlast := ((snocX_eq_iff x 1 0 a).mp h.symm).2.1
                exact (by decide : (1 : ZMod 2) ≠ 0) (hlast.trans h1)
              · have hx := ((snocX_eq_iff (J x) 0 1 a).mp h.symm).1
                have := congrArg Jinv hx
                simpa [Jinv_J] using this
              · exfalso
                simp only [u', v', snocX_add, add_zero, zero_add] at h
                have hlast := ((snocX_eq_iff (x + J x) 1 1 a).mp h.symm).2.1
                exact (by decide : (1 : ZMod 2) ≠ 0) (hlast.trans h1)
            · intro hx
              right; left
              refine ((snocX_eq_iff (J x) 0 1 a).mpr ⟨?_, h1.symm, h2.symm⟩).symm
              rw [hx, J_Jinv]
          · simp only [↓reduceIte]
            constructor
            · rintro (h | h | h)
              · exfalso
                have hlast := ((snocX_eq_iff x 1 0 a).mp h.symm).2.1
                exact (by decide : (1 : ZMod 2) ≠ 0) (hlast.trans h1)
              · have hx := ((snocX_eq_iff (J x + t0) 0 1 a).mp h.symm).1
                have hJx : J x = initX a + t0 := by
                  calc
                    J x = J x + (t0 + t0) := by rw [x_add_self, add_zero]
                    _ = (J x + t0) + t0 := by rw [add_assoc]
                    _ = initX a + t0 := by rw [hx]
                have := congrArg Jinv hJx
                simpa [Jinv_J] using this
              · exfalso
                simp only [u', v', snocX_add, add_zero, zero_add] at h
                have hlast := ((snocX_eq_iff (x + (J x + t0)) 1 1 a).mp h.symm).2.1
                exact (by decide : (1 : ZMod 2) ≠ 0) (hlast.trans h1)
            · intro hx
              right; left
              refine ((snocX_eq_iff (J x + t0) 0 1 a).mpr ⟨?_, h1.symm, h2.symm⟩).symm
              rw [hx, J_Jinv, add_assoc, x_add_self, add_zero]
        let e : {idx : ι ⊕ (Bool × X m) // a = u' idx ∨ a = v' idx ∨ a = u' idx + v' idx} ≃ Bool :=
          { toFun := fun ⟨idx, hidx⟩ =>
              match idx, hidx with
              | Sum.inl i, hi => absurd hi (hno_inl i)
              | Sum.inr (b, _), _ => b
            invFun := fun b =>
              ⟨Sum.inr (b, if b then Jinv (initX a + t0) else Jinv (initX a)),
                (hchar b _).mpr rfl⟩
            left_inv := fun ⟨idx, hidx⟩ => by
              cases idx with
              | inl i => exact absurd hidx (hno_inl i)
              | inr p =>
                rcases p with ⟨b, x⟩
                have hx := (hchar b x).mp hidx
                apply Subtype.ext
                simp [hx]
            right_inv := fun _ => rfl }
        rw [Fintype.card_congr e, Fintype.card_bool]
      · have hno_inl : ∀ i : ι,
            ¬ (a = u' (Sum.inl i) ∨ a = v' (Sum.inl i) ∨ a = u' (Sum.inl i) + v' (Sum.inl i)) := by
          intro i h
          simp only [u', v', snocX_add, add_zero] at h
          rcases h with h | h | h
          · have hlast := ((snocX_eq_iff (u i) 0 0 a).mp h.symm).2.1
            exact (by decide : (0 : ZMod 2) ≠ 1) (hlast.trans h1)
          · have hlast := ((snocX_eq_iff (v i) 0 0 a).mp h.symm).2.1
            exact (by decide : (0 : ZMod 2) ≠ 1) (hlast.trans h1)
          · have hlast := ((snocX_eq_iff (u i + v i) 0 0 a).mp h.symm).2.1
            exact (by decide : (0 : ZMod 2) ≠ 1) (hlast.trans h1)
        have hchar : ∀ (b : Bool) (x : X m),
            (a = u' (Sum.inr (b, x)) ∨ a = v' (Sum.inr (b, x)) ∨
              a = u' (Sum.inr (b, x)) + v' (Sum.inr (b, x))) ↔
            x = initX a := by
          intro b x
          cases b
          · constructor
            · rintro (h | h | h)
              · exact ((snocX_eq_iff x 1 0 a).mp h.symm).1
              · exfalso
                have hlast := ((snocX_eq_iff (J x) 0 1 a).mp h.symm).2.2
                exact (by decide : (1 : ZMod 2) ≠ 0) (hlast.trans h2)
              · exfalso
                simp only [u', v', snocX_add, add_zero, zero_add] at h
                have hlast := ((snocX_eq_iff (x + J x) 1 1 a).mp h.symm).2.2
                exact (by decide : (1 : ZMod 2) ≠ 0) (hlast.trans h2)
            · intro hx
              left
              exact ((snocX_eq_iff x 1 0 a).mpr ⟨hx, h1.symm, h2.symm⟩).symm
          · constructor
            · rintro (h | h | h)
              · exact ((snocX_eq_iff x 1 0 a).mp h.symm).1
              · exfalso
                have hlast := ((snocX_eq_iff (J x + t0) 0 1 a).mp h.symm).2.2
                exact (by decide : (1 : ZMod 2) ≠ 0) (hlast.trans h2)
              · exfalso
                simp only [u', v', snocX_add, add_zero, zero_add] at h
                have hlast := ((snocX_eq_iff (x + (J x + t0)) 1 1 a).mp h.symm).2.2
                exact (by decide : (1 : ZMod 2) ≠ 0) (hlast.trans h2)
            · intro hx
              left
              exact ((snocX_eq_iff x 1 0 a).mpr ⟨hx, h1.symm, h2.symm⟩).symm
        let e : {idx : ι ⊕ (Bool × X m) // a = u' idx ∨ a = v' idx ∨ a = u' idx + v' idx} ≃ Bool :=
          { toFun := fun ⟨idx, hidx⟩ =>
              match idx, hidx with
              | Sum.inl i, hi => absurd hi (hno_inl i)
              | Sum.inr (b, _), _ => b
            invFun := fun b => ⟨Sum.inr (b, initX a), (hchar b _).mpr rfl⟩
            left_inv := fun ⟨idx, hidx⟩ => by
              cases idx with
              | inl i => exact absurd hidx (hno_inl i)
              | inr p =>
                rcases p with ⟨b, x⟩
                have hx := (hchar b x).mp hidx
                apply Subtype.ext
                simp [hx]
            right_inv := fun _ => rfl }
        rw [Fintype.card_congr e, Fintype.card_bool]
      · have hno_inl : ∀ i : ι,
            ¬ (a = u' (Sum.inl i) ∨ a = v' (Sum.inl i) ∨ a = u' (Sum.inl i) + v' (Sum.inl i)) := by
          intro i h
          simp only [u', v', snocX_add, add_zero] at h
          rcases h with h | h | h
          · have hlast := ((snocX_eq_iff (u i) 0 0 a).mp h.symm).2.1
            exact (by decide : (0 : ZMod 2) ≠ 1) (hlast.trans h1)
          · have hlast := ((snocX_eq_iff (v i) 0 0 a).mp h.symm).2.1
            exact (by decide : (0 : ZMod 2) ≠ 1) (hlast.trans h1)
          · have hlast := ((snocX_eq_iff (u i + v i) 0 0 a).mp h.symm).2.1
            exact (by decide : (0 : ZMod 2) ≠ 1) (hlast.trans h1)
        have hchar : ∀ (b : Bool) (x : X m),
            (a = u' (Sum.inr (b, x)) ∨ a = v' (Sum.inr (b, x)) ∨
              a = u' (Sum.inr (b, x)) + v' (Sum.inr (b, x))) ↔
            x = if b then J (initX a + t0) else J (initX a) := by
          intro b x
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte]
            constructor
            · rintro (h | h | h)
              · exfalso
                have hlast := ((snocX_eq_iff x 1 0 a).mp h.symm).2.2
                exact (by decide : (0 : ZMod 2) ≠ 1) (hlast.trans h2)
              · exfalso
                have hlast := ((snocX_eq_iff (J x) 0 1 a).mp h.symm).2.1
                exact (by decide : (0 : ZMod 2) ≠ 1) (hlast.trans h1)
              · simp only [u', v', snocX_add, add_zero, zero_add] at h
                have hx := ((snocX_eq_iff (x + J x) 1 1 a).mp h.symm).1
                rw [add_J_eq_Jinv] at hx
                have := congrArg J hx
                simpa [J_Jinv] using this
            · intro hx
              right; right
              simp only [u', v', snocX_add, add_zero, zero_add]
              refine ((snocX_eq_iff (x + J x) 1 1 a).mpr ⟨?_, h1.symm, h2.symm⟩).symm
              rw [add_J_eq_Jinv, hx, Jinv_J]
          · simp only [↓reduceIte]
            constructor
            · rintro (h | h | h)
              · exfalso
                have hlast := ((snocX_eq_iff x 1 0 a).mp h.symm).2.2
                exact (by decide : (0 : ZMod 2) ≠ 1) (hlast.trans h2)
              · exfalso
                have hlast := ((snocX_eq_iff (J x + t0) 0 1 a).mp h.symm).2.1
                exact (by decide : (0 : ZMod 2) ≠ 1) (hlast.trans h1)
              · simp only [u', v', snocX_add, add_zero, zero_add] at h
                have hx := ((snocX_eq_iff (x + (J x + t0)) 1 1 a).mp h.symm).1
                rw [← add_assoc, add_J_eq_Jinv] at hx
                have hJx : Jinv x = initX a + t0 := by
                  calc
                    Jinv x = Jinv x + (t0 + t0) := by rw [x_add_self, add_zero]
                    _ = (Jinv x + t0) + t0 := by rw [add_assoc]
                    _ = initX a + t0 := by rw [hx]
                have := congrArg J hJx
                simpa [J_Jinv] using this
            · intro hx
              right; right
              simp only [u', v', snocX_add, add_zero, zero_add]
              refine ((snocX_eq_iff (x + (J x + t0)) 1 1 a).mpr ⟨?_, h1.symm, h2.symm⟩).symm
              rw [← add_assoc, add_J_eq_Jinv, hx, Jinv_J, add_assoc, x_add_self, add_zero]
        let e : {idx : ι ⊕ (Bool × X m) // a = u' idx ∨ a = v' idx ∨ a = u' idx + v' idx} ≃ Bool :=
          { toFun := fun ⟨idx, hidx⟩ =>
              match idx, hidx with
              | Sum.inl i, hi => absurd hi (hno_inl i)
              | Sum.inr (b, _), _ => b
            invFun := fun b =>
              ⟨Sum.inr (b, if b then J (initX a + t0) else J (initX a)),
                (hchar b _).mpr rfl⟩
            left_inv := fun ⟨idx, hidx⟩ => by
              cases idx with
              | inl i => exact absurd hidx (hno_inl i)
              | inr p =>
                rcases p with ⟨b, x⟩
                have hx := (hchar b x).mp hidx
                apply Subtype.ext
                simp [hx]
            right_inv := fun _ => rfl }
        rw [Fintype.card_congr e, Fintype.card_bool]
    · have hB_inl : ∀ i : ι, B (m + 1) (u' (Sum.inl i)) (v' (Sum.inl i)) = B m (u i) (v i) := by
        intro i
        simp [u', v', B_snocX]
      have hB_t0 : B m t0 (J t0) = 1 := by
        simp only [t0, B, J, dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
          zero_add]
        rw [Finset.sum_eq_single ⟨0, hm⟩]
        · simp
        · intro j _ hj
          simp [Pi.single_eq_of_ne hj]
        · intro h
          exact absurd (Finset.mem_univ _) h
      let f : Bool × X m → ZMod 2 := fun p => B (m + 1) (u' (Sum.inr p)) (v' (Sum.inr p))
      let φ : Bool × X m → Bool × X m := fun p => (!p.1, p.2 + t0)
      have hφ_inv : ∀ p : Bool × X m, φ (φ p) = p := by
        rintro ⟨b, x⟩
        simp only [φ, Bool.not_not, add_assoc, x_add_self, add_zero]
      have hf_step : ∀ x : X m, f (true, x + t0) = f (false, x) + 1 := by
        intro x
        simp only [f, u', v', B_snocX, mul_one, mul_zero, add_zero]
        rw [B_add_right, B_J_add, B_add_left, B_self, add_zero, hB_t0]
        have h2 := zmod2_add_self (B m x t0)
        calc
          B m x (J x) + 1 + B m x t0 + B m x t0 + 1
            = B m x (J x) + 1 + (B m x t0 + B m x t0) + 1 := by ring
          _ = B m x (J x) + 1 + 0 + 1 := by rw [h2]
          _ = B m x (J x) + 1 + 1 := by simp
      have hf_flip : ∀ p : Bool × X m, f (φ p) = f p + 1 := by
        rintro ⟨b, x⟩
        cases b
        · exact hf_step x
        · have h := hf_step (x + t0)
          simp only [add_assoc, x_add_self, add_zero] at h
          simp only [φ, Bool.not_true]
          rw [h, add_assoc, zmod2_add_self, add_zero]
      have hnew_eq :
          Fintype.card {p : Bool × X m // f p = 1} =
          Fintype.card {p : Bool × X m // f p = 0} := by
        refine Fintype.card_congr
          { toFun := fun ⟨p, hp⟩ => ⟨φ p, by rw [hf_flip, hp]; decide⟩
            invFun := fun ⟨p, hp⟩ => ⟨φ p, by rw [hf_flip, hp]; decide⟩
            left_inv := fun ⟨p, _⟩ => Subtype.ext (hφ_inv p)
            right_inv := fun ⟨p, _⟩ => Subtype.ext (hφ_inv p) }
      have hsplit : ∀ c : ZMod 2,
          Fintype.card {idx : ι ⊕ (Bool × X m) // B (m + 1) (u' idx) (v' idx) = c} =
          Fintype.card {i : ι // B m (u i) (v i) = c} +
          Fintype.card {p : Bool × X m // f p = c} := by
        intro c
        let e : {idx : ι ⊕ (Bool × X m) // B (m + 1) (u' idx) (v' idx) = c} ≃
            {i : ι // B m (u i) (v i) = c} ⊕ {p : Bool × X m // f p = c} :=
          { toFun := fun ⟨idx, hidx⟩ =>
              match idx, hidx with
              | Sum.inl i, hi => Sum.inl ⟨i, by rw [← hB_inl i]; exact hi⟩
              | Sum.inr p, hp => Sum.inr ⟨p, hp⟩
            invFun := fun s =>
              match s with
              | Sum.inl ⟨i, hi⟩ => ⟨Sum.inl i, by rw [hB_inl i]; exact hi⟩
              | Sum.inr ⟨p, hp⟩ => ⟨Sum.inr p, hp⟩
            left_inv := fun ⟨idx, _⟩ => by cases idx <;> rfl
            right_inv := fun s => by cases s <;> rfl }
        rw [Fintype.card_congr e, Fintype.card_sum]
      rw [hsplit 1, hsplit 0, hbal, hnew_eq]
      ring

private lemma main_proof :
    ∀ m : ℕ, 0 < m →
      let F := ZMod 2
      let X := (Fin m → F) × (Fin m → F)
      let B := fun x y : X => dotProduct x.1 y.2 + dotProduct x.2 y.1
      let T := 2*((4^m-1)/3)
      ∃ u v : Fin T → X,
        (∀ i, u i ≠ 0 ∧ v i ≠ 0 ∧ u i ≠ v i) ∧
        (∀ a : X, a ≠ 0 →
          Nat.card {i : Fin T // a=u i ∨ a=v i ∨ a=u i+v i} = 2) ∧
        Nat.card {i : Fin T // B (u i) (v i)=1} =
          Nat.card {i : Fin T // B (u i) (v i)=0}+2 := by
  intro m hm
  rcases exists_cover m hm with ⟨ι, hFin, hDec, hcard, u, v, hne, hcov, hbal⟩
  letI : Fintype ι := hFin
  letI : DecidableEq ι := hDec
  let T := 2 * ((4 ^ m - 1) / 3)
  let e : Fin T ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => u (e i), fun i => v (e i), ?_, ?_, ?_⟩
  · intro i
    exact hne (e i)
  · intro a ha
    rw [Nat.card_eq_fintype_card]
    have eSub : {i : Fin T // a = u (e i) ∨ a = v (e i) ∨ a = u (e i) + v (e i)} ≃
        {j : ι // a = u j ∨ a = v j ∨ a = u j + v j} :=
      Equiv.subtypeEquiv e (fun _ => Iff.rfl)
    rw [Fintype.card_congr eSub]
    exact hcov a ha
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    have e1 : {i : Fin T // B m (u (e i)) (v (e i)) = 1} ≃ {j : ι // B m (u j) (v j) = 1} :=
      Equiv.subtypeEquiv e (fun _ => Iff.rfl)
    have e0 : {i : Fin T // B m (u (e i)) (v (e i)) = 0} ≃ {j : ι // B m (u j) (v j) = 0} :=
      Equiv.subtypeEquiv e (fun _ => Iff.rfl)
    change Fintype.card {i : Fin T // B m (u (e i)) (v (e i)) = 1} =
      Fintype.card {i : Fin T // B m (u (e i)) (v (e i)) = 0} + 2
    rw [Fintype.card_congr e1, Fintype.card_congr e0]
    exact hbal

end PEqualNP.Outside.L_pcx_470_aux

theorem PEqualNP.Outside.L_pcx_470 : (∀ m : ℕ, 0 < m →
  let F := ZMod 2
  let X := (Fin m → F) × (Fin m → F)
  let B := fun x y : X => dotProduct x.1 y.2 + dotProduct x.2 y.1
  let T := 2*((4^m-1)/3)
  ∃ u v : Fin T → X,
    (∀ i, u i ≠ 0 ∧ v i ≠ 0 ∧ u i ≠ v i) ∧
    (∀ a : X, a ≠ 0 →
      Nat.card {i : Fin T // a=u i ∨ a=v i ∨ a=u i+v i} = 2) ∧
    Nat.card {i : Fin T // B (u i) (v i)=1} =
      Nat.card {i : Fin T // B (u i) (v i)=0}+2) := by
  exact PEqualNP.Outside.L_pcx_470_aux.main_proof

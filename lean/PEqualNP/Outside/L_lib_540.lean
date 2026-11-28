import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_540

private abbrev K := ZMod 2

-- ============================================================
-- Section 1: Basic ZMod 2 / Bool helpers & Linear Shift Steps
-- ============================================================

private lemma zmod2_add_self (a : K) : a + a = 0 := by
  fin_cases a <;> decide

private lemma zmod2_eq_zero_or_one (a : K) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma zmod2_sub_eq_add (a b : K) : a - b = a + b := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> rcases zmod2_eq_zero_or_one b with rfl | rfl <;> decide

private lemma zmod2_neg_eq (a : K) : -a = a := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> decide

private def asField (b : Bool) : K := if b then 1 else 0

private def asBool (a : K) : Bool := decide (a = 1)

private lemma asField_injective : Function.Injective asField := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

private lemma asBool_asField (b : Bool) : asBool (asField b) = b := by
  cases b <;> decide

private lemma asField_asBool (a : K) : asField (asBool a) = a := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> decide

private lemma asBool_injective : Function.Injective asBool := by
  intro a b h
  have := congrArg asField h
  simpa only [asField_asBool] using this

private lemma asField_xor (a b : Bool) : asField (xor a b) = asField a + asField b := by
  cases a <;> cases b <;> decide

private lemma asField_and (a b : Bool) : asField (a && b) = asField a * asField b := by
  cases a <;> cases b <;> decide

private lemma asField_not (a : Bool) : asField (!a) = asField a + 1 := by
  cases a <;> decide

private def toVec {w : Nat} (x : Fin w → Bool) : Fin w → K := fun i => asField (x i)

private def ofVec {w : Nat} (v : Fin w → K) : Fin w → Bool := fun i => asBool (v i)

private lemma toVec_ofVec {w : Nat} (v : Fin w → K) : toVec (ofVec v) = v := by
  funext i; exact asField_asBool (v i)

private lemma ofVec_toVec {w : Nat} (x : Fin w → Bool) : ofVec (toVec x) = x := by
  funext i; exact asBool_asField (x i)

private lemma toVec_injective {w : Nat} : Function.Injective (@toVec w) := by
  intro x y h
  have := congrArg ofVec h
  simpa only [ofVec_toVec] using this

private lemma ofVec_injective {w : Nat} : Function.Injective (@ofVec w) := by
  intro u v h
  have := congrArg toVec h
  simpa only [toVec_ofVec] using this

private def linStepF {d : Nat} (τ : Fin d → K) : (Fin (d + 1) → K) →ₗ[K] (Fin (d + 1) → K) where
  toFun v := Fin.snoc (α := fun _ : Fin (d + 1) => K) (fun j : Fin d => v j.succ)
    (v 0 + ∑ j : Fin d, τ j * v j.succ)
  map_add' u v := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Pi.add_apply, Fin.snoc_last, mul_add, Finset.sum_add_distrib]
      ring
    · simp only [Pi.add_apply, Fin.snoc_castSucc]
  map_smul' c v := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Fin.snoc_last, mul_add,
        Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _; ring
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Fin.snoc_castSucc]

private def linStepFInv {d : Nat} (τ : Fin d → K) : (Fin (d + 1) → K) →ₗ[K] (Fin (d + 1) → K) where
  toFun v := Fin.cons (α := fun _ : Fin (d + 1) => K)
    (v (Fin.last d) + ∑ j : Fin d, τ j * v j.castSucc) (fun j : Fin d => v j.castSucc)
  map_add' u v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Pi.add_apply, Fin.cons_zero, mul_add, Finset.sum_add_distrib]
      ring
    · simp only [Pi.add_apply, Fin.cons_succ]
  map_smul' c v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Fin.cons_zero, mul_add,
        Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _; ring
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Fin.cons_succ]

private lemma linStepFInv_linStepF {d : Nat} (τ : Fin d → K) (v : Fin (d + 1) → K) :
    linStepFInv τ (linStepF τ v) = v := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [linStepFInv, linStepF, LinearMap.coe_mk, AddHom.coe_mk, Fin.cons_zero,
      Fin.snoc_last, Fin.snoc_castSucc]
    rw [add_assoc, zmod2_add_self, add_zero]
  · simp only [linStepFInv, linStepF, LinearMap.coe_mk, AddHom.coe_mk, Fin.cons_succ,
      Fin.snoc_castSucc]

private lemma linStepF_linStepFInv {d : Nat} (τ : Fin d → K) (v : Fin (d + 1) → K) :
    linStepF τ (linStepFInv τ v) = v := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [linStepFInv, linStepF, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_last,
      Fin.cons_zero, Fin.cons_succ]
    rw [add_assoc, zmod2_add_self, add_zero]
  · simp only [linStepFInv, linStepF, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_castSucc,
      Fin.cons_succ]

private lemma linStepF_single_zero {d : Nat} (τ : Fin d → K) :
    linStepF τ (Pi.single (0 : Fin (d + 1)) (1 : K)) = Pi.single (Fin.last d) 1 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [linStepF, Fin.succ_ne_zero]
  · simp [linStepF, Fin.succ_ne_zero, Fin.castSucc_ne_last]

private def phiF {d L : Nat} (taps : Fin L → Fin d → K) :
    Nat → (Fin (d + 1) → K) →ₗ[K] (Fin (d + 1) → K)
  | 0 => LinearMap.id
  | k + 1 =>
    if h : k < L then (linStepF (taps ⟨k, h⟩)).comp (phiF taps k)
    else phiF taps k

private def phiFInv {d L : Nat} (taps : Fin L → Fin d → K) :
    Nat → (Fin (d + 1) → K) →ₗ[K] (Fin (d + 1) → K)
  | 0 => LinearMap.id
  | k + 1 =>
    if h : k < L then (phiFInv taps k).comp (linStepFInv (taps ⟨k, h⟩))
    else phiFInv taps k

private lemma phiFInv_phiF {d L : Nat} (taps : Fin L → Fin d → K) (k : Nat)
    (v : Fin (d + 1) → K) : phiFInv taps k (phiF taps k v) = v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [phiF, phiFInv]
    split_ifs with h
    · simp only [LinearMap.comp_apply, linStepFInv_linStepF, ih]
    · exact ih

private lemma phiF_phiFInv {d L : Nat} (taps : Fin L → Fin d → K) (k : Nat)
    (v : Fin (d + 1) → K) : phiF taps k (phiFInv taps k v) = v := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    simp only [phiF, phiFInv]
    by_cases h : k < L
    · rw [dite_eq_left h, dite_eq_left h, LinearMap.comp_apply, LinearMap.comp_apply, ih, linStepF_linStepFInv]
    · rw [dite_eq_right h, dite_eq_right h]; exact ih v

private lemma phiF_injective {d L : Nat} (taps : Fin L → Fin d → K) (k : Nat) :
    Function.Injective (phiF taps k) := by
  intro u v h
  have := congrArg (phiFInv taps k) h
  simpa only [phiFInv_phiF] using this

private lemma phiF_shift {d L : Nat} (taps : Fin L → Fin d → K) (i r : Nat)
    (p : Fin (d + 1)) (hir : i + r ≤ L) (hpr : p.val + r < d + 1) (v : Fin (d + 1) → K) :
    phiF taps (i + r) v p = phiF taps i v ⟨p.val + r, hpr⟩ := by
  induction r generalizing p with
  | zero =>
    simp only [Nat.add_zero]
  | succ r ih =>
    have hlt : i + r < L := by omega
    have hp : p.val < d := by omega
    let q : Fin d := ⟨p.val, hp⟩
    have hpeq : p = q.castSucc := by ext; rfl
    have hstep : phiF taps ((i + r) + 1) v p = phiF taps (i + r) v q.succ := by
      simp only [phiF, hlt, dite_true, LinearMap.comp_apply]
      rw [hpeq]
      simp only [linStepF, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_castSucc]
    change phiF taps ((i + r) + 1) v p = _
    rw [hstep]
    have ih' := ih q.succ (by omega) (by simp [q]; omega)
    rw [ih']
    exact congrArg (phiF taps i v) (Fin.ext (by simp [q]; omega))

private def disp {d L : Nat} (taps : Fin L → Fin d → K) (i : Fin L) : Fin (d + 1) → K :=
  phiFInv taps (i.val + 1) (Pi.single (Fin.last d) 1)

private lemma phiF_disp {d L : Nat} (taps : Fin L → Fin d → K) (i : Fin L) :
    phiF taps (i.val + 1) (disp taps i) = Pi.single (Fin.last d) 1 :=
  phiF_phiFInv taps (i.val + 1) (Pi.single (Fin.last d) 1)

private lemma disp_ne_zero {d L : Nat} (taps : Fin L → Fin d → K) (i : Fin L) :
    disp taps i ≠ 0 := by
  intro h
  have h1 := phiF_disp taps i
  rw [h, map_zero] at h1
  have h2 := congrFun h1 (Fin.last d)
  simp at h2

-- ============================================================
-- Section 2: Main Reduction from Linear Identity Rows
-- ============================================================

private lemma dotProduct_toggle {w : Nat} (a : Fin w → K) (p₀ : Fin w) (hp₀ : a p₀ = 1)
    (v : Fin w → K) :
    dotProduct a (Function.update v p₀ (v p₀ + 1)) = dotProduct a v + 1 := by
  have hupd : Function.update v p₀ (v p₀ + 1) = v + Pi.single p₀ 1 := by
    funext i
    by_cases hi : i = p₀
    · subst hi; simp
    · simp [Function.update, hi, Pi.single_eq_of_ne hi]
  rw [hupd, dotProduct_add, dotProduct_single, mul_one, hp₀]

private lemma card_dotProduct_eq_zero {d : Nat} (a : Fin (d + 1) → K) (ha : a ≠ 0) :
    2 * (Finset.univ.filter (fun x : Fin (d + 1) → Bool => dotProduct a (toVec x) = 0)).card =
      2 ^ (d + 1) := by
  have hex : ∃ p₀ : Fin (d + 1), a p₀ = 1 := by
    by_contra h
    push_neg at h
    apply ha
    funext i
    rcases zmod2_eq_zero_or_one (a i) with h0 | h1
    · exact h0
    · exact absurd h1 (h i)
  obtain ⟨p₀, hp₀⟩ := hex
  let A := Finset.univ.filter (fun x : Fin (d + 1) → Bool => dotProduct a (toVec x) = 0)
  let B := Finset.univ.filter (fun x : Fin (d + 1) → Bool => dotProduct a (toVec x) = 1)
  let tog : (Fin (d + 1) → Bool) → (Fin (d + 1) → Bool) := fun x => Function.update x p₀ (!(x p₀))
  have htog_vec : ∀ x, toVec (tog x) = Function.update (toVec x) p₀ (toVec x p₀ + 1) := by
    intro x; funext i
    by_cases hi : i = p₀
    · subst hi; simp [tog, toVec, asField_not]
    · simp [tog, toVec, Function.update, hi]
  have htog_dot : ∀ x, dotProduct a (toVec (tog x)) = dotProduct a (toVec x) + 1 := by
    intro x; rw [htog_vec, dotProduct_toggle a p₀ hp₀]
  have htog_inv : ∀ x, tog (tog x) = x := by
    intro x; funext i
    by_cases hi : i = p₀
    · subst hi; simp [tog]
    · simp [tog, Function.update, hi]
  have hcardAB : A.card = B.card := by
    refine Finset.card_bij (fun x _ => tog x) ?_ ?_ ?_
    · intro x hx
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [htog_dot, hx, zero_add]
    · intro x₁ _ x₂ _ h
      have := congrArg tog h
      simpa only [htog_inv] using this
    · intro y hy
      refine ⟨tog y, ?_, htog_inv y⟩
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [htog_dot, hy, zmod2_add_self]
  have hunion : A ∪ B = Finset.univ := by
    ext x
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact zmod2_eq_zero_or_one (dotProduct a (toVec x))
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hxA hxB
    rw [hxA] at hxB
    exact absurd hxB (by decide)
  have htot : A.card + B.card = 2 ^ (d + 1) := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_pi]
    simp
  change 2 * A.card = 2 ^ (d + 1)
  omega

private lemma card_vec_dotProduct_eq_one {d : Nat} (v : Fin (d + 1) → K) (hv : v ≠ 0) :
    2 * (Finset.univ.filter (fun a : Fin (d + 1) → K => dotProduct a v = 1)).card =
      2 ^ (d + 1) := by
  have hex : ∃ p₀ : Fin (d + 1), v p₀ = 1 := by
    by_contra h
    push_neg at h
    apply hv
    funext i
    rcases zmod2_eq_zero_or_one (v i) with h0 | h1
    · exact h0
    · exact absurd h1 (h i)
  obtain ⟨p₀, hp₀⟩ := hex
  let A := Finset.univ.filter (fun a : Fin (d + 1) → K => dotProduct a v = 1)
  let B := Finset.univ.filter (fun a : Fin (d + 1) → K => dotProduct a v = 0)
  let tog : (Fin (d + 1) → K) → (Fin (d + 1) → K) := fun a => Function.update a p₀ (a p₀ + 1)
  have htog_dot : ∀ a, dotProduct (tog a) v = dotProduct a v + 1 := by
    intro a
    rw [dotProduct_comm, dotProduct_toggle v p₀ hp₀, dotProduct_comm]
  have htog_inv : ∀ a, tog (tog a) = a := by
    intro a; funext i
    by_cases hi : i = p₀
    · subst hi; simp [tog, add_assoc, zmod2_add_self]
    · simp [tog, Function.update, hi]
  have hcardAB : A.card = B.card := by
    refine Finset.card_bij (fun a _ => tog a) ?_ ?_ ?_
    · intro a ha
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [htog_dot, ha, zmod2_add_self]
    · intro a₁ _ a₂ _ h
      have := congrArg tog h
      simpa only [htog_inv] using this
    · intro b hb
      refine ⟨tog b, ?_, htog_inv b⟩
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      rw [htog_dot, hb, zero_add]
  have hunion : A ∪ B = Finset.univ := by
    ext a
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rcases zmod2_eq_zero_or_one (dotProduct a v) with h0 | h1
    · exact Or.inr h0
    · exact Or.inl h1
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a haA haB
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at haA haB
    rw [haA] at haB
    exact absurd haB (by decide)
  have htot : A.card + B.card = 2 ^ (d + 1) := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_pi]
    simp [ZMod.card]
  change 2 * A.card = 2 ^ (d + 1)
  omega

private def winVec {d L : Nat} (word : Fin (L + d + 1) → Bool) (r : Nat) (hr : r ≤ L) :
    Fin (d + 1) → K :=
  fun pos => asField (word ⟨r + pos.val, by omega⟩)

private lemma winVec_congr {d L : Nat} (word : Fin (L + d + 1) → Bool) {r₁ r₂ : Nat}
    (hr₁ : r₁ ≤ L) (hr₂ : r₂ ≤ L) (h : r₁ = r₂) :
    winVec word r₁ hr₁ = winVec word r₂ hr₂ := by
  subst h; rfl

private lemma winVec_ext {d L : Nat} {w₁ w₂ : Fin (L + d + 1) → Bool}
    (h : ∀ (r : Nat) (hr : r ≤ L), winVec w₁ r hr = winVec w₂ r hr) : w₁ = w₂ := by
  funext k
  apply asField_injective
  by_cases hk : k.val < L
  · have h0 := congrFun (h k.val (by omega)) 0
    simpa only [winVec, Fin.val_zero, Nat.add_zero] using h0
  · have hL := congrFun (h L (le_refl L)) ⟨k.val - L, by omega⟩
    have heq : (⟨L + (k.val - L), by omega⟩ : Fin (L + d + 1)) = k := by
      ext; simp; omega
    simpa only [winVec, heq] using hL

private lemma fin_ofNat_eq_mk {n k : Nat} [NeZero n] (hk : k < n) :
    Fin.ofNat n k = ⟨k, hk⟩ := by
  ext
  simp [Fin.ofNat, Nat.mod_eq_of_lt hk]

private lemma buildFromLinearRows {d L : Nat}
    (taps : Fin L → Fin d → K)
    (hId : ∀ v, phiF taps L v = v)
    (I : Finset (Fin L))
    (a : Fin (d + 1) → K)
    (hIne : I.Nonempty)
    (hInj : ∀ i₁ ∈ I, ∀ i₂ ∈ I, disp taps i₁ = disp taps i₂ → i₁ = i₂)
    (hDot : ∀ i ∈ I, dotProduct a (disp taps i) = 1)
    (hSize : 2 ^ (d + 1) * min L (2 ^ (d + 1)) ≤ 10 * 2 ^ (d + 1) * I.card) :
    let w := d + 1
    let D := 2 ^ w
    let X := Fin w → Bool
    let S := Fin L × (Fin (w + 1) → Bool)
    ∃ (m : Nat) (edge : Fin m → X × X) (base : S → Bool) (port : Bool → Fin m → S),
      D * min L D ≤ 20 * m ∧ Function.Injective edge ∧
      (∀ u v : Fin m, (edge u).1 ≠ (edge v).2) ∧
      ∀ rev : Bool, Function.Injective (port rev) ∧ (∀ j, base (port rev j) = false) ∧
        ∀ enabled : Finset (Fin m), ∀ x y : X,
          (Finset.univ.filter (fun word : Fin (L + d + 1) → Bool =>
            (∀ pos : Fin w,
              word (Fin.ofNat (L + d + 1) pos.val) = x pos ∧
              word (Fin.ofNat (L + d + 1) (L + pos.val)) = y pos) ∧
            ∀ i : Fin L,
              let s : S := (i, fun off => word (Fin.ofNat (L + d + 1) (i.val + off.val)))
              base s = true ∨ s ∈ enabled.image (port rev))).card =
                (if x = y then 1 else 0) +
                (if ∃ j ∈ enabled, edge j = (if rev then (y, x) else (x, y)) then 1 else 0) := by
  classical
  haveI : NeZero (L + d + 1) := ⟨by omega⟩
  let w := d + 1
  let D := 2 ^ w
  let X := Fin w → Bool
  let S := Fin L × (Fin (w + 1) → Bool)
  have ha : a ≠ 0 := by
    obtain ⟨i₀, hi₀⟩ := hIne
    intro h0
    have hd := hDot i₀ hi₀
    rw [h0, zero_dotProduct] at hd
    exact absurd hd (by decide)
  let A : Finset X := Finset.univ.filter (fun x : X => dotProduct a (toVec x) = 0)
  have hAcard : 2 * A.card = D := card_dotProduct_eq_zero a ha
  let P : Finset (X × Fin L) := A ×ˢ I
  let m : Nat := P.card
  have hm : m = A.card * I.card := Finset.card_product A I
  let e : Fin m ≃ {p : X × Fin L // p ∈ P} := (Fintype.equivFinOfCardEq (Fintype.card_coe P)).symm
  let edge : Fin m → X × X := fun j =>
    let p := (e j).1
    (p.1, ofVec (toVec p.1 + disp taps p.2))
  let base : S → Bool := fun s =>
    decide (asField (s.2 (Fin.last w)) =
      asField (s.2 0) + ∑ j : Fin d, taps s.1 j * asField (s.2 j.succ.castSucc))
  let flip : Fin L → (Fin w → K) → S := fun i u =>
    (i, Fin.snoc (α := fun _ : Fin (w + 1) => Bool) (ofVec u)
      (asBool (u 0 + ∑ j : Fin d, taps i j * u j.succ + 1)))
  let port : Bool → Fin m → S := fun rev j =>
    let p := (e j).1
    let u := if rev then toVec p.1 + disp taps p.2 else toVec p.1
    flip p.2 (phiF taps p.2.val u)
  -- Helper properties of edge and port
  have hmemA : ∀ j : Fin m, dotProduct a (toVec (edge j).1) = 0 := by
    intro j
    have hp := (Finset.mem_product.mp (e j).2).1
    exact (Finset.mem_filter.mp hp).2
  have hmemB : ∀ j : Fin m, dotProduct a (toVec (edge j).2) = 1 := by
    intro j
    have hp := Finset.mem_product.mp (e j).2
    have h1 := (Finset.mem_filter.mp hp.1).2
    have h2 := hDot (e j).1.2 hp.2
    show dotProduct a (toVec (ofVec (toVec (e j).1.1 + disp taps (e j).1.2))) = 1
    rw [toVec_ofVec, dotProduct_add, h1, h2, zero_add]
  have hedge_inj : Function.Injective edge := by
    intro j₁ j₂ h
    have h1 : (e j₁).1.1 = (e j₂).1.1 := by simpa [edge] using congrArg Prod.fst h
    have h2 : ofVec (toVec (e j₁).1.1 + disp taps (e j₁).1.2) =
        ofVec (toVec (e j₂).1.1 + disp taps (e j₂).1.2) := by
      simpa [edge] using congrArg Prod.snd h
    have h2' := ofVec_injective h2
    rw [h1] at h2'
    have hdisp : disp taps (e j₁).1.2 = disp taps (e j₂).1.2 := add_left_cancel h2'
    have hi : (e j₁).1.2 = (e j₂).1.2 :=
      hInj _ (Finset.mem_product.mp (e j₁).2).2 _ (Finset.mem_product.mp (e j₂).2).2 hdisp
    apply e.injective
    apply Subtype.ext
    exact Prod.ext h1 hi
  have hedge_disj : ∀ u v : Fin m, (edge u).1 ≠ (edge v).2 := by
    intro u v h
    have h1 := hmemA u
    have h2 := hmemB v
    rw [h] at h1
    rw [h1] at h2
    exact absurd h2 (by decide)
  have hflip_inj : ∀ i₁ i₂ u₁ u₂, flip i₁ u₁ = flip i₂ u₂ → i₁ = i₂ ∧ u₁ = u₂ := by
    intro i₁ i₂ u₁ u₂ h
    have hi : i₁ = i₂ := congrArg Prod.fst h
    subst hi
    refine ⟨rfl, ?_⟩
    have hv : Fin.snoc (α := fun _ : Fin (w + 1) => Bool) (ofVec u₁)
        (asBool (u₁ 0 + ∑ j : Fin d, taps i₁ j * u₁ j.succ + 1)) =
      Fin.snoc (α := fun _ : Fin (w + 1) => Bool) (ofVec u₂)
        (asBool (u₂ 0 + ∑ j : Fin d, taps i₁ j * u₂ j.succ + 1)) := congrArg Prod.snd h
    apply ofVec_injective
    funext p
    have hp := congrFun hv p.castSucc
    simpa only [Fin.snoc_castSucc] using hp
  have hbase_flip : ∀ i u, base (flip i u) = false := by
    intro i u
    simp only [base, flip, Fin.snoc_last, asField_asBool, decide_eq_false_iff_not]
    have h0 : (Fin.snoc (α := fun _ : Fin (w + 1) => Bool) (ofVec u)
        (asBool (u 0 + ∑ j : Fin d, taps i j * u j.succ + 1))) 0 = ofVec u 0 := by
      change Fin.snoc _ _ ((0 : Fin w).castSucc) = _
      rw [Fin.snoc_castSucc]
    have hsucc : ∀ j : Fin d, (Fin.snoc (α := fun _ : Fin (w + 1) => Bool) (ofVec u)
        (asBool (u 0 + ∑ j : Fin d, taps i j * u j.succ + 1))) j.succ.castSucc = ofVec u j.succ := by
      intro j; rw [Fin.snoc_castSucc]
    simp only [h0, hsucc, ofVec, asField_asBool]
    intro heq
    have h1 : (1 : K) = 0 := by
      have := congrArg (fun z => z + (u 0 + ∑ j : Fin d, taps i j * u j.succ)) heq
      rw [add_comm (u 0 + ∑ j : Fin d, taps i j * u j.succ) 1, add_assoc (1 : K),
        zmod2_add_self, add_zero] at this
      exact this
    exact one_ne_zero h1
  -- Window transition equivalences
  have hbase_iff : ∀ (word : Fin (L + d + 1) → Bool) (i : Fin L),
      base (i, fun off => word (Fin.ofNat (L + d + 1) (i.val + off.val))) = true ↔
        winVec word (i.val + 1) (by omega) = linStepF (taps i) (winVec word i.val (by omega)) := by
    intro word i
    have hmk : ∀ off : Fin (w + 1),
        Fin.ofNat (L + d + 1) (i.val + off.val) = ⟨i.val + off.val, by omega⟩ :=
      fun off => fin_ofNat_eq_mk (by omega)
    simp only [base, decide_eq_true_eq, hmk]
    constructor
    · intro h
      funext p
      refine Fin.lastCases ?_ (fun j => ?_) p
      · simp only [winVec, linStepF, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_last]
        have heq1 : (⟨i.val + 1 + (Fin.last d).val, by omega⟩ : Fin (L + d + 1)) =
            ⟨i.val + (Fin.last w).val, by omega⟩ := by ext; simp [w]; omega
        have heq0 : (⟨i.val + (0 : Fin (d + 1)).val, by omega⟩ : Fin (L + d + 1)) =
            ⟨i.val + (0 : Fin (w + 1)).val, by omega⟩ := by ext; simp
        have heqj : ∀ j : Fin d,
            (⟨i.val + j.succ.val, by omega⟩ : Fin (L + d + 1)) =
            ⟨i.val + j.succ.castSucc.val, by omega⟩ := by intro j; ext; simp
        simp only [heq1, heq0, heqj]
        exact h
      · simp only [winVec, linStepF, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_castSucc]
        congr 2; ext; simp; omega
    · intro h
      have hlast := congrFun h (Fin.last d)
      simp only [winVec, linStepF, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_last] at hlast
      have heq1 : (⟨i.val + (Fin.last w).val, by omega⟩ : Fin (L + d + 1)) =
          ⟨i.val + 1 + (Fin.last d).val, by omega⟩ := by ext; simp [w]; omega
      have heq0 : (⟨i.val + (0 : Fin (w + 1)).val, by omega⟩ : Fin (L + d + 1)) =
          ⟨i.val + (0 : Fin (d + 1)).val, by omega⟩ := by ext; simp
      have heqj : ∀ j : Fin d,
          (⟨i.val + j.succ.castSucc.val, by omega⟩ : Fin (L + d + 1)) =
          ⟨i.val + j.succ.val, by omega⟩ := by intro j; ext; simp
      simp only [heq1, heq0, heqj]
      exact hlast
  have hflip_iff : ∀ (word : Fin (L + d + 1) → Bool) (i : Fin L) (i' : Fin L) (u : Fin w → K),
      (i, fun off => word (Fin.ofNat (L + d + 1) (i.val + off.val))) = flip i' u ↔
        i = i' ∧ winVec word i.val (by omega) = u ∧
        winVec word (i.val + 1) (by omega) = linStepF (taps i) u + Pi.single (Fin.last d) 1 := by
    intro word i i' u
    have hmk : ∀ off : Fin (w + 1),
        Fin.ofNat (L + d + 1) (i.val + off.val) = ⟨i.val + off.val, by omega⟩ :=
      fun off => fin_ofNat_eq_mk (by omega)
    constructor
    · intro h
      have hi : i = i' := congrArg Prod.fst h
      subst hi
      have hs : (fun off : Fin (w + 1) => word ⟨i.val + off.val, by omega⟩) =
          Fin.snoc (α := fun _ : Fin (w + 1) => Bool) (ofVec u)
            (asBool (u 0 + ∑ j : Fin d, taps i j * u j.succ + 1)) := by
        simpa only [flip, hmk] using congrArg Prod.snd h
      have hwin : winVec word i.val (by omega) = u := by
        funext p
        have hp := congrFun hs p.castSucc
        simp only [Fin.snoc_castSucc, ofVec, Fin.val_castSucc] at hp
        simp only [winVec]
        rw [hp, asField_asBool]
      refine ⟨rfl, hwin, ?_⟩
      funext p
      refine Fin.lastCases ?_ (fun j => ?_) p
      · have hl := congrFun hs (Fin.last w)
        simp only [Fin.snoc_last] at hl
        simp only [winVec, Pi.add_apply, linStepF, LinearMap.coe_mk, AddHom.coe_mk,
          Fin.snoc_last, Pi.single_eq_same]
        have heq1 : (⟨i.val + 1 + (Fin.last d).val, by omega⟩ : Fin (L + d + 1)) =
            ⟨i.val + (Fin.last w).val, by omega⟩ := by ext; simp [w]; omega
        rw [heq1, hl, asField_asBool]
      · simp only [winVec, Pi.add_apply, linStepF, LinearMap.coe_mk, AddHom.coe_mk,
          Fin.snoc_castSucc, Pi.single_eq_of_ne (Fin.castSucc_ne_last j), add_zero]
        have hp := congrFun hwin j.succ
        simp only [winVec] at hp
        rw [← hp]
        congr 2; ext; simp; omega
    · rintro ⟨rfl, hwin, hnext⟩
      dsimp only [flip]
      refine Prod.ext rfl ?_
      dsimp only
      funext off
      rw [hmk off]
      refine Fin.lastCases ?_ (fun p => ?_) off
      · simp only [Fin.snoc_last]
        apply asField_injective
        rw [asField_asBool]
        have hl := congrFun hnext (Fin.last d)
        simp only [winVec, Pi.add_apply, linStepF, LinearMap.coe_mk, AddHom.coe_mk,
          Fin.snoc_last, Pi.single_eq_same] at hl
        have heq1 : (⟨i.val + (Fin.last w).val, by omega⟩ : Fin (L + d + 1)) =
            ⟨i.val + 1 + (Fin.last d).val, by omega⟩ := by ext; simp [w]; omega
        rw [heq1]
        exact hl
      · simp only [Fin.snoc_castSucc, ofVec]
        apply asField_injective
        rw [asField_asBool]
        exact congrFun hwin p
  -- Default word construction
  let defWord : (Fin w → K) → Fin (L + d + 1) → Bool := fun u k =>
    asBool (if h : k.val < L then phiF taps k.val u 0 else phiF taps L u ⟨k.val - L, by omega⟩)
  have hdefWin : ∀ (u : Fin w → K) (r : Nat) (hr : r ≤ L),
      winVec (defWord u) r hr = phiF taps r u := by
    intro u r hr
    funext pos
    simp only [winVec, defWord, asField_asBool]
    split_ifs with hlt
    · have hsh := phiF_shift taps r pos.val 0 (by omega) (by have := pos.isLt; simp; omega) u
      simpa only [Fin.val_zero, Nat.zero_add] using hsh
    · have hsh := phiF_shift taps r (L - r) ⟨r + pos.val - L, by omega⟩ (by omega) (by simp; omega) u
      have h1 : r + (L - r) = L := by omega
      have h2 : (⟨r + pos.val - L + (L - r), by omega⟩ : Fin (d + 1)) = pos := by
        ext; simp; omega
      rw [h1, h2] at hsh
      exact hsh
  -- Port word construction
  let portWord : (Fin w → K) → (Fin w → K) → Fin L → Fin (L + d + 1) → Bool :=
    fun src dst i₀ k => if k.val < i₀.val + d + 1 then defWord src k else defWord dst k
  have hportWin_le : ∀ (src dst : Fin w → K) (i₀ : Fin L) (r : Nat) (hr : r ≤ L),
      r ≤ i₀.val → winVec (portWord src dst i₀) r hr = phiF taps r src := by
    intro src dst i₀ r hr hle
    funext pos
    have hlt : r + pos.val < i₀.val + d + 1 := by have := pos.isLt; omega
    simp only [winVec, portWord, hlt, ite_true]
    exact congrFun (hdefWin src r hr) pos
  have hportWin_gt : ∀ (src dst : Fin w → K) (i₀ : Fin L)
      (hjump : phiF taps (i₀.val + 1) dst = phiF taps (i₀.val + 1) src + Pi.single (Fin.last d) 1)
      (r : Nat) (hr : r ≤ L),
      i₀.val + 1 ≤ r → winVec (portWord src dst i₀) r hr = phiF taps r dst := by
    intro src dst i₀ hjump r hr hge
    funext pos
    simp only [winVec, portWord]
    split_ifs with hlt
    · have hq : r + pos.val - (i₀.val + 1) < d := by omega
      let q : Fin (d + 1) := ⟨r + pos.val - (i₀.val + 1), by omega⟩
      have hqne : q ≠ Fin.last d := by intro heq; have := congrArg Fin.val heq; simp [q] at this; omega
      have hsrc := congrFun (hdefWin src (i₀.val + 1) (by omega)) q
      have hdst := congrFun (hdefWin dst (i₀.val + 1) (by omega)) q
      have hidx : (⟨i₀.val + 1 + q.val, by omega⟩ : Fin (L + d + 1)) = ⟨r + pos.val, by omega⟩ := by
        ext; simp [q]; omega
      simp only [winVec, hidx] at hsrc hdst
      have hagree : phiF taps (i₀.val + 1) src q = phiF taps (i₀.val + 1) dst q := by
        rw [hjump]; simp [Pi.single_eq_of_ne hqne]
      have hdef_dst := congrFun (hdefWin dst r hr) pos
      simp only [winVec] at hdef_dst
      rw [hsrc, hagree, ← hdst, hdef_dst]
    · exact congrFun (hdefWin dst r hr) pos
  -- Assemble all conclusions
  refine ⟨m, edge, base, port, ?_, hedge_inj, hedge_disj, ?_⟩
  · have : 20 * m = 10 * D * I.card := by
      rw [hm]
      have h1 : 20 * (A.card * I.card) = 10 * (2 * A.card) * I.card := by ring
      rw [h1, hAcard]
    rw [this]; exact hSize
  · intro rev
    refine ⟨?_, ?_, ?_⟩
    · -- port rev injective
      intro j₁ j₂ h
      obtain ⟨hi, hphi⟩ := hflip_inj _ _ _ _ h
      have hi_val : (e j₁).1.2.val = (e j₂).1.2.val := congrArg Fin.val hi
      rw [hi_val] at hphi
      have hu := phiF_injective taps (e j₂).1.2.val hphi
      have hx : (e j₁).1.1 = (e j₂).1.1 := by
        apply toVec_injective
        cases rev
        · simp only [Bool.false_eq_true, ite_false] at hu
          exact hu
        · simp only [ite_true] at hu
          rw [hi] at hu
          exact add_right_cancel hu
      apply e.injective; apply Subtype.ext; exact Prod.ext hx hi
    · -- base (port rev j) = false
      intro j
      exact hbase_flip _ _
    · -- Exact word count
      intro enabled x y
      let Pred : (Fin (L + d + 1) → Bool) → Prop := fun word =>
        (∀ pos : Fin w,
          word (Fin.ofNat (L + d + 1) pos.val) = x pos ∧
          word (Fin.ofNat (L + d + 1) (L + pos.val)) = y pos) ∧
        ∀ i : Fin L,
          let s : S := (i, fun off => word (Fin.ofNat (L + d + 1) (i.val + off.val)))
          base s = true ∨ s ∈ enabled.image (port rev)
      have hend_iff : ∀ word : Fin (L + d + 1) → Bool,
          (∀ pos : Fin w,
            word (Fin.ofNat (L + d + 1) pos.val) = x pos ∧
            word (Fin.ofNat (L + d + 1) (L + pos.val)) = y pos) ↔
          (winVec word 0 (Nat.zero_le L) = toVec x ∧ winVec word L (le_refl L) = toVec y) := by
        intro word
        have hmk0 : ∀ pos : Fin w, Fin.ofNat (L + d + 1) pos.val = ⟨0 + pos.val, by omega⟩ :=
          fun pos => by simpa using fin_ofNat_eq_mk (n := L + d + 1) (k := pos.val) (by omega)
        have hmkL : ∀ pos : Fin w, Fin.ofNat (L + d + 1) (L + pos.val) = ⟨L + pos.val, by omega⟩ :=
          fun pos => fin_ofNat_eq_mk (by omega)
        constructor
        · intro h
          refine ⟨funext fun pos => ?_, funext fun pos => ?_⟩
          · simp only [winVec, toVec, ← hmk0 pos, (h pos).1]
          · simp only [winVec, toVec, ← hmkL pos, (h pos).2]
        · rintro ⟨h0, hL⟩ pos
          refine ⟨asField_injective ?_, asField_injective ?_⟩
          · rw [hmk0 pos]; exact congrFun h0 pos
          · rw [hmkL pos]; exact congrFun hL pos
      -- Helper: any Pred word is either defWord (with x=y) or portWord (for some j ∈ enabled)
      have hclassify : ∀ word, Pred word →
          (x = y ∧ word = defWord (toVec x)) ∨
          (∃ j ∈ enabled, edge j = (if rev then (y, x) else (x, y)) ∧
            word = portWord (toVec x) (toVec y) (e j).1.2) := by
        intro word hpred
        have ⟨hstart, hfin⟩ := (hend_iff word).mp hpred.1
        let bad := Finset.univ.filter (fun i : Fin L =>
          base (i, fun off => word (Fin.ofNat (L + d + 1) (i.val + off.val))) = false)
        by_cases hbad : bad.Nonempty
        · -- Uses at least one port: take earliest row i₁
          let i₁ := bad.min' hbad
          have hi₁_mem : i₁ ∈ bad := Finset.min'_mem bad hbad
          have hi₁_base : base (i₁, fun off => word (Fin.ofNat (L + d + 1) (i₁.val + off.val))) = false :=
            (Finset.mem_filter.mp hi₁_mem).2
          have hpre : ∀ r (hr : r ≤ L), r ≤ i₁.val → winVec word r hr = phiF taps r (toVec x) := by
            intro r hr hle
            induction r with
            | zero => simpa [phiF] using hstart
            | succ r ih =>
              have hrlt : r < L := by omega
              let ir : Fin L := ⟨r, hrlt⟩
              have hir_not_bad : ir ∉ bad := by
                intro hmem
                have hmin := Finset.min'_le bad ir hmem
                have : i₁.val ≤ r := hmin
                omega
              have hir_base : base (ir, fun off => word (Fin.ofNat (L + d + 1) (ir.val + off.val))) = true := by
                by_cases hb : base (ir, fun off => word (Fin.ofNat (L + d + 1) (ir.val + off.val))) = true
                · exact hb
                · have hmem : ir ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ ir, Bool.eq_false_iff.mpr hb⟩
                  exact absurd hmem hir_not_bad
              have hstep := (hbase_iff word ir).mp hir_base
              rw [hstep, ih (by omega) (by omega)]
              simp [phiF, hrlt, ir]
          -- At row i₁, word must use some port rev j
          have hport_mem : (i₁, fun off => word (Fin.ofNat (L + d + 1) (i₁.val + off.val))) ∈
              enabled.image (port rev) := by
            rcases hpred.2 i₁ with hb | hp
            · rw [hi₁_base] at hb; exact absurd hb (by decide)
            · exact hp
          obtain ⟨j, hj_en, hj_eq⟩ := Finset.mem_image.mp hport_mem
          let xj := (e j).1.1
          let ij := (e j).1.2
          let yj := ofVec (toVec xj + disp taps ij)
          let src : Fin w → K := if rev then toVec xj + disp taps ij else toVec xj
          let dst : Fin w → K := if rev then toVec xj else toVec xj + disp taps ij
          have hj_eq' : (i₁, fun off => word (Fin.ofNat (L + d + 1) (i₁.val + off.val))) =
              flip ij (phiF taps ij.val src) := hj_eq.symm
          obtain ⟨hi_eq, hwin_i₁, hwin_i₁_succ⟩ := (hflip_iff word i₁ ij (phiF taps ij.val src)).mp hj_eq'
          have hsrc_eq : toVec x = src := by
            have h1 := hpre i₁.val (by omega) (le_refl _)
            rw [h1] at hwin_i₁
            rw [← hi_eq] at hwin_i₁
            exact phiF_injective taps i₁.val hwin_i₁
          have hdst_jump : phiF taps (i₁.val + 1) dst =
              phiF taps (i₁.val + 1) src + Pi.single (Fin.last d) 1 := by
            have hsd : dst = src + disp taps i₁ := by
              rw [hi_eq]
              cases rev
              · simp only [src, dst, Bool.false_eq_true, ite_false]
              · simp only [src, dst, ite_true]
                symm
                rw [add_assoc]
                have hz : disp taps ij + disp taps ij = 0 := by funext p; exact zmod2_add_self _
                rw [hz, add_zero]
            rw [hsd, map_add, phiF_disp]
          have hwin_succ_dst : winVec word (i₁.val + 1) (by omega) = phiF taps (i₁.val + 1) dst := by
            rw [hwin_i₁_succ, hdst_jump]
            simp only [phiF, i₁.isLt, dite_true, LinearMap.comp_apply, ← hi_eq]
          -- Show dotProduct a dst ≠ dotProduct a src' for any port rev j'
          have hdot_dst : dotProduct a dst = if rev then 0 else 1 := by
            cases rev
            · simp only [dst, ite_false]
              simpa [edge, toVec_ofVec] using hmemB j
            · simp only [dst, ite_true]
              simpa [edge] using hmemA j
          -- For all r ≥ i₁.val + 1, word follows base and equals phiF taps r dst
          have hpost : ∀ k (hk : i₁.val + 1 + k ≤ L),
              winVec word (i₁.val + 1 + k) hk = phiF taps (i₁.val + 1 + k) dst := by
            intro k
            induction k with
            | zero =>
              intro hk; simpa using hwin_succ_dst
            | succ k ih =>
              intro hk
              let r := i₁.val + 1 + k
              have hrlt : r < L := by omega
              let ir : Fin L := ⟨r, hrlt⟩
              have hwin_r : winVec word r (by omega) = phiF taps r dst := ih (by omega)
              have hir_base : base (ir, fun off => word (Fin.ofNat (L + d + 1) (ir.val + off.val))) = true := by
                rcases hpred.2 ir with hb | hp
                · exact hb
                · exfalso
                  obtain ⟨j', _, hj'_eq⟩ := Finset.mem_image.mp hp
                  let src' : Fin w → K := if rev then toVec (e j').1.1 + disp taps (e j').1.2 else toVec (e j').1.1
                  obtain ⟨hi'_eq, hwin_r', _⟩ :=
                    (hflip_iff word ir (e j').1.2 (phiF taps (e j').1.2.val src')).mp hj'_eq.symm
                  rw [hwin_r] at hwin_r'
                  have hr_eq : r = (e j').1.2.val := congrArg Fin.val hi'_eq
                  rw [← hr_eq] at hwin_r'
                  have hdst_eq_src' : dst = src' := phiF_injective taps r hwin_r'
                  have hdot_src' : dotProduct a src' = if rev then 1 else 0 := by
                    cases rev
                    · simp only [src', ite_false]; simpa [edge] using hmemA j'
                    · simp only [src', ite_true]; simpa [edge, toVec_ofVec] using hmemB j'
                  rw [hdst_eq_src', hdot_src'] at hdot_dst
                  cases rev <;> simp at hdot_dst
              have hstep := (hbase_iff word ir).mp hir_base
              have hidx : i₁.val + 1 + (k + 1) = ir.val + 1 := by simp [ir, r]; omega
              rw [winVec_congr word hk (by omega) hidx]
              rw [hstep, show winVec word ir.val (by omega) = phiF taps r dst from hwin_r]
              rw [hidx]
              simp [phiF, hrlt, ir, r]
          have hdst_eq_y : toVec y = dst := by
            have hL := hpost (L - (i₁.val + 1)) (by omega)
            have h1 : i₁.val + 1 + (L - (i₁.val + 1)) = L := by omega
            have hL' : winVec word L (le_refl L) = phiF taps L dst := by
              rw [← winVec_congr word (by omega) (le_refl L) h1, hL, h1]
            rw [hfin, hId] at hL'
            exact hL'
          have hedge_eq : edge j = (if rev then (y, x) else (x, y)) := by
            cases rev
            · simp only [Bool.false_eq_true, ite_false, src, dst] at hsrc_eq hdst_eq_y ⊢
              apply Prod.ext
              · exact (toVec_injective hsrc_eq).symm
              · apply toVec_injective; rw [toVec_ofVec]; exact hdst_eq_y.symm
            · simp only [ite_true, src, dst] at hsrc_eq hdst_eq_y ⊢
              apply Prod.ext
              · exact (toVec_injective hdst_eq_y).symm
              · apply toVec_injective; rw [toVec_ofVec]; exact hsrc_eq.symm
          have hword_eq : word = portWord (toVec x) (toVec y) ij := by
            apply winVec_ext
            intro r hr
            rw [← hi_eq]
            by_cases hle : r ≤ i₁.val
            · rw [hpre r hr hle, hportWin_le _ _ _ r hr hle]
            · have hge : i₁.val + 1 ≤ r := by omega
              have h1 : i₁.val + 1 + (r - (i₁.val + 1)) = r := by omega
              have hp1 : winVec word r hr = phiF taps r dst := by
                rw [← winVec_congr word (by omega) hr h1, hpost (r - (i₁.val + 1)) (by omega), h1]
              rw [hp1, hportWin_gt _ _ _ (by rw [hsrc_eq, hdst_eq_y]; exact hdst_jump) r hr hge,
                hdst_eq_y]
          exact Or.inr ⟨j, hj_en, hedge_eq, hword_eq⟩
        · -- No port used: word follows base everywhere
          have hall : ∀ r (hr : r ≤ L), winVec word r hr = phiF taps r (toVec x) := by
            intro r hr
            induction r with
            | zero => simpa [phiF] using hstart
            | succ r ih =>
              have hrlt : r < L := by omega
              let ir : Fin L := ⟨r, hrlt⟩
              have hir_base : base (ir, fun off => word (Fin.ofNat (L + d + 1) (ir.val + off.val))) = true := by
                cases hb : base (ir, fun off => word (Fin.ofNat (L + d + 1) (ir.val + off.val)))
                · exact absurd ⟨ir, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩ hbad
                · rfl
              have hstep := (hbase_iff word ir).mp hir_base
              rw [hstep, ih (by omega)]
              simp [phiF, hrlt, ir]
          have hxy : x = y := by
            apply toVec_injective
            have hL := hall L (le_refl L)
            rw [hfin, hId] at hL
            exact hL.symm
          have hword_eq : word = defWord (toVec x) := by
            apply winVec_ext
            intro r hr
            rw [hall r hr, hdefWin]
          exact Or.inl ⟨hxy, hword_eq⟩
      -- Helper: defWord (toVec x) satisfies Pred when x = y
      have hdef_pred : x = y → Pred (defWord (toVec x)) := by
        intro hxy; subst hxy
        refine ⟨(hend_iff _).mpr ⟨by rw [hdefWin]; rfl, by rw [hdefWin, hId]⟩, ?_⟩
        intro i
        left
        rw [hbase_iff, hdefWin, hdefWin]
        simp [phiF, i.isLt]
      -- Helper: portWord satisfies Pred when edge j = target
      have hport_pred : ∀ j ∈ enabled, edge j = (if rev then (y, x) else (x, y)) →
          Pred (portWord (toVec x) (toVec y) (e j).1.2) := by
        intro j hj_en hedge_eq
        let ij := (e j).1.2
        have hsrc_val : toVec x = if rev then toVec (e j).1.1 + disp taps ij else toVec (e j).1.1 := by
          cases rev
          · simp only [Bool.false_eq_true, ite_false] at hedge_eq ⊢
            exact congrArg (fun p => toVec p.1) hedge_eq.symm
          · simp only [ite_true] at hedge_eq ⊢
            have := congrArg (fun p => toVec p.2) hedge_eq.symm
            simpa only [edge, toVec_ofVec] using this
        have hdst_val : toVec y = if rev then toVec (e j).1.1 else toVec (e j).1.1 + disp taps ij := by
          cases rev
          · simp only [Bool.false_eq_true, ite_false] at hedge_eq ⊢
            have := congrArg (fun p => toVec p.2) hedge_eq.symm
            simpa only [edge, toVec_ofVec] using this
          · simp only [ite_true] at hedge_eq ⊢
            exact congrArg (fun p => toVec p.1) hedge_eq.symm
        have hjump : phiF taps (ij.val + 1) (toVec y) =
            phiF taps (ij.val + 1) (toVec x) + Pi.single (Fin.last d) 1 := by
          have hxy_d : toVec y = toVec x + disp taps ij := by
            rw [hsrc_val, hdst_val]
            cases rev
            · simp only [Bool.false_eq_true, ite_false]
            · simp only [ite_true]
              symm
              rw [add_assoc]
              have hz : disp taps ij + disp taps ij = 0 := by funext p; exact zmod2_add_self _
              rw [hz, add_zero]
          rw [hxy_d, map_add, phiF_disp]
        refine ⟨(hend_iff _).mpr ⟨?_, ?_⟩, ?_⟩
        · rw [hportWin_le _ _ _ 0 (Nat.zero_le L) (Nat.zero_le _)]; rfl
        · rw [hportWin_gt _ _ _ hjump L (le_refl L) (by omega), hId]
        · intro i
          by_cases hlt : i.val < ij.val
          · left
            rw [hbase_iff, hportWin_le _ _ _ (i.val + 1) (by omega) (by omega),
              hportWin_le _ _ _ i.val (by omega) (by omega)]
            simp [phiF, i.isLt]
          · by_cases heq : i = ij
            · right
              rw [heq]
              refine Finset.mem_image.mpr ⟨j, hj_en, ?_⟩
              symm
              change (ij, fun off => (portWord (toVec x) (toVec y) ij) (Fin.ofNat (L + d + 1) (ij.val + off.val))) =
                flip ij (phiF taps ij.val (if rev then toVec (e j).1.1 + disp taps ij else toVec (e j).1.1))
              rw [hflip_iff]
              refine ⟨rfl, ?_, ?_⟩
              · rw [hportWin_le _ _ _ ij.val (by omega) (le_refl _), hsrc_val]
              · rw [hportWin_gt _ _ _ hjump (ij.val + 1) (by omega) (le_refl _), hjump, hsrc_val]
                simp [phiF, ij.isLt]
            · left
              have hgt : ij.val + 1 ≤ i.val := by
                have : i.val ≠ ij.val := fun h => heq (Fin.ext h)
                omega
              rw [hbase_iff, hportWin_gt _ _ _ hjump (i.val + 1) (by omega) (by omega),
                hportWin_gt _ _ _ hjump i.val (by omega) hgt]
              simp [phiF, i.isLt]
      -- Compute exact cardinality by case split on x = y
      change (Finset.univ.filter Pred).card =
        (if x = y then 1 else 0) +
        (if ∃ j ∈ enabled, edge j = (if rev then (y, x) else (x, y)) then 1 else 0)
      by_cases hxy : x = y
      · have hno_edge : ¬ ∃ j ∈ enabled, edge j = (if rev then (y, x) else (x, y)) := by
          rintro ⟨j, _, hj⟩
          have h12 : (edge j).1 = (edge j).2 := by
            rw [hj]; cases rev <;> simp [hxy]
          exact hedge_disj j j h12
        rw [if_pos hxy, if_neg hno_edge, add_zero]
        have hset : Finset.univ.filter Pred = {defWord (toVec x)} := by
          ext word
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hp
            rcases hclassify word hp with ⟨_, hw⟩ | ⟨j, hjen, hjeq, _⟩
            · exact hw
            · exact absurd ⟨j, hjen, hjeq⟩ hno_edge
          · intro hw; rw [hw]; exact hdef_pred hxy
        rw [hset, Finset.card_singleton]
      · simp only [hxy, ite_false, zero_add]
        by_cases hex : ∃ j ∈ enabled, edge j = (if rev then (y, x) else (x, y))
        · simp only [hex, ite_true]
          obtain ⟨j₀, hj₀_en, hj₀_eq⟩ := hex
          have hset : Finset.univ.filter Pred = {portWord (toVec x) (toVec y) (e j₀).1.2} := by
            ext word
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · intro hp
              rcases hclassify word hp with ⟨heq, _⟩ | ⟨j, _, hjeq, hw⟩
              · exact absurd heq hxy
              · have hjj : j = j₀ := hedge_inj (hjeq.trans hj₀_eq.symm)
                rw [hw, hjj]
            · intro hw; rw [hw]; exact hport_pred j₀ hj₀_en hj₀_eq
          rw [hset, Finset.card_singleton]
        · simp only [hex, ite_false]
          have hset : Finset.univ.filter Pred = ∅ := by
            ext word
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            intro hp
            rcases hclassify word hp with ⟨heq, _⟩ | ⟨j, hjen, hjeq, _⟩
            · exact hxy heq
            · exact hex ⟨j, hjen, hjeq⟩
          rw [hset, Finset.card_empty]

-- ============================================================
-- Section 3: Short-Block Case (L ≤ 10 * w) — Linear Identity Rows + Basis Form
-- ============================================================

private def pull {a b : Nat} (f : Fin a → Fin b) : (Fin b → K) →ₗ[K] (Fin a → K) where
  toFun x := x ∘ f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def idx {n : Nat} (hn : 0 < n) (t i : Nat) : Fin n :=
  ⟨(t + i) % n, Nat.mod_lt _ hn⟩

private def win {n k : Nat} (hn : 0 < n) (t : Nat) : (Fin n → K) →ₗ[K] (Fin k → K) :=
  pull (fun i => idx hn t i.val)

private def Good {n k : Nat} (hn : 0 < n) (c : (Fin k → K) →ₗ[K] (Fin n → K)) : Prop :=
  ∀ t, Function.Bijective ((win (k := k) hn t).comp c)

private lemma idx_add {n : Nat} (hn : 0 < n) (t : Nat) (i : Fin n) :
    idx hn t i.val = (⟨t % n, Nat.mod_lt _ hn⟩ : Fin n) + i := by
  ext
  exact (Nat.mod_add_mod t n i.val).symm

private lemma into_window {n k : Nat} (hn : 0 < n) (hkn : k ≤ n) (t : Nat) (p : Fin n) :
    (∃ i : Fin k, p = idx hn t i.val) ∨ ∃ i : Fin (n - k), p = idx hn (t + k) i.val := by
  haveI : NeZero n := ⟨by omega⟩
  let a : Fin n := ⟨t % n, Nat.mod_lt _ hn⟩
  let z := p - a
  have hz : p = idx hn t z.val := by
    rw [idx_add]
    change p = a + (p - a)
    rw [add_comm, sub_add_cancel]
  by_cases h : z.val < k
  · exact Or.inl ⟨⟨z.val, h⟩, hz⟩
  · refine Or.inr ⟨⟨z.val - k, by have := z.isLt; omega⟩, ?_⟩
    refine hz.trans ?_
    apply Fin.ext
    change (t + z.val) % n = (t + k + (z.val - k)) % n
    congr 1; omega

private lemma dual_good {n k : Nat} (hn : 0 < n) (hkn : k ≤ n)
    {c : (Fin k → K) →ₗ[K] (Fin n → K)} (hc : Good hn c) :
    ∃ b : (Fin (n - k) → K) →ₗ[K] (Fin n → K), Good hn b := by
  let e0 := LinearEquiv.ofBijective ((win (k := k) hn 0).comp c) (hc 0)
  let M : (Fin k → K) →ₗ[K] (Fin n → K) := c.comp e0.symm.toLinearMap
  have hMgood : Good hn M := fun t => (hc t).comp e0.symm.bijective
  have hMpref : ∀ (u : Fin k → K) (i : Fin k), M u ⟨i.val, by omega⟩ = u i := by
    intro u i
    have h := congrFun (e0.apply_symm_apply u) i
    change ((win (k := k) hn 0) (M u)) i = u i at h
    simpa [win, pull, idx, Nat.mod_eq_of_lt (show i.val < n by omega)] using h
  let b : (Fin (n - k) → K) →ₗ[K] (Fin n → K) :=
    { toFun := fun w p =>
        if h : p.val < k then
          ∑ q : Fin (n - k), M (Pi.single ⟨p.val, h⟩ 1) ⟨k + q.val, by omega⟩ * w q
        else
          w ⟨p.val - k, by omega⟩
      map_add' := fun w₁ w₂ => by
        funext p
        simp only [Pi.add_apply]
        split_ifs with h
        · simp only [mul_add, Finset.sum_add_distrib]
        · rfl
      map_smul' := fun r w => by
        funext p
        dsimp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        split_ifs with h
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q _; ring
        · rfl }
  have hdot : ∀ (u : Fin k → K) (w : Fin (n - k) → K),
      ∑ p : Fin n, M u p * b w p = 0 := by
    intro u w
    have hsum_split : ∑ p : Fin n, M u p * b w p =
        (∑ i : Fin k, M u ⟨i.val, by omega⟩ * b w ⟨i.val, by omega⟩) +
        (∑ q : Fin (n - k), M u ⟨k + q.val, by omega⟩ * b w ⟨k + q.val, by omega⟩) := by
      have hne : k + (n - k) = n := by omega
      let eFin : Fin (k + (n - k)) ≃ Fin n := finCongr hne
      rw [← Equiv.sum_comp eFin, Fin.sum_univ_add]
      congr 1
    rw [hsum_split]
    have hpart1 : ∑ i : Fin k, M u ⟨i.val, by omega⟩ * b w ⟨i.val, by omega⟩ =
        ∑ q : Fin (n - k), M u ⟨k + q.val, by omega⟩ * w q := by
      have h1 : ∀ i : Fin k, M u ⟨i.val, by omega⟩ * b w ⟨i.val, by omega⟩ =
          ∑ q : Fin (n - k), (u i * M (Pi.single i 1) ⟨k + q.val, by omega⟩) * w q := by
        intro i
        rw [hMpref u i]
        simp only [b, LinearMap.coe_mk, AddHom.coe_mk, i.isLt, dite_true, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _; ring
      simp_rw [h1]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      rw [← Finset.sum_mul]
      congr 1
      have hu : u = ∑ i : Fin k, u i • Pi.single i (1 : K) := by
        funext j; simp [Finset.sum_apply, Pi.single_apply, mul_ite]
      conv_rhs => rw [hu]
      simp [map_sum, map_smul, Finset.sum_apply, smul_eq_mul]
    have hpart2 : ∑ q : Fin (n - k), M u ⟨k + q.val, by omega⟩ * b w ⟨k + q.val, by omega⟩ =
        ∑ q : Fin (n - k), M u ⟨k + q.val, by omega⟩ * w q := by
      apply Finset.sum_congr rfl
      intro q _
      have hnotlt : ¬ (k + q.val < k) := by omega
      simp only [b, LinearMap.coe_mk, AddHom.coe_mk, hnotlt, dite_false]
      congr 2; ext; simp
    rw [hpart1, hpart2, zmod2_add_self]
  refine ⟨b, fun t => ?_⟩
  rw [← Finite.injective_iff_bijective]
  rw [injective_iff_map_eq_zero]
  intro w hw
  have hall : ∀ p : Fin n, b w p = 0 := by
    intro p
    let s := t + (n - k)
    rcases into_window hn (k := n - k) (by omega) t p with ⟨i, hp⟩ | ⟨i, hp⟩
    · rw [hp]; exact congrFun hw i
    · have hsz : n - (n - k) = k := by omega
      obtain ⟨u, hu⟩ := (hMgood s).2 (fun j => (Pi.single p 1 : Fin n → K) (idx hn s j.val))
      have horth := hdot u w
      suffices hh : ∑ q : Fin n, M u q * b w q = ∑ q : Fin n, (Pi.single p (1 : K) : Fin n → K) q * b w q by
        rw [hh] at horth
        simpa [Pi.single_apply] using horth
      apply Finset.sum_congr rfl
      intro q _
      rcases into_window hn (k := n - k) (by omega) t q with ⟨j, hq⟩ | ⟨j, hq⟩
      · have hz : b w q = 0 := by rw [hq]; exact congrFun hw j
        simp [hz]
      · rw [hq]
        exact congrArg (· * b w (idx hn s j.val)) (congrFun hu (Fin.cast hsz j))
  funext q
  have hq := hall ⟨k + q.val, by omega⟩
  have hnotlt : ¬ (k + q.val < k) := by omega
  simp only [b, LinearMap.coe_mk, AddHom.coe_mk, hnotlt, dite_false] at hq
  simpa using hq

private lemma double_good {n k : Nat} (hk : 0 < k) (hkn : k ≤ n)
    {c : (Fin k → K) →ₗ[K] (Fin n → K)} (hc : Good (by omega) c) :
    ∃ b : (Fin k → K) →ₗ[K] (Fin (n + k) → K), Good (by omega) b := by
  have hn : 0 < n := by omega
  have hnk : 0 < n + k := by omega
  let f (p : Fin (n + k)) : Fin n :=
    if h : p.val < k then ⟨p.val, by omega⟩ else ⟨p.val - k, by have := p.isLt; omega⟩
  refine ⟨(pull f).comp c, ?_⟩
  suffices H : ∀ t < n + k, Function.Bijective ((win (k := k) hnk t).comp ((pull f).comp c)) by
    intro t
    convert H (t % (n + k)) (Nat.mod_lt _ hnk) using 1
    ext x i
    change c x (f (idx hnk t i.val)) = c x (f (idx hnk (t % (n + k)) i.val))
    simp [idx, Nat.mod_add_mod]
  intro t ht
  by_cases h : t < k
  · haveI : NeZero k := ⟨by omega⟩
    let rot : Fin k → Fin k := fun i => (⟨t, h⟩ : Fin k) + i
    have hr : Function.Bijective (fun (x : Fin k → K) => x ∘ rot) := by
      let e : Equiv.Perm (Fin k) := Equiv.addLeft (⟨t, h⟩ : Fin k)
      exact (Equiv.arrowCongr e.symm (Equiv.refl K)).bijective
    have he (i : Fin k) : f (idx hnk t i.val) = idx hn 0 (rot i).val := by
      have hi := i.isLt
      have hti : t + i.val < n + k := by omega
      simp only [idx, Nat.mod_eq_of_lt hti, Nat.zero_add, f]
      have hev : (rot i).val = (t + i.val) % k := rfl
      have hm : (t + i.val) % k < n := by have := Nat.mod_lt (t + i.val) hk; omega
      simp only [hev, Nat.mod_eq_of_lt hm]
      split <;> rename_i hh
      · apply Fin.ext; exact (Nat.mod_eq_of_lt hh).symm
      · apply Fin.ext
        exact ((Nat.mod_eq_sub_mod (by omega : k ≤ t + i.val)).trans (Nat.mod_eq_of_lt (by omega))).symm
    convert hr.comp (hc 0) using 1
    ext x i
    exact congrArg (c x) (he i)
  · have he (i : Fin k) : f (idx hnk t i.val) = idx hn (t - k) i.val := by
      have hi := i.isLt
      by_cases hh : t + i.val < n + k
      · simp only [idx, Nat.mod_eq_of_lt hh, f, dite_eq_right (show ¬ t + i.val < k by omega)]
        apply Fin.ext
        change t + i.val - k = (t - k + i.val) % n
        rw [Nat.mod_eq_of_lt (by omega : t - k + i.val < n)]
        omega
      · have hm : (t + i.val) % (n + k) = t + i.val - (n + k) :=
          (Nat.mod_eq_sub_mod (by omega : n + k ≤ t + i.val)).trans (Nat.mod_eq_of_lt (by omega))
        have hm' : (t - k + i.val) % n = t - k + i.val - n :=
          (Nat.mod_eq_sub_mod (by omega : n ≤ t - k + i.val)).trans (Nat.mod_eq_of_lt (by omega))
        simp only [idx, hm, hm', f, dite_eq_left (show t + i.val - (n + k) < k by omega)]
        apply Fin.ext
        change t + i.val - (n + k) = t - k + i.val - n
        omega
    convert hc (t - k) using 1
    ext x i
    exact congrArg (c x) (he i)

private def Feasible (n k : Nat) : Prop :=
  ∃ (hn : 0 < n) (c : (Fin k → K) →ₗ[K] (Fin n → K)), Good hn c

private lemma exists_good (n : Nat) : ∀ k, 0 < k → k ≤ n → Feasible n k := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro k hk hkn
    by_cases h : n = k
    · subst n
      haveI : NeZero k := ⟨by omega⟩
      refine ⟨hk, LinearMap.id, fun t => ?_⟩
      let e : Equiv.Perm (Fin k) := Equiv.addLeft (⟨t % k, Nat.mod_lt _ hk⟩ : Fin k)
      convert (Equiv.arrowCongr e.symm (Equiv.refl K)).bijective using 1
      ext x i
      exact congrArg x (idx_add hk t i)
    · by_cases h₂ : k ≤ n - k
      · obtain ⟨_, c, hc⟩ := ih (n - k) (by omega) k hk h₂
        obtain ⟨b, hb⟩ := double_good hk h₂ hc
        have he : n - k + k = n := by omega
        exact he ▸ (show Feasible (n - k + k) k from ⟨by omega, b, hb⟩)
      · have hl : 0 < n - k := by omega
        have hle : n - k ≤ k := by omega
        obtain ⟨_, c, hc⟩ := ih k (by omega) (n - k) hl hle
        obtain ⟨b, hb⟩ := double_good hl hle hc
        have he : k + (n - k) = n := by omega
        have H : Feasible n (n - k) :=
          (congrArg (fun m => Feasible m (n - k)) he).mp ⟨by omega, b, hb⟩
        obtain ⟨hn, b, hb⟩ := H
        obtain ⟨a, ha⟩ := dual_good hn (Nat.sub_le n k) hb
        have he' : n - (n - k) = k := by omega
        exact he' ▸ (show Feasible n (n - (n - k)) from ⟨hn, a, ha⟩)

private lemma row_expansion {d : Nat} (f : (Fin (d + 1) → K) →ₗ[K] K)
    (h : f (Pi.single 0 1) = 1) (v : Fin (d + 1) → K) :
    f v = v 0 + ∑ j : Fin d, f (Pi.single j.succ 1) * v j.succ := by
  have hv : (∑ j : Fin (d + 1), v j • (Pi.single j (1 : K))) = v := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply, mul_ite]
  calc
    f v = f (∑ j : Fin (d + 1), v j • Pi.single j 1) := congrArg f hv.symm
    _ = ∑ j : Fin (d + 1), v j * f (Pi.single j 1) := by simp
    _ = _ := by simp [Fin.sum_univ_succ, h, mul_comm]

private lemma linear_id_rows {d L : Nat} (hw : d + 1 ≤ L) :
    ∃ taps : Fin L → Fin d → K, ∀ v, phiF taps L v = v := by
  obtain ⟨hL, code, hc⟩ := exists_good L (d + 1) (Nat.succ_pos d) hw
  let E (a : Nat) := LinearEquiv.ofBijective ((win (k := d + 1) hL a).comp code) (hc a)
  let coord (p : Nat) : Fin L := ⟨p % L, Nat.mod_lt _ hL⟩
  let f (a : Nat) : (Fin (d + 1) → K) →ₗ[K] K :=
    (LinearMap.proj (coord (a + d + 1))).comp (code.comp (E a).symm.toLinearMap)
  have eval (a : Nat) (u : Fin (d + 1) → K) (i : Fin (d + 1)) :
      E a u i = code u (coord (a + i.val)) := rfl
  have feedback (a : Nat) (u : Fin (d + 1) → K) :
      f a (E a u) = code u (coord (a + d + 1)) := by
    change code ((E a).symm (E a u)) _ = _
    rw [LinearEquiv.symm_apply_apply]
  have first (a : Nat) : f a (Pi.single 0 1) = 1 := by
    let u := (E a).symm (Pi.single 0 1)
    have hu : E a u = Pi.single 0 1 := (E a).apply_symm_apply _
    by_contra h
    have hz : f a (Pi.single 0 1) = 0 := by
      rcases zmod2_eq_zero_or_one (f a (Pi.single 0 1)) with h0 | h1
      · exact h0
      · exact absurd h1 h
    have hv : E (a + 1) u = 0 := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [eval, Fin.val_last, Nat.add_right_comm] using (feedback a u).symm.trans (hu ▸ hz)
      · have hj := congrFun hu j.succ
        simp only [eval, Fin.val_succ, Pi.single_apply, Fin.succ_ne_zero, ite_false] at hj
        simpa only [eval, Pi.zero_apply, Fin.val_castSucc, Nat.add_assoc, Nat.add_comm 1] using hj
    have h0 : u = 0 := (E (a + 1)).injective (hv.trans ((E (a + 1)).map_zero).symm)
    have he := congrFun hu 0
    simp [h0] at he
  let taps : Fin L → Fin d → K := fun row j => f row.val (Pi.single j.succ 1)
  refine ⟨taps, fun v => ?_⟩
  let u := (E 0).symm v
  have hstep : ∀ (a : Nat), a ≤ L → phiF taps a v = E a u := by
    intro a
    induction a with
    | zero =>
      intro _; simp [phiF, u]
    | succ a ih =>
      intro ha
      have halt : a < L := by omega
      simp only [phiF, halt, dite_true, LinearMap.comp_apply, ih (by omega)]
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [linStepF, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_last, taps]
        rw [← row_expansion (f a) (first a) (E a u), feedback a u]
        simp only [eval, Fin.val_last]
        exact congrArg (code u) (Fin.ext (by
          change (a + d + 1) % L = (a + 1 + d) % L
          rw [show a + d + 1 = a + 1 + d by omega]))
      · simp only [linStepF, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_castSucc, eval,
          Fin.val_succ, Fin.val_castSucc]
        exact congrArg (code u) (Fin.ext (by
          change (a + (j.val + 1)) % L = (a + 1 + j.val) % L
          rw [show a + (j.val + 1) = a + 1 + j.val by omega]))
  have hL_eq := hstep L (le_refl L)
  rw [hL_eq]
  have hEL : E L u = E 0 u := by
    funext i
    simp only [eval, coord, Nat.zero_add, Nat.add_mod_left]
  rw [hEL]
  exact (E 0).apply_symm_apply v

private def buildFormAux {w : Nat} (δ : Fin w → Fin w → K) : (k : Nat) → k ≤ w → (Fin k → K)
  | 0, _ => fun i => Fin.elim0 i
  | k + 1, hk =>
    let prev := buildFormAux δ k (by omega)
    let nextBit : K := 1 + ∑ j : Fin k, prev j * δ ⟨k, by omega⟩ ⟨j.val, by omega⟩
    Fin.snoc (α := fun _ : Fin (k + 1) => K) prev nextBit

private lemma buildFormAux_spec {w : Nat} (δ : Fin w → Fin w → K)
    (hdiag : ∀ i : Fin w, δ i i = 1)
    (hlow : ∀ i j : Fin w, i.val < j.val → δ i j = 0) :
    ∀ (k : Nat) (hk : k ≤ w) (i : Fin w), i.val < k →
      ∑ j : Fin k, buildFormAux δ k hk j * δ i ⟨j.val, by omega⟩ = 1 := by
  intro k
  induction k with
  | zero => intro _ _ hi; omega
  | succ k ih =>
    intro hk i hi
    simp only [buildFormAux, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      Fin.val_castSucc, Fin.val_last]
    by_cases hlt : i.val < k
    · have hzero : δ i ⟨k, by omega⟩ = 0 := hlow i ⟨k, by omega⟩ hlt
      rw [hzero, mul_zero, add_zero]
      exact ih (by omega) i hlt
    · have hik : i.val = k := by omega
      have heq : i = ⟨k, by omega⟩ := Fin.ext hik
      rw [heq, hdiag ⟨k, by omega⟩, mul_one]
      have hcomm : (∑ x : Fin k, buildFormAux δ k (by omega) x * δ ⟨k, by omega⟩ ⟨x.val, by omega⟩) +
          (1 + ∑ j : Fin k, buildFormAux δ k (by omega) j * δ ⟨k, by omega⟩ ⟨j.val, by omega⟩) =
          1 + ((∑ x : Fin k, buildFormAux δ k (by omega) x * δ ⟨k, by omega⟩ ⟨x.val, by omega⟩) +
            ∑ x : Fin k, buildFormAux δ k (by omega) x * δ ⟨k, by omega⟩ ⟨x.val, by omega⟩) := by ring
      rw [hcomm, zmod2_add_self, add_zero]

private lemma short_block_data {d L : Nat} (hw : d + 1 ≤ L) (hshort : L ≤ 10 * (d + 1)) :
    ∃ (taps : Fin L → Fin d → K) (I : Finset (Fin L)) (a : Fin (d + 1) → K),
      (∀ v, phiF taps L v = v) ∧ I.Nonempty ∧
      (∀ i₁ ∈ I, ∀ i₂ ∈ I, disp taps i₁ = disp taps i₂ → i₁ = i₂) ∧
      (∀ i ∈ I, dotProduct a (disp taps i) = 1) ∧
      2 ^ (d + 1) * min L (2 ^ (d + 1)) ≤ 10 * 2 ^ (d + 1) * I.card := by
  obtain ⟨taps, hId⟩ := linear_id_rows hw
  let I : Finset (Fin L) := Finset.univ.filter (fun i : Fin L => i.val < d + 1)
  have hIcard : I.card = d + 1 := by
    have hbij : I.card = (Finset.univ : Finset (Fin (d + 1))).card := by
      refine Finset.card_bij (fun i hi => ⟨i.val, (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro i₁ _ i₂ _ h; exact Fin.ext (Fin.mk.inj h)
      · intro j _
        exact ⟨⟨j.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩, rfl⟩
    simpa using hbij
  have hphi_i : ∀ i : Fin L, phiF taps i.val (disp taps i) = Pi.single 0 1 := by
    intro i
    have h1 : linStepF (taps i) (phiF taps i.val (disp taps i)) = Pi.single (Fin.last d) 1 := by
      have := phiF_disp taps i
      simpa only [phiF, i.isLt, dite_true, LinearMap.comp_apply] using this
    rw [← linStepF_single_zero (taps i)] at h1
    have h2 := congrArg (linStepFInv (taps i)) h1
    simpa only [linStepFInv_linStepF] using h2
  have hdisp_tri : ∀ (i : Fin L) (hi : i.val < d + 1) (q : Fin (d + 1)),
      i.val ≤ q.val →
        disp taps i q = if q.val = i.val then 1 else 0 := by
    intro i hi q hle
    have hsh := phiF_shift taps 0 i.val ⟨q.val - i.val, by omega⟩ (by omega) (by simp; omega) (disp taps i)
    simp only [Nat.zero_add, phiF, LinearMap.id_apply] at hsh
    have hqeq : (⟨q.val - i.val + i.val, by omega⟩ : Fin (d + 1)) = q := by ext; simp; omega
    rw [hqeq, hphi_i i] at hsh
    rw [← hsh, Pi.single_apply]
    by_cases heq : q.val = i.val
    · have h0 : (⟨q.val - i.val, by omega⟩ : Fin (d + 1)) = 0 := by ext; simp; omega
      simp [heq, h0]
    · have h0 : (⟨q.val - i.val, by omega⟩ : Fin (d + 1)) ≠ 0 := by
        intro hc; have := congrArg Fin.val hc; simp at this; omega
      simp [heq, h0]
  let δ : Fin (d + 1) → Fin (d + 1) → K := fun j => disp taps ⟨j.val, by omega⟩
  let a : Fin (d + 1) → K := buildFormAux δ (d + 1) (le_refl _)
  refine ⟨taps, I, a, hId, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨0, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.succ_pos d⟩⟩
  · intro i₁ hi₁ i₂ hi₂ heq
    have h1 := (Finset.mem_filter.mp hi₁).2
    have h2 := (Finset.mem_filter.mp hi₂).2
    by_contra hne
    rcases lt_or_gt_of_ne (fun hv => hne (Fin.ext hv)) with hlt | hgt
    · have e1 := hdisp_tri i₁ h1 ⟨i₂.val, h2⟩ (by simp; omega)
      have e2 := hdisp_tri i₂ h2 ⟨i₂.val, h2⟩ (le_refl _)
      rw [heq] at e1
      have : (1 : K) = 0 := by
        rw [e2] at e1
        simp [Nat.ne_of_gt hlt] at e1
      exact absurd this (by decide)
    · have e1 := hdisp_tri i₂ h2 ⟨i₁.val, h1⟩ (by simp; omega)
      have e2 := hdisp_tri i₁ h1 ⟨i₁.val, h1⟩ (le_refl _)
      rw [← heq] at e1
      have : (1 : K) = 0 := by
        rw [e2] at e1
        simp [Nat.ne_of_gt hgt] at e1
      exact absurd this (by decide)
  · intro i hi
    have hlt := (Finset.mem_filter.mp hi).2
    have hspec := buildFormAux_spec δ
      (fun j => by simpa [δ] using hdisp_tri ⟨j.val, by omega⟩ j.isLt j (le_refl _))
      (fun j₁ j₂ h12 => by
        have := hdisp_tri ⟨j₁.val, by omega⟩ j₁.isLt j₂ (by simp; omega)
        simpa [δ, Nat.ne_of_gt h12] using this)
      (d + 1) (le_refl _) ⟨i.val, hlt⟩ hlt
    simpa [a, δ, dotProduct] using hspec
  · rw [hIcard]
    have hmin : min L (2 ^ (d + 1)) ≤ 10 * (d + 1) := le_trans (min_le_left _ _) hshort
    calc
      2 ^ (d + 1) * min L (2 ^ (d + 1)) ≤ 2 ^ (d + 1) * (10 * (d + 1)) :=
        Nat.mul_le_mul_left _ hmin
      _ = 10 * 2 ^ (d + 1) * (d + 1) := by ring

-- ============================================================
-- Section 4: U₁ * L * U₂ Matrix Factorization & 2-Sweep Realization
-- ============================================================

private def IsUnitUpper {n : Nat} (M : Matrix (Fin n) (Fin n) K) : Prop :=
  (∀ i, M i i = 1) ∧ (∀ i j, j < i → M i j = 0)

private def IsUnitLower {n : Nat} (M : Matrix (Fin n) (Fin n) K) : Prop :=
  (∀ i, M i i = 1) ∧ (∀ i j, i < j → M i j = 0)

private lemma ulu_decomp : ∀ (n : Nat) (M : Matrix (Fin n) (Fin n) K),
    Function.Injective M.mulVec →
      ∃ (U1 U1i L Li U2 : Matrix (Fin n) (Fin n) K),
        IsUnitUpper U1 ∧ IsUnitUpper U1i ∧ U1 * U1i = 1 ∧ U1i * U1 = 1 ∧
        IsUnitLower L ∧ IsUnitLower Li ∧ L * Li = 1 ∧ Li * L = 1 ∧
        IsUnitUpper U2 ∧ M = U1 * L * U2 := by
  intro n
  induction n with
  | zero =>
    intro M _
    refine ⟨1, 1, 1, 1, 1, ?_, ?_, by simp, by simp, ?_, ?_, by simp, by simp, ?_, ?_⟩
    · exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    · exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    · exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    · exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    · exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    · ext i; exact Fin.elim0 i
  | succ n ih =>
    intro M hMinj
    -- Step 1: Pick elementary upper-triangular E with E * E = 1 so (E * M) 0 0 = 1
    have hE_ex : ∃ (e : Fin n → K),
        let E : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
          Matrix.of fun i j => Fin.cases (Fin.cases 1 e j) (fun i' => Fin.cases 0 (fun j' => if i' = j' then 1 else 0) j) i
        (E * M) 0 0 = 1 := by
      by_cases h00 : M 0 0 = 1
      · refine ⟨0, ?_⟩
        simp [Matrix.mul_apply, Fin.sum_univ_succ, h00]
      · have h00z : M 0 0 = 0 := by
          rcases zmod2_eq_zero_or_one (M 0 0) with h | h
          · exact h
          · exact absurd h h00
        have hcol : ∃ i' : Fin n, M i'.succ 0 = 1 := by
          by_contra h
          push_neg at h
          have hv : M.mulVec (Pi.single 0 1) = 0 := by
            funext i
            simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
              Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.zero_apply]
            refine Fin.cases h00z (fun i' => ?_) i
            rcases zmod2_eq_zero_or_one (M i'.succ 0) with h0 | h1
            · exact h0
            · exact absurd h1 (h i')
          have h0 : (Pi.single 0 (1 : K) : Fin (n + 1) → K) = 0 :=
            hMinj (by rw [hv, Matrix.mulVec_zero])
          have := congrFun h0 0
          simp at this
        obtain ⟨i₀, hi₀⟩ := hcol
        refine ⟨Pi.single i₀ 1, ?_⟩
        simp [Matrix.mul_apply, Fin.sum_univ_succ, h00z, Pi.single_apply, hi₀]
    obtain ⟨evec, hN00⟩ := hE_ex
    let E : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
      Matrix.of fun i j =>
        Fin.cases (Fin.cases 1 evec j) (fun i' => Fin.cases 0 (fun j' => if i' = j' then 1 else 0) j) i
    have hEE : E * E = 1 := by
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
      · simp [E, Matrix.mul_apply, Fin.sum_univ_succ]
      · simp [E, Matrix.mul_apply, Fin.sum_univ_succ, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true, zmod2_add_self,
          Matrix.one_apply, (Fin.succ_ne_zero j').symm]
      · simp [E, Matrix.mul_apply, Fin.sum_univ_succ]
      · simp [E, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    let N := E * M
    have hN00' : N 0 0 = 1 := hN00
    have hNinj : Function.Injective N.mulVec := by
      intro u v h
      apply hMinj
      have := congrArg E.mulVec h
      simpa only [N, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hEE, Matrix.one_mul] using this
    let r : Fin n → K := fun j' => N 0 j'.succ
    let c : Fin n → K := fun i' => N i'.succ 0
    let N' : Matrix (Fin n) (Fin n) K := Matrix.of fun i' j' => N i'.succ j'.succ + c i' * r j'
    have hN'inj : Function.Injective N'.mulVec := by
      intro u₁ u₂ hu
      let v' : Fin n → K := u₁ + u₂
      have hv' : N'.mulVec v' = 0 := by
        rw [Matrix.mulVec_add, hu]
        funext i; exact zmod2_add_self _
      let v : Fin (n + 1) → K := Fin.cons (dotProduct r v') v'
      have hNv : N.mulVec v = 0 := by
        funext i
        refine Fin.cases ?_ (fun i' => ?_) i
        · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, v, Fin.cons_zero, Fin.cons_succ,
            hN00', one_mul, Pi.zero_apply]
          change (∑ j : Fin n, r j * v' j) + ∑ j : Fin n, r j * v' j = 0
          exact zmod2_add_self _
        · have hi' := congrFun hv' i'
          simp only [Matrix.mulVec, dotProduct, N', Matrix.of_apply, add_mul, Finset.sum_add_distrib,
            Pi.zero_apply] at hi'
          simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, v, Fin.cons_zero, Fin.cons_succ,
            Pi.zero_apply]
          have h1 : c i' * ∑ j : Fin n, r j * v' j = ∑ j : Fin n, c i' * r j * v' j := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
          change c i' * (∑ j : Fin n, r j * v' j) + ∑ j : Fin n, N i'.succ j.succ * v' j = 0
          rw [h1, add_comm]
          exact hi'
      have hv0 : v = 0 := hNinj (by rw [hNv, Matrix.mulVec_zero])
      funext j'
      have hj' : u₁ j' + u₂ j' = 0 := by
        have := congrFun hv0 j'.succ
        simpa [v, v'] using this
      have := congrArg (fun z => z + u₂ j') hj'
      simpa only [add_assoc, zmod2_add_self, add_zero, zero_add] using this
    obtain ⟨U1', U1i', L', Li', U2', hU1', hU1i', hU1r', hU1l', hL', hLi', hLr', hLl', hU2', hN'eq⟩ :=
      ih N' hN'inj
    let c' : Fin n → K := U1i'.mulVec c
    -- Assemble block matrices:
    -- U1 = E * [[1, 0], [0, U1']] = [[1, evec * U1'], [0, U1']]
    -- U1i = [[1, 0], [0, U1i']] * E = [[1, evec], [0, U1i']]
    -- L = [[1, 0], [c', I]] * [[1, 0], [0, L']] = [[1, 0], [c', L']]
    -- Li = [[1, 0], [0, Li']] * [[1, 0], [c', I]] = [[1, 0], [Li' * c', Li']]
    -- U2 = [[1, 0], [0, U2']] * [[1, r], [0, I]] = [[1, r], [0, U2']]
    let U1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
      Matrix.of fun i j =>
        Fin.cases (Fin.cases 1 (fun j' => ∑ k : Fin n, evec k * U1' k j') j)
          (fun i' => Fin.cases 0 (fun j' => U1' i' j') j) i
    let U1i : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
      Matrix.of fun i j =>
        Fin.cases (Fin.cases 1 evec j) (fun i' => Fin.cases 0 (fun j' => U1i' i' j') j) i
    let L : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
      Matrix.of fun i j =>
        Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases (c' i') (fun j' => L' i' j') j) i
    let Li : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
      Matrix.of fun i j =>
        Fin.cases (Fin.cases 1 (fun _ => 0) j)
          (fun i' => Fin.cases ((Li'.mulVec c') i') (fun j' => Li' i' j') j) i
    let U2 : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
      Matrix.of fun i j =>
        Fin.cases (Fin.cases 1 r j) (fun i' => Fin.cases 0 (fun j' => U2' i' j') j) i
    refine ⟨U1, U1i, L, Li, U2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- IsUnitUpper U1
      refine ⟨fun i => Fin.cases (by simp [U1]) (fun i' => by simp [U1, hU1'.1 i']) i, ?_⟩
      intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · intro hij; exact absurd hij (Fin.not_lt_zero j)
      · refine Fin.cases (fun _ => by simp [U1]) (fun j' hij => ?_) j
        simp only [U1, Matrix.of_apply, Fin.cases_succ]
        exact hU1'.2 i' j' (Fin.succ_lt_succ_iff.mp hij)
    · -- IsUnitUpper U1i
      refine ⟨fun i => Fin.cases (by simp [U1i]) (fun i' => by simp [U1i, hU1i'.1 i']) i, ?_⟩
      intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · intro hij; exact absurd hij (Fin.not_lt_zero j)
      · refine Fin.cases (fun _ => by simp [U1i]) (fun j' hij => ?_) j
        simp only [U1i, Matrix.of_apply, Fin.cases_succ]
        exact hU1i'.2 i' j' (Fin.succ_lt_succ_iff.mp hij)
    · -- U1 * U1i = 1
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
      · simp [U1, U1i, Matrix.mul_apply, Fin.sum_univ_succ]
      · simp only [U1, U1i, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_succ, Fin.cases_zero,
          Fin.cases_succ, one_mul, Matrix.one_apply, (Fin.succ_ne_zero j').symm, ite_false]
        have hsum : ∑ k : Fin n, (∑ t : Fin n, evec t * U1' t k) * U1i' k j' = evec j' := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          have hinner : ∀ t : Fin n, ∑ k : Fin n, evec t * U1' t k * U1i' k j' =
              evec t * (U1' * U1i') t j' := by
            intro t; rw [Matrix.mul_apply, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _; ring
          simp_rw [hinner, hU1r', Matrix.one_apply, mul_ite, mul_one, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [hsum, zmod2_add_self]
      · simp [U1, U1i, Matrix.mul_apply, Fin.sum_univ_succ]
      · simp only [U1, U1i, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_succ, Fin.cases_succ,
          Fin.cases_zero, zero_mul, zero_add, Matrix.one_apply, Fin.succ_inj]
        exact congrFun (congrFun hU1r' i') j'
    · -- U1i * U1 = 1
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
      · simp [U1, U1i, Matrix.mul_apply, Fin.sum_univ_succ]
      · simp only [U1, U1i, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_succ, Fin.cases_zero,
          Fin.cases_succ, one_mul, Matrix.one_apply, (Fin.succ_ne_zero j').symm, ite_false]
        exact zmod2_add_self _
      · simp [U1, U1i, Matrix.mul_apply, Fin.sum_univ_succ]
      · simp only [U1, U1i, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_succ, Fin.cases_succ,
          Fin.cases_zero, zero_mul, zero_add, Matrix.one_apply, Fin.succ_inj]
        exact congrFun (congrFun hU1l' i') j'
    · -- IsUnitLower L
      refine ⟨fun i => Fin.cases (by simp [L]) (fun i' => by simp [L, hL'.1 i']) i, ?_⟩
      intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases (fun hij => absurd hij (lt_irrefl _)) (fun j' _ => by simp [L]) j
      · refine Fin.cases (fun hij => absurd hij (Fin.not_lt_zero _)) (fun j' hij => ?_) j
        simp only [L, Matrix.of_apply, Fin.cases_succ]
        exact hL'.2 i' j' (Fin.succ_lt_succ_iff.mp hij)
    · -- IsUnitLower Li
      refine ⟨fun i => Fin.cases (by simp [Li]) (fun i' => by simp [Li, hLi'.1 i']) i, ?_⟩
      intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases (fun hij => absurd hij (lt_irrefl _)) (fun j' _ => by simp [Li]) j
      · refine Fin.cases (fun hij => absurd hij (Fin.not_lt_zero _)) (fun j' hij => ?_) j
        simp only [Li, Matrix.of_apply, Fin.cases_succ]
        exact hLi'.2 i' j' (Fin.succ_lt_succ_iff.mp hij)
    · -- L * Li = 1
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
      · simp [L, Li, Matrix.mul_apply, Fin.sum_univ_succ]
      · simp [L, Li, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, (Fin.succ_ne_zero j').symm]
      · simp only [L, Li, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_succ, Fin.cases_succ,
          Fin.cases_zero, mul_one, Matrix.one_apply, Fin.succ_ne_zero, ite_false]
        have h1 : ∑ k : Fin n, L' i' k * (Li'.mulVec c') k = c' i' := by
          have := congrFun (by rw [Matrix.mulVec_mulVec, hLr', Matrix.one_mulVec] :
            L'.mulVec (Li'.mulVec c') = c') i'
          exact this
        rw [h1, zmod2_add_self]
      · simp only [L, Li, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_succ, Fin.cases_succ,
          Fin.cases_zero, mul_zero, zero_add, Matrix.one_apply, Fin.succ_inj]
        exact congrFun (congrFun hLr' i') j'
    · -- Li * L = 1
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
      · simp [L, Li, Matrix.mul_apply, Fin.sum_univ_succ]
      · simp [L, Li, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, (Fin.succ_ne_zero j').symm]
      · simp only [L, Li, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_succ, Fin.cases_succ,
          Fin.cases_zero, mul_one, Matrix.one_apply, Fin.succ_ne_zero, ite_false]
        change (Li'.mulVec c') i' + (Li'.mulVec c') i' = 0
        exact zmod2_add_self _
      · simp only [L, Li, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_succ, Fin.cases_succ,
          Fin.cases_zero, mul_zero, zero_add, Matrix.one_apply, Fin.succ_inj]
        exact congrFun (congrFun hLl' i') j'
    · -- IsUnitUpper U2
      refine ⟨fun i => Fin.cases (by simp [U2]) (fun i' => by simp [U2, hU2'.1 i']) i, ?_⟩
      intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · intro hij; exact absurd hij (Fin.not_lt_zero j)
      · refine Fin.cases (fun _ => by simp [U2]) (fun j' hij => ?_) j
        simp only [U2, Matrix.of_apply, Fin.cases_succ]
        exact hU2'.2 i' j' (Fin.succ_lt_succ_iff.mp hij)
    · -- M = U1 * L * U2: equivalently N = E * (U1 * L * U2) since E * E = 1
      have hU1_eq : U1 = E * Matrix.of (fun i j =>
          Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => U1' i' j') j) i) := by
        ext i j
        refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
          simp [U1, E, Matrix.mul_apply, Fin.sum_univ_succ]
      have hM_eq : M = E * N := by
        rw [← Matrix.mul_assoc, hEE, Matrix.one_mul]
      rw [hM_eq, hU1_eq, Matrix.mul_assoc, Matrix.mul_assoc]
      congr 1
      let B1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
        Matrix.of fun i j =>
          Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => U1' i' j') j) i
      change N = B1 * (L * U2)
      have hU1c' : U1'.mulVec c' = c := by
        simp only [c', Matrix.mulVec_mulVec, hU1r', Matrix.one_mulVec]
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
      · simp [B1, L, U2, Matrix.mul_apply, Fin.sum_univ_succ, hN00']
      · simp [B1, L, U2, Matrix.mul_apply, Fin.sum_univ_succ, r]
      · simp only [B1, L, U2, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_succ, Fin.cases_succ,
          Fin.cases_zero, zero_mul, zero_add, mul_one, mul_zero, Finset.sum_const_zero, add_zero]
        exact (congrFun hU1c' i').symm
      · simp only [B1, L, U2, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_succ, Fin.cases_succ,
          Fin.cases_zero, zero_mul, zero_add, mul_add, Finset.sum_add_distrib]
        have h1 : ∑ k : Fin n, U1' i' k * (c' k * r j') = c i' * r j' := by
          have : ∑ k : Fin n, U1' i' k * (c' k * r j') = (U1'.mulVec c') i' * r j' := by
            simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
            apply Finset.sum_congr rfl; intro k _; ring
          rw [this, hU1c']
        have h2 : ∑ k : Fin n, U1' i' k * (∑ t : Fin n, L' k t * U2' t j') = (U1' * L' * U2') i' j' := by
          rw [Matrix.mul_assoc, Matrix.mul_apply]
          apply Finset.sum_congr rfl; intro k _
          rw [Matrix.mul_apply]
        rw [h1, h2, ← hN'eq]
        simp only [N', Matrix.of_apply]
        rw [add_comm (c i' * r j'), add_assoc, zmod2_add_self, add_zero]

private def sweepTaps {d : Nat} (A B : Matrix (Fin (d + 1)) (Fin (d + 1)) K) :
    Fin (d + 1) → Fin d → K :=
  fun k j =>
    if h : k.val + 1 + j.val < d + 1 then B k ⟨k.val + 1 + j.val, h⟩
    else A k ⟨k.val + 1 + j.val - (d + 1), by omega⟩

private lemma sweep_realize {d : Nat} (A B : Matrix (Fin (d + 1)) (Fin (d + 1)) K)
    (hA : IsUnitLower A) (hB : IsUnitUpper B) (x y : Fin (d + 1) → K)
    (hxy : A.mulVec y = B.mulVec x) :
    phiF (sweepTaps A B) (d + 1) x = y := by
  let state (r : Nat) (hr : r ≤ d + 1) (p : Fin (d + 1)) : K :=
    if h : r + p.val < d + 1 then x ⟨r + p.val, h⟩ else y ⟨r + p.val - (d + 1), by have := p.isLt; omega⟩
  have hinv : ∀ (r : Nat) (hr : r ≤ d + 1), phiF (sweepTaps A B) r x = state r hr := by
    intro r
    induction r with
    | zero =>
      intro hr; funext p
      have h0 : 0 + p.val < d + 1 := by have := p.isLt; omega
      simp only [phiF, LinearMap.id_apply, state, h0, dite_true]
      congr 1; ext; simp
    | succ r ih =>
      intro hr
      have hrlt : r < d + 1 := by omega
      simp only [phiF, hrlt, dite_true, LinearMap.comp_apply, ih (by omega)]
      funext p
      refine Fin.lastCases ?_ (fun j => ?_) p
      · simp only [linStepF, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_last]
        have hst_last : state (r + 1) hr (Fin.last d) = y ⟨r, hrlt⟩ := by
          have hn : ¬ (r + 1 + d < d + 1) := by omega
          simp only [state, Fin.val_last, hn, dite_false]
          congr 1; ext; simp; omega
        rw [hst_last]
        have hst0 : state r (by omega) 0 = x ⟨r, hrlt⟩ := by
          have h0 : r + (0 : Fin (d + 1)).val < d + 1 := by simp; omega
          simp only [state, h0, dite_true]
          rfl
        rw [hst0]
        -- Relate sum over j : Fin d to A.mulVec y ⟨r, hrlt⟩ = B.mulVec x ⟨r, hrlt⟩
        let kr : Fin (d + 1) := ⟨r, hrlt⟩
        have hmul := congrFun hxy kr
        simp only [Matrix.mulVec, dotProduct] at hmul
        -- Split sum over q : Fin (d+1) into q = kr, q > kr, q < kr
        have hA_split : ∑ q : Fin (d + 1), A kr q * y q =
            y kr + ∑ q ∈ Finset.univ.filter (fun q : Fin (d + 1) => q.val < r), A kr q * y q := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ kr), hA.1 kr, one_mul]
          congr 1
          symm
          refine Finset.sum_subset (fun q hq => by
            have hltq := (Finset.mem_filter.mp hq).2
            exact Finset.mem_erase.mpr ⟨fun heq => by have := congrArg Fin.val heq; simp [kr] at this; omega, Finset.mem_univ _⟩) ?_
          intro q hq hnot
          have hne := (Finset.mem_erase.mp hq).1
          have hge : r ≤ q.val := by
            simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hnot
          have hgt : kr < q := by
            change r < q.val
            have : q.val ≠ r := fun heq => hne (Fin.ext heq)
            omega
          rw [hA.2 kr q hgt, zero_mul]
        have hB_split : ∑ q : Fin (d + 1), B kr q * x q =
            x kr + ∑ q ∈ Finset.univ.filter (fun q : Fin (d + 1) => r < q.val), B kr q * x q := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ kr), hB.1 kr, one_mul]
          congr 1
          symm
          refine Finset.sum_subset (fun q hq => by
            have hgtq := (Finset.mem_filter.mp hq).2
            exact Finset.mem_erase.mpr ⟨fun heq => by have := congrArg Fin.val heq; simp [kr] at this; omega, Finset.mem_univ _⟩) ?_
          intro q hq hnot
          have hne := (Finset.mem_erase.mp hq).1
          have hle : q.val ≤ r := by
            simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hnot
          have hltq : q < kr := by
            change q.val < r
            have : q.val ≠ r := fun heq => hne (Fin.ext heq)
            omega
          rw [hB.2 kr q hltq, zero_mul]
        -- Split sum over j : Fin d into upper (r + 1 + j < d + 1) and lower (r + 1 + j ≥ d + 1)
        let S_hi := Finset.univ.filter (fun j : Fin d => r + 1 + j.val < d + 1)
        let S_lo := Finset.univ.filter (fun j : Fin d => ¬ (r + 1 + j.val < d + 1))
        have hsum_j : ∑ j : Fin d, sweepTaps A B kr j * state r (by omega) j.succ =
            (∑ q ∈ Finset.univ.filter (fun q : Fin (d + 1) => r < q.val), B kr q * x q) +
            (∑ q ∈ Finset.univ.filter (fun q : Fin (d + 1) => q.val < r), A kr q * y q) := by
          have hun : S_hi ∪ S_lo = Finset.univ := by
            ext j; simp only [S_hi, S_lo, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; exact em _
          have hdj : Disjoint S_hi S_lo := by
            rw [Finset.disjoint_left]; intro j h1 h2
            exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
          rw [← hun, Finset.sum_union hdj]
          congr 1
          · refine Finset.sum_bij (fun j hj => ⟨r + 1 + j.val, (Finset.mem_filter.mp hj).2⟩) ?_ ?_ ?_ ?_
            · intro j _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
            · intro j₁ _ j₂ _ h; exact Fin.ext (by have := Fin.mk.inj h; omega)
            · intro q hq
              have hqr := (Finset.mem_filter.mp hq).2
              refine ⟨⟨q.val - (r + 1), by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp; omega⟩, ?_⟩
              ext; simp; omega
            · intro j hj
              have hltj : r + 1 + j.val < d + 1 := (Finset.mem_filter.mp hj).2
              have hstj : r + (j.val + 1) < d + 1 := by omega
              simp only [sweepTaps, state, kr, hltj, Fin.val_succ, hstj, dite_true]
              exact congrArg (B kr ⟨r + 1 + j.val, hltj⟩ * ·)
                (congrArg x (Fin.ext (by show r + (j.val + 1) = r + 1 + j.val; omega)))
          · refine Finset.sum_bij (fun j hj => ⟨r + 1 + j.val - (d + 1), by have := j.isLt; omega⟩) ?_ ?_ ?_ ?_
            · intro j hj
              have hn := (Finset.mem_filter.mp hj).2
              have := j.isLt
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
            · intro j₁ hj₁ j₂ hj₂ h
              have h1 := (Finset.mem_filter.mp hj₁).2
              have h2 := (Finset.mem_filter.mp hj₂).2
              exact Fin.ext (by have := Fin.mk.inj h; omega)
            · intro q hq
              have hqr := (Finset.mem_filter.mp hq).2
              refine ⟨⟨q.val + d - r, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp; omega⟩, ?_⟩
              ext; simp; omega
            · intro j hj
              have hnj : ¬ (r + 1 + j.val < d + 1) := (Finset.mem_filter.mp hj).2
              have hstj : ¬ (r + (j.val + 1) < d + 1) := by omega
              simp only [sweepTaps, state, kr, hnj, Fin.val_succ, hstj, dite_false]
              exact congrArg (A kr ⟨r + 1 + j.val - (d + 1), by have := j.isLt; omega⟩ * ·)
                (congrArg y (Fin.ext (by show r + (j.val + 1) - (d + 1) = r + 1 + j.val - (d + 1); omega)))
        rw [hA_split, hB_split] at hmul
        rw [hsum_j, ← add_assoc]
        have := congrArg (fun z => z + ∑ q ∈ Finset.univ.filter (fun q : Fin (d + 1) => q.val < r), A kr q * y q) hmul
        simpa only [add_assoc, zmod2_add_self, add_zero] using this.symm
      · simp only [linStepF, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_castSucc, state,
          Fin.val_castSucc, Fin.val_succ]
        have heq : r + 1 + j.val = r + (j.val + 1) := by omega
        simp only [heq]
  rw [hinv (d + 1) (le_refl _)]
  funext p
  have hn : ¬ (d + 1 + p.val < d + 1) := by omega
  simp only [state, hn, dite_false]
  congr 1; ext; simp

private lemma phiF_append {d L₁ L₂ : Nat} (t₁ : Fin L₁ → Fin d → K) (t₂ : Fin L₂ → Fin d → K)
    (v : Fin (d + 1) → K) :
    let t : Fin (L₁ + L₂) → Fin d → K := fun i =>
      if h : i.val < L₁ then t₁ ⟨i.val, h⟩ else t₂ ⟨i.val - L₁, by omega⟩
    phiF t (L₁ + L₂) v = phiF t₂ L₂ (phiF t₁ L₁ v) := by
  intro t
  have h1 : ∀ k, k ≤ L₁ → phiF t k v = phiF t₁ k v := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hk1 : k < L₁ := by omega
      have hk12 : k < L₁ + L₂ := by omega
      simp only [phiF, hk1, hk12, dite_true, LinearMap.comp_apply, ih (by omega), t]
  have h2 : ∀ k, k ≤ L₂ → phiF t (L₁ + k) v = phiF t₂ k (phiF t₁ L₁ v) := by
    intro k
    induction k with
    | zero => intro _; simpa [phiF] using h1 L₁ (le_refl _)
    | succ k ih =>
      intro hk
      have hk2 : k < L₂ := by omega
      have hk12 : L₁ + k < L₁ + L₂ := by omega
      have hnot : ¬ (L₁ + k < L₁) := by omega
      change phiF t ((L₁ + k) + 1) v = _
      simp only [phiF, hk2, hk12, dite_true, LinearMap.comp_apply, ih (by omega), t, hnot, dite_false]
      congr 2; ext; simp
  exact h2 L₂ (le_refl _)

private lemma undo_in_two_sweeps {d : Nat} (M : Matrix (Fin (d + 1)) (Fin (d + 1)) K)
    (hMinj : Function.Injective M.mulVec) :
    ∃ taps : Fin (2 * (d + 1)) → Fin d → K, ∀ x, phiF taps (2 * (d + 1)) x = M.mulVec x := by
  obtain ⟨U1, _, L, Li, U2, hU1, _, _, _, hL, hLi, hLr, hLl, hU2, hMeq⟩ := ulu_decomp (d + 1) M hMinj
  let t₁ := sweepTaps Li U2
  let t₂ := sweepTaps (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) K) U1
  have h1 : IsUnitLower (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) K) :=
    ⟨fun i => by simp, fun i j hij => by simp [Matrix.one_apply, ne_of_lt hij]⟩
  let t : Fin ((d + 1) + (d + 1)) → Fin d → K := fun i =>
    if h : i.val < d + 1 then t₁ ⟨i.val, h⟩ else t₂ ⟨i.val - (d + 1), by omega⟩
  refine ⟨fun i => t ⟨i.val, by omega⟩, fun x => ?_⟩
  have heq_t : ∀ k, k ≤ 2 * (d + 1) →
      phiF (fun i : Fin (2 * (d + 1)) => t ⟨i.val, by omega⟩) k x = phiF t k x := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hlt1 : k < 2 * (d + 1) := by omega
      have hlt2 : k < (d + 1) + (d + 1) := by omega
      simp only [phiF, hlt1, hlt2, dite_true, LinearMap.comp_apply, ih (by omega)]
  rw [heq_t (2 * (d + 1)) (le_refl _)]
  have h2w : 2 * (d + 1) = (d + 1) + (d + 1) := by omega
  rw [h2w, phiF_append t₁ t₂ x]
  have hs1 : phiF t₁ (d + 1) x = (L * U2).mulVec x := by
    apply sweep_realize Li U2 hLi hU2
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hLl, Matrix.one_mul]
  have hs2 : phiF t₂ (d + 1) ((L * U2).mulVec x) = U1.mulVec ((L * U2).mulVec x) := by
    apply sweep_realize 1 U1 h1 hU1
    rw [Matrix.one_mulVec]
  rw [hs1, hs2, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← hMeq]

-- ============================================================
-- Section 5: Maximal-Period LFSR via GaloisField 2 (d + 1) & Long Blocks
-- ============================================================

private lemma exists_max_period_lfsr (d : Nat) :
    ∃ (τ : Fin d → K),
      ∀ (i j : Nat), i < 2 ^ (d + 1) - 1 → j < 2 ^ (d + 1) - 1 →
        (linStepF τ)^[i] (Pi.single (Fin.last d) 1) = (linStepF τ)^[j] (Pi.single (Fin.last d) 1) →
        i = j := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let w := d + 1
  let F := GaloisField 2 w
  have hcardF : Nat.card F = 2 ^ w := GaloisField.card 2 w (Nat.succ_ne_zero d)
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hcardF]; positivity)
  haveI : Fintype F := Fintype.ofFinite F
  have hfcard : Fintype.card F = 2 ^ w := by rw [← Nat.card_eq_fintype_card, hcardF]
  have hchar2 : ∀ x : F, x + x = 0 := by
    intro x
    have h2 : (2 : F) = 0 := by
      have h2k : (2 : K) = 0 := rfl
      rw [← map_ofNat (algebraMap K F) 2, h2k, map_zero]
    calc
      x + x = (1 + 1) * x := by ring
      _ = (2 : F) * x := by norm_num
      _ = 0 := by rw [h2, zero_mul]
  obtain ⟨α, hα_gen⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hcardUnits : Nat.card Fˣ = 2 ^ w - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hfcard]
  have hord : orderOf α = 2 ^ w - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hα_gen, hcardUnits]
  let aF : F := (α : F)
  -- Power-basis linear map B : (Fin w → K) →ₗ[K] F
  let B : (Fin w → K) →ₗ[K] F :=
    { toFun := fun v => ∑ i : Fin w, v i • aF ^ i.val
      map_add' := fun u v => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r v => by
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum]
        apply Finset.sum_congr rfl; intro i _; rw [mul_smul] }
  have hBinj : Function.Injective B := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hvne
    let S := Finset.univ.filter (fun i : Fin w => v i ≠ 0)
    have hSne : S.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      apply hvne; funext i
      by_contra hi
      have : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rw [h] at this; exact Finset.notMem_empty _ this
    let imax := S.max' hSne
    let k := imax.val
    have hklt : k < w := imax.isLt
    have hvk : v imax = 1 := by
      rcases zmod2_eq_zero_or_one (v imax) with h0 | h1
      · exact absurd h0 (Finset.mem_filter.mp (Finset.max'_mem S hSne)).2
      · exact h1
    have hvgt : ∀ i : Fin w, k < i.val → v i = 0 := by
      intro i hi
      by_contra hne
      have hle := Finset.le_max' S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      have : i.val ≤ k := hle
      omega
    -- Express aF^k as a K-linear combination of aF^0, ..., aF^(k-1)
    let Bk : (Fin k → K) →ₗ[K] F :=
      { toFun := fun c => ∑ j : Fin k, c j • aF ^ j.val
        map_add' := fun u₁ u₂ => by simp [add_smul, Finset.sum_add_distrib]
        map_smul' := fun r u => by
          simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum]
          apply Finset.sum_congr rfl; intro j _; rw [mul_smul] }
    have hak_mem : aF ^ k ∈ LinearMap.range Bk := by
      refine ⟨fun j => v ⟨j.val, by omega⟩, ?_⟩
      change ∑ j : Fin k, v ⟨j.val, by omega⟩ • aF ^ j.val = aF ^ k
      have hsum_le : ∑ i : Fin w, v i • aF ^ i.val =
          aF ^ k + ∑ j : Fin k, v ⟨j.val, by omega⟩ • aF ^ j.val := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ imax), hvk, one_smul]
        congr 1
        have hsub : ∑ i ∈ Finset.univ.erase imax, v i • aF ^ i.val =
            ∑ i ∈ Finset.univ.filter (fun i : Fin w => i.val < k), v i • aF ^ i.val := by
          symm
          refine Finset.sum_subset (fun i hi => by
            have hlt := (Finset.mem_filter.mp hi).2
            exact Finset.mem_erase.mpr ⟨fun heq => by have := congrArg Fin.val heq; omega, Finset.mem_univ _⟩) ?_
          intro i hi hnot
          have hne := (Finset.mem_erase.mp hi).1
          have hge : k ≤ i.val := by
            simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hnot
          have hgt : k < i.val := by
            have : i.val ≠ k := fun heq => hne (Fin.ext heq)
            omega
          rw [hvgt i hgt, zero_smul]
        rw [hsub]
        refine (Finset.sum_bij (fun (j : Fin k) _ => (⟨j.val, by omega⟩ : Fin w)) ?_ ?_ ?_ ?_).symm
        · intro j _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩
        · intro j₁ _ j₂ _ h; exact Fin.ext (Fin.mk.inj h)
        · intro i hi
          have hlt := (Finset.mem_filter.mp hi).2
          exact ⟨⟨i.val, hlt⟩, Finset.mem_univ _, rfl⟩
        · intro j _; rfl
      have hv0 : aF ^ k + ∑ j : Fin k, v ⟨j.val, by omega⟩ • aF ^ j.val = 0 := by
        rw [← hsum_le]; exact hv
      have := congrArg (fun z => aF ^ k + z) hv0
      simpa only [← add_assoc, hchar2, zero_add, add_zero] using this
    have hkpos : 0 < k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      obtain ⟨c, hc⟩ := hak_mem
      have h1 : (1 : F) = 0 := by
        rw [← pow_zero aF, ← hk0, ← hc]
        simp [Bk, hk0]
      exact one_ne_zero h1
    have hpow_mem : ∀ m : Nat, aF ^ m ∈ LinearMap.range Bk := by
      intro m
      induction m with
      | zero =>
        refine ⟨Pi.single ⟨0, hkpos⟩ 1, ?_⟩
        simp [Bk, Pi.single_apply]
      | succ m ih =>
        obtain ⟨c, hc⟩ := ih
        have hstep : aF ^ (m + 1) = ∑ j : Fin k, c j • aF ^ (j.val + 1) := by
          rw [pow_succ', ← hc]
          simp only [Bk, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [Algebra.mul_smul_comm, pow_succ']
        rw [hstep]
        refine Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ ?_)
        by_cases hlt : j.val + 1 < k
        · refine ⟨Pi.single ⟨j.val + 1, hlt⟩ 1, ?_⟩
          simp [Bk, Pi.single_apply]
        · have heq : j.val + 1 = k := by have := j.isLt; omega
          rw [heq]; exact hak_mem
    have hBk_surj : Function.Surjective Bk := by
      intro x
      by_cases hx : x = 0
      · exact ⟨0, by rw [map_zero, hx]⟩
      · have hmem : Units.mk0 x hx ∈ Subgroup.zpowers α := hα_gen (Units.mk0 x hx)
        obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hmem
        have h2w : 2 ≤ 2 ^ w := by
          calc
            2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (Nat.succ_pos d)
        have hord_pos : 0 < orderOf α := by rw [hord]; omega
        let q : Nat := (z % (orderOf α : Int)).toNat
        have hq_eq : (q : Int) = z % (orderOf α : Int) :=
          Int.toNat_of_nonneg (Int.emod_nonneg z (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hord_pos)))
        have hpow_u : α ^ q = Units.mk0 x hx := by
          rw [← zpow_natCast, hq_eq, zpow_mod_orderOf, hz]
        have hx_eq : x = aF ^ q := by
          have := congrArg (fun u : Fˣ => (u : F)) hpow_u
          simpa [aF] using this.symm
        rw [hx_eq]
        exact hpow_mem q
    have hcard_le : Fintype.card F ≤ Fintype.card (Fin k → K) :=
      Fintype.card_le_of_surjective Bk hBk_surj
    have hcard_k : Fintype.card (Fin k → K) = 2 ^ k := by
      simp [Fintype.card_pi, ZMod.card]
    rw [hfcard, hcard_k] at hcard_le
    have hlt_pow : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by omega) hklt
    omega
  have hBbij : Function.Bijective B := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hBinj, ?_⟩
    rw [hfcard]; simp [Fintype.card_pi, ZMod.card]
  let eB := LinearEquiv.ofBijective B hBbij
  let c : Fin w → K := eB.symm (aF ^ w)
  have hc_sum : ∑ i : Fin w, c i • aF ^ i.val = aF ^ w := eB.apply_symm_apply (aF ^ w)
  have hc0 : c 0 = 1 := by
    rcases zmod2_eq_zero_or_one (c 0) with h0 | h1
    · exfalso
      have h1 : aF ^ w = aF * ∑ j : Fin d, c j.succ • aF ^ j.val := by
        rw [← hc_sum, Fin.sum_univ_succ, h0, zero_smul, zero_add, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [Algebra.mul_smul_comm, Fin.val_succ, pow_succ']
      have haF_ne : aF ≠ 0 := α.ne_zero
      have h2 : aF ^ d = ∑ j : Fin d, c j.succ • aF ^ j.val := by
        apply mul_left_cancel₀ haF_ne
        rw [← pow_succ', show d + 1 = w from rfl, h1]
      let u₁ : Fin w → K := Fin.snoc (α := fun _ : Fin w => K) (fun j : Fin d => c j.succ) 0
      let u₂ : Fin w → K := Pi.single (Fin.last d) 1
      have hBu : B u₁ = B u₂ := by
        have hBu₁ : B u₁ = ∑ j : Fin d, c j.succ • aF ^ j.val := by
          change ∑ i : Fin (d + 1), u₁ i • aF ^ i.val = _
          simp [u₁, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
        have hBu₂ : B u₂ = aF ^ d := by
          simp [B, u₂, Pi.single_apply]
        rw [hBu₁, hBu₂, h2]
      have hu_eq : u₁ = u₂ := hBinj hBu
      have hlast := congrFun hu_eq (Fin.last d)
      simp [u₁, u₂, Fin.snoc_last] at hlast
    · exact h1
  let τ : Fin d → K := fun j => c j.succ
  let φ : F →ₗ[K] K := (LinearMap.proj (0 : Fin w)).comp eB.symm.toLinearMap
  have hφ1 : φ 1 = 1 := by
    have hB0 : B (Pi.single (0 : Fin w) (1 : K)) = 1 := by simp [B, Pi.single_apply]
    have hsymm : eB.symm 1 = Pi.single (0 : Fin w) (1 : K) := by
      apply eB.injective
      rw [eB.apply_symm_apply]; exact hB0.symm
    change (eB.symm 1) 0 = 1
    rw [hsymm]; simp
  let ψ : F →ₗ[K] (Fin w → K) :=
    { toFun := fun z i => φ (aF ^ i.val * z)
      map_add' := fun z₁ z₂ => by funext i; simp [mul_add, map_add]
      map_smul' := fun r z => by
        funext i
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [Algebra.mul_smul_comm, map_smul, smul_eq_mul] }
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    by_contra hzne
    have hmul0 : ∀ v : Fin w → K, φ (B v * z) = 0 := by
      intro v
      have h1 : B v * z = ∑ i : Fin w, v i • (aF ^ i.val * z) := by
        simp only [B, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _; rw [Algebra.smul_mul_assoc]
      rw [h1, map_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [map_smul, smul_eq_mul]
      have hi := congrFun hz i
      simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hi
      rw [hi, mul_zero]
    have h1 := hmul0 (eB.symm z⁻¹)
    have hBz : B (eB.symm z⁻¹) = z⁻¹ := eB.apply_symm_apply z⁻¹
    rw [hBz, inv_mul_cancel₀ hzne, hφ1] at h1
    exact one_ne_zero h1
  have hψbij : Function.Bijective ψ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hψinj, ?_⟩
    rw [hfcard]; simp [Fintype.card_pi, ZMod.card]
  have hψstep : ∀ z : F, ψ (aF * z) = linStepF τ (ψ z) := by
    intro z
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [ψ, linStepF, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_last, Fin.val_last,
        Fin.val_zero, pow_zero, one_mul, Fin.val_succ]
      have hpow : aF ^ d * (aF * z) = aF ^ w * z := by
        rw [← mul_assoc, ← pow_succ]
      rw [hpow, ← hc_sum, Fin.sum_univ_succ, hc0, one_smul, Fin.val_zero, pow_zero, add_mul,
        one_mul, map_add]
      congr 1
      have hsum : (∑ j : Fin d, c j.succ • aF ^ j.succ.val) * z =
          ∑ j : Fin d, τ j • (aF ^ (j.val + 1) * z) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [Algebra.smul_mul_assoc]; rfl
      rw [hsum, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, smul_eq_mul]
    · simp only [ψ, linStepF, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_castSucc,
        Fin.val_castSucc, Fin.val_succ]
      rw [← mul_assoc, ← pow_succ]
  have hψiter : ∀ (k : Nat) (z : F), (linStepF τ)^[k] (ψ z) = ψ (aF ^ k * z) := by
    intro k
    induction k with
    | zero => intro z; simp
    | succ k ih =>
      intro z
      rw [Function.iterate_succ_apply', ih, ← hψstep, ← mul_assoc, ← pow_succ']
  obtain ⟨z₀, hz₀⟩ := hψbij.2 (Pi.single (Fin.last d) 1)
  have hz₀_ne : z₀ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hz₀
    have := congrFun hz₀ (Fin.last d)
    simp at this
  refine ⟨τ, fun i j hi hj heq => ?_⟩
  rw [← hz₀, hψiter i z₀, hψiter j z₀] at heq
  have hmul : aF ^ i * z₀ = aF ^ j * z₀ := hψinj heq
  have hpowF : aF ^ i = aF ^ j := mul_right_cancel₀ hz₀_ne hmul
  have hpowU : α ^ i = α ^ j := Units.ext (by simpa [aF] using hpowF)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hdiff : α ^ (j - i) = 1 := by
      apply mul_left_cancel (a := α ^ i)
      rw [← pow_add, show i + (j - i) = j by omega, hpowU, mul_one]
    have hdvd : orderOf α ∣ j - i := orderOf_dvd_of_pow_eq_one hdiff
    have hle : orderOf α ≤ j - i := Nat.le_of_dvd (by omega) hdvd
    rw [hord] at hle
    change 2 ^ (d + 1) - 1 ≤ j - i at hle
    omega
  · have hdiff : α ^ (i - j) = 1 := by
      apply mul_left_cancel (a := α ^ j)
      rw [← pow_add, show j + (i - j) = i by omega, hpowU, mul_one]
    have hdvd : orderOf α ∣ i - j := orderOf_dvd_of_pow_eq_one hdiff
    have hle : orderOf α ≤ i - j := Nat.le_of_dvd (by omega) hdvd
    rw [hord] at hle
    change 2 ^ (d + 1) - 1 ≤ i - j at hle
    omega

private lemma exists_good_linear_form {d L : Nat} (taps : Fin L → Fin d → K)
    (J : Finset (Fin L)) :
    ∃ a : Fin (d + 1) → K,
      J.card ≤ 2 * (J.filter (fun i => dotProduct a (disp taps i) = 1)).card := by
  classical
  have hdouble :
      ∑ a : Fin (d + 1) → K, 2 * (J.filter (fun i => dotProduct a (disp taps i) = 1)).card =
        2 ^ (d + 1) * J.card := by
    rw [← Finset.mul_sum]
    have hswap : ∑ a : Fin (d + 1) → K, (J.filter (fun i => dotProduct a (disp taps i) = 1)).card =
        ∑ i ∈ J, (Finset.univ.filter (fun a : Fin (d + 1) → K => dotProduct a (disp taps i) = 1)).card := by
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    rw [hswap, Finset.mul_sum]
    have hterm : ∀ i ∈ J,
        2 * (Finset.univ.filter (fun a : Fin (d + 1) → K => dotProduct a (disp taps i) = 1)).card =
          2 ^ (d + 1) := fun i _ => card_vec_dotProduct_eq_one (disp taps i) (disp_ne_zero taps i)
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, mul_comm]
  by_contra h
  push_neg at h
  have hlt : ∑ a : Fin (d + 1) → K, 2 * (J.filter (fun i => dotProduct a (disp taps i) = 1)).card <
      ∑ _a : Fin (d + 1) → K, J.card :=
    Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ _⟩ (fun a _ => h a)
  rw [hdouble, Finset.sum_const, Finset.card_univ, Fintype.card_pi] at hlt
  simp [ZMod.card, smul_eq_mul] at hlt

private lemma long_block_data {d L : Nat} (hlong : 10 * (d + 1) < L) :
    ∃ (taps : Fin L → Fin d → K) (I : Finset (Fin L)) (a : Fin (d + 1) → K),
      (∀ v, phiF taps L v = v) ∧ I.Nonempty ∧
      (∀ i₁ ∈ I, ∀ i₂ ∈ I, disp taps i₁ = disp taps i₂ → i₁ = i₂) ∧
      (∀ i ∈ I, dotProduct a (disp taps i) = 1) ∧
      2 ^ (d + 1) * min L (2 ^ (d + 1)) ≤ 10 * 2 ^ (d + 1) * I.card := by
  let w := d + 1
  let D := 2 ^ w
  have hDge2 : 2 ≤ D := by
    calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (Nat.succ_pos d)
  obtain ⟨τ, hτ⟩ := exists_max_period_lfsr d
  let L₁ := L - 2 * w
  have hLsplit : L₁ + 2 * w = L := by omega
  let t₁ : Fin L₁ → Fin d → K := fun _ => τ
  have ht₁_iter : ∀ k, k ≤ L₁ → ∀ v, phiF t₁ k v = (linStepF τ)^[k] v := by
    intro k
    induction k with
    | zero => intro _ v; rfl
    | succ k ih =>
      intro hk v
      have hlt : k < L₁ := by omega
      simp only [phiF, hlt, dite_true, LinearMap.comp_apply, ih (by omega) v, t₁]
      rw [Function.iterate_succ_apply']
  let M : Matrix (Fin w) (Fin w) K := LinearMap.toMatrix' (phiFInv t₁ L₁)
  have hMmul : ∀ v, M.mulVec v = phiFInv t₁ L₁ v := fun v => LinearMap.toMatrix'_mulVec _ v
  have hMinj : Function.Injective M.mulVec := by
    intro u v h
    have h' : phiFInv t₁ L₁ u = phiFInv t₁ L₁ v := by simpa only [hMmul] using h
    have := congrArg (phiF t₁ L₁) h'
    simpa only [phiF_phiFInv] using this
  obtain ⟨t₂, ht₂⟩ := undo_in_two_sweeps M hMinj
  let taps : Fin L → Fin d → K := fun i =>
    if h : i.val < L₁ then t₁ ⟨i.val, h⟩ else t₂ ⟨i.val - L₁, by omega⟩
  have hphi_pre : ∀ k, k ≤ L₁ → ∀ v, phiF taps k v = (linStepF τ)^[k] v := by
    intro k hk v
    have heq : phiF taps k v = phiF t₁ k v := by
      induction k with
      | zero => rfl
      | succ k ih =>
        have hk1 : k < L₁ := by omega
        have hkL : k < L := by omega
        simp only [phiF, hk1, hkL, dite_true, LinearMap.comp_apply, ih (by omega), taps]
    rw [heq, ht₁_iter k hk v]
  have hId : ∀ v, phiF taps L v = v := by
    intro v
    let tcat : Fin (L₁ + 2 * w) → Fin d → K := fun i =>
      if h : i.val < L₁ then t₁ ⟨i.val, h⟩ else t₂ ⟨i.val - L₁, by omega⟩
    have heq_cat : ∀ k, k ≤ L → phiF taps k v = phiF tcat k v := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        have hkL : k < L := by omega
        have hkC : k < L₁ + 2 * w := by omega
        simp only [phiF, hkL, hkC, dite_true, LinearMap.comp_apply, ih (by omega), taps, tcat]
    rw [heq_cat L (le_refl L), ← hLsplit, phiF_append t₁ t₂ v, ht₂, hMmul, phiFInv_phiF]
  let t := min L₁ (D - 1)
  have ht_pos : 1 ≤ t := by
    have : 1 ≤ L₁ := by omega
    have : 1 ≤ D - 1 := by omega
    exact le_min ‹_› ‹_›
  have ht_le_L₁ : t ≤ L₁ := min_le_left _ _
  have ht_le_D : t ≤ D - 1 := min_le_right _ _
  let J : Finset (Fin L) := Finset.univ.filter (fun i : Fin L => i.val < t)
  have hJcard : J.card = t := by
    have hbij : J.card = (Finset.univ : Finset (Fin t)).card := by
      refine Finset.card_bij (fun i hi => ⟨i.val, (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro i₁ _ i₂ _ h; exact Fin.ext (Fin.mk.inj h)
      · intro j _
        exact ⟨⟨j.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩, rfl⟩
    simpa using hbij
  have hJinj : ∀ i₁ ∈ J, ∀ i₂ ∈ J, disp taps i₁ = disp taps i₂ → i₁ = i₂ := by
    intro i₁ hi₁ i₂ hi₂ heq
    have h1 := (Finset.mem_filter.mp hi₁).2
    have h2 := (Finset.mem_filter.mp hi₂).2
    have hp1 : (linStepF τ)^[i₁.val + 1] (disp taps i₁) = Pi.single (Fin.last d) 1 := by
      rw [← hphi_pre (i₁.val + 1) (by omega), phiF_disp]
    have hp2 : (linStepF τ)^[i₂.val + 1] (disp taps i₁) = Pi.single (Fin.last d) 1 := by
      rw [heq, ← hphi_pre (i₂.val + 1) (by omega), phiF_disp]
    by_contra hne
    rcases lt_or_gt_of_ne (fun hv => hne (Fin.ext hv)) with hlt | hgt
    · have hloop : (linStepF τ)^[i₂.val - i₁.val] (Pi.single (Fin.last d) 1) =
          (linStepF τ)^[0] (Pi.single (Fin.last d) 1) := by
        calc
          (linStepF τ)^[i₂.val - i₁.val] (Pi.single (Fin.last d) 1)
              = (linStepF τ)^[i₂.val - i₁.val] ((linStepF τ)^[i₁.val + 1] (disp taps i₁)) := by rw [hp1]
          _ = (linStepF τ)^[i₂.val - i₁.val + (i₁.val + 1)] (disp taps i₁) := by rw [← Function.iterate_add_apply]
          _ = (linStepF τ)^[i₂.val + 1] (disp taps i₁) := by rw [show i₂.val - i₁.val + (i₁.val + 1) = i₂.val + 1 by omega]
          _ = Pi.single (Fin.last d) 1 := hp2
          _ = (linStepF τ)^[0] (Pi.single (Fin.last d) 1) := rfl
      have hlt1 : i₂.val - i₁.val < 2 ^ (d + 1) - 1 := by change _ < D - 1; omega
      have hlt0 : 0 < 2 ^ (d + 1) - 1 := by change 0 < D - 1; omega
      have hz := hτ (i₂.val - i₁.val) 0 hlt1 hlt0 hloop
      omega
    · have hloop : (linStepF τ)^[i₁.val - i₂.val] (Pi.single (Fin.last d) 1) =
          (linStepF τ)^[0] (Pi.single (Fin.last d) 1) := by
        calc
          (linStepF τ)^[i₁.val - i₂.val] (Pi.single (Fin.last d) 1)
              = (linStepF τ)^[i₁.val - i₂.val] ((linStepF τ)^[i₂.val + 1] (disp taps i₁)) := by rw [hp2]
          _ = (linStepF τ)^[i₁.val - i₂.val + (i₂.val + 1)] (disp taps i₁) := by rw [← Function.iterate_add_apply]
          _ = (linStepF τ)^[i₁.val + 1] (disp taps i₁) := by rw [show i₁.val - i₂.val + (i₂.val + 1) = i₁.val + 1 by omega]
          _ = Pi.single (Fin.last d) 1 := hp1
          _ = (linStepF τ)^[0] (Pi.single (Fin.last d) 1) := rfl
      have hlt1 : i₁.val - i₂.val < 2 ^ (d + 1) - 1 := by change _ < D - 1; omega
      have hlt0 : 0 < 2 ^ (d + 1) - 1 := by change 0 < D - 1; omega
      have hz := hτ (i₁.val - i₂.val) 0 hlt1 hlt0 hloop
      omega
  obtain ⟨a, ha⟩ := exists_good_linear_form taps J
  let I := J.filter (fun i => dotProduct a (disp taps i) = 1)
  have hIge : t ≤ 2 * I.card := by simpa [hJcard, I] using ha
  have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨taps, I, a, hId, hIne, ?_, ?_, ?_⟩
  · intro i₁ hi₁ i₂ hi₂ heq
    exact hJinj i₁ (Finset.mem_filter.mp hi₁).1 i₂ (Finset.mem_filter.mp hi₂).1 heq
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · have hmin_le : min L D ≤ 10 * I.card := by
      by_cases hcase : L₁ ≤ D - 1
      · have ht_eq : t = L₁ := min_eq_left hcase
        have h1 : min L D ≤ L := min_le_left L D
        omega
      · have ht_eq : t = D - 1 := min_eq_right (by omega)
        have hDeven : D = 2 * 2 ^ d := by
          change 2 ^ (d + 1) = 2 * 2 ^ d
          rw [pow_succ, mul_comm]
        have h1 : min L D ≤ D := min_le_right L D
        omega
    calc
      D * min L D ≤ D * (10 * I.card) := Nat.mul_le_mul_left D hmin_le
      _ = 10 * D * I.card := by ring

end PEqualNP.Outside.L_lib_540

theorem PEqualNP.Outside.L_lib_540 :
    ∀ (d L : Nat),
  let w := d+1
  let D := 2^w
  w ≤ L →
    let X := Fin w → Bool
    let S := Fin L × (Fin (w+1) → Bool)
    ∃ (m : Nat) (edge : Fin m → X × X) (base : S → Bool) (port : Bool → Fin m → S),
      D * min L D ≤ 20*m ∧ Function.Injective edge ∧
      (∀ u v : Fin m, (edge u).1 ≠ (edge v).2) ∧
      ∀ rev : Bool, Function.Injective (port rev) ∧ (∀ j, base (port rev j) = false) ∧
        ∀ enabled : Finset (Fin m), ∀ x y : X,
          (Finset.univ.filter (fun word : Fin (L+d+1) → Bool =>
            (∀ pos : Fin w,
              word (Fin.ofNat (L+d+1) pos.val) = x pos ∧
              word (Fin.ofNat (L+d+1) (L+pos.val)) = y pos) ∧
            ∀ i : Fin L,
              let s : S := (i,fun off => word (Fin.ofNat (L+d+1) (i.val+off.val)))
              base s = true ∨ s ∈ enabled.image (port rev))).card =
                (if x = y then 1 else 0) +
                (if ∃ j ∈ enabled, edge j = (if rev then (y,x) else (x,y)) then 1 else 0) := by
  intro d L w D hw X S
  by_cases hshort : L ≤ 10 * (d + 1)
  · obtain ⟨taps, I, a, hId, hIne, hInj, hDot, hSize⟩ :=
      PEqualNP.Outside.L_lib_540.short_block_data hw hshort
    exact PEqualNP.Outside.L_lib_540.buildFromLinearRows taps hId I a hIne hInj hDot hSize
  · obtain ⟨taps, I, a, hId, hIne, hInj, hDot, hSize⟩ :=
      PEqualNP.Outside.L_lib_540.long_block_data (d := d) (L := L) (by omega)
    exact PEqualNP.Outside.L_lib_540.buildFromLinearRows taps hId I a hIne hInj hDot hSize


import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_451_aux

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma zmod2_sub_eq_add (a b : ZMod 2) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  rcases zmod2_cases a with rfl | rfl
  · exact absurd rfl h
  · rfl

private lemma zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  have e := congrArg (· + b) h
  rw [add_assoc, zmod2_add_self, add_zero, zero_add] at e
  exact e

private lemma zmod2_decide_eq_iff (a b c : ZMod 2) :
    (decide (a = c) = decide (b = c)) ↔ a = b := by
  rcases zmod2_cases a with rfl | rfl <;>
  rcases zmod2_cases b with rfl | rfl <;>
  rcases zmod2_cases c with rfl | rfl <;> simp

private lemma zmod2_decide_add_one (u d : ZMod 2) (bb : Bool) :
    decide (u = d + 1) = bb ↔ u + d = if bb then 1 else 0 := by
  rcases zmod2_cases u with rfl | rfl <;> rcases zmod2_cases d with rfl | rfl <;> cases bb <;> decide

private lemma zmod2_decide_add_one_false (u d : ZMod 2) :
    decide (u = d + 1) = false ↔ u + d = 0 := by
  rcases zmod2_cases u with rfl | rfl <;> rcases zmod2_cases d with rfl | rfl <;> decide

private lemma zmod2_decide_eq_zero (v : ZMod 2) (b : Bool) :
    decide (v = 0) = b ↔ v = if b then 0 else 1 := by
  rcases zmod2_cases v with rfl | rfl <;> cases b <;> decide

private def chi (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

private lemma chi_zero : chi 0 = 1 := rfl

private lemma chi_one : chi 1 = -1 := rfl

private lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> decide

private lemma chi_abs (a : ZMod 2) : |chi a| = 1 := by
  fin_cases a <;> decide

private lemma chi_sq (a : ZMod 2) : chi a * chi a = 1 := by
  fin_cases a <;> decide

private lemma chi_inj {a b : ZMod 2} (h : chi a = chi b) : a = b := by
  rcases zmod2_cases a with rfl | rfl <;>
  rcases zmod2_cases b with rfl | rfl <;> simp_all [chi]

private lemma sum_chi_linear {W : Type*} [AddCommGroup W] [Fintype W]
    (ℓ : W → ZMod 2) (hadd : ∀ x y : W, ℓ (x + y) = ℓ x + ℓ y) :
    (∑ x : W, chi (ℓ x)) = if (∀ x : W, ℓ x = 0) then (Fintype.card W : ℤ) else 0 := by
  classical
  by_cases hall : ∀ x : W, ℓ x = 0
  · simp [hall, chi_zero]
  · simp only [hall, ↓reduceIte]
    have hex : ∃ v : W, ℓ v = 1 := by
      by_contra hno
      apply hall
      intro x
      by_contra hx
      exact hno ⟨x, zmod2_eq_one_of_ne_zero hx⟩
    rcases hex with ⟨v, hv⟩
    have hshift : (∑ x : W, chi (ℓ x)) = ∑ x : W, chi (ℓ (x + v)) :=
      (Equiv.sum_comp (Equiv.addRight v) (fun x => chi (ℓ x))).symm
    have hneg : (∑ x : W, chi (ℓ (x + v))) = -(∑ x : W, chi (ℓ x)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [hadd, hv, chi_add, chi_one]
      ring
    linarith

private lemma nat_card_subspace {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (U : Submodule (ZMod 2) W) :
    Nat.card ↥U = 2 ^ Module.finrank (ZMod 2) U := by
  classical
  have : Fintype ↥U := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := ↥U)
  rw [ZMod.card 2] at h
  exact h

private lemma sum_chi_inner_prod (r : ℕ) :
    (∑ x : (Fin r → ZMod 2) × (Fin r → ZMod 2), chi (∑ i : Fin r, x.1 i * x.2 i)) =
      (2 ^ r : ℤ) := by
  induction r with
  | zero =>
    simp [chi_zero]
  | succ r ih =>
    let e : ((Fin (r + 1) → ZMod 2) × (Fin (r + 1) → ZMod 2)) ≃
        ((ZMod 2 × ZMod 2) × ((Fin r → ZMod 2) × (Fin r → ZMod 2))) :=
      { toFun := fun x => ((x.1 0, x.2 0), (fun i => x.1 i.succ, fun i => x.2 i.succ))
        invFun := fun y => (Fin.cons y.1.1 y.2.1, Fin.cons y.1.2 y.2.2)
        left_inv := fun ⟨a, b⟩ => Prod.ext (Fin.cons_self_tail a) (Fin.cons_self_tail b)
        right_inv := fun ⟨⟨a0, b0⟩, ⟨a', b'⟩⟩ => by
          refine Prod.ext (Prod.ext rfl rfl) (Prod.ext ?_ ?_)
          · funext i; rfl
          · funext i; rfl }
    rw [← Equiv.sum_comp e.symm]
    rw [Fintype.sum_prod_type]
    have hsplit : ∀ (p : ZMod 2 × ZMod 2) (q : (Fin r → ZMod 2) × (Fin r → ZMod 2)),
        chi (∑ i : Fin (r + 1), (e.symm (p, q)).1 i * (e.symm (p, q)).2 i) =
        chi (p.1 * p.2) * chi (∑ i : Fin r, q.1 i * q.2 i) := by
      intro p q
      rw [Fin.sum_univ_succ, chi_add]
      rfl
    simp_rw [hsplit, ← Finset.mul_sum, ih, ← Finset.sum_mul]
    have h2 : (∑ p : ZMod 2 × ZMod 2, chi (p.1 * p.2)) = 2 := by decide
    rw [h2, pow_succ]
    ring

private def quadB {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2) (u v : Fin n → ZMod 2) : ZMod 2 :=
  f (u + v) + f u + f v + f 0

private lemma quad_bilinear {n : ℕ} {f : (Fin n → ZMod 2) → ZMod 2}
    (hf : ∀ p u v : Fin n → ZMod 2,
      f (p + u + v) + f (p + u) + f (p + v) + f p = f (u + v) + f u + f v + f 0) :
    (∀ u v, quadB f u v = quadB f v u) ∧ (∀ u, quadB f u u = 0) ∧
    (∀ u₁ u₂ v, quadB f (u₁ + u₂) v = quadB f u₁ v + quadB f u₂ v) ∧
    (∀ u v₁ v₂, quadB f u (v₁ + v₂) = quadB f u v₁ + quadB f u v₂) := by
  have hsym : ∀ u v, quadB f u v = quadB f v u := by
    intro u v; simp only [quadB]; rw [add_comm u v]; ring
  have halt : ∀ u, quadB f u u = 0 := by
    intro u
    simp only [quadB]
    have huu : u + u = 0 := by funext i; exact zmod2_add_self (u i)
    rw [huu]
    have e : f 0 + f u + f u + f 0 = (f 0 + f 0) + (f u + f u) := by ring
    rw [e, zmod2_add_self, zmod2_add_self, add_zero]
  have haddL : ∀ u₁ u₂ v, quadB f (u₁ + u₂) v = quadB f u₁ v + quadB f u₂ v := by
    intro u₁ u₂ v
    have h1 := hf u₁ u₂ v
    have h2 : quadB f (u₁ + u₂) v = f (u₁ + u₂ + v) + f (u₁ + u₂) + f v + f 0 := rfl
    have h3 : quadB f u₁ v = f (u₁ + v) + f u₁ + f v + f 0 := rfl
    have h4 : quadB f u₂ v = f (u₁ + u₂ + v) + f (u₁ + u₂) + f (u₁ + v) + f u₁ := h1.symm
    rw [h2, h3, h4]
    have hsum : (f (u₁ + v) + f u₁ + f v + f 0) +
        (f (u₁ + u₂ + v) + f (u₁ + u₂) + f (u₁ + v) + f u₁) =
        (f (u₁ + u₂ + v) + f (u₁ + u₂) + f v + f 0) +
        ((f (u₁ + v) + f (u₁ + v)) + (f u₁ + f u₁)) := by ring
    rw [hsum, zmod2_add_self, zmod2_add_self, add_zero, add_zero]
  have haddR : ∀ u v₁ v₂, quadB f u (v₁ + v₂) = quadB f u v₁ + quadB f u v₂ := by
    intro u v₁ v₂
    rw [hsym u (v₁ + v₂), haddL, hsym v₁ u, hsym v₂ u]
  exact ⟨hsym, halt, haddL, haddR⟩

private lemma exists_symplectic_basis {n : ℕ} (B : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2)
    (hsym : ∀ u v, B u v = B v u) (halt : ∀ u, B u u = 0)
    (haddL : ∀ u₁ u₂ v, B (u₁ + u₂) v = B u₁ v + B u₂ v)
    (haddR : ∀ u v₁ v₂, B u (v₁ + v₂) = B u v₁ + B u v₂) :
    ∀ W : Submodule (ZMod 2) (Fin n → ZMod 2),
      let RadW : Submodule (ZMod 2) (Fin n → ZMod 2) :=
        { carrier := {w | w ∈ W ∧ ∀ v ∈ W, B w v = 0}
          zero_mem' := ⟨W.zero_mem, fun v _ => by
            have h0 := haddL 0 0 v; rw [zero_add, zmod2_add_self] at h0; exact h0⟩
          , add_mem' := fun hx hy => ⟨W.add_mem hx.1 hy.1, fun v hv => by
            rw [haddL, hx.2 v hv, hy.2 v hv, zero_add]⟩
          smul_mem' := fun c x hx => by
            rcases zmod2_cases c with rfl | rfl
            · refine ⟨by simp, fun v _ => ?_⟩
              simp only [zero_smul]
              have h0 := haddL 0 0 v; rw [zero_add, zmod2_add_self] at h0; exact h0
            · simpa only [one_smul] using hx }
      ∃ (m : ℕ) (a b : Fin m → Fin n → ZMod 2),
        2 * m + Module.finrank (ZMod 2) RadW = Module.finrank (ZMod 2) W ∧
        (∀ i, a i ∈ W ∧ b i ∈ W) ∧
        (∀ i j, B (a i) (a j) = 0 ∧ B (b i) (b j) = 0 ∧
          B (a i) (b j) = if i = j then 1 else 0) := by
  have hB0L : ∀ v, B 0 v = 0 := by
    intro v
    have h0 := haddL 0 0 v; rw [zero_add, zmod2_add_self] at h0; exact h0
  have hBsmulL : ∀ (c : ZMod 2) (u v : Fin n → ZMod 2), B (c • u) v = c * B u v := by
    intro c u v
    rcases zmod2_cases c with rfl | rfl
    · simp [hB0L]
    · simp
  have hBsmulR : ∀ (c : ZMod 2) (u v : Fin n → ZMod 2), B u (c • v) = c * B u v := by
    intro c u v; rw [hsym, hBsmulL, hsym]
  intro W
  induction hdim : Module.finrank (ZMod 2) W using Nat.strong_induction_on generalizing W with
  | ind d ih =>
    intro RadW
    by_cases htriv : ∀ x ∈ W, ∀ y ∈ W, B x y = 0
    · refine ⟨0, Fin.elim0, Fin.elim0, ?_, fun i => i.elim0, fun i => i.elim0⟩
      have hReq : RadW = W := by
        ext x
        exact ⟨fun hx => hx.1, fun hx => ⟨hx, fun v hv => htriv x hx v hv⟩⟩
      rw [hReq]
      omega
    · have hex : ∃ x₀ ∈ W, ∃ y₀ ∈ W, B x₀ y₀ = 1 := by
        by_contra hno
        apply htriv
        intro x hx y hy
        by_contra hne
        exact hno ⟨x, hx, y, hy, zmod2_eq_one_of_ne_zero hne⟩
      rcases hex with ⟨x₀, hx₀, y₀, hy₀, hBxy⟩
      let W' : Submodule (ZMod 2) (Fin n → ZMod 2) :=
        { carrier := {w | w ∈ W ∧ B w x₀ = 0 ∧ B w y₀ = 0}
          zero_mem' := ⟨W.zero_mem, hB0L x₀, hB0L y₀⟩
          , add_mem' := fun hx hy => ⟨W.add_mem hx.1 hy.1,
            by rw [haddL, hx.2.1, hy.2.1, zero_add],
            by rw [haddL, hx.2.2, hy.2.2, zero_add]⟩
          smul_mem' := fun c x hx => ⟨W.smul_mem c hx.1,
            by rw [hBsmulL, hx.2.1, mul_zero],
            by rw [hBsmulL, hx.2.2, mul_zero]⟩ }
      have hByx : B y₀ x₀ = 1 := by rw [hsym, hBxy]
      let splitE : ↥W ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) × ↥W' :=
        { toFun := fun w =>
            ((B w.1 y₀, B w.1 x₀),
             ⟨w.1 + (B w.1 y₀) • x₀ + (B w.1 x₀) • y₀,
              ⟨W.add_mem (W.add_mem w.2 (W.smul_mem _ hx₀)) (W.smul_mem _ hy₀),
               by
                rw [haddL, haddL, hBsmulL, hBsmulL, halt, hByx, mul_zero, mul_one, add_zero,
                  zmod2_add_self],
               by
                rw [haddL, haddL, hBsmulL, hBsmulL, hBxy, halt, mul_one, mul_zero, add_zero,
                  zmod2_add_self]⟩⟩)
          map_add' := fun u v => by
            refine Prod.ext (Prod.ext (haddL u.1 v.1 y₀) (haddL u.1 v.1 x₀)) (Subtype.ext ?_)
            change (u.1 + v.1) + B (u.1 + v.1) y₀ • x₀ + B (u.1 + v.1) x₀ • y₀ =
              (u.1 + B u.1 y₀ • x₀ + B u.1 x₀ • y₀) + (v.1 + B v.1 y₀ • x₀ + B v.1 x₀ • y₀)
            rw [haddL, haddL, add_smul, add_smul]
            abel
          map_smul' := fun c u => by
            refine Prod.ext (Prod.ext (hBsmulL c u.1 y₀) (hBsmulL c u.1 x₀)) (Subtype.ext ?_)
            change c • u.1 + B (c • u.1) y₀ • x₀ + B (c • u.1) x₀ • y₀ =
              c • (u.1 + B u.1 y₀ • x₀ + B u.1 x₀ • y₀)
            rw [hBsmulL, hBsmulL, smul_add, smul_add, mul_smul, mul_smul]
          invFun := fun p =>
            ⟨p.2.1 + p.1.1 • x₀ + p.1.2 • y₀,
             W.add_mem (W.add_mem p.2.2.1 (W.smul_mem _ hx₀)) (W.smul_mem _ hy₀)⟩
          left_inv := fun w => by
            apply Subtype.ext
            change w.1 + B w.1 y₀ • x₀ + B w.1 x₀ • y₀ + B w.1 y₀ • x₀ + B w.1 x₀ • y₀ = w.1
            funext i
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            have h1 : w.1 i + B w.1 y₀ * x₀ i + B w.1 x₀ * y₀ i + B w.1 y₀ * x₀ i +
                B w.1 x₀ * y₀ i =
                w.1 i + ((B w.1 y₀ * x₀ i + B w.1 y₀ * x₀ i) +
                  (B w.1 x₀ * y₀ i + B w.1 x₀ * y₀ i)) := by ring
            rw [h1, zmod2_add_self, zmod2_add_self, add_zero, add_zero]
          right_inv := fun ⟨⟨c₁, c₂⟩, ⟨w', hw'⟩⟩ => by
            have h1 : B (w' + c₁ • x₀ + c₂ • y₀) y₀ = c₁ := by
              rw [haddL, haddL, hw'.2.2, hBsmulL, hBsmulL, hBxy, halt]; ring
            have h2 : B (w' + c₁ • x₀ + c₂ • y₀) x₀ = c₂ := by
              rw [haddL, haddL, hw'.2.1, hBsmulL, hBsmulL, halt, hByx]; ring
            refine Prod.ext (Prod.ext h1 h2) (Subtype.ext ?_)
            change (w' + c₁ • x₀ + c₂ • y₀) + B (w' + c₁ • x₀ + c₂ • y₀) y₀ • x₀ +
              B (w' + c₁ • x₀ + c₂ • y₀) x₀ • y₀ = w'
            rw [h1, h2]
            funext i
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            have h3 : w' i + c₁ * x₀ i + c₂ * y₀ i + c₁ * x₀ i + c₂ * y₀ i =
                w' i + ((c₁ * x₀ i + c₁ * x₀ i) + (c₂ * y₀ i + c₂ * y₀ i)) := by ring
            rw [h3, zmod2_add_self, zmod2_add_self, add_zero, add_zero] }
      have hdim_split : Module.finrank (ZMod 2) W = 2 + Module.finrank (ZMod 2) W' := by
        rw [splitE.finrank_eq, Module.finrank_prod, Module.finrank_prod, Module.finrank_self]
      have hlt : Module.finrank (ZMod 2) W' < d := by omega
      obtain ⟨m', a', b', hdim', hmem', hsymp'⟩ := ih (Module.finrank (ZMod 2) W') hlt W' rfl
      have hRad_eq : RadW =
          { carrier := {w | w ∈ W' ∧ ∀ v ∈ W', B w v = 0}
            zero_mem' := ⟨W'.zero_mem, fun v _ => hB0L v⟩
            , add_mem' := fun hx hy => ⟨W'.add_mem hx.1 hy.1, fun v hv => by
              rw [haddL, hx.2 v hv, hy.2 v hv, zero_add]⟩
            smul_mem' := fun c x hx => ⟨W'.smul_mem c hx.1, fun v hv => by
              rw [hBsmulL, hx.2 v hv, mul_zero]⟩ } := by
        ext w
        constructor
        · intro hw
          exact ⟨⟨hw.1, hw.2 x₀ hx₀, hw.2 y₀ hy₀⟩, fun v hv => hw.2 v hv.1⟩
        · intro hw
          refine ⟨hw.1.1, fun v hv => ?_⟩
          have hv_eq : v = (splitE.symm (splitE ⟨v, hv⟩)).1 := by
            rw [splitE.symm_apply_apply]
          rw [hv_eq]
          change B w ((v + B v y₀ • x₀ + B v x₀ • y₀) + B v y₀ • x₀ + B v x₀ • y₀) = 0
          rw [haddR, haddR, hBsmulR, hBsmulR, hw.1.2.1, hw.1.2.2, mul_zero, mul_zero, add_zero, add_zero]
          exact hw.2 _ (splitE ⟨v, hv⟩).2.2
      refine ⟨m' + 1, Fin.cons x₀ a', Fin.cons y₀ b', ?_, ?_, ?_⟩
      · rw [hRad_eq]
        omega
      · intro i
        refine Fin.cases ⟨hx₀, hy₀⟩ (fun j => ⟨(hmem' j).1.1, (hmem' j).2.1⟩) i
      · intro i j
        refine Fin.cases ?_ (fun i' => ?_) i
        · refine Fin.cases ?_ (fun j' => ?_) j
          · simp [halt, hBxy]
          · simp only [Fin.cons_zero, Fin.cons_succ]
            rw [ite_eq_right_iff.mpr (fun h => absurd h.symm (Fin.succ_ne_zero j'))]
            refine ⟨?_, ?_, ?_⟩
            · rw [hsym]; exact (hmem' j').1.2.1
            · rw [hsym]; exact (hmem' j').2.2.2
            · rw [hsym]; exact (hmem' j').2.2.1
        · refine Fin.cases ?_ (fun j' => ?_) j
          · simp only [Fin.cons_succ, Fin.cons_zero, Fin.succ_ne_zero, ↓reduceIte]
            exact ⟨(hmem' i').1.2.1, (hmem' i').2.2.2, (hmem' i').1.2.2⟩
          · simp only [Fin.cons_succ, Fin.succ_inj]
            exact hsymp' i' j'

private def dotLin {n : ℕ} (v : Fin n → ZMod 2) : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun := fun x => dotProduct v x
  map_add' := fun x y => dotProduct_add v x y
  map_smul' := fun c x => by simp [dotProduct_smul]

private def dotEquiv (n : ℕ) : (Fin n → ZMod 2) ≃ₗ[ZMod 2] ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) where
  toFun := dotLin
  map_add' := fun u v => by apply LinearMap.ext; intro x; exact add_dotProduct u v x
  map_smul' := fun c u => by apply LinearMap.ext; intro x; simp [dotLin, smul_dotProduct]
  invFun := fun ℓ j => ℓ (Pi.single j 1)
  left_inv := fun v => by funext j; simp [dotLin]
  right_inv := fun ℓ => by
    apply LinearMap.ext
    intro x
    change ∑ j : Fin n, ℓ (Pi.single j 1) * x j = ℓ x
    have hx : x = ∑ j : Fin n, x j • Pi.single j (1 : ZMod 2) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hx]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, smul_eq_mul, mul_comm]

private def perpSub {n : ℕ} (S : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  { carrier := {α | ∀ u ∈ S, dotProduct α u = 0}
    zero_mem' := fun u _ => zero_dotProduct u
    , add_mem' := fun h1 h2 u hu => by rw [add_dotProduct, h1 u hu, h2 u hu, zero_add]
    smul_mem' := fun c α h1 u hu => by rw [smul_dotProduct, h1 u hu, smul_zero] }

private lemma finrank_perpSub {n : ℕ} (S : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Module.finrank (ZMod 2) (perpSub S) + Module.finrank (ZMod 2) S = n := by
  let res : (Fin n → ZMod 2) →ₗ[ZMod 2] (↥S →ₗ[ZMod 2] ZMod 2) :=
    { toFun := fun α => (dotLin α).comp S.subtype
      map_add' := fun α₁ α₂ => by apply LinearMap.ext; intro u; exact add_dotProduct α₁ α₂ u.1
      map_smul' := fun c α => by
        apply LinearMap.ext; intro u; simp [dotLin, smul_dotProduct] }
  have hker : LinearMap.ker res = perpSub S := by
    ext α
    simp only [LinearMap.mem_ker]
    constructor
    · intro h u hu; exact LinearMap.congr_fun h ⟨u, hu⟩
    · intro h; apply LinearMap.ext; intro ⟨u, hu⟩; exact h u hu
  have hsurj : Function.Surjective res := by
    intro g
    obtain ⟨S', hS'⟩ := Submodule.exists_isCompl S
    let ℓ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := g.comp (S.projectionOnto S' hS')
    refine ⟨(dotEquiv n).symm ℓ, ?_⟩
    apply LinearMap.ext
    intro u
    change dotLin ((dotEquiv n).symm ℓ) u.1 = g u
    have h1 : dotLin ((dotEquiv n).symm ℓ) = ℓ := (dotEquiv n).apply_symm_apply ℓ
    rw [h1]
    exact congrArg g (Submodule.projectionOnto_apply_left hS' u)
  have hrn := LinearMap.finrank_range_add_finrank_ker res
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker, Module.finrank_fin_fun,
    Module.finrank_linearMap, Module.finrank_self, mul_one, add_comm] at hrn
  exact hrn

private lemma perpSub_perpSub {n : ℕ} (S : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    perpSub (perpSub S) = S := by
  have hle : S ≤ perpSub (perpSub S) := by
    intro u hu α hα
    rw [dotProduct_comm]
    exact hα u hu
  have h1 := finrank_perpSub S
  have h2 := finrank_perpSub (perpSub S)
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

private lemma flat_charge_pow2 {n : ℕ} {f : (Fin n → ZMod 2) → ZMod 2}
    (hf : ∀ p u v : Fin n → ZMod 2,
      f (p + u + v) + f (p + u) + f (p + v) + f p = f (u + v) + f u + f v + f 0)
    (a : Fin n → ZMod 2) (S : Submodule (ZMod 2) (Fin n → ZMod 2)) [Fintype ↥S] :
    let val : ℤ := ∑ x : ↥S, chi (f (a + x.1))
    val = 0 ∨ ∃ r : ℕ, val.natAbs = 2 ^ r := by
  classical
  intro val
  obtain ⟨hsym, _, haddL, haddR⟩ := quad_bilinear hf
  have hB0L : ∀ v, quadB f 0 v = 0 := by
    intro v; have h0 := haddL 0 0 v; rw [zero_add, zmod2_add_self] at h0; exact h0
  have hquad_shift : ∀ u v : Fin n → ZMod 2,
      f (a + (u + v)) + f (a + u) = f (a + v) + f a + quadB f u v := by
    intro u v
    have h2 : f (a + u + v) + f (a + u) + f (a + v) + f a = quadB f u v := hf a u v
    have h3 : f (a + (u + v)) + f (a + u) =
        (f (a + u + v) + f (a + u) + f (a + v) + f a) + (f (a + v) + f a) := by
      have e : (f (a + u + v) + f (a + u) + f (a + v) + f a) + (f (a + v) + f a) =
          f (a + u + v) + f (a + u) + ((f (a + v) + f (a + v)) + (f a + f a)) := by ring
      rw [e, zmod2_add_self, zmod2_add_self, add_zero, add_zero, add_assoc]
    rw [h3, h2, add_comm]
  have hsq : val * val =
      ∑ v : ↥S, chi (f (a + v.1) + f a) * ∑ u : ↥S, chi (quadB f u.1 v.1) := by
    dsimp only [val]
    rw [Finset.sum_mul]
    have h1 : ∀ u : ↥S, chi (f (a + u.1)) * ∑ y : ↥S, chi (f (a + y.1)) =
        ∑ v : ↥S, chi (f (a + v.1) + f a) * chi (quadB f u.1 v.1) := by
      intro u
      rw [Finset.mul_sum]
      rw [← Equiv.sum_comp (Equiv.addLeft u)]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      change chi (f (a + u.1)) * chi (f (a + (u.1 + v.1))) = _
      rw [← chi_add, add_comm (f (a + u.1)), hquad_shift u.1 v.1, chi_add]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ => (Finset.mul_sum _ _ _).symm)
  let RadS : Submodule (ZMod 2) ↥S :=
    { carrier := {v | ∀ u : ↥S, quadB f u.1 v.1 = 0}
      zero_mem' := fun u => by change quadB f u.1 0 = 0; rw [hsym, hB0L]
      , add_mem' := fun hx hy u => by change quadB f u.1 (_ + _) = 0; rw [haddR, hx u, hy u, zero_add]
      smul_mem' := fun c x hx u => by
        rcases zmod2_cases c with rfl | rfl
        · simp only [zero_smul, ZeroMemClass.coe_zero]; rw [hsym, hB0L]
        · simpa only [one_smul] using hx u }
  have hinner : ∀ v : ↥S,
      (∑ u : ↥S, chi (quadB f u.1 v.1)) = if v ∈ RadS then (Fintype.card ↥S : ℤ) else 0 := by
    intro v
    have h1 := sum_chi_linear (fun u : ↥S => quadB f u.1 v.1) (fun u₁ u₂ => haddL u₁.1 u₂.1 v.1)
    rw [h1]
    by_cases hv : v ∈ RadS
    · have hv' : ∀ u : ↥S, quadB f u.1 v.1 = 0 := hv
      rw [if_pos hv', if_pos hv]
    · have hv' : ¬ ∀ u : ↥S, quadB f u.1 v.1 = 0 := hv
      rw [if_neg hv', if_neg hv]
  simp_rw [hinner] at hsq
  have hRad_lin : ∀ v₁ v₂ : ↥RadS,
      f (a + (v₁.1.1 + v₂.1.1)) + f a = (f (a + v₁.1.1) + f a) + (f (a + v₂.1.1) + f a) := by
    intro v₁ v₂
    have h1 := hquad_shift v₁.1.1 v₂.1.1
    have hB0 : quadB f v₁.1.1 v₂.1.1 = 0 := v₂.2 v₁.1
    rw [hB0, add_zero] at h1
    have h2 : f (a + (v₁.1.1 + v₂.1.1)) + f (a + v₁.1.1) + (f (a + v₁.1.1) + f a) =
        f (a + v₂.1.1) + f a + (f (a + v₁.1.1) + f a) := congrArg (· + (f (a + v₁.1.1) + f a)) h1
    have h3 : f (a + (v₁.1.1 + v₂.1.1)) + f (a + v₁.1.1) + (f (a + v₁.1.1) + f a) =
        f (a + (v₁.1.1 + v₂.1.1)) + f a + (f (a + v₁.1.1) + f (a + v₁.1.1)) := by ring
    rw [h3, zmod2_add_self, add_zero] at h2
    rw [h2, add_comm]
  have : Fintype ↥RadS := Fintype.ofFinite _
  let ℓR : ↥RadS → ZMod 2 := fun v => f (a + v.1.1) + f a
  have hsum_rad : (∑ v : ↥S, chi (f (a + v.1) + f a) * if v ∈ RadS then (Fintype.card ↥S : ℤ) else 0) =
      (Fintype.card ↥S : ℤ) * ∑ v : ↥RadS, chi (ℓR v) := by
    rw [Finset.mul_sum]
    have hfilt : (∑ v : ↥S, chi (f (a + v.1) + f a) * if v ∈ RadS then (Fintype.card ↥S : ℤ) else 0) =
        ∑ v ∈ Finset.univ.filter (fun v : ↥S => v ∈ RadS), (Fintype.card ↥S : ℤ) * chi (f (a + v.1) + f a) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      split_ifs <;> ring
    rw [hfilt]
    refine Finset.sum_bij (fun v hv => ⟨v, (Finset.mem_filter.mp hv).2⟩) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro _ _ _ _ h; exact congrArg Subtype.val h
    · intro v _; exact ⟨v.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, v.2⟩, rfl⟩
    · intro _ _; rfl
  have hRlin := sum_chi_linear ℓR hRad_lin
  rw [hsum_rad, hRlin] at hsq
  by_cases hall : ∀ v : ↥RadS, ℓR v = 0
  · rw [if_pos hall] at hsq
    right
    have hcardS : Fintype.card ↥S = 2 ^ Module.finrank (ZMod 2) S := by
      rw [← Nat.card_eq_fintype_card, nat_card_subspace]
    have hcardR : Fintype.card ↥RadS = 2 ^ Module.finrank (ZMod 2) RadS := by
      rw [← Nat.card_eq_fintype_card, nat_card_subspace]
    have hnat : val.natAbs * val.natAbs =
        2 ^ (Module.finrank (ZMod 2) S + Module.finrank (ZMod 2) RadS) := by
      have hz : ((val.natAbs * val.natAbs : ℕ) : ℤ) =
          ((2 ^ (Module.finrank (ZMod 2) S + Module.finrank (ZMod 2) RadS) : ℕ) : ℤ) := by
        rw [Nat.cast_mul, ← Int.abs_eq_natAbs, abs_mul_abs_self, hsq, hcardS, hcardR, pow_add]
        push_cast
        rfl
      exact Int.ofNat.inj hz
    have heven : Even (Module.finrank (ZMod 2) S + Module.finrank (ZMod 2) RadS) := by
      by_contra hodd
      have hrem : (Module.finrank (ZMod 2) S + Module.finrank (ZMod 2) RadS) % 2 = 1 := by
        rw [Nat.even_iff] at hodd; omega
      set e := (Module.finrank (ZMod 2) S + Module.finrank (ZMod 2) RadS) / 2
      have heq : Module.finrank (ZMod 2) S + Module.finrank (ZMod 2) RadS = 2 * e + 1 := by omega
      rw [heq, pow_succ, pow_mul] at hnat
      have hdiv : 2 ^ e ∣ val.natAbs := by
        have hsq' : (2 ^ e) ^ 2 ∣ val.natAbs ^ 2 :=
          ⟨2, by rw [pow_two, hnat, ← pow_mul, mul_comm 2 e, pow_mul]⟩
        exact (Nat.pow_dvd_pow_iff (by omega : 2 ≠ 0)).mp hsq'
      rcases hdiv with ⟨q, hq⟩
      rw [hq] at hnat
      have hpos : 0 < 2 ^ e * 2 ^ e := by positivity
      have hq2 : q * q = 2 := by
        have hmul : (2 ^ e * 2 ^ e) * (q * q) = (2 ^ e * 2 ^ e) * 2 := by
          calc (2 ^ e * 2 ^ e) * (q * q) = (2 ^ e * q) * (2 ^ e * q) := by ring
            _ = (2 ^ 2) ^ e * 2 := hnat
            _ = (2 ^ e * 2 ^ e) * 2 := by rw [← pow_mul, two_mul, pow_add]
        exact Nat.eq_of_mul_eq_mul_left hpos hmul
      have hq_le : q ≤ 2 := by nlinarith
      interval_cases q <;> omega
    rcases heven with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    have hsq2 : val.natAbs ^ 2 = (2 ^ r) ^ 2 := by
      rw [pow_two, hnat, hr, ← two_mul, mul_comm 2 r, pow_mul]
    exact Nat.pow_left_injective (by omega : 2 ≠ 0) hsq2
  · rw [if_neg hall, mul_zero] at hsq
    left
    exact mul_self_eq_zero.mp hsq

private lemma sum_eq_card_mul_bound {ι : Type*} (s : Finset ι) (g : ι → ℤ) (C : ℤ)
    (hbound : ∀ i ∈ s, |g i| ≤ C) (heq : ∑ i ∈ s, g i = (s.card : ℤ) * C) :
    ∀ i ∈ s, g i = C := by
  intro i hi
  by_contra hne
  have hle : ∀ j ∈ s, g j ≤ C := fun j hj => le_trans (le_abs_self _) (hbound j hj)
  have hlt : g i < C := lt_of_le_of_ne (hle i hi) hne
  have hsum_lt : ∑ j ∈ s, g j < ∑ _j ∈ s, C := Finset.sum_lt_sum hle ⟨i, hi, hlt⟩
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum_lt
  linarith

private lemma sum_eq_neg_card_mul_bound {ι : Type*} (s : Finset ι) (g : ι → ℤ) (C : ℤ)
    (hbound : ∀ i ∈ s, |g i| ≤ C) (heq : ∑ i ∈ s, g i = -((s.card : ℤ) * C)) :
    ∀ i ∈ s, g i = -C := by
  have h := sum_eq_card_mul_bound s (fun i => -g i) C (fun i hi => by rw [abs_neg]; exact hbound i hi)
    (by rw [Finset.sum_neg_distrib, heq, neg_neg])
  intro i hi
  linarith [h i hi]

private def mkPrefixTree : ℕ → ℕ → Finset (List Bool) × Finset (List Bool)
  | 0, _ => ({[]}, ∅)
  | m + 1, t =>
    if t ≤ 1 then ({[]}, ∅)
    else
      let t₀ := t / 2
      let t₁ := t - t₀
      let r₀ := mkPrefixTree m t₀
      let r₁ := mkPrefixTree m t₁
      (insert [] (r₀.1.image (false :: ·) ∪ r₁.1.image (true :: ·)),
       insert [] (r₀.2.image (false :: ·) ∪ r₁.2.image (true :: ·)))

private lemma mkPrefixTree_props (m : ℕ) :
    ∀ t : ℕ, 1 ≤ t → t ≤ 2 ^ m →
      let N := (mkPrefixTree m t).1
      let J := (mkPrefixTree m t).2
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      (N \ J).card = t ∧
      (∀ p ∈ N, p.length ≤ m) ∧
      ((N \ J).filter (fun p => ∀ b ∈ p, b = false)).card = 1 := by
  induction m with
  | zero =>
    intro t ht1 htm
    have ht : t = 1 := by simp at htm; omega
    subst ht
    simp [mkPrefixTree]
    rfl
  | succ m ih =>
    intro t ht1 htm
    by_cases h1 : t ≤ 1
    · have ht : t = 1 := by omega
      subst ht
      simp [mkPrefixTree]
      rfl
    · dsimp only [mkPrefixTree]
      rw [ite_eq_right_iff.mpr (fun h => absurd h h1)]
      set t₀ := t / 2
      set t₁ := t - t₀
      have ht0_1 : 1 ≤ t₀ := by omega
      have ht0_le : t₀ ≤ 2 ^ m := by rw [pow_succ] at htm; omega
      have ht1_1 : 1 ≤ t₁ := by omega
      have ht1_le : t₁ ≤ 2 ^ m := by rw [pow_succ] at htm; omega
      obtain ⟨h0_nil, h0_sub, h0_par, h0_ch, h0_card, h0_len, h0_zero⟩ := ih t₀ ht0_1 ht0_le
      obtain ⟨h1_nil, h1_sub, h1_par, h1_ch, h1_card, h1_len, _⟩ := ih t₁ ht1_1 ht1_le
      set N₀ := (mkPrefixTree m t₀).1
      set J₀ := (mkPrefixTree m t₀).2
      set N₁ := (mkPrefixTree m t₁).1
      set J₁ := (mkPrefixTree m t₁).2
      set N := insert ([] : List Bool) (N₀.image (false :: ·) ∪ N₁.image (true :: ·))
      set J := insert ([] : List Bool) (J₀.image (false :: ·) ∪ J₁.image (true :: ·))
      have hnil : [] ∈ N := Finset.mem_insert_self _ _
      have hsub : J ⊆ N := by
        intro p hp
        simp only [J, N, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
        rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨q, h0_sub hq, rfl⟩)
        · exact Or.inr (Or.inr ⟨q, h1_sub hq, rfl⟩)
      have hpar : ∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J := by
        intro p b hp
        cases p with
        | nil => exact Finset.mem_insert_self _ _
        | cons c rest =>
          simp only [N, Finset.mem_insert, Finset.mem_union, Finset.mem_image, List.cons_append] at hp
          rcases hp with h0 | ⟨q, hq, heq⟩ | ⟨q, hq, heq⟩
          · exact absurd h0 (List.cons_ne_nil _ _)
          · injection heq with hc hrest
            subst hc
            rw [hrest] at hq
            exact Finset.mem_insert_of_mem (Finset.mem_union_left _
              (Finset.mem_image_of_mem _ (h0_par rest b hq)))
          · injection heq with hc hrest
            subst hc
            rw [hrest] at hq
            exact Finset.mem_insert_of_mem (Finset.mem_union_right _
              (Finset.mem_image_of_mem _ (h1_par rest b hq)))
      have hch : ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N := by
        intro p hp
        simp only [J, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
        rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
        · exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h0_nil)),
            Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ h1_nil))⟩
        · exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _
              (Finset.mem_image_of_mem _ (h0_ch q hq).1)),
            Finset.mem_insert_of_mem (Finset.mem_union_left _
              (Finset.mem_image_of_mem _ (h0_ch q hq).2))⟩
        · exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _
              (Finset.mem_image_of_mem _ (h1_ch q hq).1)),
            Finset.mem_insert_of_mem (Finset.mem_union_right _
              (Finset.mem_image_of_mem _ (h1_ch q hq).2))⟩
      have hleaves_eq : N \ J = (N₀ \ J₀).image (false :: ·) ∪ (N₁ \ J₁).image (true :: ·) := by
        ext p
        simp only [N, J, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
        constructor
        · rintro ⟨rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩, hnot⟩
          · exact absurd (Or.inl rfl) hnot
          · left
            refine ⟨q, ⟨hq, fun hqJ => hnot (Or.inr (Or.inl ⟨q, hqJ, rfl⟩))⟩, rfl⟩
          · right
            refine ⟨q, ⟨hq, fun hqJ => hnot (Or.inr (Or.inr ⟨q, hqJ, rfl⟩))⟩, rfl⟩
        · rintro (⟨q, ⟨hqN, hqJ⟩, rfl⟩ | ⟨q, ⟨hqN, hqJ⟩, rfl⟩)
          · refine ⟨Or.inr (Or.inl ⟨q, hqN, rfl⟩), ?_⟩
            rintro (h0 | ⟨q', hq', heq⟩ | ⟨q', _, heq⟩)
            · exact List.cons_ne_nil _ _ h0
            · injection heq with _ hqq'; rw [hqq'] at hq'; exact hqJ hq'
            · injection heq with hft; exact Bool.false_ne_true hft.symm
          · refine ⟨Or.inr (Or.inr ⟨q, hqN, rfl⟩), ?_⟩
            rintro (h0 | ⟨q', _, heq⟩ | ⟨q', hq', heq⟩)
            · exact List.cons_ne_nil _ _ h0
            · injection heq with hft; exact Bool.false_ne_true hft
            · injection heq with _ hqq'; rw [hqq'] at hq'; exact hqJ hq'
      have hdisj : Disjoint ((N₀ \ J₀).image (false :: ·)) ((N₁ \ J₁).image (true :: ·)) := by
        rw [Finset.disjoint_left]
        intro p hp0 hp1
        rcases Finset.mem_image.mp hp0 with ⟨_, _, rfl⟩
        rcases Finset.mem_image.mp hp1 with ⟨_, _, heq⟩
        injection heq with hft
        exact Bool.false_ne_true hft.symm
      have hcard : (N \ J).card = t := by
        rw [hleaves_eq, Finset.card_union_of_disjoint hdisj,
          Finset.card_image_of_injective _ (fun a b h => by injection h),
          Finset.card_image_of_injective _ (fun a b h => by injection h),
          h0_card, h1_card]
        omega
      have hlen : ∀ p ∈ N, p.length ≤ m + 1 := by
        intro p hp
        simp only [N, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
        rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
        · simp
        · simp only [List.length_cons]; exact Nat.succ_le_succ (h0_len q hq)
        · simp only [List.length_cons]; exact Nat.succ_le_succ (h1_len q hq)
      have hzero : ((N \ J).filter (fun p => ∀ b ∈ p, b = false)).card = 1 := by
        have hfeq : (N \ J).filter (fun p => ∀ b ∈ p, b = false) =
            ((N₀ \ J₀).filter (fun p => ∀ b ∈ p, b = false)).image (false :: ·) := by
          ext p
          rw [hleaves_eq]
          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image]
          constructor
          · rintro ⟨⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩, hall⟩
            · exact ⟨q, ⟨hq, fun b hb => hall b (List.mem_cons_of_mem _ hb)⟩, rfl⟩
            · exact absurd (hall true (List.mem_cons_self)) (by decide)
          · rintro ⟨q, ⟨hq, hall⟩, rfl⟩
            refine ⟨Or.inl ⟨q, hq, rfl⟩, fun b hb => ?_⟩
            rcases List.mem_cons.mp hb with rfl | hb'
            · rfl
            · exact hall b hb'
        rw [hfeq, Finset.card_image_of_injective _ (fun a b h => by injection h), h0_zero]
      exact ⟨hnil, hsub, hpar, hch, hcard, hlen, hzero⟩

private lemma tree_unique_leaf {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (N J : Finset (List Bool))
    (h_nil : [] ∈ N) (h_sub : J ⊆ N)
    (h_par : ∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J)
    (h_ch : ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N)
    (q : List Bool → X →ₗ[ZMod 2] ZMod 2) (offset : List Bool → ZMod 2) (x : X) :
    ∃! p, p ∈ N \ J ∧
      ∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step := by
  let maxLen := N.sup List.length
  have hex : ∀ d : ℕ, ∀ h ∈ N, maxLen - h.length ≤ d →
      (∀ step : Fin h.length, decide (q (h.take step.val) x = offset (h.take step.val)) = h.get step) →
      ∃ p ∈ N \ J,
        ∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step := by
    intro d
    induction d with
    | zero =>
      intro h hh hd hok
      have hnotJ : h ∉ J := by
        intro hJ
        have hch0 := (h_ch h hJ).1
        have hle : (h ++ [false]).length ≤ maxLen := Finset.le_sup (f := List.length) hch0
        simp only [List.length_append, List.length_singleton] at hle
        omega
      exact ⟨h, Finset.mem_sdiff.mpr ⟨hh, hnotJ⟩, hok⟩
    | succ d ih =>
      intro h hh hd hok
      by_cases hJ : h ∈ J
      · let b : Bool := decide (q h x = offset h)
        have hhb : h ++ [b] ∈ N := by
          cases hb : b
          · exact (h_ch h hJ).1
          · exact (h_ch h hJ).2
        have hle_b : (h ++ [b]).length ≤ maxLen := Finset.le_sup (f := List.length) hhb
        have hd' : maxLen - (h ++ [b]).length ≤ d := by
          simp only [List.length_append, List.length_singleton] at hle_b ⊢
          omega
        refine ih (h ++ [b]) hhb hd' (fun step => ?_)
        by_cases hs : step.val < h.length
        · have htake : (h ++ [b]).take step.val = h.take step.val :=
            List.take_append_of_le_length (Nat.le_of_lt hs)
          have hget : (h ++ [b]).get step = h.get ⟨step.val, hs⟩ := by
            simp [List.getElem_append_left hs]
          rw [htake, hget]
          exact hok ⟨step.val, hs⟩
        · have hs_eq : step.val = h.length := by
            have hlt := step.isLt
            simp only [List.length_append, List.length_singleton] at hlt
            omega
          have htake : (h ++ [b]).take step.val = h := by
            rw [hs_eq, List.take_left]
          have hget : (h ++ [b]).get step = b := by
            have : (h ++ [b])[step.val] = b := by
              simp [hs_eq]
            exact this
          rw [htake, hget]
      · exact ⟨h, Finset.mem_sdiff.mpr ⟨hh, hJ⟩, hok⟩
  obtain ⟨p, hp_mem, hp_ok⟩ := hex maxLen [] h_nil (by simp) (fun step => Fin.elim0 step)
  refine ⟨p, ⟨hp_mem, hp_ok⟩, fun p' ⟨hp'_mem, hp'_ok⟩ => ?_⟩
  by_contra hne
  have hnot_pref : ∀ (a b : List Bool), a ∈ N \ J → b ∈ N → (hlt : a.length < b.length) →
      (∀ i : Fin a.length, a.get i = b.get ⟨i.val, lt_trans i.isLt hlt⟩) → False := by
    intro a b ha hb hlt heq
    have hb_pref : ∀ k : ℕ, k ≤ b.length → b.take k ∈ N := by
      intro k hk
      have hdesc : ∀ d : ℕ, d ≤ b.length → b.take (b.length - d) ∈ N := by
        intro d
        induction d with
        | zero => intro _; simpa using hb
        | succ d ih =>
          intro hd
          have hprev := ih (by omega)
          have hsplit : b.take (b.length - d) =
              b.take (b.length - (d + 1)) ++ [b.get ⟨b.length - (d + 1), by omega⟩] := by
            have he : b.length - d = (b.length - (d + 1)) + 1 := by omega
            rw [he, List.take_succ_eq_append_getElem (by omega)]
            rfl
          rw [hsplit] at hprev
          exact h_sub (h_par _ _ hprev)
      have h1 := hdesc (b.length - k) (by omega)
      have he : b.length - (b.length - k) = k := by omega
      rw [he] at h1
      exact h1
    have ha_eq : b.take a.length = a := by
      apply List.ext_getElem
      · simp [Nat.le_of_lt hlt]
      · intro i h1 h2
        have hi : i < a.length := h2
        rw [List.getElem_take]
        exact (heq ⟨i, hi⟩).symm
    have ha_succ : b.take (a.length + 1) ∈ N := hb_pref (a.length + 1) (by omega)
    have hsplit : b.take (a.length + 1) = a ++ [b.get ⟨a.length, hlt⟩] := by
      rw [List.take_succ_eq_append_getElem hlt, ha_eq]
      rfl
    rw [hsplit] at ha_succ
    exact (Finset.mem_sdiff.mp ha).2 (h_par a _ ha_succ)
  have hagree : ∀ (k : ℕ) (hk : k < min p.length p'.length),
      p.get ⟨k, lt_of_lt_of_le hk (Nat.min_le_left _ _)⟩ =
      p'.get ⟨k, lt_of_lt_of_le hk (Nat.min_le_right _ _)⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk
      have hkp : k < p.length := lt_of_lt_of_le hk (Nat.min_le_left _ _)
      have hkp' : k < p'.length := lt_of_lt_of_le hk (Nat.min_le_right _ _)
      have htake_eq : p.take k = p'.take k := by
        apply List.ext_getElem
        · simp [Nat.le_of_lt hkp, Nat.le_of_lt hkp']
        · intro i h1 h2
          simp only [List.length_take] at h1
          have hik : i < k := by omega
          rw [List.getElem_take, List.getElem_take]
          exact ih i hik (lt_trans hik hk)
      rw [← hp_ok ⟨k, hkp⟩, ← hp'_ok ⟨k, hkp'⟩, htake_eq]
  rcases lt_trichotomy p.length p'.length with hlt | heq | hgt
  · exact hnot_pref p p' hp_mem (Finset.mem_sdiff.mp hp'_mem).1 hlt
      (fun i => hagree i.val (by omega))
  · apply hne
    symm
    apply List.ext_getElem heq
    intro i h1 h2
    exact hagree i (by omega)
  · exact hnot_pref p' p hp'_mem (Finset.mem_sdiff.mp hp_mem).1 hgt
      (fun i => (hagree i.val (by omega)).symm)


open Classical in
private lemma tree_to_aff_aux (n : ℕ) (f : (Fin n → ZMod 2) → ZMod 2) (L H : ℕ) :
    (∃ (N J : Finset (List Bool))
      (q : List Bool → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (offset out : List Bool → ZMod 2),
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      (N \ J).card ≤ L ∧ H ≤ Nat.card {x : Fin n → ZMod 2 // ∃ p ∈ N \ J,
        (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step)
        ∧ f x = out p}) →
    (∃ k : ℕ, k ≤ L ∧
      ∃ (a : Fin k → Fin n → ZMod 2) (S : Fin k → Submodule (ZMod 2) (Fin n → ZMod 2))
        (out : Fin k → ZMod 2),
        (∀ x : Fin n → ZMod 2, ∃! j : Fin k, x - a j ∈ S j) ∧
        H ≤ Nat.card {x : Fin n → ZMod 2 // ∃ j, x - a j ∈ S j ∧ f x = out j}) := by
  classical
  rintro ⟨N, J, q, offset, out, h_nil, h_sub, h_par, h_ch, hcardL, hH⟩
  let cellP : List Bool → Set (Fin n → ZMod 2) := fun p =>
    {x | ∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step}
  let liveLeaves : Finset (List Bool) := (N \ J).filter (fun p => (cellP p).Nonempty)
  have hlive_le : liveLeaves.card ≤ L := le_trans (Finset.card_filter_le _ _) hcardL
  have hcard_live : Fintype.card ↥liveLeaves = liveLeaves.card := Fintype.card_coe liveLeaves
  let eFin : Fin liveLeaves.card ≃ ↥liveLeaves :=
    (Fintype.equivOfCardEq (by rw [Fintype.card_fin, hcard_live]))
  let a : Fin liveLeaves.card → Fin n → ZMod 2 := fun j =>
    Classical.choose (Finset.mem_filter.mp (eFin j).2).2
  have ha_mem : ∀ j : Fin liveLeaves.card, a j ∈ cellP (eFin j).1 := fun j =>
    Classical.choose_spec (Finset.mem_filter.mp (eFin j).2).2
  let S : Fin liveLeaves.card → Submodule (ZMod 2) (Fin n → ZMod 2) := fun j =>
    ⨅ step : Fin (eFin j).1.length, LinearMap.ker (q ((eFin j).1.take step.val))
  have hcell_iff : ∀ (j : Fin liveLeaves.card) (x : Fin n → ZMod 2),
      x - a j ∈ S j ↔ x ∈ cellP (eFin j).1 := by
    intro j x
    simp only [S, Submodule.mem_iInf, LinearMap.mem_ker, map_sub, sub_eq_zero, cellP,
      Set.mem_setOf_eq]
    refine forall_congr' (fun step => ?_)
    have haj := ha_mem j step
    rw [← haj]
    exact (zmod2_decide_eq_iff _ _ _).symm
  refine ⟨liveLeaves.card, hlive_le, a, S, fun j => out (eFin j).1, ?_, ?_⟩
  · intro x
    obtain ⟨p, ⟨hp_mem, hp_ok⟩, hp_uniq⟩ := tree_unique_leaf N J h_nil h_sub h_par h_ch q offset x
    have hp_live : p ∈ liveLeaves := Finset.mem_filter.mpr ⟨hp_mem, ⟨x, hp_ok⟩⟩
    let j₀ : Fin liveLeaves.card := eFin.symm ⟨p, hp_live⟩
    refine ⟨j₀, ?_, fun j hj => ?_⟩
    · dsimp only
      rw [hcell_iff j₀ x]
      have hej : (eFin j₀).1 = p := congrArg Subtype.val (eFin.apply_symm_apply ⟨p, hp_live⟩)
      rw [hej]; exact hp_ok
    · dsimp only at hj
      rw [hcell_iff j x] at hj
      have hpeq : (eFin j).1 = p := hp_uniq (eFin j).1 ⟨(Finset.mem_filter.mp (eFin j).2).1, hj⟩
      have hsub : eFin j = ⟨p, hp_live⟩ := Subtype.ext hpeq
      exact eFin.injective (hsub.trans (eFin.apply_symm_apply ⟨p, hp_live⟩).symm)
  · refine le_trans hH ?_
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]
    refine Finset.card_le_card (fun x hx => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with ⟨p, hp_mem, hp_ok, hfx⟩
    have hp_live : p ∈ liveLeaves := Finset.mem_filter.mpr ⟨hp_mem, ⟨x, hp_ok⟩⟩
    let j₀ : Fin liveLeaves.card := eFin.symm ⟨p, hp_live⟩
    have hej : (eFin j₀).1 = p := congrArg Subtype.val (eFin.apply_symm_apply ⟨p, hp_live⟩)
    refine ⟨j₀, ?_, by rw [hej]; exact hfx⟩
    rw [hcell_iff j₀ x, hej]
    exact hp_ok

open Classical in
private lemma aff_to_bound_aux (n m : ℕ) (f : (Fin n → ZMod 2) → ZMod 2) (L H : ℕ)
    (Rad : Submodule (ZMod 2) (Fin n → ZMod 2)) (c₁ : ZMod 2)
    (lamR : ↥Rad →ₗ[ZMod 2] ZMod 2)
    (hcardX : Nat.card (Fin n → ZMod 2) = 2 ^ n)
    (hcardX_split : 2 ^ m * 2 ^ (n - m) = 2 ^ n)
    (htotal_eq : (∑ x : Fin n → ZMod 2, chi (f x)) =
      if (∀ r : ↥Rad, lamR r = 0) then chi c₁ * (2 ^ (n - m) : ℤ) else 0)
    (hbal_iff : (Nat.card {x : Fin n → ZMod 2 // f x = 0} =
      Nat.card {x : Fin n → ZMod 2 // f x = 1}) ↔ ¬ (∀ r : ↥Rad, lamR r = 0))
    (h450 : ∀ (a : Fin n → ZMod 2) (S : Submodule (ZMod 2) (Fin n → ZMod 2)),
      let va : ℤ := ∑ x ∈ Finset.univ.filter (fun x => x - a ∈ S), chi (f x)
      (|va| ≤ (2 ^ (n - m) : ℤ)) ∧
      ((2 ^ (n - m) : ℤ) < 2 * |va| →
        |va| = (2 ^ (n - m) : ℤ) ∧
        va = (∑ x : Fin n → ZMod 2, chi (f x)) ∧
        ∀ (b : Fin n → ZMod 2) (T : Submodule (ZMod 2) (Fin n → ZMod 2)),
          let vb : ℤ := ∑ x ∈ Finset.univ.filter (fun x => x - b ∈ T), chi (f x)
          (2 ^ (n - m) : ℤ) < 2 * |vb| → ∃ x : Fin n → ZMod 2, x - a ∈ S ∧ x - b ∈ T)) :
    (∃ k : ℕ, k ≤ L ∧
      ∃ (a : Fin k → Fin n → ZMod 2) (S : Fin k → Submodule (ZMod 2) (Fin n → ZMod 2))
        (out : Fin k → ZMod 2),
        (∀ x : Fin n → ZMod 2, ∃! j : Fin k, x - a j ∈ S j) ∧
        H ≤ Nat.card {x : Fin n → ZMod 2 // ∃ j, x - a j ∈ S j ∧ f x = out j}) →
    2 * 2 ^ m * H ≤
      Nat.card (Fin n → ZMod 2) *
        (2 ^ m + min (2 ^ m)
          (if Nat.card {x : Fin n → ZMod 2 // f x = 0} = Nat.card {x : Fin n → ZMod 2 // f x = 1}
            then L / 2 else (L + 1) / 2)) := by
  classical
  rintro ⟨k, hkL, a, S, out, hpart, hH⟩
  let cell : Fin k → Finset (Fin n → ZMod 2) := fun j =>
    Finset.univ.filter (fun x => x - a j ∈ S j)
  let val : Fin k → ℤ := fun j => ∑ x ∈ cell j, chi (f x)
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin k)) cell := by
    intro j₁ _ j₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 := (Finset.mem_filter.mp hx1).2
    have h2 := (Finset.mem_filter.mp hx2).2
    obtain ⟨j₀, _, huniq⟩ := hpart x
    exact hne ((huniq j₁ h1).trans (huniq j₂ h2).symm)
  have hunion : Finset.univ.biUnion cell = Finset.univ := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, cell, Finset.mem_filter, iff_true]
    obtain ⟨j, hj, _⟩ := hpart x
    exact ⟨j, hj⟩
  have hsum_val : ∑ j : Fin k, val j = ∑ x : Fin n → ZMod 2, chi (f x) := by
    dsimp only [val]
    rw [← Finset.sum_biUnion hdisj, hunion]
  have hsum_card : ∑ j : Fin k, (cell j).card = 2 ^ n := by
    rw [← Finset.card_biUnion hdisj, hunion, Finset.card_univ]
    simp [ZMod.card 2]
  have h2H : (2 * H : ℤ) ≤ (2 ^ n : ℤ) + ∑ j : Fin k, |val j| := by
    have hH_le : (H : ℤ) ≤ ∑ j : Fin k, (((cell j).filter (fun x => f x = out j)).card : ℤ) := by
      have h1 : H ≤ ((Finset.univ : Finset (Fin k)).biUnion
          (fun j => (cell j).filter (fun x => f x = out j))).card := by
        refine le_trans hH ?_
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        refine Finset.card_le_card (fun x hx => ?_)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, cell] at hx ⊢
        rcases hx with ⟨j, hj, hfx⟩
        exact ⟨j, hj, hfx⟩
      have h2 : ((Finset.univ : Finset (Fin k)).biUnion
          (fun j => (cell j).filter (fun x => f x = out j))).card ≤
          ∑ j : Fin k, ((cell j).filter (fun x => f x = out j)).card := Finset.card_biUnion_le
      have h12 : (H : ℤ) ≤ ((∑ j : Fin k, ((cell j).filter (fun x => f x = out j)).card : ℕ) : ℤ) := by
        exact_mod_cast le_trans h1 h2
      simpa [Nat.cast_sum] using h12
    have hcell_hit : ∀ j : Fin k,
        2 * (((cell j).filter (fun x => f x = out j)).card : ℤ) ≤ ((cell j).card : ℤ) + |val j| := by
      intro j
      have hchi_hit : ∀ x ∈ cell j,
          (if f x = out j then (2 : ℤ) else 0) = 1 + chi (out j) * chi (f x) := by
        intro x _
        have h1 : ∀ a b : ZMod 2, (if a = b then (2 : ℤ) else 0) = 1 + chi b * chi a := by
          intro a b; rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide
        exact h1 (f x) (out j)
      have hsum_j : 2 * (((cell j).filter (fun x => f x = out j)).card : ℤ) =
          ((cell j).card : ℤ) + chi (out j) * val j := by
        have h1 : 2 * (((cell j).filter (fun x => f x = out j)).card : ℤ) =
            ∑ x ∈ cell j, (if f x = out j then (2 : ℤ) else 0) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
          ring
        rw [h1, Finset.sum_congr rfl hchi_hit, Finset.sum_add_distrib, Finset.sum_const,
          nsmul_eq_mul, mul_one, ← Finset.mul_sum]
      rw [hsum_j]
      have hle : chi (out j) * val j ≤ |val j| := by
        calc chi (out j) * val j ≤ |chi (out j) * val j| := le_abs_self _
          _ = |val j| := by rw [abs_mul, chi_abs, one_mul]
      linarith
    calc (2 * H : ℤ) ≤ 2 * ∑ j : Fin k, (((cell j).filter (fun x => f x = out j)).card : ℤ) := by
            push_cast; exact mul_le_mul_of_nonneg_left hH_le (by omega)
      _ = ∑ j : Fin k, 2 * (((cell j).filter (fun x => f x = out j)).card : ℤ) := Finset.mul_sum _ _ _
      _ ≤ ∑ j : Fin k, (((cell j).card : ℤ) + |val j|) := Finset.sum_le_sum (fun j _ => hcell_hit j)
      _ = (2 ^ n : ℤ) + ∑ j : Fin k, |val j| := by
          rw [Finset.sum_add_distrib]
          congr 1
          exact_mod_cast hsum_card
  have hsum_abs_le_K : ∑ j : Fin k, |val j| ≤ (2 ^ m : ℤ) * (2 ^ (n - m) : ℤ) := by
    have h1 : ∑ j : Fin k, |val j| ≤ ∑ j : Fin k, ((cell j).card : ℤ) := by
      refine Finset.sum_le_sum (fun j _ => ?_)
      calc |val j| ≤ ∑ x ∈ cell j, |chi (f x)| := Finset.abs_sum_le_sum_abs _ _
        _ = ((cell j).card : ℤ) := by simp [chi_abs]
    have h2 : ∑ j : Fin k, ((cell j).card : ℤ) = (2 ^ n : ℤ) := by exact_mod_cast hsum_card
    have h3 : (2 ^ n : ℤ) = (2 ^ m : ℤ) * (2 ^ (n - m) : ℤ) := by exact_mod_cast hcardX_split.symm
    linarith
  have hsum_abs_le_L : ∑ j : Fin k, |val j| ≤
      ((if Nat.card {x : Fin n → ZMod 2 // f x = 0} = Nat.card {x : Fin n → ZMod 2 // f x = 1}
        then L / 2 else (L + 1) / 2 : ℕ) : ℤ) * (2 ^ (n - m) : ℤ) := by
    let P : Finset (Fin k) := Finset.univ.filter (fun j => 0 < val j)
    let N : Finset (Fin k) := Finset.univ.filter (fun j => val j < 0)
    have hPN_disj : Disjoint P N := by
      rw [Finset.disjoint_left]
      intro j hP hN
      have h1 := (Finset.mem_filter.mp hP).2
      have h2 := (Finset.mem_filter.mp hN).2
      linarith
    have hPN_card : P.card + N.card ≤ L := by
      calc P.card + N.card = (P ∪ N).card := (Finset.card_union_of_disjoint hPN_disj).symm
        _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_univ _
        _ = k := by simp
        _ ≤ L := hkL
    have hsum_PN_signed : ∑ j : Fin k, val j = (∑ j ∈ P, val j) - ∑ j ∈ N, (-val j) := by
      have h1 : ∑ j : Fin k, val j = ∑ j ∈ P ∪ N, val j := by
        symm
        refine Finset.sum_subset (Finset.subset_univ _) (fun j _ hnot => ?_)
        simp only [P, N, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hnot
        push Not at hnot
        linarith
      rw [h1, Finset.sum_union hPN_disj, Finset.sum_neg_distrib]
      ring
    have hsum_PN_abs : ∑ j : Fin k, |val j| = (∑ j ∈ P, val j) + ∑ j ∈ N, (-val j) := by
      have h1 : ∑ j : Fin k, |val j| = ∑ j ∈ P ∪ N, |val j| := by
        symm
        refine Finset.sum_subset (Finset.subset_univ _) (fun j _ hnot => ?_)
        simp only [P, N, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hnot
        push Not at hnot
        have h0 : val j = 0 := by linarith
        simp [h0]
      rw [h1, Finset.sum_union hPN_disj]
      congr 1
      · refine Finset.sum_congr rfl (fun j hj => abs_of_pos (Finset.mem_filter.mp hj).2)
      · refine Finset.sum_congr rfl (fun j hj => abs_of_neg (Finset.mem_filter.mp hj).2)
    have hlarge_uniq : ∀ j₁ j₂ : Fin k,
        (2 ^ (n - m) : ℤ) < 2 * |val j₁| → (2 ^ (n - m) : ℤ) < 2 * |val j₂| → j₁ = j₂ := by
      intro j₁ j₂ h1 h2
      obtain ⟨x, hx1, hx2⟩ := ((h450 (a j₁) (S j₁)).2 h1).2.2 (a j₂) (S j₂) h2
      obtain ⟨j₀, _, huniq⟩ := hpart x
      exact (huniq j₁ hx1).trans (huniq j₂ hx2).symm
    by_cases hbal : Nat.card {x : Fin n → ZMod 2 // f x = 0} =
        Nat.card {x : Fin n → ZMod 2 // f x = 1}
    · rw [if_pos hbal]
      have htot0 : ∑ x : Fin n → ZMod 2, chi (f x) = 0 := by
        rw [htotal_eq, if_neg (hbal_iff.mp hbal)]
      have hall_small : ∀ j : Fin k, 2 * |val j| ≤ (2 ^ (n - m) : ℤ) := by
        intro j
        by_contra hbig
        have h1 := ((h450 (a j) (S j)).2 (lt_of_not_ge hbig))
        rw [h1.2.1, htot0, abs_zero] at h1
        have hpos : (0 : ℤ) < 2 ^ (n - m) := by positivity
        linarith [h1.1]
      have heq_PN : ∑ j ∈ P, val j = ∑ j ∈ N, (-val j) := by linarith
      have h2P : 2 * ∑ j ∈ P, val j ≤ (P.card : ℤ) * (2 ^ (n - m) : ℤ) := by
        rw [Finset.mul_sum]
        calc ∑ j ∈ P, 2 * val j ≤ ∑ _j ∈ P, (2 ^ (n - m) : ℤ) := by
              refine Finset.sum_le_sum (fun j hj => ?_)
              have hpos := (Finset.mem_filter.mp hj).2
              have hs := hall_small j
              rw [abs_of_pos hpos] at hs; exact hs
          _ = (P.card : ℤ) * (2 ^ (n - m) : ℤ) := by simp
      have h2N : 2 * ∑ j ∈ N, (-val j) ≤ (N.card : ℤ) * (2 ^ (n - m) : ℤ) := by
        rw [Finset.mul_sum]
        calc ∑ j ∈ N, 2 * (-val j) ≤ ∑ _j ∈ N, (2 ^ (n - m) : ℤ) := by
              refine Finset.sum_le_sum (fun j hj => ?_)
              have hneg := (Finset.mem_filter.mp hj).2
              have hs := hall_small j
              rw [abs_of_neg hneg] at hs; exact hs
          _ = (N.card : ℤ) * (2 ^ (n - m) : ℤ) := by simp
      have hmin : P.card ≤ L / 2 ∨ N.card ≤ L / 2 := by omega
      have hCpos : (0 : ℤ) ≤ 2 ^ (n - m) := by positivity
      rcases hmin with hP | hN
      · have h1 : (P.card : ℤ) ≤ (L / 2 : ℕ) := by exact_mod_cast hP
        have hmul : (P.card : ℤ) * (2 ^ (n - m) : ℤ) ≤ ((L / 2 : ℕ) : ℤ) * (2 ^ (n - m) : ℤ) :=
          mul_le_mul_of_nonneg_right h1 hCpos
        linarith only [hsum_PN_abs, heq_PN, h2P, hmul]
      · have h1 : (N.card : ℤ) ≤ (L / 2 : ℕ) := by exact_mod_cast hN
        have hmul : (N.card : ℤ) * (2 ^ (n - m) : ℤ) ≤ ((L / 2 : ℕ) : ℤ) * (2 ^ (n - m) : ℤ) :=
          mul_le_mul_of_nonneg_right h1 hCpos
        linarith only [hsum_PN_abs, heq_PN, h2N, hmul]
    · rw [if_neg hbal]
      have hlam : ∀ r : ↥Rad, lamR r = 0 := by
        by_contra hnot; exact hbal (hbal_iff.mpr hnot)
      have htot : ∑ x : Fin n → ZMod 2, chi (f x) = chi c₁ * (2 ^ (n - m) : ℤ) := by
        rw [htotal_eq, if_pos hlam]
      have hCpos : (0 : ℤ) < 2 ^ (n - m) := by positivity
      rcases zmod2_cases c₁ with hc0 | hc1
      · rw [hc0, chi_zero, one_mul] at htot
        have hN_small : ∀ j ∈ N, 2 * (-val j) ≤ (2 ^ (n - m) : ℤ) := by
          intro j hj
          have hneg := (Finset.mem_filter.mp hj).2
          by_contra hbig
          have h1 := (h450 (a j) (S j)).2 (by rw [abs_of_neg hneg]; linarith)
          linarith only [h1.2.1, htot, hneg, hCpos]
        have h2N : 2 * ∑ j ∈ N, (-val j) ≤ (N.card : ℤ) * (2 ^ (n - m) : ℤ) := by
          rw [Finset.mul_sum]
          calc ∑ j ∈ N, 2 * (-val j) ≤ ∑ _j ∈ N, (2 ^ (n - m) : ℤ) := Finset.sum_le_sum hN_small
            _ = (N.card : ℤ) * (2 ^ (n - m) : ℤ) := by simp
        have h2P : 2 * ∑ j ∈ P, val j ≤ ((P.card : ℤ) + 1) * (2 ^ (n - m) : ℤ) := by
          by_cases hex : ∃ j₀ ∈ P, (2 ^ (n - m) : ℤ) < 2 * val j₀
          · rcases hex with ⟨j₀, hj₀, hbig0⟩
            rw [← Finset.add_sum_erase _ _ hj₀]
            have hv0 : val j₀ ≤ (2 ^ (n - m) : ℤ) :=
              le_trans (le_abs_self _) (h450 (a j₀) (S j₀)).1
            have hrest : 2 * ∑ j ∈ P.erase j₀, val j ≤
                ((P.erase j₀).card : ℤ) * (2 ^ (n - m) : ℤ) := by
              rw [Finset.mul_sum]
              calc ∑ j ∈ P.erase j₀, 2 * val j ≤ ∑ _j ∈ P.erase j₀, (2 ^ (n - m) : ℤ) := by
                    refine Finset.sum_le_sum (fun j hj => ?_)
                    have hne : j ≠ j₀ := (Finset.mem_erase.mp hj).1
                    have hpos := (Finset.mem_filter.mp (Finset.mem_erase.mp hj).2).2
                    by_contra hbig
                    have heq := hlarge_uniq j j₀ (by rw [abs_of_pos hpos]; linarith)
                      (by rw [abs_of_pos (Finset.mem_filter.mp hj₀).2]; linarith)
                    exact hne heq
                _ = ((P.erase j₀).card : ℤ) * (2 ^ (n - m) : ℤ) := by simp
            have hcard_er : ((P.erase j₀).card : ℤ) + 1 = (P.card : ℤ) := by
              exact_mod_cast Finset.card_erase_add_one hj₀
            have hrw : ((P.erase j₀).card : ℤ) * (2 ^ (n - m) : ℤ) + 2 * (2 ^ (n - m) : ℤ) =
                ((P.card : ℤ) + 1) * (2 ^ (n - m) : ℤ) := by rw [← hcard_er]; ring
            linarith only [hv0, hrest, hrw]
          · push Not at hex
            rw [Finset.mul_sum]
            have h1 : ∑ j ∈ P, 2 * val j ≤ (P.card : ℤ) * (2 ^ (n - m) : ℤ) := by
              calc ∑ j ∈ P, 2 * val j ≤ ∑ _j ∈ P, (2 ^ (n - m) : ℤ) := Finset.sum_le_sum hex
                _ = (P.card : ℤ) * (2 ^ (n - m) : ℤ) := by simp
            have hrw : ((P.card : ℤ) + 1) * (2 ^ (n - m) : ℤ) =
                (P.card : ℤ) * (2 ^ (n - m) : ℤ) + (2 ^ (n - m) : ℤ) := by ring
            linarith only [h1, hCpos, hrw]
        have hmin : P.card ≤ (L + 1) / 2 ∨ N.card + 1 ≤ (L + 1) / 2 := by omega
        rcases hmin with hP | hN
        · have h1 : (P.card : ℤ) ≤ ((L + 1) / 2 : ℕ) := by exact_mod_cast hP
          have hmul : (P.card : ℤ) * (2 ^ (n - m) : ℤ) ≤
              (((L + 1) / 2 : ℕ) : ℤ) * (2 ^ (n - m) : ℤ) :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hCpos)
          have hrw : ((P.card : ℤ) + 1) * (2 ^ (n - m) : ℤ) =
              (P.card : ℤ) * (2 ^ (n - m) : ℤ) + (2 ^ (n - m) : ℤ) := by ring
          linarith only [hsum_PN_abs, hsum_PN_signed, hsum_val, htot, h2P, hmul, hrw]
        · have h1 : (N.card : ℤ) + 1 ≤ ((L + 1) / 2 : ℕ) := by exact_mod_cast hN
          have hmul : ((N.card : ℤ) + 1) * (2 ^ (n - m) : ℤ) ≤
              (((L + 1) / 2 : ℕ) : ℤ) * (2 ^ (n - m) : ℤ) :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hCpos)
          have hrw : ((N.card : ℤ) + 1) * (2 ^ (n - m) : ℤ) =
              (N.card : ℤ) * (2 ^ (n - m) : ℤ) + (2 ^ (n - m) : ℤ) := by ring
          linarith only [hsum_PN_abs, hsum_PN_signed, hsum_val, htot, h2N, hmul, hrw]
      · rw [hc1, chi_one, neg_one_mul] at htot
        have hP_small : ∀ j ∈ P, 2 * val j ≤ (2 ^ (n - m) : ℤ) := by
          intro j hj
          have hpos := (Finset.mem_filter.mp hj).2
          by_contra hbig
          have h1 := (h450 (a j) (S j)).2 (by rw [abs_of_pos hpos]; linarith)
          linarith only [h1.2.1, htot, hpos, hCpos]
        have h2P : 2 * ∑ j ∈ P, val j ≤ (P.card : ℤ) * (2 ^ (n - m) : ℤ) := by
          rw [Finset.mul_sum]
          calc ∑ j ∈ P, 2 * val j ≤ ∑ _j ∈ P, (2 ^ (n - m) : ℤ) := Finset.sum_le_sum hP_small
            _ = (P.card : ℤ) * (2 ^ (n - m) : ℤ) := by simp
        have h2N : 2 * ∑ j ∈ N, (-val j) ≤ ((N.card : ℤ) + 1) * (2 ^ (n - m) : ℤ) := by
          by_cases hex : ∃ j₀ ∈ N, (2 ^ (n - m) : ℤ) < 2 * (-val j₀)
          · rcases hex with ⟨j₀, hj₀, hbig0⟩
            rw [← Finset.add_sum_erase _ _ hj₀]
            have hv0 : -val j₀ ≤ (2 ^ (n - m) : ℤ) :=
              le_trans (neg_le_abs _) (h450 (a j₀) (S j₀)).1
            have hrest : 2 * ∑ j ∈ N.erase j₀, (-val j) ≤
                ((N.erase j₀).card : ℤ) * (2 ^ (n - m) : ℤ) := by
              rw [Finset.mul_sum]
              calc ∑ j ∈ N.erase j₀, 2 * (-val j) ≤ ∑ _j ∈ N.erase j₀, (2 ^ (n - m) : ℤ) := by
                    refine Finset.sum_le_sum (fun j hj => ?_)
                    have hne : j ≠ j₀ := (Finset.mem_erase.mp hj).1
                    have hneg := (Finset.mem_filter.mp (Finset.mem_erase.mp hj).2).2
                    by_contra hbig
                    have heq := hlarge_uniq j j₀ (by rw [abs_of_neg hneg]; linarith)
                      (by rw [abs_of_neg (Finset.mem_filter.mp hj₀).2]; linarith)
                    exact hne heq
                _ = ((N.erase j₀).card : ℤ) * (2 ^ (n - m) : ℤ) := by simp
            have hcard_er : ((N.erase j₀).card : ℤ) + 1 = (N.card : ℤ) := by
              exact_mod_cast Finset.card_erase_add_one hj₀
            have hrw : ((N.erase j₀).card : ℤ) * (2 ^ (n - m) : ℤ) + 2 * (2 ^ (n - m) : ℤ) =
                ((N.card : ℤ) + 1) * (2 ^ (n - m) : ℤ) := by rw [← hcard_er]; ring
            linarith only [hv0, hrest, hrw]
          · push Not at hex
            rw [Finset.mul_sum]
            have h1 : ∑ j ∈ N, 2 * (-val j) ≤ (N.card : ℤ) * (2 ^ (n - m) : ℤ) := by
              calc ∑ j ∈ N, 2 * (-val j) ≤ ∑ _j ∈ N, (2 ^ (n - m) : ℤ) := Finset.sum_le_sum hex
                _ = (N.card : ℤ) * (2 ^ (n - m) : ℤ) := by simp
            have hrw : ((N.card : ℤ) + 1) * (2 ^ (n - m) : ℤ) =
                (N.card : ℤ) * (2 ^ (n - m) : ℤ) + (2 ^ (n - m) : ℤ) := by ring
            linarith only [h1, hCpos, hrw]
        have hmin : N.card ≤ (L + 1) / 2 ∨ P.card + 1 ≤ (L + 1) / 2 := by omega
        rcases hmin with hN | hP
        · have h1 : (N.card : ℤ) ≤ ((L + 1) / 2 : ℕ) := by exact_mod_cast hN
          have hmul : (N.card : ℤ) * (2 ^ (n - m) : ℤ) ≤
              (((L + 1) / 2 : ℕ) : ℤ) * (2 ^ (n - m) : ℤ) :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hCpos)
          have hrw : ((N.card : ℤ) + 1) * (2 ^ (n - m) : ℤ) =
              (N.card : ℤ) * (2 ^ (n - m) : ℤ) + (2 ^ (n - m) : ℤ) := by ring
          linarith only [hsum_PN_abs, hsum_PN_signed, hsum_val, htot, h2N, hmul, hrw]
        · have h1 : (P.card : ℤ) + 1 ≤ ((L + 1) / 2 : ℕ) := by exact_mod_cast hP
          have hmul : ((P.card : ℤ) + 1) * (2 ^ (n - m) : ℤ) ≤
              (((L + 1) / 2 : ℕ) : ℤ) * (2 ^ (n - m) : ℤ) :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hCpos)
          have hrw : ((P.card : ℤ) + 1) * (2 ^ (n - m) : ℤ) =
              (P.card : ℤ) * (2 ^ (n - m) : ℤ) + (2 ^ (n - m) : ℤ) := by ring
          linarith only [hsum_PN_abs, hsum_PN_signed, hsum_val, htot, h2P, hmul, hrw]
  set t := min (2 ^ m)
    (if Nat.card {x : Fin n → ZMod 2 // f x = 0} = Nat.card {x : Fin n → ZMod 2 // f x = 1}
      then L / 2 else (L + 1) / 2)
  have hsum_le_t : ∑ j : Fin k, |val j| ≤ (t : ℤ) * (2 ^ (n - m) : ℤ) := by
    dsimp only [t]
    rcases min_cases (2 ^ m)
      (if Nat.card {x : Fin n → ZMod 2 // f x = 0} = Nat.card {x : Fin n → ZMod 2 // f x = 1}
        then L / 2 else (L + 1) / 2) with ⟨hmin, _⟩ | ⟨hmin, _⟩
    · rw [hmin]; exact_mod_cast hsum_abs_le_K
    · rw [hmin]; exact hsum_abs_le_L
  have hZ : ((2 * 2 ^ m * H : ℕ) : ℤ) ≤ ((Nat.card (Fin n → ZMod 2) * (2 ^ m + t) : ℕ) : ℤ) := by
    rw [hcardX]
    push_cast
    have hmul : (2 ^ m : ℤ) * (2 * (H : ℤ)) ≤ (2 ^ m : ℤ) * ((2 ^ n : ℤ) + (t : ℤ) * (2 ^ (n - m) : ℤ)) :=
      mul_le_mul_of_nonneg_left (le_trans h2H (by linarith only [hsum_le_t])) (by positivity)
    have hsplitZ : (2 ^ m : ℤ) * (2 ^ (n - m) : ℤ) = (2 ^ n : ℤ) := by exact_mod_cast hcardX_split
    have hr : (2 ^ n : ℤ) * ((2 ^ m : ℤ) + (t : ℤ)) =
        (2 ^ m : ℤ) * ((2 ^ n : ℤ) + (t : ℤ) * (2 ^ (n - m) : ℤ)) := by
      calc (2 ^ n : ℤ) * ((2 ^ m : ℤ) + (t : ℤ))
          = (2 ^ m : ℤ) * (2 ^ n : ℤ) + (t : ℤ) * (2 ^ n : ℤ) := by ring
        _ = (2 ^ m : ℤ) * (2 ^ n : ℤ) + (t : ℤ) * ((2 ^ m : ℤ) * (2 ^ (n - m) : ℤ)) := by rw [← hsplitZ]
        _ = (2 ^ m : ℤ) * ((2 ^ n : ℤ) + (t : ℤ) * (2 ^ (n - m) : ℤ)) := by ring
    have hl : 2 * (2 ^ m : ℤ) * (H : ℤ) = (2 ^ m : ℤ) * (2 * (H : ℤ)) := by ring
    linarith only [hmul, hr, hl]
  exact_mod_cast hZ

open Classical in
private lemma split_imbal_sum (n m : ℕ)
    (Rad : Submodule (ZMod 2) (Fin n → ZMod 2)) [Fintype ↥Rad]
    (hdim : 2 * m + Module.finrank (ZMod 2) Rad = n)
    (cB dB : Fin m → ZMod 2) :
    ∀ (p : List Bool) (hp : p.length ≤ m)
    (extra : (Fin m → ZMod 2) × ↥Rad →ₗ[ZMod 2] ZMod 2),
    (∃ z : (Fin m → ZMod 2) × ↥Rad,
      (∀ i : Fin m, p.length ≤ i.val → z.1 i = 0) ∧ extra z = 1) →
    ∀ (γ : ZMod 2),
      let cond : ((Fin m → ZMod 2) × (Fin m → ZMod 2)) × ↥Rad → Prop := fun y =>
        (∀ step : Fin p.length,
          y.1.1 ⟨step.val, lt_of_lt_of_le step.isLt hp⟩ +
            dB ⟨step.val, lt_of_lt_of_le step.isLt hp⟩ = if p.get step then 1 else 0) ∧
        extra (y.1.2, y.2) = γ
      (∑ y ∈ Finset.univ.filter cond,
        chi (∑ i : Fin m, (if p.length ≤ i.val then (y.1.1 i + dB i) * (y.1.2 i + cB i) else 0))) =
        (2 ^ (n - m - 1) : ℤ) := by
  intro p hp extra ⟨z₀, hz₀_zero, hz₀_one⟩ γ cond
  let Vhead : Submodule (ZMod 2) ((Fin m → ZMod 2) × ↥Rad) :=
    { carrier := {z | ∀ i : Fin m, p.length ≤ i.val → z.1 i = 0}
      zero_mem' := fun _ _ => rfl
      , add_mem' := fun {a b} h1 h2 i hi => by
        change a.1 i + b.1 i = 0; rw [h1 i hi, h2 i hi, zero_add]
      smul_mem' := fun c z h1 i hi => by change c * z.1 i = 0; rw [h1 i hi, mul_zero] }
  let alphaSet : Finset (Fin m → ZMod 2) :=
    Finset.univ.filter (fun α => ∀ step : Fin p.length,
      α ⟨step.val, lt_of_lt_of_le step.isLt hp⟩ +
        dB ⟨step.val, lt_of_lt_of_le step.isLt hp⟩ = if p.get step then 1 else 0)
  have hcond_split : (∑ y ∈ Finset.univ.filter cond,
      chi (∑ i : Fin m, (if p.length ≤ i.val then (y.1.1 i + dB i) * (y.1.2 i + cB i) else 0))) =
      ∑ βr ∈ Finset.univ.filter (fun z : (Fin m → ZMod 2) × ↥Rad => extra z = γ),
        ∑ α ∈ alphaSet,
          chi (∑ i : Fin m, (if p.length ≤ i.val then (α i + dB i) * (βr.1 i + cB i) else 0)) := by
    let eSwap : (((Fin m → ZMod 2) × (Fin m → ZMod 2)) × ↥Rad) ≃
        ((Fin m → ZMod 2) × ((Fin m → ZMod 2) × ↥Rad)) :=
      Equiv.prodAssoc _ _ _
    rw [Finset.sum_filter]
    have h1 : (∑ y : ((Fin m → ZMod 2) × (Fin m → ZMod 2)) × ↥Rad,
        if cond y then
          chi (∑ i : Fin m, (if p.length ≤ i.val then (y.1.1 i + dB i) * (y.1.2 i + cB i) else 0))
        else 0) =
        ∑ z : (Fin m → ZMod 2) × ((Fin m → ZMod 2) × ↥Rad),
          if (z.1 ∈ alphaSet ∧ extra z.2 = γ) then
            chi (∑ i : Fin m, (if p.length ≤ i.val then (z.1 i + dB i) * (z.2.1 i + cB i) else 0))
          else 0 := by
      rw [← Equiv.sum_comp eSwap.symm]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      simp [eSwap, cond, alphaSet]
    rw [h1, Fintype.sum_prod_type_right]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun βr _ => ?_)
    by_cases hγ : extra βr = γ
    · simp only [hγ, ↓reduceIte, and_true, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    · simp [hγ]
  rw [hcond_split]
  have hinner_α : ∀ β : Fin m → ZMod 2,
      (∑ α ∈ alphaSet,
        chi (∑ i : Fin m, (if p.length ≤ i.val then (α i + dB i) * (β i + cB i) else 0))) =
      if (∀ i : Fin m, p.length ≤ i.val → β i = cB i) then (2 ^ (m - p.length) : ℤ) else 0 := by
    intro β
    let lift : (Fin (m - p.length) → ZMod 2) → (Fin m → ZMod 2) := fun αt i =>
      if hi : i.val < p.length then (if p.get ⟨i.val, hi⟩ then 1 else 0) + dB i
      else αt ⟨i.val - p.length, by omega⟩ + dB i
    have hbij : (∑ α ∈ alphaSet,
        chi (∑ i : Fin m, (if p.length ≤ i.val then (α i + dB i) * (β i + cB i) else 0))) =
        ∑ αt : Fin (m - p.length) → ZMod 2,
          chi (∑ j : Fin (m - p.length),
            αt j * (β ⟨p.length + j.val, by omega⟩ + cB ⟨p.length + j.val, by omega⟩)) := by
      symm
      refine Finset.sum_bij (fun αt _ => lift αt) ?_ ?_ ?_ ?_
      · intro αt _
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun step => ?_⟩
        dsimp only [lift]
        rw [dif_pos step.isLt, add_assoc, zmod2_add_self, add_zero]
      · intro α1 _ α2 _ h12
        funext j
        have hval := congrFun h12 ⟨p.length + j.val, by omega⟩
        dsimp only [lift] at hval
        have hnot : ¬ (p.length + j.val < p.length) := by omega
        rw [dif_neg hnot, dif_neg hnot] at hval
        have hidx : (⟨p.length + j.val - p.length, by omega⟩ : Fin (m - p.length)) = j :=
          Fin.ext (by dsimp only; omega)
        rw [hidx] at hval
        exact add_right_cancel hval
      · intro α hα
        have hα' := (Finset.mem_filter.mp hα).2
        refine ⟨fun j => α ⟨p.length + j.val, by omega⟩ + dB ⟨p.length + j.val, by omega⟩,
          Finset.mem_univ _, ?_⟩
        funext i
        dsimp only [lift]
        by_cases hi : i.val < p.length
        · rw [dif_pos hi]
          have hstep := hα' ⟨i.val, hi⟩
          have e := congrArg (· + dB i) hstep
          rw [add_assoc, zmod2_add_self, add_zero] at e
          exact e.symm
        · rw [dif_neg hi]
          have hfin : (⟨p.length + (i.val - p.length), by omega⟩ : Fin m) = i :=
            Fin.ext (by dsimp only; omega)
          rw [hfin, add_assoc, zmod2_add_self, add_zero]
      · intro αt _
        congr 1
        symm
        have h1 : (∑ i : Fin m, if p.length ≤ i.val then
            (lift αt i + dB i) * (β i + cB i) else 0) =
            ∑ i ∈ Finset.univ.filter (fun i : Fin m => p.length ≤ i.val),
              (lift αt i + dB i) * (β i + cB i) := by
          rw [Finset.sum_filter]
        rw [h1]
        symm
        refine Finset.sum_bij (fun j _ => ⟨p.length + j.val, by omega⟩) ?_ ?_ ?_ ?_
        · intro j _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩
        · intro j₁ _ j₂ _ h; exact Fin.ext (by have hv := congrArg Fin.val h; dsimp only at hv; omega)
        · intro i hi
          have hge := (Finset.mem_filter.mp hi).2
          exact ⟨⟨i.val - p.length, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp only; omega)⟩
        · intro j _
          dsimp only [lift]
          have hnot : ¬ (p.length + j.val < p.length) := by omega
          rw [dif_neg hnot, add_assoc, zmod2_add_self, add_zero]
          have hidx : (⟨p.length + j.val - p.length, by omega⟩ : Fin (m - p.length)) = j :=
            Fin.ext (by dsimp only; omega)
          rw [hidx]
    rw [hbij]
    let ℓt : (Fin (m - p.length) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun αt => ∑ j : Fin (m - p.length),
          αt j * (β ⟨p.length + j.val, by omega⟩ + cB ⟨p.length + j.val, by omega⟩)
        map_add' := fun a1 a2 => by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun j _ => by simp only [Pi.add_apply]; ring)
        map_smul' := fun c a1 => by
          change (∑ j : Fin (m - p.length),
              (c * a1 j) * (β ⟨p.length + j.val, by omega⟩ + cB ⟨p.length + j.val, by omega⟩)) =
            c * ∑ j : Fin (m - p.length),
              a1 j * (β ⟨p.length + j.val, by omega⟩ + cB ⟨p.length + j.val, by omega⟩)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => by ring) }
    change (∑ αt : Fin (m - p.length) → ZMod 2, chi (ℓt αt)) = _
    rw [sum_chi_linear ℓt ℓt.map_add]
    have hiff : (∀ αt : Fin (m - p.length) → ZMod 2, ℓt αt = 0) ↔
        (∀ i : Fin m, p.length ≤ i.val → β i = cB i) := by
      constructor
      · intro h i hi
        have h1 := h (Pi.single ⟨i.val - p.length, by omega⟩ 1)
        dsimp only [ℓt, LinearMap.coe_mk, AddHom.coe_mk] at h1
        rw [Finset.sum_eq_single ⟨i.val - p.length, by omega⟩] at h1
        · simp only [Pi.single_eq_same, one_mul] at h1
          have hfin : (⟨p.length + (i.val - p.length), by omega⟩ : Fin m) = i := Fin.ext (by dsimp only; omega)
          rw [hfin] at h1
          exact zmod2_eq_of_add_eq_zero h1
        · intro j _ hj; simp [Pi.single_eq_of_ne hj]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      · intro h αt
        dsimp only [ℓt, LinearMap.coe_mk, AddHom.coe_mk]
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [h ⟨p.length + j.val, by omega⟩ (by dsimp only; omega), zmod2_add_self, mul_zero]
    have hcard : (Fintype.card (Fin (m - p.length) → ZMod 2) : ℤ) = (2 ^ (m - p.length) : ℤ) := by
      simp [ZMod.card 2]
    rw [hcard]
    by_cases hc : ∀ i : Fin m, p.length ≤ i.val → β i = cB i
    · rw [if_pos (hiff.mpr hc), if_pos hc]
    · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]
  simp_rw [hinner_α]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hfin_Vhead : Module.finrank (ZMod 2) Vhead = p.length + (n - 2 * m) := by
    let eV : ↥Vhead ≃ₗ[ZMod 2] ((Fin p.length → ZMod 2) × ↥Rad) :=
      { toFun := fun z => (fun j => z.1.1 ⟨j.val, lt_of_lt_of_le j.isLt hp⟩, z.1.2)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun y =>
          ⟨(fun i => if hi : i.val < p.length then y.1 ⟨i.val, hi⟩ else 0, y.2),
           fun i hi => by simp [show ¬ i.val < p.length by omega]⟩
        left_inv := fun z => by
          apply Subtype.ext
          refine Prod.ext ?_ rfl
          funext i
          by_cases hi : i.val < p.length
          · simp [hi]
          · simp only [hi, ↓reduceDIte]
            exact (z.2 i (by omega)).symm
        right_inv := fun y => by
          refine Prod.ext ?_ rfl
          funext j; simp [j.isLt] }
    rw [eV.finrank_eq, Module.finrank_prod, Module.finrank_fin_fun]
    omega
  have hβr_card : ((Finset.univ.filter (fun z : (Fin m → ZMod 2) × ↥Rad => extra z = γ)).filter
      (fun z => ∀ i : Fin m, p.length ≤ i.val → z.1 i = cB i)).card =
      2 ^ (n - 2 * m + p.length - 1) := by
    let β₀ : Fin m → ZMod 2 := fun i => if p.length ≤ i.val then cB i else 0
    let base : (Fin m → ZMod 2) × ↥Rad := (β₀, 0)
    let z_wit : (Fin m → ZMod 2) × ↥Rad := base + (γ + extra base) • z₀
    have hz_wit : extra z_wit = γ ∧ ∀ i : Fin m, p.length ≤ i.val → z_wit.1 i = cB i := by
      refine ⟨?_, fun i hi => ?_⟩
      · dsimp only [z_wit]
        rw [map_add, map_smul, hz₀_one, smul_eq_mul, mul_one]
        have e : extra base + (γ + extra base) = γ + (extra base + extra base) := by ring
        rw [e, zmod2_add_self, add_zero]
      · change β₀ i + (γ + extra base) * z₀.1 i = cB i
        rw [hz₀_zero i hi, mul_zero, add_zero]
        simp [β₀, hi]
    let z0V : ↥Vhead := ⟨z₀, hz₀_zero⟩
    let KerType := {u : ↥Vhead // extra u.1 = 0}
    let eSplit : ↥Vhead ≃ KerType × ZMod 2 :=
      { toFun := fun u =>
          (⟨u - extra u.1 • z0V, by
            change extra (u.1 - extra u.1 • z₀) = 0
            rw [map_sub, map_smul, hz₀_one, smul_eq_mul, mul_one, sub_self]⟩, extra u.1)
        invFun := fun kc => kc.1.1 + kc.2 • z0V
        left_inv := fun u => sub_add_cancel u (extra u.1 • z0V)
        right_inv := fun kc => by
          have hex : extra (kc.1.1 + kc.2 • z0V).1 = kc.2 := by
            change extra (kc.1.1.1 + kc.2 • z₀) = kc.2
            rw [map_add, kc.1.2, zero_add, map_smul, hz₀_one, smul_eq_mul, mul_one]
          refine Prod.ext (Subtype.ext ?_) hex
          dsimp only
          rw [hex]; abel }
    have hcardV : Nat.card ↥Vhead = 2 ^ (n - 2 * m + p.length) := by
      rw [nat_card_subspace, hfin_Vhead]; congr 1; omega
    have hcardSplit : Nat.card ↥Vhead = Nat.card KerType * 2 := by
      rw [Nat.card_congr eSplit, Nat.card_prod]
      have h2 : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card 2]
      rw [h2]
    have hpos_exp0 : 1 ≤ n - 2 * m + p.length := by
      by_contra h0
      have hplen : p.length = 0 := by omega
      have hrad0 : Module.finrank (ZMod 2) Rad = 0 := by omega
      have hz1 : z₀.1 = 0 := by funext i; exact hz₀_zero i (by omega)
      have hz2 : z₀.2 = 0 := by
        have hsub : Subsingleton ↥Rad := Module.finrank_zero_iff.mp hrad0
        exact Subsingleton.elim z₀.2 0
      have hz : z₀ = 0 := Prod.ext hz1 hz2
      rw [hz, map_zero] at hz₀_one
      exact zero_ne_one hz₀_one
    have hcardKer : Nat.card KerType = 2 ^ (n - 2 * m + p.length - 1) := by
      have hpow : 2 ^ (n - 2 * m + p.length) = 2 ^ (n - 2 * m + p.length - 1) * 2 := by
        rw [← pow_succ]; congr 1; omega
      have hmul : Nat.card KerType * 2 = 2 ^ (n - 2 * m + p.length - 1) * 2 := by
        rw [← hcardSplit, hcardV, hpow]
      omega
    let eSol : {z : (Fin m → ZMod 2) × ↥Rad // extra z = γ ∧
        ∀ i : Fin m, p.length ≤ i.val → z.1 i = cB i} ≃ KerType :=
      { toFun := fun z =>
          ⟨⟨z.1 - z_wit, fun i hi => by
            change z.1.1 i - z_wit.1 i = 0
            rw [z.2.2 i hi, hz_wit.2 i hi, sub_self]⟩,
           by
            change extra (z.1 - z_wit) = 0
            rw [map_sub, z.2.1, hz_wit.1, sub_self]⟩
        invFun := fun u =>
          ⟨u.1.1 + z_wit,
           ⟨by rw [map_add, u.2, zero_add, hz_wit.1],
            fun i hi => by
              change u.1.1.1 i + z_wit.1 i = cB i
              rw [u.1.2 i hi, zero_add, hz_wit.2 i hi]⟩⟩
        left_inv := fun z => Subtype.ext (sub_add_cancel z.1 z_wit)
        right_inv := fun u => Subtype.ext (Subtype.ext (add_sub_cancel_right u.1.1 z_wit)) }
    have hcard_eq : ((Finset.univ.filter (fun z : (Fin m → ZMod 2) × ↥Rad => extra z = γ)).filter
        (fun z => ∀ i : Fin m, p.length ≤ i.val → z.1 i = cB i)).card =
        Nat.card KerType := by
      rw [Finset.filter_filter, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
        Nat.card_congr eSol]
    rw [hcard_eq, hcardKer]
  rw [hβr_card]
  push_cast
  rw [← pow_add]
  have hpos_exp : 1 ≤ n - 2 * m + p.length := by
    by_contra h0
    have hplen : p.length = 0 := by omega
    have hrad0 : Module.finrank (ZMod 2) Rad = 0 := by omega
    have hz1 : z₀.1 = 0 := by
      funext i
      exact hz₀_zero i (by omega)
    have hz2 : z₀.2 = 0 := by
      have hsub : Subsingleton ↥Rad := Module.finrank_zero_iff.mp hrad0
      exact Subsingleton.elim z₀.2 0
    have hz : z₀ = 0 := Prod.ext hz1 hz2
    rw [hz, map_zero] at hz₀_one
    exact zero_ne_one hz₀_one
  congr 1
  omega

private lemma bound_to_tree_bal (n m L H t : ℕ) (f : (Fin n → ZMod 2) → ZMod 2)
    (Rad : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hdim : 2 * m + Module.finrank (ZMod 2) Rad = n)
    (hcoordE : (Fin n → ZMod 2) ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2)) × ↥Rad)
    (cB dB : Fin m → ZMod 2) (c₁ : ZMod 2) (lamR : ↥Rad →ₗ[ZMod 2] ZMod 2)
    (hf_normal : ∀ (α β : Fin m → ZMod 2) (r : ↥Rad),
      f (hcoordE.symm ((α, β), r)) =
        c₁ + lamR r + ∑ i : Fin m, (α i + dB i) * (β i + cB i))
    (ht1 : 1 ≤ t) (htm : t ≤ 2 ^ m) (h2t_le : 2 * t ≤ L)
    (r₀ : ↥Rad) (hr₀ : lamR r₀ = 1)
    (hH_from_hits : ∀ hits : ℕ, (2 ^ n : ℤ) + (t : ℤ) * (2 ^ (n - m) : ℤ) ≤ 2 * (hits : ℤ) →
        H ≤ hits) :
    ∃ (N J : Finset (List Bool))
      (q : List Bool → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (offset out : List Bool → ZMod 2),
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      (N \ J).card ≤ L ∧ H ≤ Nat.card {x : Fin n → ZMod 2 // ∃ p ∈ N \ J,
        (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step)
        ∧ f x = out p} := by
  classical
  have : Fintype ↥Rad := Fintype.ofFinite _
  let uLin : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := fun i =>
    { toFun := fun x => (hcoordE x).1.1 i
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  let vLin : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := fun i =>
    { toFun := fun x => (hcoordE x).1.2 i
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  let rProj : (Fin n → ZMod 2) → (Fin n → ZMod 2) := fun x => (hcoordE x).2.1
  have hrProj_mem : ∀ x, rProj x ∈ Rad := fun x => (hcoordE x).2.2
  set N₀ := (mkPrefixTree m t).1
  set J₀ := (mkPrefixTree m t).2
  obtain ⟨h0_nil, h0_sub, h0_par, h0_ch, h0_card, h0_len, h0_zero⟩ :=
    mkPrefixTree_props m t ht1 htm
  let Split : Finset (List Bool) := N₀ \ J₀
  let N : Finset (List Bool) := N₀ ∪ Split.image (· ++ [false]) ∪ Split.image (· ++ [true])
  let J : Finset (List Bool) := J₀ ∪ Split
  let q : List Bool → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := fun h =>
    if hS : h ∈ Split then
      { toFun := fun x => lamR ⟨rProj x, hrProj_mem x⟩ +
          ∑ step : Fin h.length,
            if h.get step then vLin ⟨step.val, lt_of_lt_of_le step.isLt (h0_len h (Finset.mem_sdiff.mp hS).1)⟩ x else 0
        map_add' := fun x y => by
          have hr : (⟨rProj (x + y), hrProj_mem (x + y)⟩ : ↥Rad) =
              ⟨rProj x, hrProj_mem x⟩ + ⟨rProj y, hrProj_mem y⟩ := by
            have h1 := map_add hcoordE x y
            exact congrArg Prod.snd h1
          rw [hr, map_add]
          have hs : (∑ step : Fin h.length,
              if h.get step then
                vLin ⟨step.val, lt_of_lt_of_le step.isLt (h0_len h (Finset.mem_sdiff.mp hS).1)⟩ (x + y)
              else 0) =
              (∑ step : Fin h.length,
                ((if h.get step then
                  vLin ⟨step.val, lt_of_lt_of_le step.isLt (h0_len h (Finset.mem_sdiff.mp hS).1)⟩ x
                else 0) +
                (if h.get step then
                  vLin ⟨step.val, lt_of_lt_of_le step.isLt (h0_len h (Finset.mem_sdiff.mp hS).1)⟩ y
                else 0))) := by
            refine Finset.sum_congr rfl (fun step _ => ?_)
            split_ifs <;> simp [map_add]
          rw [hs, Finset.sum_add_distrib]; ring
        map_smul' := fun c x => by
          have hr : (⟨rProj (c • x), hrProj_mem (c • x)⟩ : ↥Rad) =
              c • ⟨rProj x, hrProj_mem x⟩ := by
            have h1 := map_smul hcoordE c x
            exact congrArg Prod.snd h1
          rw [hr, map_smul, smul_eq_mul, smul_eq_mul, mul_add, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl (fun step _ => ?_)
          split_ifs <;> simp [map_smul] }
    else if hh : h.length < m then uLin ⟨h.length, hh⟩ else 0
  let offset : List Bool → ZMod 2 := fun h =>
    if h ∈ Split then 0 else if hh : h.length < m then dB ⟨h.length, hh⟩ + 1 else 0
  let baseConst : (p : List Bool) → p.length ≤ m → ZMod 2 := fun p hp =>
    c₁ + ∑ step : Fin p.length,
      if p.get step then cB ⟨step.val, lt_of_lt_of_le step.isLt hp⟩ else 0
  let out : List Bool → ZMod 2 := fun p =>
    if hp : ∃ h ∈ Split, p = h ++ [true] then
      baseConst (Classical.choose hp) (h0_len _ (Finset.mem_sdiff.mp (Classical.choose_spec hp).1).1)
    else if hp' : ∃ h ∈ Split, p = h ++ [false] then
      baseConst (Classical.choose hp') (h0_len _ (Finset.mem_sdiff.mp (Classical.choose_spec hp').1).1) + 1
    else 0
  have hN_nil : [] ∈ N := Finset.mem_union_left _ (Finset.mem_union_left _ h0_nil)
  have hJ_sub : J ⊆ N := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpJ | hpS
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (h0_sub hpJ))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mp hpS).1)
  have hN_par : ∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J := by
    intro p b hp
    simp only [N, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with (hp0 | ⟨h, hS, heq⟩) | ⟨h, hS, heq⟩
    · exact Finset.mem_union_left _ (h0_par p b hp0)
    · have hpeq : p = h := (List.append_inj_left' heq rfl).symm
      rw [hpeq]; exact Finset.mem_union_right _ hS
    · have hpeq : p = h := (List.append_inj_left' heq rfl).symm
      rw [hpeq]; exact Finset.mem_union_right _ hS
  have hJ_ch : ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpJ | hpS
    · exact ⟨Finset.mem_union_left _ (Finset.mem_union_left _ (h0_ch p hpJ).1),
        Finset.mem_union_left _ (Finset.mem_union_left _ (h0_ch p hpJ).2)⟩
    · exact ⟨Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hpS)),
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hpS)⟩
  have hleaves_eq : N \ J = Split.image (· ++ [false]) ∪ Split.image (· ++ [true]) := by
    ext p
    simp only [N, J, Finset.mem_sdiff, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨(hp0 | ⟨h, hS, rfl⟩) | ⟨h, hS, rfl⟩, hnot⟩
      · exfalso; apply hnot
        by_cases hJ : p ∈ J₀
        · exact Or.inl hJ
        · exact Or.inr (Finset.mem_sdiff.mpr ⟨hp0, hJ⟩)
      · exact Or.inl ⟨h, hS, rfl⟩
      · exact Or.inr ⟨h, hS, rfl⟩
    · rintro (⟨h, hS, rfl⟩ | ⟨h, hS, rfl⟩)
      · refine ⟨Or.inl (Or.inr ⟨h, hS, rfl⟩), ?_⟩
        rintro (hJ | hS')
        · exact (Finset.mem_sdiff.mp hS).2 (h0_par h false (h0_sub hJ))
        · exact (Finset.mem_sdiff.mp hS).2 (h0_par h false (Finset.mem_sdiff.mp hS').1)
      · refine ⟨Or.inr ⟨h, hS, rfl⟩, ?_⟩
        rintro (hJ | hS')
        · exact (Finset.mem_sdiff.mp hS).2 (h0_par h true (h0_sub hJ))
        · exact (Finset.mem_sdiff.mp hS).2 (h0_par h true (Finset.mem_sdiff.mp hS').1)
  have hdisj_ft : Disjoint (Split.image (· ++ [false])) (Split.image (· ++ [true])) := by
    rw [Finset.disjoint_left]
    intro p hp0 hp1
    rcases Finset.mem_image.mp hp0 with ⟨h1, _, rfl⟩
    rcases Finset.mem_image.mp hp1 with ⟨h2, _, heq⟩
    have hlast := List.append_inj_right' heq rfl
    simp at hlast
  have hcard_leaves : (N \ J).card ≤ L := by
    rw [hleaves_eq, Finset.card_union_of_disjoint hdisj_ft,
      Finset.card_image_of_injective _ (fun a b h => List.append_inj_left' h rfl),
      Finset.card_image_of_injective _ (fun a b h => List.append_inj_left' h rfl),
      h0_card]
    omega
  refine ⟨N, J, q, offset, out, hN_nil, hJ_sub, hN_par, hJ_ch, hcard_leaves, ?_⟩
  apply hH_from_hits
  have hleaf_not_split : ∀ (h : List Bool) (i : Fin h.length), h ∈ Split → h.take i.val ∉ Split := by
    intro h i hS htake
    have hdesc : ∀ k : ℕ, k ≤ h.length → h.take k ∈ N₀ → k < h.length → h.take k ∈ J₀ := by
      intro k hk hN' hlt
      have h1 : ∀ d : ℕ, d ≤ h.length → h.take (h.length - d) ∈ N₀ := by
        intro d; induction d with
        | zero => intro _; simpa using (Finset.mem_sdiff.mp hS).1
        | succ d ih =>
          intro hd
          have hp := ih (by omega)
          have hsp : h.take (h.length - d) =
              h.take (h.length - (d + 1)) ++ [h.get ⟨h.length - (d + 1), by omega⟩] := by
            have he : h.length - d = (h.length - (d + 1)) + 1 := by omega
            rw [he, List.take_succ_eq_append_getElem (by omega)]; rfl
          rw [hsp] at hp
          exact h0_sub (h0_par _ _ hp)
      have hnext : h.take (k + 1) ∈ N₀ := by
        have h2 := h1 (h.length - (k + 1)) (by omega)
        have he : h.length - (h.length - (k + 1)) = k + 1 := by omega
        rwa [he] at h2
      have hsp : h.take (k + 1) = h.take k ++ [h.get ⟨k, hlt⟩] := by
        rw [List.take_succ_eq_append_getElem hlt]; rfl
      rw [hsp] at hnext
      exact h0_par _ _ hnext
    exact (Finset.mem_sdiff.mp htake).2
      (hdesc i.val (Nat.le_of_lt i.isLt) (Finset.mem_sdiff.mp htake).1 i.isLt)
  have htotal_hits : 2 * (Nat.card {x : Fin n → ZMod 2 // ∃ p ∈ N \ J,
      (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step) ∧
      f x = out p} : ℤ) =
      (2 ^ n : ℤ) + ∑ p ∈ N \ J,
        chi (out p) * ∑ x ∈ Finset.univ.filter (fun x =>
          ∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step),
          chi (f x) := by
    let cellT : List Bool → Finset (Fin n → ZMod 2) := fun p =>
      Finset.univ.filter (fun x =>
        ∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step)
    have hdisjT : Set.PairwiseDisjoint (N \ J : Finset (List Bool)) cellT := by
      intro p₁ hp1 p₂ hp2 hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      obtain ⟨p₀, _, huniq⟩ := tree_unique_leaf N J hN_nil hJ_sub hN_par hJ_ch q offset x
      exact hne ((huniq p₁ ⟨hp1, (Finset.mem_filter.mp hx1).2⟩).trans
        (huniq p₂ ⟨hp2, (Finset.mem_filter.mp hx2).2⟩).symm)
    have hunionT : (N \ J).biUnion cellT = Finset.univ := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true, cellT, Finset.mem_filter, true_and]
      obtain ⟨p, ⟨hp, hok⟩, _⟩ := tree_unique_leaf N J hN_nil hJ_sub hN_par hJ_ch q offset x
      exact ⟨p, hp, hok⟩
    have hcard_hits : Nat.card {x : Fin n → ZMod 2 // ∃ p ∈ N \ J,
        (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step) ∧
        f x = out p} =
        ∑ p ∈ N \ J, ((cellT p).filter (fun x => f x = out p)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.card_biUnion]
      · congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, cellT]
      · intro p₁ hp1 p₂ hp2 hne
        exact (hdisjT hp1 hp2 hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [hcard_hits]
    push_cast
    rw [Finset.mul_sum]
    have hper : ∀ p ∈ N \ J,
        2 * (((cellT p).filter (fun x => f x = out p)).card : ℤ) =
        ((cellT p).card : ℤ) + chi (out p) * ∑ x ∈ cellT p, chi (f x) := by
      intro p _
      have h1 : 2 * (((cellT p).filter (fun x => f x = out p)).card : ℤ) =
          ∑ x ∈ cellT p, (1 + chi (out p) * chi (f x)) := by
        rw [← Finset.sum_congr rfl (fun x _ => show (if f x = out p then (2 : ℤ) else 0) =
          1 + chi (out p) * chi (f x) by
            have h1 : ∀ a b : ZMod 2, (if a = b then (2 : ℤ) else 0) = 1 + chi b * chi a := by
              intro a b; rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide
            exact h1 (f x) (out p))]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        ring
      rw [h1, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib]
    congr 1
    have htot_c : ∑ p ∈ N \ J, (cellT p).card = 2 ^ n := by
      rw [← Finset.card_biUnion hdisjT, hunionT, Finset.card_univ]; simp [ZMod.card 2]
    exact_mod_cast htot_c
  rw [htotal_hits]
  have heach_leaf : ∀ (h : List Bool) (hS : h ∈ Split) (b : Bool),
      chi (out (h ++ [b])) * ∑ x ∈ Finset.univ.filter (fun x =>
        ∀ step : Fin (h ++ [b]).length,
          decide (q ((h ++ [b]).take step.val) x = offset ((h ++ [b]).take step.val)) =
            (h ++ [b]).get step),
        chi (f x) = (2 ^ (n - m - 1) : ℤ) := by
    intro h hS b
    have hhlen : h.length ≤ m := h0_len h (Finset.mem_sdiff.mp hS).1
    let extra : (Fin m → ZMod 2) × ↥Rad →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun z => lamR z.2 +
          ∑ step : Fin h.length, if h.get step then z.1 ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ else 0
        map_add' := fun z₁ z₂ => by
          change lamR (z₁.2 + z₂.2) + _ = _
          rw [map_add]
          have hs : (∑ step : Fin h.length,
              if h.get step then (z₁ + z₂).1 ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ else 0) =
              (∑ step : Fin h.length, if h.get step then z₁.1 ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ else 0) +
              (∑ step : Fin h.length, if h.get step then z₂.1 ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ else 0) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun step _ => ?_)
            split_ifs <;> simp
          rw [hs]; ring
        map_smul' := fun c z => by
          change lamR (c • z.2) + _ = _
          rw [map_smul, smul_eq_mul, smul_eq_mul, mul_add, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl (fun step _ => ?_)
          split_ifs <;> simp }
    have hextra_nz : ∃ z : (Fin m → ZMod 2) × ↥Rad,
        (∀ i : Fin m, h.length ≤ i.val → z.1 i = 0) ∧ extra z = 1 := by
      refine ⟨(0, r₀), fun _ _ => rfl, ?_⟩
      dsimp only [extra, LinearMap.coe_mk, AddHom.coe_mk]
      simp [hr₀]
    let γ : ZMod 2 := if b then 0 else 1
    have hout_eq : out (h ++ [b]) = baseConst h hhlen + γ := by
      cases b
      · dsimp only [out, γ]
        have hnotT : ¬ ∃ h' ∈ Split, h ++ [false] = h' ++ [true] := by
          rintro ⟨h', _, heq⟩
          have := List.append_inj_right' heq rfl
          simp at this
        have hexF : ∃ h' ∈ Split, h ++ [false] = h' ++ [false] := ⟨h, hS, rfl⟩
        rw [dif_neg hnotT, dif_pos hexF]
        have hch_eq : Classical.choose hexF = h :=
          (List.append_inj_left' (Classical.choose_spec hexF).2 rfl).symm
        have hbc : ∀ (p₁ p₂ : List Bool) (hp₁ : p₁.length ≤ m) (hp₂ : p₂.length ≤ m),
            p₁ = p₂ → baseConst p₁ hp₁ = baseConst p₂ hp₂ := by rintro p _ hp₁ hp₂ rfl; rfl
        rw [show (if false = true then (0 : ZMod 2) else 1) = 1 from rfl]
        exact congrArg (· + 1) (hbc (Classical.choose hexF) h (by rw [hch_eq]; exact hhlen) hhlen hch_eq)
      · dsimp only [out, γ]
        have hexT : ∃ h' ∈ Split, h ++ [true] = h' ++ [true] := ⟨h, hS, rfl⟩
        simp only [hexT, ↓reduceDIte, ↓reduceIte, add_zero]
        have hch_eq : Classical.choose hexT = h :=
          (List.append_inj_left' (Classical.choose_spec hexT).2 rfl).symm
        have hbc : ∀ (p₁ p₂ : List Bool) (hp₁ : p₁.length ≤ m) (hp₂ : p₂.length ≤ m),
            p₁ = p₂ → baseConst p₁ hp₁ = baseConst p₂ hp₂ := by rintro p _ hp₁ hp₂ rfl; rfl
        exact hbc (Classical.choose hexT) h (by rw [hch_eq]; exact hhlen) hhlen hch_eq
    rw [hout_eq, Finset.mul_sum]
    have htrans := (split_imbal_sum n m Rad hdim cB dB) h hhlen extra hextra_nz γ
    rw [← htrans]
    refine Finset.sum_bij (fun x _ => hcoordE x) ?_ ?_ ?_ ?_
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro step
        have hstep_b := hx' ⟨step.val, by rw [List.length_append, List.length_singleton]; omega⟩
        have htake : (h ++ [b]).take step.val = h.take step.val :=
          List.take_append_of_le_length (Nat.le_of_lt step.isLt)
        have hget : (h ++ [b]).get ⟨step.val, by rw [List.length_append, List.length_singleton]; omega⟩ = h.get step := by
          simp [List.getElem_append_left step.isLt]
        rw [htake, hget] at hstep_b
        have hnotS := hleaf_not_split h step hS
        have hq_eq : q (h.take step.val) x =
            (if hh : (h.take step.val).length < m then uLin ⟨(h.take step.val).length, hh⟩ else 0) x := by
          dsimp only [q]; rw [dif_neg hnotS]
        have hoff_eq : offset (h.take step.val) =
            (if hh : (h.take step.val).length < m then dB ⟨(h.take step.val).length, hh⟩ + 1 else 0) := by
          dsimp only [offset]; rw [if_neg hnotS]
        rw [hq_eq, hoff_eq] at hstep_b
        have hlt : (h.take step.val).length < m := by
          rw [List.length_take_of_le (Nat.le_of_lt step.isLt)]
          exact lt_of_lt_of_le step.isLt hhlen
        have hfin : (⟨(h.take step.val).length, hlt⟩ : Fin m) =
            ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ :=
          Fin.ext (List.length_take_of_le (Nat.le_of_lt step.isLt))
        rw [dif_pos hlt, dif_pos hlt, hfin] at hstep_b
        exact (zmod2_decide_add_one (uLin ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ x)
          (dB ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩) (h.get step)).mp hstep_b
      · have hlast := hx' ⟨h.length, by simp⟩
        have htake : (h ++ [b]).take h.length = h := List.take_left
        have hget : (h ++ [b]).get ⟨h.length, by simp⟩ = b := by simp
        rw [htake, hget] at hlast
        have hq_eq : q h x = lamR ⟨rProj x, hrProj_mem x⟩ +
            ∑ step : Fin h.length,
              (if h.get step then vLin ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ x else 0) := by
          dsimp only [q]; rw [dif_pos hS]; rfl
        have hoff_eq : offset h = 0 := by dsimp only [offset]; rw [if_pos hS]
        rw [hq_eq, hoff_eq] at hlast
        exact (zmod2_decide_eq_zero _ b).mp hlast
    · intro x₁ _ x₂ _ h12; exact hcoordE.injective h12
    · intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      refine ⟨hcoordE.symm y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun step => ?_⟩,
        hcoordE.apply_symm_apply y⟩
      have huv : ∀ i : Fin m, uLin i (hcoordE.symm y) = y.1.1 i ∧ vLin i (hcoordE.symm y) = y.1.2 i := by
        intro i
        have h1 := hcoordE.apply_symm_apply y
        exact ⟨congrFun (congrArg (fun z => z.1.1) h1) i, congrFun (congrArg (fun z => z.1.2) h1) i⟩
      have hrp : (⟨rProj (hcoordE.symm y), hrProj_mem (hcoordE.symm y)⟩ : ↥Rad) = y.2 := by
        exact congrArg Prod.snd (hcoordE.apply_symm_apply y)
      by_cases hs : step.val < h.length
      · have htake : (h ++ [b]).take step.val = h.take step.val :=
          List.take_append_of_le_length (Nat.le_of_lt hs)
        have hget : (h ++ [b]).get step = h.get ⟨step.val, hs⟩ := by
          simp [List.getElem_append_left hs]
        rw [htake, hget]
        have hnotS := hleaf_not_split h ⟨step.val, hs⟩ hS
        have hlt : (h.take step.val).length < m := by
          rw [List.length_take_of_le (Nat.le_of_lt hs)]
          exact lt_of_lt_of_le hs hhlen
        have hfin : (⟨(h.take step.val).length, hlt⟩ : Fin m) =
            ⟨step.val, lt_of_lt_of_le hs hhlen⟩ :=
          Fin.ext (List.length_take_of_le (Nat.le_of_lt hs))
        have hq_eq : q (h.take step.val) (hcoordE.symm y) = y.1.1 ⟨step.val, lt_of_lt_of_le hs hhlen⟩ := by
          dsimp only [q]; rw [dif_neg hnotS, dif_pos hlt, hfin, (huv _).1]
        have hoff_eq : offset (h.take step.val) = dB ⟨step.val, lt_of_lt_of_le hs hhlen⟩ + 1 := by
          dsimp only [offset]; rw [if_neg hnotS, dif_pos hlt, hfin]
        rw [hq_eq, hoff_eq]
        exact (zmod2_decide_add_one _ _ _).mpr (hy'.1 ⟨step.val, hs⟩)
      · have hs_eq : step.val = h.length := by
          have hlt := step.isLt; simp at hlt; omega
        have htake : (h ++ [b]).take step.val = h := by rw [hs_eq, List.take_left]
        have hget : (h ++ [b]).get step = b := by
          have : (h ++ [b])[step.val] = b := by simp [hs_eq]
          exact this
        rw [htake, hget]
        have hq_eq : q h (hcoordE.symm y) = lamR ⟨rProj (hcoordE.symm y), hrProj_mem (hcoordE.symm y)⟩ +
            ∑ st : Fin h.length,
              (if h.get st then vLin ⟨st.val, lt_of_lt_of_le st.isLt hhlen⟩ (hcoordE.symm y) else 0) := by
          dsimp only [q]; rw [dif_pos hS]; rfl
        have hoff_eq : offset h = 0 := by dsimp only [offset]; rw [if_pos hS]
        rw [hq_eq, hoff_eq]
        rw [hrp]
        have hsum_v : (∑ st : Fin h.length,
            if h.get st then vLin ⟨st.val, lt_of_lt_of_le st.isLt hhlen⟩ (hcoordE.symm y) else 0) =
            ∑ st : Fin h.length, if h.get st then y.1.2 ⟨st.val, lt_of_lt_of_le st.isLt hhlen⟩ else 0 := by
          refine Finset.sum_congr rfl (fun st _ => by split_ifs <;> simp [(huv _).2])
        rw [hsum_v]
        have hex := hy'.2
        change lamR y.2 + ∑ st : Fin h.length,
          (if h.get st then y.1.2 ⟨st.val, lt_of_lt_of_le st.isLt hhlen⟩ else 0) = γ at hex
        rw [hex]
        dsimp only [γ]
        cases b <;> decide
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      rw [← chi_add]
      congr 1
      have hfx := hf_normal (hcoordE x).1.1 (hcoordE x).1.2 (hcoordE x).2
      rw [hcoordE.symm_apply_apply] at hfx
      rw [hfx]
      have hcond1 : ∀ step : Fin h.length,
          (hcoordE x).1.1 ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ +
            dB ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ = if h.get step then 1 else 0 := by
        intro step
        have hstep_b := hx' ⟨step.val, by rw [List.length_append, List.length_singleton]; omega⟩
        have htake : (h ++ [b]).take step.val = h.take step.val :=
          List.take_append_of_le_length (Nat.le_of_lt step.isLt)
        have hget : (h ++ [b]).get ⟨step.val, by rw [List.length_append, List.length_singleton]; omega⟩ = h.get step := by
          simp [List.getElem_append_left step.isLt]
        rw [htake, hget] at hstep_b
        have hnotS := hleaf_not_split h step hS
        have hlt : (h.take step.val).length < m := by
          rw [List.length_take_of_le (Nat.le_of_lt step.isLt)]
          exact lt_of_lt_of_le step.isLt hhlen
        have hfin : (⟨(h.take step.val).length, hlt⟩ : Fin m) =
            ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ :=
          Fin.ext (List.length_take_of_le (Nat.le_of_lt step.isLt))
        have hq_eq : q (h.take step.val) x = uLin ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ x := by
          dsimp only [q]; rw [dif_neg hnotS, dif_pos hlt, hfin]
        have hoff_eq : offset (h.take step.val) = dB ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ + 1 := by
          dsimp only [offset]; rw [if_neg hnotS, dif_pos hlt, hfin]
        rw [hq_eq, hoff_eq] at hstep_b
        exact (zmod2_decide_add_one (uLin ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ x)
          (dB ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩) (h.get step)).mp hstep_b
      have hcond2 : lamR (hcoordE x).2 +
          ∑ step : Fin h.length,
            (if h.get step then (hcoordE x).1.2 ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ else 0) = γ := by
        have hlast := hx' ⟨h.length, by simp⟩
        have htake : (h ++ [b]).take h.length = h := List.take_left
        have hget : (h ++ [b]).get ⟨h.length, by simp⟩ = b := by simp
        rw [htake, hget] at hlast
        have hq_eq : q h x = lamR ⟨rProj x, hrProj_mem x⟩ +
            ∑ step : Fin h.length,
              (if h.get step then vLin ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ x else 0) := by
          dsimp only [q]; rw [dif_pos hS]; rfl
        have hoff_eq : offset h = 0 := by dsimp only [offset]; rw [if_pos hS]
        rw [hq_eq, hoff_eq] at hlast
        exact (zmod2_decide_eq_zero _ b).mp hlast
      have hsplit_sum : (∑ i : Fin m, ((hcoordE x).1.1 i + dB i) * ((hcoordE x).1.2 i + cB i)) =
          (∑ step : Fin h.length,
            if h.get step then (hcoordE x).1.2 ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ +
              cB ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ else 0) +
          (∑ i : Fin m, if h.length ≤ i.val then
            ((hcoordE x).1.1 i + dB i) * ((hcoordE x).1.2 i + cB i) else 0) := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => i.val < h.length)]
        congr 1
        · symm
          refine Finset.sum_bij (fun step _ => ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩) ?_ ?_ ?_ ?_
          · intro step _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, step.isLt⟩
          · intro s₁ _ s₂ _ h12; exact Fin.ext (by have hv := congrArg Fin.val h12; dsimp only at hv; exact hv)
          · intro i hi; exact ⟨⟨i.val, (Finset.mem_filter.mp hi).2⟩, Finset.mem_univ _, Fin.ext rfl⟩
          · intro step _
            rw [hcond1 step]
            cases h.get step <;> simp
        · rw [Finset.sum_filter]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have hiff : ¬ i.val < h.length ↔ h.length ≤ i.val := by omega
          by_cases hi : h.length ≤ i.val
          · rw [if_pos (hiff.mpr hi), if_pos hi]
          · rw [if_neg (fun h' => hi (hiff.mp h')), if_neg hi]
      have hhead_split : (∑ step : Fin h.length,
          if h.get step then (hcoordE x).1.2 ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ +
            cB ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ else 0) =
          (∑ step : Fin h.length,
            if h.get step then (hcoordE x).1.2 ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ else 0) +
          (∑ step : Fin h.length,
            if h.get step then cB ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun step _ => by cases h.get step <;> simp)
      rw [hsplit_sum, hhead_split]
      dsimp only [baseConst]
      set S1 := ∑ step : Fin h.length,
        if h.get step then cB ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ else 0
      set S2 := ∑ step : Fin h.length,
        if h.get step then (hcoordE x).1.2 ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ else 0
      set S3 := ∑ i : Fin m, if h.length ≤ i.val then
        ((hcoordE x).1.1 i + dB i) * ((hcoordE x).1.2 i + cB i) else 0
      have hlam_eq : lamR (hcoordE x).2 + S2 = γ := hcond2
      have e : c₁ + S1 + γ + (c₁ + lamR (hcoordE x).2 + (S2 + S1 + S3)) =
          S3 + ((c₁ + c₁) + (S1 + S1) + (γ + (lamR (hcoordE x).2 + S2))) := by ring
      rw [e, hlam_eq]
      simp only [zmod2_add_self, add_zero, zero_add]
  have hsum_all : (∑ p ∈ N \ J,
      chi (out p) * ∑ x ∈ Finset.univ.filter (fun x =>
        ∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step),
        chi (f x)) = (t : ℤ) * (2 ^ (n - m) : ℤ) := by
    rw [hleaves_eq, Finset.sum_union hdisj_ft,
      Finset.sum_image (fun a _ b _ h => List.append_inj_left' h rfl),
      Finset.sum_image (fun a _ b _ h => List.append_inj_left' h rfl)]
    have hsf : (∑ h ∈ Split, chi (out (h ++ [false])) *
        ∑ x ∈ Finset.univ.filter (fun x =>
          ∀ step : Fin (h ++ [false]).length,
            decide (q ((h ++ [false]).take step.val) x = offset ((h ++ [false]).take step.val)) =
              (h ++ [false]).get step),
          chi (f x)) = (t : ℤ) * (2 ^ (n - m - 1) : ℤ) := by
      rw [Finset.sum_congr rfl (fun h hS => heach_leaf h hS false), Finset.sum_const, nsmul_eq_mul]
      change (Split.card : ℤ) * (2 ^ (n - m - 1) : ℤ) = _
      dsimp only [Split]; rw [h0_card]
    have hst : (∑ h ∈ Split, chi (out (h ++ [true])) *
        ∑ x ∈ Finset.univ.filter (fun x =>
          ∀ step : Fin (h ++ [true]).length,
            decide (q ((h ++ [true]).take step.val) x = offset ((h ++ [true]).take step.val)) =
              (h ++ [true]).get step),
          chi (f x)) = (t : ℤ) * (2 ^ (n - m - 1) : ℤ) := by
      rw [Finset.sum_congr rfl (fun h hS => heach_leaf h hS true), Finset.sum_const, nsmul_eq_mul]
      change (Split.card : ℤ) * (2 ^ (n - m - 1) : ℤ) = _
      dsimp only [Split]; rw [h0_card]
    rw [hsf, hst]
    have hnm1 : 1 ≤ n - m := by
      by_contra h0
      have hrad0 : Module.finrank (ZMod 2) Rad = 0 := by omega
      have hsub : Subsingleton ↥Rad := Module.finrank_zero_iff.mp hrad0
      have hr0' : r₀ = 0 := Subsingleton.elim r₀ 0
      rw [hr0', map_zero] at hr₀
      exact zero_ne_one hr₀
    have hpow2 : (2 ^ (n - m) : ℤ) = 2 * (2 ^ (n - m - 1) : ℤ) := by
      rw [mul_comm, ← pow_succ]
      congr 1; omega
    rw [hpow2]; ring
  rw [hsum_all]

private lemma bound_to_tree_imbal (n m L H t : ℕ) (f : (Fin n → ZMod 2) → ZMod 2)
    (Rad : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hdim : 2 * m + Module.finrank (ZMod 2) Rad = n)
    (hcoordE : (Fin n → ZMod 2) ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2)) × ↥Rad)
    (cB dB : Fin m → ZMod 2) (c₁ : ZMod 2) (lamR : ↥Rad →ₗ[ZMod 2] ZMod 2)
    (hf_normal : ∀ (α β : Fin m → ZMod 2) (r : ↥Rad),
      f (hcoordE.symm ((α, β), r)) =
        c₁ + lamR r + ∑ i : Fin m, (α i + dB i) * (β i + cB i))
    (ht1 : 1 ≤ t) (htm : t ≤ 2 ^ m) (h2t_le : 2 * t - 1 ≤ L)
    (hlam0 : ∀ r : ↥Rad, lamR r = 0)
    (hH_from_hits : ∀ hits : ℕ, (2 ^ n : ℤ) + (t : ℤ) * (2 ^ (n - m) : ℤ) ≤ 2 * (hits : ℤ) →
        H ≤ hits) :
    ∃ (N J : Finset (List Bool))
      (q : List Bool → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (offset out : List Bool → ZMod 2),
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      (N \ J).card ≤ L ∧ H ≤ Nat.card {x : Fin n → ZMod 2 // ∃ p ∈ N \ J,
        (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step)
        ∧ f x = out p} := by
  classical
  have : Fintype ↥Rad := Fintype.ofFinite _
  have hcardR : Fintype.card ↥Rad = 2 ^ (n - 2 * m) := by
    rw [← Nat.card_eq_fintype_card, nat_card_subspace]
    congr 1; omega
  let uLin : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := fun i =>
    { toFun := fun x => (hcoordE x).1.1 i
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  let vLin : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := fun i =>
    { toFun := fun x => (hcoordE x).1.2 i
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  set N₀ := (mkPrefixTree m t).1
  set J₀ := (mkPrefixTree m t).2
  obtain ⟨h0_nil, h0_sub, h0_par, h0_ch, h0_card, h0_len, h0_zero⟩ :=
    mkPrefixTree_props m t ht1 htm
  let ZeroLeaves : Finset (List Bool) := (N₀ \ J₀).filter (fun p => ∀ b ∈ p, b = false)
  let Split : Finset (List Bool) := (N₀ \ J₀).filter (fun p => ¬ (∀ b ∈ p, b = false))
  have hSplit_card : Split.card = t - 1 := by
    have hsum := Finset.card_filter_add_card_filter_not (s := N₀ \ J₀)
      (p := fun p : List Bool => ∀ b ∈ p, b = false)
    rw [h0_zero, h0_card] at hsum
    change 1 + Split.card = t at hsum
    omega
  let N : Finset (List Bool) := N₀ ∪ Split.image (· ++ [false]) ∪ Split.image (· ++ [true])
  let J : Finset (List Bool) := J₀ ∪ Split
  let q : List Bool → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := fun h =>
    if hS : h ∈ Split then
      { toFun := fun x =>
          ∑ step : Fin h.length,
            if h.get step then vLin ⟨step.val, lt_of_lt_of_le step.isLt (h0_len h (Finset.mem_sdiff.mp (Finset.mem_filter.mp hS).1).1)⟩ x else 0
        map_add' := fun x y => by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun step _ => ?_)
          split_ifs <;> simp [map_add]
        map_smul' := fun c x => by
          rw [smul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun step _ => ?_)
          split_ifs <;> simp [map_smul] }
    else if hh : h.length < m then uLin ⟨h.length, hh⟩ else 0
  let offset : List Bool → ZMod 2 := fun h =>
    if h ∈ Split then 0 else if hh : h.length < m then dB ⟨h.length, hh⟩ + 1 else 0
  let baseConst : (p : List Bool) → p.length ≤ m → ZMod 2 := fun p hp =>
    c₁ + ∑ step : Fin p.length,
      if p.get step then cB ⟨step.val, lt_of_lt_of_le step.isLt hp⟩ else 0
  let out : List Bool → ZMod 2 := fun p =>
    if hp : ∃ h ∈ Split, p = h ++ [true] then
      baseConst (Classical.choose hp) (h0_len _ (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Classical.choose_spec hp).1).1).1)
    else if hp' : ∃ h ∈ Split, p = h ++ [false] then
      baseConst (Classical.choose hp') (h0_len _ (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Classical.choose_spec hp').1).1).1) + 1
    else c₁
  have hN_nil : [] ∈ N := Finset.mem_union_left _ (Finset.mem_union_left _ h0_nil)
  have hJ_sub : J ⊆ N := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpJ | hpS
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (h0_sub hpJ))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp hpS).1).1)
  have hN_par : ∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J := by
    intro p b hp
    simp only [N, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with (hp0 | ⟨h, hS, heq⟩) | ⟨h, hS, heq⟩
    · exact Finset.mem_union_left _ (h0_par p b hp0)
    · have hpeq : p = h := (List.append_inj_left' heq rfl).symm
      rw [hpeq]; exact Finset.mem_union_right _ hS
    · have hpeq : p = h := (List.append_inj_left' heq rfl).symm
      rw [hpeq]; exact Finset.mem_union_right _ hS
  have hJ_ch : ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpJ | hpS
    · exact ⟨Finset.mem_union_left _ (Finset.mem_union_left _ (h0_ch p hpJ).1),
        Finset.mem_union_left _ (Finset.mem_union_left _ (h0_ch p hpJ).2)⟩
    · exact ⟨Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hpS)),
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hpS)⟩
  have hleaves_eq : N \ J = ZeroLeaves ∪ Split.image (· ++ [false]) ∪ Split.image (· ++ [true]) := by
    ext p
    simp only [N, J, ZeroLeaves, Split, Finset.mem_sdiff, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter]
    constructor
    · rintro ⟨(hp0 | ⟨h, hS, rfl⟩) | ⟨h, hS, rfl⟩, hnot⟩
      · left; left
        have hnotJ : p ∉ J₀ := fun hJ => hnot (Or.inl hJ)
        refine ⟨⟨hp0, hnotJ⟩, ?_⟩
        by_contra hnotz
        exact hnot (Or.inr ⟨⟨hp0, hnotJ⟩, hnotz⟩)
      · left; right; exact ⟨h, hS, rfl⟩
      · right; exact ⟨h, hS, rfl⟩
    · rintro ((⟨⟨hp0, hnotJ⟩, hz⟩ | ⟨h, ⟨⟨hN, hnotJ⟩, hnz⟩, rfl⟩) | ⟨h, ⟨⟨hN, hnotJ⟩, hnz⟩, rfl⟩)
      · refine ⟨Or.inl (Or.inl hp0), ?_⟩
        rintro (hJ | ⟨_, hnz⟩)
        · exact hnotJ hJ
        · exact hnz hz
      · refine ⟨Or.inl (Or.inr ⟨h, ⟨⟨hN, hnotJ⟩, hnz⟩, rfl⟩), ?_⟩
        rintro (hJ | ⟨⟨hN', _⟩, _⟩)
        · exact hnotJ (h0_par h false (h0_sub hJ))
        · exact hnotJ (h0_par h false hN')
      · refine ⟨Or.inr ⟨h, ⟨⟨hN, hnotJ⟩, hnz⟩, rfl⟩, ?_⟩
        rintro (hJ | ⟨⟨hN', _⟩, _⟩)
        · exact hnotJ (h0_par h true (h0_sub hJ))
        · exact hnotJ (h0_par h true hN')
  have hdisj_z_f : Disjoint ZeroLeaves (Split.image (· ++ [false])) := by
    rw [Finset.disjoint_left]
    intro p hpZ hpF
    rcases Finset.mem_image.mp hpF with ⟨h, hS, rfl⟩
    have hN := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hpZ).1).1
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hS).1).2 (h0_par h false hN)
  have hdisj_zf_t : Disjoint (ZeroLeaves ∪ Split.image (· ++ [false])) (Split.image (· ++ [true])) := by
    rw [Finset.disjoint_left]
    intro p hpZF hpT
    rcases Finset.mem_image.mp hpT with ⟨h, hS, rfl⟩
    rcases Finset.mem_union.mp hpZF with hpZ | hpF
    · have hN := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hpZ).1).1
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hS).1).2 (h0_par h true hN)
    · rcases Finset.mem_image.mp hpF with ⟨h', _, heq⟩
      have := List.append_inj_right' heq rfl
      simp at this
  have hcard_leaves : (N \ J).card ≤ L := by
    rw [hleaves_eq, Finset.card_union_of_disjoint hdisj_zf_t,
      Finset.card_union_of_disjoint hdisj_z_f,
      Finset.card_image_of_injective _ (fun a b h => List.append_inj_left' h rfl),
      Finset.card_image_of_injective _ (fun a b h => List.append_inj_left' h rfl),
      h0_zero, hSplit_card]
    omega
  refine ⟨N, J, q, offset, out, hN_nil, hJ_sub, hN_par, hJ_ch, hcard_leaves, ?_⟩
  apply hH_from_hits
  have hleaf_not_split : ∀ (h : List Bool) (i : Fin h.length), h ∈ N₀ \ J₀ → h.take i.val ∉ Split := by
    intro h i hL0 htake
    have hdesc : ∀ k : ℕ, k ≤ h.length → h.take k ∈ N₀ → k < h.length → h.take k ∈ J₀ := by
      intro k hk hN' hlt
      have h1 : ∀ d : ℕ, d ≤ h.length → h.take (h.length - d) ∈ N₀ := by
        intro d; induction d with
        | zero => intro _; simpa using (Finset.mem_sdiff.mp hL0).1
        | succ d ih =>
          intro hd
          have hp := ih (by omega)
          have hsp : h.take (h.length - d) =
              h.take (h.length - (d + 1)) ++ [h.get ⟨h.length - (d + 1), by omega⟩] := by
            have he : h.length - d = (h.length - (d + 1)) + 1 := by omega
            rw [he, List.take_succ_eq_append_getElem (by omega)]; rfl
          rw [hsp] at hp
          exact h0_sub (h0_par _ _ hp)
      have hnext : h.take (k + 1) ∈ N₀ := by
        have h2 := h1 (h.length - (k + 1)) (by omega)
        have he : h.length - (h.length - (k + 1)) = k + 1 := by omega
        rwa [he] at h2
      have hsp : h.take (k + 1) = h.take k ++ [h.get ⟨k, hlt⟩] := by
        rw [List.take_succ_eq_append_getElem hlt]; rfl
      rw [hsp] at hnext
      exact h0_par _ _ hnext
    have htkL := (Finset.mem_filter.mp htake).1
    exact (Finset.mem_sdiff.mp htkL).2
      (hdesc i.val (Nat.le_of_lt i.isLt) (Finset.mem_sdiff.mp htkL).1 i.isLt)
  have htotal_hits : 2 * (Nat.card {x : Fin n → ZMod 2 // ∃ p ∈ N \ J,
      (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step) ∧
      f x = out p} : ℤ) =
      (2 ^ n : ℤ) + ∑ p ∈ N \ J,
        chi (out p) * ∑ x ∈ Finset.univ.filter (fun x =>
          ∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step),
          chi (f x) := by
    let cellT : List Bool → Finset (Fin n → ZMod 2) := fun p =>
      Finset.univ.filter (fun x =>
        ∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step)
    have hdisjT : Set.PairwiseDisjoint (N \ J : Finset (List Bool)) cellT := by
      intro p₁ hp1 p₂ hp2 hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      obtain ⟨p₀, _, huniq⟩ := tree_unique_leaf N J hN_nil hJ_sub hN_par hJ_ch q offset x
      exact hne ((huniq p₁ ⟨hp1, (Finset.mem_filter.mp hx1).2⟩).trans
        (huniq p₂ ⟨hp2, (Finset.mem_filter.mp hx2).2⟩).symm)
    have hunionT : (N \ J).biUnion cellT = Finset.univ := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true, cellT, Finset.mem_filter, true_and]
      obtain ⟨p, ⟨hp, hok⟩, _⟩ := tree_unique_leaf N J hN_nil hJ_sub hN_par hJ_ch q offset x
      exact ⟨p, hp, hok⟩
    have hcard_hits : Nat.card {x : Fin n → ZMod 2 // ∃ p ∈ N \ J,
        (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step) ∧
        f x = out p} =
        ∑ p ∈ N \ J, ((cellT p).filter (fun x => f x = out p)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.card_biUnion]
      · congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, cellT]
      · intro p₁ hp1 p₂ hp2 hne
        exact (hdisjT hp1 hp2 hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [hcard_hits]
    push_cast
    rw [Finset.mul_sum]
    have hper : ∀ p ∈ N \ J,
        2 * (((cellT p).filter (fun x => f x = out p)).card : ℤ) =
        ((cellT p).card : ℤ) + chi (out p) * ∑ x ∈ cellT p, chi (f x) := by
      intro p _
      have h1 : 2 * (((cellT p).filter (fun x => f x = out p)).card : ℤ) =
          ∑ x ∈ cellT p, (1 + chi (out p) * chi (f x)) := by
        rw [← Finset.sum_congr rfl (fun x _ => show (if f x = out p then (2 : ℤ) else 0) =
          1 + chi (out p) * chi (f x) by
            have h1 : ∀ a b : ZMod 2, (if a = b then (2 : ℤ) else 0) = 1 + chi b * chi a := by
              intro a b; rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide
            exact h1 (f x) (out p))]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        ring
      rw [h1, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib]
    congr 1
    have htot_c : ∑ p ∈ N \ J, (cellT p).card = 2 ^ n := by
      rw [← Finset.card_biUnion hdisjT, hunionT, Finset.card_univ]; simp [ZMod.card 2]
    exact_mod_cast htot_c
  rw [htotal_hits]
  have hzero_leaf : ∀ p ∈ ZeroLeaves,
      chi (out p) * ∑ x ∈ Finset.univ.filter (fun x =>
        ∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step),
        chi (f x) = (2 ^ (n - m) : ℤ) := by
    intro p hpZ
    have hpL0 : p ∈ N₀ \ J₀ := (Finset.mem_filter.mp hpZ).1
    have hp_false : ∀ b ∈ p, b = false := (Finset.mem_filter.mp hpZ).2
    have hplen : p.length ≤ m := h0_len p (Finset.mem_sdiff.mp hpL0).1
    have hout_p : out p = c₁ := by
      dsimp only [out]
      have hnotT : ¬ ∃ h ∈ Split, p = h ++ [true] := by
        rintro ⟨h, hS, rfl⟩
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hS).1).2
          (h0_par h true (Finset.mem_sdiff.mp hpL0).1)
      have hnotF : ¬ ∃ h ∈ Split, p = h ++ [false] := by
        rintro ⟨h, hS, rfl⟩
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hS).1).2
          (h0_par h false (Finset.mem_sdiff.mp hpL0).1)
      rw [dif_neg hnotT, dif_neg hnotF]
    rw [hout_p, Finset.mul_sum]
    let condZ : ((Fin m → ZMod 2) × (Fin m → ZMod 2)) × ↥Rad → Prop := fun y =>
      ∀ step : Fin p.length,
        y.1.1 ⟨step.val, lt_of_lt_of_le step.isLt hplen⟩ +
          dB ⟨step.val, lt_of_lt_of_le step.isLt hplen⟩ = 0
    have hsum_eq : (∑ x ∈ Finset.univ.filter (fun x =>
        ∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step),
        chi c₁ * chi (f x)) =
        ∑ y ∈ Finset.univ.filter condZ,
          chi (∑ i : Fin m, if p.length ≤ i.val then (y.1.1 i + dB i) * (y.1.2 i + cB i) else 0) := by
      refine Finset.sum_bij (fun x _ => hcoordE x) ?_ ?_ ?_ ?_
      · intro x hx
        have hx' := (Finset.mem_filter.mp hx).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun step => ?_⟩
        have hstep := hx' step
        have hnotS := hleaf_not_split p step hpL0
        have hlt : (p.take step.val).length < m := by
          rw [List.length_take_of_le (Nat.le_of_lt step.isLt)]
          exact lt_of_lt_of_le step.isLt hplen
        have hfin : (⟨(p.take step.val).length, hlt⟩ : Fin m) =
            ⟨step.val, lt_of_lt_of_le step.isLt hplen⟩ :=
          Fin.ext (List.length_take_of_le (Nat.le_of_lt step.isLt))
        have hq_eq : q (p.take step.val) x = uLin ⟨step.val, lt_of_lt_of_le step.isLt hplen⟩ x := by
          dsimp only [q]; rw [dif_neg hnotS, dif_pos hlt, hfin]
        have hoff_eq : offset (p.take step.val) = dB ⟨step.val, lt_of_lt_of_le step.isLt hplen⟩ + 1 := by
          dsimp only [offset]; rw [if_neg hnotS, dif_pos hlt, hfin]
        rw [hq_eq, hoff_eq] at hstep
        have hpf : p.get step = false := hp_false _ (List.get_mem p step)
        rw [hpf] at hstep
        exact (zmod2_decide_add_one_false _ _).mp hstep
      · intro x₁ _ x₂ _ h12; exact hcoordE.injective h12
      · intro y hy
        have hy' := (Finset.mem_filter.mp hy).2
        refine ⟨hcoordE.symm y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun step => ?_⟩,
          hcoordE.apply_symm_apply y⟩
        have hnotS := hleaf_not_split p step hpL0
        have hlt : (p.take step.val).length < m := by
          rw [List.length_take_of_le (Nat.le_of_lt step.isLt)]
          exact lt_of_lt_of_le step.isLt hplen
        have hfin : (⟨(p.take step.val).length, hlt⟩ : Fin m) =
            ⟨step.val, lt_of_lt_of_le step.isLt hplen⟩ :=
          Fin.ext (List.length_take_of_le (Nat.le_of_lt step.isLt))
        have hu : uLin ⟨step.val, lt_of_lt_of_le step.isLt hplen⟩ (hcoordE.symm y) =
            y.1.1 ⟨step.val, lt_of_lt_of_le step.isLt hplen⟩ :=
          congrFun (congrArg (fun z => z.1.1) (hcoordE.apply_symm_apply y)) _
        have hq_eq : q (p.take step.val) (hcoordE.symm y) = y.1.1 ⟨step.val, lt_of_lt_of_le step.isLt hplen⟩ := by
          dsimp only [q]; rw [dif_neg hnotS, dif_pos hlt, hfin, hu]
        have hoff_eq : offset (p.take step.val) = dB ⟨step.val, lt_of_lt_of_le step.isLt hplen⟩ + 1 := by
          dsimp only [offset]; rw [if_neg hnotS, dif_pos hlt, hfin]
        rw [hq_eq, hoff_eq]
        have hpf : p.get step = false := hp_false _ (List.get_mem p step)
        rw [hpf]
        exact (zmod2_decide_add_one_false _ _).mpr (hy' step)
      · intro x hx
        have hx' := (Finset.mem_filter.mp hx).2
        rw [← chi_add]
        congr 1
        have hfx := hf_normal (hcoordE x).1.1 (hcoordE x).1.2 (hcoordE x).2
        rw [hcoordE.symm_apply_apply] at hfx
        rw [hfx, hlam0, add_zero, ← add_assoc, zmod2_add_self, zero_add]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        by_cases hi : p.length ≤ i.val
        · rw [if_pos hi]
        · rw [if_neg hi]
          have hlt : i.val < p.length := by omega
          have hstep := hx' ⟨i.val, hlt⟩
          have hnotS := hleaf_not_split p ⟨i.val, hlt⟩ hpL0
          have hlt' : (p.take i.val).length < m := by
            rw [List.length_take_of_le (Nat.le_of_lt hlt)]
            exact lt_of_lt_of_le hlt hplen
          have hfin : (⟨(p.take i.val).length, hlt'⟩ : Fin m) = i :=
            Fin.ext (List.length_take_of_le (Nat.le_of_lt hlt))
          have hq_eq : q (p.take i.val) x = uLin i x := by
            dsimp only [q]; rw [dif_neg hnotS, dif_pos hlt', hfin]
          have hoff_eq : offset (p.take i.val) = dB i + 1 := by
            dsimp only [offset]; rw [if_neg hnotS, dif_pos hlt', hfin]
          rw [hq_eq, hoff_eq] at hstep
          have hpf : p.get ⟨i.val, hlt⟩ = false := hp_false _ (List.get_mem p ⟨i.val, hlt⟩)
          rw [hpf] at hstep
          have h0 : (hcoordE x).1.1 i + dB i = 0 :=
            (zmod2_decide_add_one_false _ _).mp hstep
          rw [h0, zero_mul]
    rw [hsum_eq]
    let eZ : {y : ((Fin m → ZMod 2) × (Fin m → ZMod 2)) × ↥Rad // condZ y} ≃
        (((Fin (m - p.length) → ZMod 2) × (Fin (m - p.length) → ZMod 2)) ×
          ((Fin p.length → ZMod 2) × ↥Rad)) :=
      { toFun := fun y =>
          ((fun j => y.1.1.1 ⟨p.length + j.val, by omega⟩ + dB ⟨p.length + j.val, by omega⟩,
            fun j => y.1.1.2 ⟨p.length + j.val, by omega⟩ + cB ⟨p.length + j.val, by omega⟩),
           (fun j => y.1.1.2 ⟨j.val, lt_of_lt_of_le j.isLt hplen⟩, y.1.2))
        invFun := fun z =>
          ⟨((fun i => if hi : i.val < p.length then dB i
              else z.1.1 ⟨i.val - p.length, by omega⟩ + dB i,
             fun i => if hi : i.val < p.length then z.2.1 ⟨i.val, hi⟩
              else z.1.2 ⟨i.val - p.length, by omega⟩ + cB i), z.2.2),
           fun step => by simp [step.isLt, zmod2_add_self]⟩
        left_inv := fun y => by
          apply Subtype.ext
          refine Prod.ext (Prod.ext ?_ ?_) rfl
          · funext i
            by_cases hi : i.val < p.length
            · simp only [hi, ↓reduceDIte]
              exact (zmod2_eq_of_add_eq_zero (y.2 ⟨i.val, hi⟩)).symm
            · simp only [hi, ↓reduceDIte]
              have hfin : (⟨p.length + (i.val - p.length), by omega⟩ : Fin m) = i :=
                Fin.ext (by dsimp only; omega)
              rw [hfin, add_assoc, zmod2_add_self, add_zero]
          · funext i
            by_cases hi : i.val < p.length
            · simp [hi]
            · simp only [hi, ↓reduceDIte]
              have hfin : (⟨p.length + (i.val - p.length), by omega⟩ : Fin m) = i :=
                Fin.ext (by dsimp only; omega)
              rw [hfin, add_assoc, zmod2_add_self, add_zero]
        right_inv := fun z => by
          refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ rfl)
          · funext j
            have hnot : ¬ p.length + j.val < p.length := by omega
            simp only [hnot, ↓reduceDIte, add_assoc, zmod2_add_self, add_zero]
            have hfin : (⟨p.length + j.val - p.length, by omega⟩ : Fin (m - p.length)) = j :=
              Fin.ext (by dsimp only; omega)
            rw [hfin]
          · funext j
            have hnot : ¬ p.length + j.val < p.length := by omega
            simp only [hnot, ↓reduceDIte, add_assoc, zmod2_add_self, add_zero]
            have hfin : (⟨p.length + j.val - p.length, by omega⟩ : Fin (m - p.length)) = j :=
              Fin.ext (by dsimp only; omega)
            rw [hfin]
          · funext j; simp [j.isLt] }
    have hsum_z : (∑ y ∈ Finset.univ.filter condZ,
        chi (∑ i : Fin m, if p.length ≤ i.val then (y.1.1 i + dB i) * (y.1.2 i + cB i) else 0)) =
        ∑ z : ((Fin (m - p.length) → ZMod 2) × (Fin (m - p.length) → ZMod 2)) ×
          ((Fin p.length → ZMod 2) × ↥Rad),
          chi (∑ j : Fin (m - p.length), z.1.1 j * z.1.2 j) := by
      rw [← Finset.sum_coe_sort]
      refine Finset.sum_bij (fun y _ => eZ ⟨y.1, (Finset.mem_filter.mp y.2).2⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro y₁ _ y₂ _ h12
        have h' := eZ.injective h12
        exact Subtype.ext (congrArg (fun z : {y : ((Fin m → ZMod 2) × (Fin m → ZMod 2)) × ↥Rad // condZ y} => z.1) h')
      · intro z _
        refine ⟨⟨(eZ.symm z).1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (eZ.symm z).2⟩⟩,
          Finset.mem_univ _, eZ.apply_symm_apply z⟩
      · intro y _
        congr 1
        rw [← Finset.sum_filter]
        symm
        refine Finset.sum_bij (fun j _ => ⟨p.length + j.val, by omega⟩) ?_ ?_ ?_ ?_
        · intro j _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩
        · intro j₁ _ j₂ _ h12; exact Fin.ext (by have hv := congrArg Fin.val h12; dsimp only at hv; omega)
        · intro i hi
          have hge := (Finset.mem_filter.mp hi).2
          exact ⟨⟨i.val - p.length, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp only; omega)⟩
        · intro j _; rfl
    rw [hsum_z, Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
      Fintype.card_pi, Fintype.card_fin, ZMod.card 2, Finset.prod_const, hcardR]
    rw [← Finset.mul_sum, sum_chi_inner_prod (m - p.length)]
    push_cast
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have heach_split : ∀ (h : List Bool) (hS : h ∈ Split) (b : Bool),
      chi (out (h ++ [b])) * ∑ x ∈ Finset.univ.filter (fun x =>
        ∀ step : Fin (h ++ [b]).length,
          decide (q ((h ++ [b]).take step.val) x = offset ((h ++ [b]).take step.val)) =
            (h ++ [b]).get step),
        chi (f x) = (2 ^ (n - m - 1) : ℤ) := by
    intro h hS b
    have hL0 : h ∈ N₀ \ J₀ := (Finset.mem_filter.mp hS).1
    have hhlen : h.length ≤ m := h0_len h (Finset.mem_sdiff.mp hL0).1
    have hhas_true : ∃ step : Fin h.length, h.get step = true := by
      have hnz := (Finset.mem_filter.mp hS).2
      by_contra hno
      apply hnz
      intro bb hbb
      obtain ⟨step, rfl⟩ := List.mem_iff_get.mp hbb
      cases hgb : h.get step
      · rfl
      · exact absurd ⟨step, hgb⟩ hno
    rcases hhas_true with ⟨step₀, hstep₀⟩
    let extra : (Fin m → ZMod 2) × ↥Rad →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun z =>
          ∑ step : Fin h.length, if h.get step then z.1 ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ else 0
        map_add' := fun z₁ z₂ => by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun step _ => by split_ifs <;> simp)
        map_smul' := fun c z => by
          rw [smul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun step _ => by split_ifs <;> simp) }
    have hextra_nz : ∃ z : (Fin m → ZMod 2) × ↥Rad,
        (∀ i : Fin m, h.length ≤ i.val → z.1 i = 0) ∧ extra z = 1 := by
      let idx₀ : Fin m := ⟨step₀.val, lt_of_lt_of_le step₀.isLt hhlen⟩
      refine ⟨(Pi.single idx₀ 1, 0), fun i hi => ?_, ?_⟩
      · have hne : i ≠ idx₀ := fun heq => by
          have := congrArg Fin.val heq; dsimp only [idx₀] at this; omega
        simp [Pi.single_eq_of_ne hne]
      · dsimp only [extra, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Finset.sum_eq_single step₀]
        · simp only [hstep₀, ↓reduceIte]
          exact Pi.single_eq_same (M := fun _ : Fin m => ZMod 2) idx₀ (1 : ZMod 2)
        · intro step _ hne
          have hne' : (⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ : Fin m) ≠ idx₀ := fun h' =>
            hne (Fin.ext (by have hv := congrArg Fin.val h'; dsimp only [idx₀] at hv; exact hv))
          split_ifs <;> simp [Pi.single_eq_of_ne hne']
        · intro hm; exact absurd (Finset.mem_univ _) hm
    let γ : ZMod 2 := if b then 0 else 1
    have hout_eq : out (h ++ [b]) = baseConst h hhlen + γ := by
      cases b
      · dsimp only [out, γ]
        have hnotT : ¬ ∃ h' ∈ Split, h ++ [false] = h' ++ [true] := by
          rintro ⟨h', _, heq⟩
          have := List.append_inj_right' heq rfl
          simp at this
        have hexF : ∃ h' ∈ Split, h ++ [false] = h' ++ [false] := ⟨h, hS, rfl⟩
        rw [dif_neg hnotT, dif_pos hexF]
        have hch_eq : Classical.choose hexF = h :=
          (List.append_inj_left' (Classical.choose_spec hexF).2 rfl).symm
        have hbc : ∀ (p₁ p₂ : List Bool) (hp₁ : p₁.length ≤ m) (hp₂ : p₂.length ≤ m),
            p₁ = p₂ → baseConst p₁ hp₁ = baseConst p₂ hp₂ := by rintro p _ hp₁ hp₂ rfl; rfl
        rw [show (if false = true then (0 : ZMod 2) else 1) = 1 from rfl]
        exact congrArg (· + 1) (hbc (Classical.choose hexF) h (by rw [hch_eq]; exact hhlen) hhlen hch_eq)
      · dsimp only [out, γ]
        have hexT : ∃ h' ∈ Split, h ++ [true] = h' ++ [true] := ⟨h, hS, rfl⟩
        simp only [hexT, ↓reduceDIte, ↓reduceIte, add_zero]
        have hch_eq : Classical.choose hexT = h :=
          (List.append_inj_left' (Classical.choose_spec hexT).2 rfl).symm
        have hbc : ∀ (p₁ p₂ : List Bool) (hp₁ : p₁.length ≤ m) (hp₂ : p₂.length ≤ m),
            p₁ = p₂ → baseConst p₁ hp₁ = baseConst p₂ hp₂ := by rintro p _ hp₁ hp₂ rfl; rfl
        exact hbc (Classical.choose hexT) h (by rw [hch_eq]; exact hhlen) hhlen hch_eq
    rw [hout_eq, Finset.mul_sum]
    have htrans := (split_imbal_sum n m Rad hdim cB dB) h hhlen extra hextra_nz γ
    rw [← htrans]
    refine Finset.sum_bij (fun x _ => hcoordE x) ?_ ?_ ?_ ?_
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro step
        have hstep_b := hx' ⟨step.val, by rw [List.length_append, List.length_singleton]; omega⟩
        have htake : (h ++ [b]).take step.val = h.take step.val :=
          List.take_append_of_le_length (Nat.le_of_lt step.isLt)
        have hget : (h ++ [b]).get ⟨step.val, by rw [List.length_append, List.length_singleton]; omega⟩ = h.get step := by
          simp [List.getElem_append_left step.isLt]
        rw [htake, hget] at hstep_b
        have hnotS := hleaf_not_split h step hL0
        have hlt : (h.take step.val).length < m := by
          rw [List.length_take_of_le (Nat.le_of_lt step.isLt)]
          exact lt_of_lt_of_le step.isLt hhlen
        have hfin : (⟨(h.take step.val).length, hlt⟩ : Fin m) =
            ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ :=
          Fin.ext (List.length_take_of_le (Nat.le_of_lt step.isLt))
        have hq_eq : q (h.take step.val) x = uLin ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ x := by
          dsimp only [q]; rw [dif_neg hnotS, dif_pos hlt, hfin]
        have hoff_eq : offset (h.take step.val) = dB ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ + 1 := by
          dsimp only [offset]; rw [if_neg hnotS, dif_pos hlt, hfin]
        rw [hq_eq, hoff_eq] at hstep_b
        exact (zmod2_decide_add_one (uLin ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ x)
          (dB ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩) (h.get step)).mp hstep_b
      · have hlast := hx' ⟨h.length, by simp⟩
        have htake : (h ++ [b]).take h.length = h := List.take_left
        have hget : (h ++ [b]).get ⟨h.length, by simp⟩ = b := by simp
        rw [htake, hget] at hlast
        have hq_eq : q h x = ∑ step : Fin h.length,
            (if h.get step then vLin ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ x else 0) := by
          dsimp only [q]; rw [dif_pos hS]; rfl
        have hoff_eq : offset h = 0 := by dsimp only [offset]; rw [if_pos hS]
        rw [hq_eq, hoff_eq] at hlast
        exact (zmod2_decide_eq_zero _ b).mp hlast
    · intro x₁ _ x₂ _ h12; exact hcoordE.injective h12
    · intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      refine ⟨hcoordE.symm y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun step => ?_⟩,
        hcoordE.apply_symm_apply y⟩
      have huv : ∀ i : Fin m, uLin i (hcoordE.symm y) = y.1.1 i ∧ vLin i (hcoordE.symm y) = y.1.2 i := by
        intro i
        have h1 := hcoordE.apply_symm_apply y
        exact ⟨congrFun (congrArg (fun z => z.1.1) h1) i, congrFun (congrArg (fun z => z.1.2) h1) i⟩
      by_cases hs : step.val < h.length
      · have htake : (h ++ [b]).take step.val = h.take step.val :=
          List.take_append_of_le_length (Nat.le_of_lt hs)
        have hget : (h ++ [b]).get step = h.get ⟨step.val, hs⟩ := by
          simp [List.getElem_append_left hs]
        rw [htake, hget]
        have hnotS := hleaf_not_split h ⟨step.val, hs⟩ hL0
        have hlt : (h.take step.val).length < m := by
          rw [List.length_take_of_le (Nat.le_of_lt hs)]
          exact lt_of_lt_of_le hs hhlen
        have hfin : (⟨(h.take step.val).length, hlt⟩ : Fin m) =
            ⟨step.val, lt_of_lt_of_le hs hhlen⟩ :=
          Fin.ext (List.length_take_of_le (Nat.le_of_lt hs))
        have hq_eq : q (h.take step.val) (hcoordE.symm y) = y.1.1 ⟨step.val, lt_of_lt_of_le hs hhlen⟩ := by
          dsimp only [q]; rw [dif_neg hnotS, dif_pos hlt, hfin, (huv _).1]
        have hoff_eq : offset (h.take step.val) = dB ⟨step.val, lt_of_lt_of_le hs hhlen⟩ + 1 := by
          dsimp only [offset]; rw [if_neg hnotS, dif_pos hlt, hfin]
        rw [hq_eq, hoff_eq]
        exact (zmod2_decide_add_one _ _ _).mpr (hy'.1 ⟨step.val, hs⟩)
      · have hs_eq : step.val = h.length := by
          have hlt := step.isLt; simp at hlt; omega
        have htake : (h ++ [b]).take step.val = h := by rw [hs_eq, List.take_left]
        have hget : (h ++ [b]).get step = b := by
          have : (h ++ [b])[step.val] = b := by simp [hs_eq]
          exact this
        rw [htake, hget]
        have hq_eq : q h (hcoordE.symm y) = ∑ st : Fin h.length,
            (if h.get st then vLin ⟨st.val, lt_of_lt_of_le st.isLt hhlen⟩ (hcoordE.symm y) else 0) := by
          dsimp only [q]; rw [dif_pos hS]; rfl
        have hoff_eq : offset h = 0 := by dsimp only [offset]; rw [if_pos hS]
        rw [hq_eq, hoff_eq]
        have hsum_v : (∑ st : Fin h.length,
            if h.get st then vLin ⟨st.val, lt_of_lt_of_le st.isLt hhlen⟩ (hcoordE.symm y) else 0) =
            ∑ st : Fin h.length, if h.get st then y.1.2 ⟨st.val, lt_of_lt_of_le st.isLt hhlen⟩ else 0 := by
          refine Finset.sum_congr rfl (fun st _ => by split_ifs <;> simp [(huv _).2])
        rw [hsum_v]
        have hex := hy'.2
        change ∑ st : Fin h.length,
          (if h.get st then y.1.2 ⟨st.val, lt_of_lt_of_le st.isLt hhlen⟩ else 0) = γ at hex
        rw [hex]
        dsimp only [γ]
        cases b <;> decide
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      rw [← chi_add]
      congr 1
      have hfx := hf_normal (hcoordE x).1.1 (hcoordE x).1.2 (hcoordE x).2
      rw [hcoordE.symm_apply_apply] at hfx
      rw [hfx, hlam0, add_zero]
      have hcond1 : ∀ step : Fin h.length,
          (hcoordE x).1.1 ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ +
            dB ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ = if h.get step then 1 else 0 := by
        intro step
        have hstep_b := hx' ⟨step.val, by rw [List.length_append, List.length_singleton]; omega⟩
        have htake : (h ++ [b]).take step.val = h.take step.val :=
          List.take_append_of_le_length (Nat.le_of_lt step.isLt)
        have hget : (h ++ [b]).get ⟨step.val, by rw [List.length_append, List.length_singleton]; omega⟩ = h.get step := by
          simp [List.getElem_append_left step.isLt]
        rw [htake, hget] at hstep_b
        have hnotS := hleaf_not_split h step hL0
        have hlt : (h.take step.val).length < m := by
          rw [List.length_take_of_le (Nat.le_of_lt step.isLt)]
          exact lt_of_lt_of_le step.isLt hhlen
        have hfin : (⟨(h.take step.val).length, hlt⟩ : Fin m) =
            ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ :=
          Fin.ext (List.length_take_of_le (Nat.le_of_lt step.isLt))
        have hq_eq : q (h.take step.val) x = uLin ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ x := by
          dsimp only [q]; rw [dif_neg hnotS, dif_pos hlt, hfin]
        have hoff_eq : offset (h.take step.val) = dB ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ + 1 := by
          dsimp only [offset]; rw [if_neg hnotS, dif_pos hlt, hfin]
        rw [hq_eq, hoff_eq] at hstep_b
        exact (zmod2_decide_add_one (uLin ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ x)
          (dB ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩) (h.get step)).mp hstep_b
      have hcond2 : ∑ step : Fin h.length,
          (if h.get step then (hcoordE x).1.2 ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ else 0) = γ := by
        have hlast := hx' ⟨h.length, by simp⟩
        have htake : (h ++ [b]).take h.length = h := List.take_left
        have hget : (h ++ [b]).get ⟨h.length, by simp⟩ = b := by simp
        rw [htake, hget] at hlast
        have hq_eq : q h x = ∑ step : Fin h.length,
            (if h.get step then vLin ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ x else 0) := by
          dsimp only [q]; rw [dif_pos hS]; rfl
        have hoff_eq : offset h = 0 := by dsimp only [offset]; rw [if_pos hS]
        rw [hq_eq, hoff_eq] at hlast
        exact (zmod2_decide_eq_zero _ b).mp hlast
      have hsplit_sum : (∑ i : Fin m, ((hcoordE x).1.1 i + dB i) * ((hcoordE x).1.2 i + cB i)) =
          (∑ step : Fin h.length,
            if h.get step then (hcoordE x).1.2 ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ +
              cB ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ else 0) +
          (∑ i : Fin m, if h.length ≤ i.val then
            ((hcoordE x).1.1 i + dB i) * ((hcoordE x).1.2 i + cB i) else 0) := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => i.val < h.length)]
        congr 1
        · symm
          refine Finset.sum_bij (fun step _ => ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩) ?_ ?_ ?_ ?_
          · intro step _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, step.isLt⟩
          · intro s₁ _ s₂ _ h12; exact Fin.ext (by have hv := congrArg Fin.val h12; dsimp only at hv; exact hv)
          · intro i hi; exact ⟨⟨i.val, (Finset.mem_filter.mp hi).2⟩, Finset.mem_univ _, Fin.ext rfl⟩
          · intro step _
            rw [hcond1 step]
            cases h.get step <;> simp
        · rw [Finset.sum_filter]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have hiff : ¬ i.val < h.length ↔ h.length ≤ i.val := by omega
          by_cases hi : h.length ≤ i.val
          · rw [if_pos (hiff.mpr hi), if_pos hi]
          · rw [if_neg (fun h' => hi (hiff.mp h')), if_neg hi]
      have hhead_split : (∑ step : Fin h.length,
          if h.get step then (hcoordE x).1.2 ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ +
            cB ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ else 0) =
          (∑ step : Fin h.length,
            if h.get step then (hcoordE x).1.2 ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ else 0) +
          (∑ step : Fin h.length,
            if h.get step then cB ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun step _ => by cases h.get step <;> simp)
      rw [hsplit_sum, hhead_split]
      dsimp only [baseConst]
      set S1 := ∑ step : Fin h.length,
        if h.get step then cB ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ else 0
      set S2 := ∑ step : Fin h.length,
        if h.get step then (hcoordE x).1.2 ⟨step.val, lt_of_lt_of_le step.isLt hhlen⟩ else 0
      set S3 := ∑ i : Fin m, if h.length ≤ i.val then
        ((hcoordE x).1.1 i + dB i) * ((hcoordE x).1.2 i + cB i) else 0
      have e : c₁ + S1 + γ + (c₁ + (S2 + S1 + S3)) =
          S3 + ((c₁ + c₁) + (S1 + S1) + (γ + S2)) := by ring
      rw [e, hcond2]
      simp only [zmod2_add_self, add_zero, zero_add]
  have hsum_all : (∑ p ∈ N \ J,
      chi (out p) * ∑ x ∈ Finset.univ.filter (fun x =>
        ∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step),
        chi (f x)) = (t : ℤ) * (2 ^ (n - m) : ℤ) := by
    rw [hleaves_eq, Finset.sum_union hdisj_zf_t, Finset.sum_union hdisj_z_f,
      Finset.sum_image (fun a _ b _ h => List.append_inj_left' h rfl),
      Finset.sum_image (fun a _ b _ h => List.append_inj_left' h rfl)]
    have hsz : (∑ p ∈ ZeroLeaves, chi (out p) *
        ∑ x ∈ Finset.univ.filter (fun x =>
          ∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step),
          chi (f x)) = (2 ^ (n - m) : ℤ) := by
      rw [Finset.sum_congr rfl hzero_leaf, Finset.sum_const, nsmul_eq_mul]
      change (ZeroLeaves.card : ℤ) * (2 ^ (n - m) : ℤ) = _
      dsimp only [ZeroLeaves]; rw [h0_zero]; simp
    have hsf : (∑ h ∈ Split, chi (out (h ++ [false])) *
        ∑ x ∈ Finset.univ.filter (fun x =>
          ∀ step : Fin (h ++ [false]).length,
            decide (q ((h ++ [false]).take step.val) x = offset ((h ++ [false]).take step.val)) =
              (h ++ [false]).get step),
          chi (f x)) = ((t - 1 : ℕ) : ℤ) * (2 ^ (n - m - 1) : ℤ) := by
      rw [Finset.sum_congr rfl (fun h hS => heach_split h hS false), Finset.sum_const, nsmul_eq_mul, hSplit_card]
    have hst : (∑ h ∈ Split, chi (out (h ++ [true])) *
        ∑ x ∈ Finset.univ.filter (fun x =>
          ∀ step : Fin (h ++ [true]).length,
            decide (q ((h ++ [true]).take step.val) x = offset ((h ++ [true]).take step.val)) =
              (h ++ [true]).get step),
          chi (f x)) = ((t - 1 : ℕ) : ℤ) * (2 ^ (n - m - 1) : ℤ) := by
      rw [Finset.sum_congr rfl (fun h hS => heach_split h hS true), Finset.sum_const, nsmul_eq_mul, hSplit_card]
    rw [hsz, hsf, hst]
    by_cases ht_eq1 : t = 1
    · subst ht_eq1; simp
    · have hm_pos : 1 ≤ m := by
        by_contra hm0
        have hm' : m = 0 := by omega
        rw [hm', pow_zero] at htm
        omega
      have hnm1 : 1 ≤ n - m := by omega
      have hpow2 : (2 ^ (n - m) : ℤ) = 2 * (2 ^ (n - m - 1) : ℤ) := by
        rw [mul_comm, ← pow_succ]
        congr 1; omega
      have ht1_cast : ((t - 1 : ℕ) : ℤ) + 1 = (t : ℤ) := by omega
      calc (2 ^ (n - m) : ℤ) + ((t - 1 : ℕ) : ℤ) * (2 ^ (n - m - 1) : ℤ) +
              ((t - 1 : ℕ) : ℤ) * (2 ^ (n - m - 1) : ℤ)
          = (2 ^ (n - m) : ℤ) + ((t - 1 : ℕ) : ℤ) * (2 * (2 ^ (n - m - 1) : ℤ)) := by ring
        _ = (2 ^ (n - m) : ℤ) + ((t - 1 : ℕ) : ℤ) * (2 ^ (n - m) : ℤ) := by rw [← hpow2]
        _ = (((t - 1 : ℕ) : ℤ) + 1) * (2 ^ (n - m) : ℤ) := by ring
        _ = (t : ℤ) * (2 ^ (n - m) : ℤ) := by rw [ht1_cast]
  rw [hsum_all]

private lemma main_proof (n : ℕ) (f : (Fin n → ZMod 2) → ZMod 2)
    (hf : ∀ p u v : Fin n → ZMod 2,
      f (p + u + v) + f (p + u) + f (p + v) + f p = f (u + v) + f u + f v + f 0)
    (L H : ℕ) (hL : 0 < L) :
    let F := ZMod 2
    let X := Fin n → F
    let B := fun u v : X => f (u + v) + f u + f v + f 0
    let m := (n - (Nat.card {u : X // ∀ v : X, B u v = 0}).log2) / 2
    let bal := Nat.card {x : X // f x = 0} = Nat.card {x : X // f x = 1}
    let K := 2 ^ m
    let t := min K (if bal then L / 2 else (L + 1) / 2)
    let bound := 2 * K * H ≤ Nat.card X * (K + t)
    let affineCan := ∃ k : ℕ, k ≤ L ∧
      ∃ (a : Fin k → X) (S : Fin k → Submodule F X) (out : Fin k → F),
        (∀ x : X, ∃! j : Fin k, x - a j ∈ S j) ∧
        H ≤ Nat.card {x : X // ∃ j, x - a j ∈ S j ∧ f x = out j}
    let treeCan := ∃ (N J : Finset (List Bool))
      (q : List Bool → X →ₗ[F] F) (offset out : List Bool → F),
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      (N \ J).card ≤ L ∧ H ≤ Nat.card {x : X // ∃ p ∈ N \ J,
        (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step)
        ∧ f x = out p}
    (affineCan ↔ bound) ∧ (treeCan ↔ bound) := by
  classical
  dsimp only
  obtain ⟨hsym, halt, haddL, haddR⟩ := quad_bilinear hf
  have hB0L : ∀ v, quadB f 0 v = 0 := by
    intro v
    have h0 := haddL 0 0 v; rw [zero_add, zmod2_add_self] at h0; exact h0
  have hBsmulL : ∀ (c : ZMod 2) (u v : Fin n → ZMod 2), quadB f (c • u) v = c * quadB f u v := by
    intro c u v
    rcases zmod2_cases c with rfl | rfl
    · simp [hB0L]
    · simp
  have hBsmulR : ∀ (c : ZMod 2) (u v : Fin n → ZMod 2), quadB f u (c • v) = c * quadB f u v := by
    intro c u v
    rw [hsym, hBsmulL, hsym]
  obtain ⟨m, aB, bB, hdim_symp, _, hsymp⟩ := exists_symplectic_basis (quadB f) hsym halt haddL haddR ⊤
  let Rad : Submodule (ZMod 2) (Fin n → ZMod 2) :=
    { carrier := {w | ∀ v : Fin n → ZMod 2, quadB f w v = 0}
      zero_mem' := hB0L
      , add_mem' := fun hx hy v => by rw [haddL, hx v, hy v, zero_add]
      smul_mem' := fun c x hx v => by rw [hBsmulL, hx v, mul_zero] }
  let RadTop : Submodule (ZMod 2) (Fin n → ZMod 2) :=
    { carrier := {w | w ∈ (⊤ : Submodule (ZMod 2) (Fin n → ZMod 2)) ∧
        ∀ v ∈ (⊤ : Submodule (ZMod 2) (Fin n → ZMod 2)), quadB f w v = 0}
      zero_mem' := ⟨trivial, fun v _ => hB0L v⟩
      , add_mem' := fun hx hy => ⟨trivial, fun v _ => by
        rw [haddL, hx.2 v trivial, hy.2 v trivial, zero_add]⟩
      smul_mem' := fun c x hx => ⟨trivial, fun v _ => by rw [hBsmulL, hx.2 v trivial, mul_zero]⟩ }
  have hRad_eq_top : RadTop = Rad := by
    ext w
    simp [RadTop, Rad]
  change 2 * m + Module.finrank (ZMod 2) RadTop = Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (Fin n → ZMod 2)) at hdim_symp
  rw [hRad_eq_top, finrank_top, Module.finrank_fin_fun] at hdim_symp
  have hm_eq : (n - (Nat.card {u : Fin n → ZMod 2 // ∀ v : Fin n → ZMod 2, quadB f u v = 0}).log2) / 2 = m := by
    have hcardR : Nat.card {u : Fin n → ZMod 2 // ∀ v : Fin n → ZMod 2, quadB f u v = 0} =
        2 ^ Module.finrank (ZMod 2) Rad := nat_card_subspace Rad
    rw [hcardR, Nat.log2_two_pow]
    omega
  change ((∃ k ≤ L,
      ∃ (a : Fin k → Fin n → ZMod 2) (S : Fin k → Submodule (ZMod 2) (Fin n → ZMod 2))
        (out : Fin k → ZMod 2),
        (∀ x : Fin n → ZMod 2, ∃! j : Fin k, x - a j ∈ S j) ∧
        H ≤ Nat.card {x : Fin n → ZMod 2 // ∃ j, x - a j ∈ S j ∧ f x = out j}) ↔
      2 * 2 ^ ((n - (Nat.card {u : Fin n → ZMod 2 // ∀ v : Fin n → ZMod 2, quadB f u v = 0}).log2) / 2) * H ≤
        Nat.card (Fin n → ZMod 2) *
          (2 ^ ((n - (Nat.card {u : Fin n → ZMod 2 // ∀ v : Fin n → ZMod 2, quadB f u v = 0}).log2) / 2) +
            min (2 ^ ((n - (Nat.card {u : Fin n → ZMod 2 // ∀ v : Fin n → ZMod 2, quadB f u v = 0}).log2) / 2))
              (if Nat.card {x : Fin n → ZMod 2 // f x = 0} = Nat.card {x : Fin n → ZMod 2 // f x = 1}
                then L / 2 else (L + 1) / 2))) ∧
    ((∃ (N J : Finset (List Bool))
      (q : List Bool → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (offset out : List Bool → ZMod 2),
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      (N \ J).card ≤ L ∧ H ≤ Nat.card {x : Fin n → ZMod 2 // ∃ p ∈ N \ J,
        (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step)
        ∧ f x = out p}) ↔
      2 * 2 ^ ((n - (Nat.card {u : Fin n → ZMod 2 // ∀ v : Fin n → ZMod 2, quadB f u v = 0}).log2) / 2) * H ≤
        Nat.card (Fin n → ZMod 2) *
          (2 ^ ((n - (Nat.card {u : Fin n → ZMod 2 // ∀ v : Fin n → ZMod 2, quadB f u v = 0}).log2) / 2) +
            min (2 ^ ((n - (Nat.card {u : Fin n → ZMod 2 // ∀ v : Fin n → ZMod 2, quadB f u v = 0}).log2) / 2))
              (if Nat.card {x : Fin n → ZMod 2 // f x = 0} = Nat.card {x : Fin n → ZMod 2 // f x = 1}
                then L / 2 else (L + 1) / 2)))
  rw [hm_eq]
  have hm_le : 2 * m ≤ n := by omega
  have hcardX : Nat.card (Fin n → ZMod 2) = 2 ^ n := by
    rw [Nat.card_eq_fintype_card]; simp [ZMod.card 2]
  have hcardX_split : 2 ^ m * 2 ^ (n - m) = 2 ^ n := by
    rw [← pow_add]; congr 1; omega
  let uLin : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := fun i =>
    { toFun := fun x => quadB f x (bB i)
      map_add' := fun x y => haddL x y (bB i)
      map_smul' := fun c x => hBsmulL c x (bB i) }
  let vLin : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := fun i =>
    { toFun := fun x => quadB f x (aB i)
      map_add' := fun x y => haddL x y (aB i)
      map_smul' := fun c x => hBsmulL c x (aB i) }
  let rProj : (Fin n → ZMod 2) → (Fin n → ZMod 2) := fun x =>
    x + ∑ i : Fin m, (uLin i x • aB i + vLin i x • bB i)
  have hB_rProj_a : ∀ (x : Fin n → ZMod 2) (j : Fin m), quadB f (rProj x) (aB j) = 0 := by
    intro x j
    dsimp only [rProj]
    rw [haddL]
    have hsum : quadB f (∑ i : Fin m, (uLin i x • aB i + vLin i x • bB i)) (aB j) =
        ∑ i : Fin m, (uLin i x * quadB f (aB i) (aB j) + vLin i x * quadB f (bB i) (aB j)) := by
      have hlin : ∀ s : Finset (Fin m),
          quadB f (∑ i ∈ s, (uLin i x • aB i + vLin i x • bB i)) (aB j) =
          ∑ i ∈ s, (uLin i x * quadB f (aB i) (aB j) + vLin i x * quadB f (bB i) (aB j)) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp [hB0L]
        | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, haddL, ih, haddL, hBsmulL, hBsmulL]
      exact hlin Finset.univ
    rw [hsum, Finset.sum_eq_single j]
    · rw [(hsymp j j).1, hsym (bB j) (aB j), (hsymp j j).2.2]
      simp [vLin, zmod2_add_self]
    · intro i _ hij
      rw [(hsymp i j).1, hsym (bB i) (aB j), (hsymp j i).2.2, if_neg (Ne.symm hij)]
      ring
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  have hB_rProj_b : ∀ (x : Fin n → ZMod 2) (j : Fin m), quadB f (rProj x) (bB j) = 0 := by
    intro x j
    dsimp only [rProj]
    rw [haddL]
    have hsum : quadB f (∑ i : Fin m, (uLin i x • aB i + vLin i x • bB i)) (bB j) =
        ∑ i : Fin m, (uLin i x * quadB f (aB i) (bB j) + vLin i x * quadB f (bB i) (bB j)) := by
      have hlin : ∀ s : Finset (Fin m),
          quadB f (∑ i ∈ s, (uLin i x • aB i + vLin i x • bB i)) (bB j) =
          ∑ i ∈ s, (uLin i x * quadB f (aB i) (bB j) + vLin i x * quadB f (bB i) (bB j)) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp [hB0L]
        | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, haddL, ih, haddL, hBsmulL, hBsmulL]
      exact hlin Finset.univ
    rw [hsum, Finset.sum_eq_single j]
    · rw [(hsymp j j).2.1, (hsymp j j).2.2]
      simp [uLin, zmod2_add_self]
    · intro i _ hij
      rw [(hsymp i j).2.1, (hsymp i j).2.2, if_neg hij]
      ring
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  let spanAB : Submodule (ZMod 2) (Fin n → ZMod 2) :=
    Submodule.span (ZMod 2) (Set.range aB ∪ Set.range bB)
  have hrProj_mem : ∀ x : Fin n → ZMod 2, rProj x ∈ Rad := by
    let orthAB : Submodule (ZMod 2) (Fin n → ZMod 2) :=
      { carrier := {w | ∀ i : Fin m, quadB f w (aB i) = 0 ∧ quadB f w (bB i) = 0}
        zero_mem' := fun i => ⟨hB0L _, hB0L _⟩
        , add_mem' := fun hx hy i => ⟨by rw [haddL, (hx i).1, (hy i).1, zero_add],
          by rw [haddL, (hx i).2, (hy i).2, zero_add]⟩
        smul_mem' := fun c x hx i => ⟨by rw [hBsmulL, (hx i).1, mul_zero],
          by rw [hBsmulL, (hx i).2, mul_zero]⟩ }
    have hRad_le : Rad ≤ orthAB := fun w hw i => ⟨hw (aB i), hw (bB i)⟩
    have hfin_orth : Module.finrank (ZMod 2) orthAB = Module.finrank (ZMod 2) Rad := by
      let ev : (Fin n → ZMod 2) →ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
        { toFun := fun x => (fun i => vLin i x, fun i => uLin i x)
          map_add' := fun x y => Prod.ext (by funext i; exact map_add (vLin i) x y)
            (by funext i; exact map_add (uLin i) x y)
          map_smul' := fun c x => Prod.ext (by funext i; exact map_smul (vLin i) c x)
            (by funext i; exact map_smul (uLin i) c x) }
      have hker : LinearMap.ker ev = orthAB := by
        ext w
        simp only [LinearMap.mem_ker, ev, LinearMap.coe_mk, AddHom.coe_mk,
          Prod.mk_eq_zero, funext_iff, Pi.zero_apply]
        exact ⟨fun ⟨h1, h2⟩ i => ⟨h1 i, h2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
      have hsurj : Function.Surjective ev := by
        intro ⟨α, β⟩
        refine ⟨∑ i : Fin m, (β i • aB i + α i • bB i), ?_⟩
        refine Prod.ext ?_ ?_
        · funext j
          change quadB f (∑ i : Fin m, (β i • aB i + α i • bB i)) (aB j) = α j
          have hlin : ∀ s : Finset (Fin m),
              quadB f (∑ i ∈ s, (β i • aB i + α i • bB i)) (aB j) =
              ∑ i ∈ s, (β i * quadB f (aB i) (aB j) + α i * quadB f (bB i) (aB j)) := by
            intro s; induction s using Finset.induction_on with
            | empty => simp [hB0L]
            | insert a s ha ih =>
              rw [Finset.sum_insert ha, Finset.sum_insert ha, haddL, ih, haddL, hBsmulL, hBsmulL]
          rw [hlin Finset.univ, Finset.sum_eq_single j]
          · rw [(hsymp j j).1, hsym (bB j) (aB j), (hsymp j j).2.2]; simp
          · intro i _ hij
            rw [(hsymp i j).1, hsym (bB i) (aB j), (hsymp j i).2.2, if_neg (Ne.symm hij)]; ring
          · intro hmem; exact absurd (Finset.mem_univ _) hmem
        · funext j
          change quadB f (∑ i : Fin m, (β i • aB i + α i • bB i)) (bB j) = β j
          have hlin : ∀ s : Finset (Fin m),
              quadB f (∑ i ∈ s, (β i • aB i + α i • bB i)) (bB j) =
              ∑ i ∈ s, (β i * quadB f (aB i) (bB j) + α i * quadB f (bB i) (bB j)) := by
            intro s; induction s using Finset.induction_on with
            | empty => simp [hB0L]
            | insert a s ha ih =>
              rw [Finset.sum_insert ha, Finset.sum_insert ha, haddL, ih, haddL, hBsmulL, hBsmulL]
          rw [hlin Finset.univ, Finset.sum_eq_single j]
          · rw [(hsymp j j).2.1, (hsymp j j).2.2]; simp
          · intro i _ hij
            rw [(hsymp i j).2.1, (hsymp i j).2.2, if_neg hij]; ring
          · intro hmem; exact absurd (Finset.mem_univ _) hmem
      have hrn := LinearMap.finrank_range_add_finrank_ker ev
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker, Module.finrank_fin_fun,
        Module.finrank_prod, Module.finrank_fin_fun] at hrn
      omega
    have hEq : Rad = orthAB := Submodule.eq_of_le_of_finrank_eq hRad_le hfin_orth.symm
    intro x
    rw [hEq]
    exact fun i => ⟨hB_rProj_a x i, hB_rProj_b x i⟩
  let hcoordE : (Fin n → ZMod 2) ≃ₗ[ZMod 2] ((Fin m → ZMod 2) × (Fin m → ZMod 2)) × ↥Rad :=
    { toFun := fun x => ((fun i => uLin i x, fun i => vLin i x), ⟨rProj x, hrProj_mem x⟩)
      map_add' := fun x y => by
        refine Prod.ext (Prod.ext (by funext i; exact map_add (uLin i) x y)
          (by funext i; exact map_add (vLin i) x y)) (Subtype.ext ?_)
        change (x + y) + ∑ i : Fin m, (uLin i (x + y) • aB i + vLin i (x + y) • bB i) =
          (x + ∑ i : Fin m, (uLin i x • aB i + vLin i x • bB i)) +
          (y + ∑ i : Fin m, (uLin i y • aB i + vLin i y • bB i))
        simp_rw [map_add, add_smul]
        have h1 : ∀ i : Fin m,
            uLin i x • aB i + uLin i y • aB i + (vLin i x • bB i + vLin i y • bB i) =
            (uLin i x • aB i + vLin i x • bB i) + (uLin i y • aB i + vLin i y • bB i) := fun i => by abel
        simp_rw [h1, Finset.sum_add_distrib]
        abel
      map_smul' := fun c x => by
        refine Prod.ext (Prod.ext (by funext i; exact map_smul (uLin i) c x)
          (by funext i; exact map_smul (vLin i) c x)) (Subtype.ext ?_)
        change c • x + ∑ i : Fin m, (uLin i (c • x) • aB i + vLin i (c • x) • bB i) =
          c • (x + ∑ i : Fin m, (uLin i x • aB i + vLin i x • bB i))
        simp_rw [map_smul, smul_eq_mul]
        rw [smul_add, Finset.smul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [smul_add, mul_smul, mul_smul]
      invFun := fun y => y.2.1 + ∑ i : Fin m, (y.1.1 i • aB i + y.1.2 i • bB i)
      left_inv := fun x => by
        change (x + ∑ i : Fin m, (uLin i x • aB i + vLin i x • bB i)) +
          ∑ i : Fin m, (uLin i x • aB i + vLin i x • bB i) = x
        funext j
        simp only [Pi.add_apply]
        rw [add_assoc, zmod2_add_self, add_zero]
      right_inv := fun ⟨⟨α, β⟩, ⟨r, hr⟩⟩ => by
        have hu : ∀ j : Fin m, uLin j (r + ∑ i : Fin m, (α i • aB i + β i • bB i)) = α j := by
          intro j
          change quadB f (r + ∑ i : Fin m, (α i • aB i + β i • bB i)) (bB j) = α j
          rw [haddL, hr (bB j), zero_add]
          have hlin : ∀ s : Finset (Fin m),
              quadB f (∑ i ∈ s, (α i • aB i + β i • bB i)) (bB j) =
              ∑ i ∈ s, (α i * quadB f (aB i) (bB j) + β i * quadB f (bB i) (bB j)) := by
            intro s; induction s using Finset.induction_on with
            | empty => simp [hB0L]
            | insert a s ha ih =>
              rw [Finset.sum_insert ha, Finset.sum_insert ha, haddL, ih, haddL, hBsmulL, hBsmulL]
          rw [hlin Finset.univ, Finset.sum_eq_single j]
          · rw [(hsymp j j).2.1, (hsymp j j).2.2]; simp
          · intro i _ hij; rw [(hsymp i j).2.1, (hsymp i j).2.2, if_neg hij]; ring
          · intro hmem; exact absurd (Finset.mem_univ _) hmem
        have hv : ∀ j : Fin m, vLin j (r + ∑ i : Fin m, (α i • aB i + β i • bB i)) = β j := by
          intro j
          change quadB f (r + ∑ i : Fin m, (α i • aB i + β i • bB i)) (aB j) = β j
          rw [haddL, hr (aB j), zero_add]
          have hlin : ∀ s : Finset (Fin m),
              quadB f (∑ i ∈ s, (α i • aB i + β i • bB i)) (aB j) =
              ∑ i ∈ s, (α i * quadB f (aB i) (aB j) + β i * quadB f (bB i) (aB j)) := by
            intro s; induction s using Finset.induction_on with
            | empty => simp [hB0L]
            | insert a s ha ih =>
              rw [Finset.sum_insert ha, Finset.sum_insert ha, haddL, ih, haddL, hBsmulL, hBsmulL]
          rw [hlin Finset.univ, Finset.sum_eq_single j]
          · rw [(hsymp j j).1, hsym (bB j) (aB j), (hsymp j j).2.2]; simp
          · intro i _ hij; rw [(hsymp i j).1, hsym (bB i) (aB j), (hsymp j i).2.2, if_neg (Ne.symm hij)]; ring
          · intro hmem; exact absurd (Finset.mem_univ _) hmem
        refine Prod.ext (Prod.ext (funext hu) (funext hv)) (Subtype.ext ?_)
        change (r + ∑ i : Fin m, (α i • aB i + β i • bB i)) +
          ∑ i : Fin m, (uLin i (r + ∑ j : Fin m, (α j • aB j + β j • bB j)) • aB i +
            vLin i (r + ∑ j : Fin m, (α j • aB j + β j • bB j)) • bB i) = r
        simp_rw [hu, hv]
        funext j
        simp only [Pi.add_apply]
        rw [add_assoc, zmod2_add_self, add_zero] }
  let cB : Fin m → ZMod 2 := fun i => f (aB i) + f 0
  let dB : Fin m → ZMod 2 := fun i => f (bB i) + f 0
  let c₁ : ZMod 2 := f 0 + ∑ i : Fin m, cB i * dB i
  let lamR : ↥Rad →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun r => f r.1 + f 0
      map_add' := fun r₁ r₂ => by
        have h1 : f (r₁.1 + r₂.1) + f r₁.1 + f r₂.1 + f 0 = 0 := r₁.2 r₂.1
        change f (r₁.1 + r₂.1) + f 0 = (f r₁.1 + f 0) + (f r₂.1 + f 0)
        have e : f (r₁.1 + r₂.1) + f 0 =
            (f (r₁.1 + r₂.1) + f r₁.1 + f r₂.1 + f 0) + (f r₁.1 + f 0) + (f r₂.1 + f 0) := by
          have e1 : (f (r₁.1 + r₂.1) + f r₁.1 + f r₂.1 + f 0) + (f r₁.1 + f 0) + (f r₂.1 + f 0) =
              f (r₁.1 + r₂.1) + f 0 + ((f r₁.1 + f r₁.1) + (f r₂.1 + f r₂.1) + (f 0 + f 0)) := by ring
          rw [e1]
          simp only [zmod2_add_self, add_zero, zero_add]
        rw [e, h1, zero_add]
      map_smul' := fun c r => by
        rcases zmod2_cases c with rfl | rfl
        · simp [zmod2_add_self]
        · simp }
  have hf_normal : ∀ (α β : Fin m → ZMod 2) (r : ↥Rad),
      f (hcoordE.symm ((α, β), r)) =
        c₁ + lamR r + ∑ i : Fin m, (α i + dB i) * (β i + cB i) := by
    intro α β r
    have hadd_f : ∀ x y : Fin n → ZMod 2, f (x + y) = f x + f y + f 0 + quadB f x y := by
      intro x y
      have h1 : quadB f x y = f (x + y) + f x + f y + f 0 := rfl
      rw [h1]
      have e : f x + f y + f 0 + (f (x + y) + f x + f y + f 0) =
          f (x + y) + ((f x + f x) + (f y + f y) + (f 0 + f 0)) := by ring
      rw [e]
      simp only [zmod2_add_self, add_zero, zero_add]
    have hsum_f : ∀ s : Finset (Fin m),
        f (∑ i ∈ s, (α i • aB i + β i • bB i)) + f 0 =
        ∑ i ∈ s, (α i * cB i + β i * dB i + α i * β i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [zmod2_add_self]
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd_f]
        have hB_disj : quadB f (α i • aB i + β i • bB i) (∑ j ∈ s, (α j • aB j + β j • bB j)) = 0 := by
          have hlin : ∀ t : Finset (Fin m), i ∉ t →
              quadB f (α i • aB i + β i • bB i) (∑ j ∈ t, (α j • aB j + β j • bB j)) = 0 := by
            intro t hit
            induction t using Finset.induction_on with
            | empty => rw [Finset.sum_empty, hsym, hB0L]
            | insert j t hj iht =>
              have hij : i ≠ j := fun h => hit (h ▸ Finset.mem_insert_self j t)
              have hit' : i ∉ t := fun h => hit (Finset.mem_insert_of_mem h)
              rw [Finset.sum_insert hj, haddR, iht hit', add_zero, haddL, haddR, haddR,
                hBsmulL, hBsmulL, hBsmulL, hBsmulL, hBsmulR, hBsmulR, hBsmulR, hBsmulR,
                (hsymp i j).1, (hsymp i j).2.1, (hsymp i j).2.2, if_neg hij,
                hsym (bB i) (aB j), (hsymp j i).2.2, if_neg (Ne.symm hij)]
              ring
          exact hlin s hi
        rw [hB_disj, add_zero]
        have hpair : f (α i • aB i + β i • bB i) + f 0 = α i * cB i + β i * dB i + α i * β i := by
          rw [hadd_f, hBsmulL, hBsmulR, (hsymp i i).2.2, if_pos rfl, mul_one]
          have ha : f (α i • aB i) + f 0 = α i * cB i := by
            rcases zmod2_cases (α i) with h0 | h1
            · rw [h0, zero_smul, zero_mul, zmod2_add_self]
            · rw [h1, one_smul, one_mul]
          have hb : f (β i • bB i) + f 0 = β i * dB i := by
            rcases zmod2_cases (β i) with h0 | h1
            · rw [h0, zero_smul, zero_mul, zmod2_add_self]
            · rw [h1, one_smul, one_mul]
          have e : f (α i • aB i) + f (β i • bB i) + f 0 + α i * β i + f 0 =
              (f (α i • aB i) + f 0) + (f (β i • bB i) + f 0) + α i * β i := by ring
          rw [e, ha, hb]
        have e : f (α i • aB i + β i • bB i) + f (∑ j ∈ s, (α j • aB j + β j • bB j)) + f 0 + f 0 =
            (f (α i • aB i + β i • bB i) + f 0) + (f (∑ j ∈ s, (α j • aB j + β j • bB j)) + f 0) := by
          have e1 : (f (α i • aB i + β i • bB i) + f 0) + (f (∑ j ∈ s, (α j • aB j + β j • bB j)) + f 0) =
              f (α i • aB i + β i • bB i) + f (∑ j ∈ s, (α j • aB j + β j • bB j)) + f 0 + f 0 := by ring
          exact e1.symm
        rw [e, hpair, ih]
    change f (r.1 + ∑ i : Fin m, (α i • aB i + β i • bB i)) = _
    rw [hadd_f, r.2, add_zero]
    have hfull := hsum_f Finset.univ
    have he1 : f r.1 + f (∑ i : Fin m, (α i • aB i + β i • bB i)) + f 0 =
        f 0 + (f r.1 + f 0) + (f (∑ i : Fin m, (α i • aB i + β i • bB i)) + f 0) := by
      have e : f 0 + (f r.1 + f 0) + (f (∑ i : Fin m, (α i • aB i + β i • bB i)) + f 0) =
          f r.1 + f (∑ i : Fin m, (α i • aB i + β i • bB i)) + f 0 + (f 0 + f 0) := by ring
      rw [e, zmod2_add_self, add_zero]
    rw [he1, hfull]
    change f 0 + lamR r + ∑ i : Fin m, (α i * cB i + β i * dB i + α i * β i) =
      (f 0 + ∑ i : Fin m, cB i * dB i) + lamR r + ∑ i : Fin m, (α i + dB i) * (β i + cB i)
    have hsum_eq : (∑ i : Fin m, (α i + dB i) * (β i + cB i)) =
        (∑ i : Fin m, cB i * dB i) + ∑ i : Fin m, (α i * cB i + β i * dB i + α i * β i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsum_eq]
    have e2 : f 0 + ∑ i : Fin m, cB i * dB i + lamR r +
        ((∑ i : Fin m, cB i * dB i) + ∑ i : Fin m, (α i * cB i + β i * dB i + α i * β i)) =
        f 0 + lamR r + ∑ i : Fin m, (α i * cB i + β i * dB i + α i * β i) +
        ((∑ i : Fin m, cB i * dB i) + ∑ i : Fin m, cB i * dB i) := by ring
    rw [e2, zmod2_add_self, add_zero]
  have : Fintype ↥Rad := Fintype.ofFinite _
  have hcardR : Fintype.card ↥Rad = 2 ^ (n - 2 * m) := by
    rw [← Nat.card_eq_fintype_card, nat_card_subspace]
    congr 1; omega
  have htotal_eq : (∑ x : Fin n → ZMod 2, chi (f x)) =
      if (∀ r : ↥Rad, lamR r = 0) then chi c₁ * (2 ^ (n - m) : ℤ) else 0 := by
    rw [← Equiv.sum_comp hcoordE.symm.toEquiv]
    dsimp only [LinearEquiv.coe_toEquiv]
    rw [Fintype.sum_prod_type]
    have h1 : ∀ (ab : (Fin m → ZMod 2) × (Fin m → ZMod 2)) (r : ↥Rad),
        chi (f (hcoordE.symm (ab, r))) =
        chi c₁ * chi (∑ i : Fin m, (ab.1 i + dB i) * (ab.2 i + cB i)) * chi (lamR r) := by
      intro ab r
      rw [hf_normal ab.1 ab.2 r, chi_add, chi_add]
      ring
    simp_rw [h1, ← Finset.mul_sum, sum_chi_linear lamR lamR.map_add]
    by_cases hlam : ∀ r : ↥Rad, lamR r = 0
    · rw [if_pos hlam, if_pos hlam]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      let shift : ((Fin m → ZMod 2) × (Fin m → ZMod 2)) ≃ ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
        { toFun := fun ab => (ab.1 + dB, ab.2 + cB)
          invFun := fun ab => (ab.1 + dB, ab.2 + cB)
          left_inv := fun ab => Prod.ext (by funext i; simp [add_assoc, zmod2_add_self])
            (by funext i; simp [add_assoc, zmod2_add_self])
          right_inv := fun ab => Prod.ext (by funext i; simp [add_assoc, zmod2_add_self])
            (by funext i; simp [add_assoc, zmod2_add_self]) }
      have hsum_ab : (∑ ab : (Fin m → ZMod 2) × (Fin m → ZMod 2),
          chi (∑ i : Fin m, (ab.1 i + dB i) * (ab.2 i + cB i))) = (2 ^ m : ℤ) := by
        rw [← Equiv.sum_comp shift.symm]
        have h2 : ∀ ab : (Fin m → ZMod 2) × (Fin m → ZMod 2),
            (shift.symm ab).1 = ab.1 + dB ∧ (shift.symm ab).2 = ab.2 + cB := fun _ => ⟨rfl, rfl⟩
        have h3 : ∀ ab : (Fin m → ZMod 2) × (Fin m → ZMod 2),
            (∑ i : Fin m, ((shift.symm ab).1 i + dB i) * ((shift.symm ab).2 i + cB i)) =
            ∑ i : Fin m, ab.1 i * ab.2 i := by
          intro ab
          refine Finset.sum_congr rfl (fun i _ => ?_)
          change (ab.1 i + dB i + dB i) * (ab.2 i + cB i + cB i) = ab.1 i * ab.2 i
          rw [add_assoc, zmod2_add_self, add_zero, add_assoc, zmod2_add_self, add_zero]
        simp_rw [h3]
        exact sum_chi_inner_prod m
      rw [hsum_ab, hcardR]
      push_cast
      rw [mul_assoc, ← pow_add]
      congr 2
      omega
    · rw [if_neg hlam, if_neg hlam]; simp
  have hcharge_eq : ∀ P : (Fin n → ZMod 2) → Prop,
      (Nat.card {x : Fin n → ZMod 2 // P x ∧ f x = 0} : ℤ) -
      (Nat.card {x : Fin n → ZMod 2 // P x ∧ f x = 1} : ℤ) =
      ∑ x ∈ Finset.univ.filter P, chi (f x) := by
    intro P
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]
    have hsplit : (∑ x ∈ Finset.univ.filter P, chi (f x)) =
        (∑ x ∈ (Finset.univ.filter P).filter (fun x => f x = 0), (1 : ℤ)) +
        (∑ x ∈ (Finset.univ.filter P).filter (fun x => f x ≠ 0), (-1 : ℤ)) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter P) (fun x => f x = 0)]
      congr 1
      · refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [(Finset.mem_filter.mp hx).2]; rfl
      · refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [zmod2_eq_one_of_ne_zero (Finset.mem_filter.mp hx).2]; rfl
    rw [hsplit]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg, Finset.filter_filter]
    have h1 : Finset.univ.filter (fun x => P x ∧ f x ≠ 0) =
        Finset.univ.filter (fun x => P x ∧ f x = 1) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun ⟨hP, hne⟩ => ⟨hP, zmod2_eq_one_of_ne_zero hne⟩
      · exact fun ⟨hP, h1⟩ => ⟨hP, h1 ▸ one_ne_zero⟩
    rw [h1]
    ring
  have hbal_iff : (Nat.card {x : Fin n → ZMod 2 // f x = 0} =
      Nat.card {x : Fin n → ZMod 2 // f x = 1}) ↔ ¬ (∀ r : ↥Rad, lamR r = 0) := by
    have h1 := hcharge_eq (fun _ => True)
    simp only [true_and, Finset.filter_true] at h1
    rw [htotal_eq] at h1
    constructor
    · intro hbal hlam
      rw [hbal, sub_self, if_pos hlam] at h1
      have hne : chi c₁ * (2 ^ (n - m) : ℤ) ≠ 0 := by
        apply mul_ne_zero
        · have h1 : ∀ c : ZMod 2, chi c ≠ 0 := by intro c; rcases zmod2_cases c with rfl | rfl <;> decide
          exact h1 c₁
        · positivity
      exact hne h1.symm
    · intro hnot
      rw [if_neg hnot] at h1
      omega
  have hW_bound : ∀ α : Fin n → ZMod 2,
      |∑ x : Fin n → ZMod 2, chi (f x + dotProduct α x)| ≤ (2 ^ (n - m) : ℤ) := by
    intro α
    let fα : (Fin n → ZMod 2) → ZMod 2 := fun x => f x + dotProduct α x
    have hfα : ∀ p u v : Fin n → ZMod 2,
        fα (p + u + v) + fα (p + u) + fα (p + v) + fα p = fα (u + v) + fα u + fα v + fα 0 := by
      intro p u v
      dsimp only [fα]
      simp only [dotProduct_add, dotProduct_zero]
      have h1 := hf p u v
      have hl : (f (p + u + v) + (α ⬝ᵥ p + α ⬝ᵥ u + α ⬝ᵥ v)) + (f (p + u) + (α ⬝ᵥ p + α ⬝ᵥ u)) +
          (f (p + v) + (α ⬝ᵥ p + α ⬝ᵥ v)) + (f p + α ⬝ᵥ p) =
          (f (p + u + v) + f (p + u) + f (p + v) + f p) +
          (((α ⬝ᵥ p + α ⬝ᵥ p) + (α ⬝ᵥ p + α ⬝ᵥ p)) +
            ((α ⬝ᵥ u + α ⬝ᵥ u) + (α ⬝ᵥ v + α ⬝ᵥ v))) := by ring
      have hr : (f (u + v) + (α ⬝ᵥ u + α ⬝ᵥ v)) + (f u + α ⬝ᵥ u) + (f v + α ⬝ᵥ v) + (f 0 + 0) =
          (f (u + v) + f u + f v + f 0) + ((α ⬝ᵥ u + α ⬝ᵥ u) + (α ⬝ᵥ v + α ⬝ᵥ v)) := by ring
      rw [hl, hr, h1, zmod2_add_self, zmod2_add_self, zmod2_add_self]
      ring
    have hBα : ∀ u v, fα (u + v) + fα u + fα v + fα 0 = quadB f u v := by
      intro u v
      dsimp only [fα, quadB]
      simp only [dotProduct_add, dotProduct_zero]
      have e : (f (u + v) + (α ⬝ᵥ u + α ⬝ᵥ v)) + (f u + α ⬝ᵥ u) + (f v + α ⬝ᵥ v) + (f 0 + 0) =
          (f (u + v) + f u + f v + f 0) + ((α ⬝ᵥ u + α ⬝ᵥ u) + (α ⬝ᵥ v + α ⬝ᵥ v)) := by ring
      rw [e, zmod2_add_self, zmod2_add_self, add_zero, add_zero]
    have hsq : (∑ x : Fin n → ZMod 2, chi (fα x)) * (∑ x : Fin n → ZMod 2, chi (fα x)) =
        ∑ u : Fin n → ZMod 2, chi (fα u + fα 0) * ∑ x : Fin n → ZMod 2, chi (quadB f x u) := by
      rw [Finset.sum_mul]
      have h1 : ∀ x : Fin n → ZMod 2, chi (fα x) * ∑ y : Fin n → ZMod 2, chi (fα y) =
          ∑ u : Fin n → ZMod 2, chi (fα u + fα 0) * chi (quadB f x u) := by
        intro x
        rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addLeft x)]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [← chi_add]
        change chi (fα x + fα (x + u)) = _
        have hfx : fα x + fα (x + u) = (fα u + fα 0) + quadB f x u := by
          rw [← hBα x u]
          have e : fα u + fα 0 + (fα (x + u) + fα x + fα u + fα 0) =
              fα x + fα (x + u) + ((fα u + fα u) + (fα 0 + fα 0)) := by ring
          rw [e, zmod2_add_self, zmod2_add_self, add_zero, add_zero]
        rw [hfx, chi_add]
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun u _ => (Finset.mul_sum _ _ _).symm)
    have hinner : ∀ u : Fin n → ZMod 2,
        (∑ x : Fin n → ZMod 2, chi (quadB f x u)) = if u ∈ Rad then (2 ^ n : ℤ) else 0 := by
      intro u
      let ℓ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
        { toFun := fun x => quadB f x u
          map_add' := fun x y => haddL x y u
          map_smul' := fun c x => hBsmulL c x u }
      have h1 := sum_chi_linear ℓ ℓ.map_add
      have hiff : (∀ x, ℓ x = 0) ↔ u ∈ Rad :=
        ⟨fun h v => by rw [hsym]; exact h v,
         fun h x => by change quadB f x u = 0; rw [hsym]; exact h x⟩
      have hcard : (Fintype.card (Fin n → ZMod 2) : ℤ) = (2 ^ n : ℤ) := by
        simp [ZMod.card 2]
      change (∑ x : Fin n → ZMod 2, chi (ℓ x)) = _
      rw [h1, hcard]
      by_cases hu : u ∈ Rad
      · rw [if_pos (hiff.mpr hu), if_pos hu]
      · rw [if_neg (fun h => hu (hiff.mp h)), if_neg hu]
    simp_rw [hinner] at hsq
    have hle : (∑ x : Fin n → ZMod 2, chi (fα x)) * (∑ x : Fin n → ZMod 2, chi (fα x)) ≤
        (2 ^ (n - m) : ℤ) * (2 ^ (n - m) : ℤ) := by
      rw [hsq]
      calc ∑ u : Fin n → ZMod 2, chi (fα u + fα 0) * (if u ∈ Rad then (2 ^ n : ℤ) else 0)
          ≤ ∑ u : Fin n → ZMod 2, (if u ∈ Rad then (2 ^ n : ℤ) else 0) := by
            refine Finset.sum_le_sum (fun u _ => ?_)
            by_cases hu : u ∈ Rad
            · rw [if_pos hu]
              have h1 : chi (fα u + fα 0) ≤ 1 := le_trans (le_abs_self _) (le_of_eq (chi_abs _))
              have hpos : (0 : ℤ) ≤ 2 ^ n := by positivity
              nlinarith
            · rw [if_neg hu, mul_zero]
        _ = (Fintype.card ↥Rad : ℤ) * (2 ^ n : ℤ) := by
            rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
            congr 1
            rw [Fintype.card_subtype]
        _ = (2 ^ (n - m) : ℤ) * (2 ^ (n - m) : ℤ) := by
            rw [hcardR]
            push_cast
            rw [← pow_add, ← pow_add]
            congr 1
            omega
    have hpos : (0 : ℤ) ≤ 2 ^ (n - m) := by positivity
    nlinarith [sq_abs (∑ x : Fin n → ZMod 2, chi (fα x))]
  have hflat_avg : ∀ (a : Fin n → ZMod 2) (S : Submodule (ZMod 2) (Fin n → ZMod 2)),
      (Nat.card ↥(perpSub S) : ℤ) * (∑ x ∈ Finset.univ.filter (fun x => x - a ∈ S), chi (f x)) =
      ∑ α ∈ Finset.univ.filter (fun α => α ∈ perpSub S),
        chi (dotProduct α a) * (∑ x : Fin n → ZMod 2, chi (f x + dotProduct α x)) := by
    intro a S
    have : Fintype ↥(perpSub S) := Fintype.ofFinite _
    have h1 : (∑ α ∈ Finset.univ.filter (fun α => α ∈ perpSub S),
        chi (dotProduct α a) * (∑ x : Fin n → ZMod 2, chi (f x + dotProduct α x))) =
        ∑ x : Fin n → ZMod 2, chi (f x) *
          ∑ α : ↥(perpSub S), chi (dotProduct α.1 (x + a)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      refine Finset.sum_bij (fun α hα => ⟨α, (Finset.mem_filter.mp hα).2⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro _ _ _ _ h; exact congrArg Subtype.val h
      · intro α _; exact ⟨α.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, α.2⟩, rfl⟩
      · intro α _
        rw [dotProduct_add, chi_add, chi_add]
        ring
    rw [h1]
    have h2 : ∀ x : Fin n → ZMod 2,
        (∑ α : ↥(perpSub S), chi (dotProduct α.1 (x + a))) =
        if x - a ∈ S then (Nat.card ↥(perpSub S) : ℤ) else 0 := by
      intro x
      let ℓ : ↥(perpSub S) →ₗ[ZMod 2] ZMod 2 :=
        { toFun := fun α => dotProduct α.1 (x + a)
          map_add' := fun α₁ α₂ => add_dotProduct α₁.1 α₂.1 (x + a)
          map_smul' := fun c α => by
            change dotProduct (c • α.1) (x + a) = c • dotProduct α.1 (x + a)
            rw [smul_dotProduct] }
      have hlin := sum_chi_linear ℓ ℓ.map_add
      have hiff : (∀ α : ↥(perpSub S), ℓ α = 0) ↔ x - a ∈ S := by
        have hsub : x - a = x + a := by funext i; exact zmod2_sub_eq_add (x i) (a i)
        rw [hsub]
        conv_rhs => rw [← perpSub_perpSub S]
        constructor
        · intro h α hα; rw [dotProduct_comm]; exact h ⟨α, hα⟩
        · intro h α; change dotProduct α.1 (x + a) = 0; rw [dotProduct_comm]; exact h α.1 α.2
      change (∑ α : ↥(perpSub S), chi (ℓ α)) = _
      rw [hlin, Nat.card_eq_fintype_card]
      by_cases hx : x - a ∈ S
      · rw [if_pos (hiff.mpr hx), if_pos hx]
      · rw [if_neg (fun h => hx (hiff.mp h)), if_neg hx]
    simp_rw [h2]
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    split_ifs <;> ring
  have h450 : ∀ (a : Fin n → ZMod 2) (S : Submodule (ZMod 2) (Fin n → ZMod 2)),
      let va : ℤ := ∑ x ∈ Finset.univ.filter (fun x => x - a ∈ S), chi (f x)
      (|va| ≤ (2 ^ (n - m) : ℤ)) ∧
      ((2 ^ (n - m) : ℤ) < 2 * |va| →
        |va| = (2 ^ (n - m) : ℤ) ∧
        va = (∑ x : Fin n → ZMod 2, chi (f x)) ∧
        ∀ (b : Fin n → ZMod 2) (T : Submodule (ZMod 2) (Fin n → ZMod 2)),
          let vb : ℤ := ∑ x ∈ Finset.univ.filter (fun x => x - b ∈ T), chi (f x)
          (2 ^ (n - m) : ℤ) < 2 * |vb| → ∃ x : Fin n → ZMod 2, x - a ∈ S ∧ x - b ∈ T) := by
    intro a S va
    have hcardP_pos : (0 : ℤ) < (Nat.card ↥(perpSub S) : ℤ) := by
      rw [nat_card_subspace]; positivity
    have hcardP_eq : ((Finset.univ.filter (fun α : Fin n → ZMod 2 => α ∈ perpSub S)).card : ℤ) =
        (Nat.card ↥(perpSub S) : ℤ) := by
      have : Fintype ↥(perpSub S) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hleC : |va| ≤ (2 ^ (n - m) : ℤ) := by
      have h1 : (Nat.card ↥(perpSub S) : ℤ) * |va| ≤
          (Nat.card ↥(perpSub S) : ℤ) * (2 ^ (n - m) : ℤ) := by
        calc (Nat.card ↥(perpSub S) : ℤ) * |va|
            = |(Nat.card ↥(perpSub S) : ℤ) * va| := by
              rw [abs_mul, abs_of_pos hcardP_pos]
          _ = |∑ α ∈ Finset.univ.filter (fun α => α ∈ perpSub S),
                chi (dotProduct α a) * (∑ x : Fin n → ZMod 2, chi (f x + dotProduct α x))| := by
              rw [hflat_avg a S]
          _ ≤ ∑ α ∈ Finset.univ.filter (fun α => α ∈ perpSub S),
                |chi (dotProduct α a) * (∑ x : Fin n → ZMod 2, chi (f x + dotProduct α x))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _α ∈ Finset.univ.filter (fun α => α ∈ perpSub S), (2 ^ (n - m) : ℤ) := by
              refine Finset.sum_le_sum (fun α _ => ?_)
              rw [abs_mul, chi_abs, one_mul]
              exact hW_bound α
          _ = (Nat.card ↥(perpSub S) : ℤ) * (2 ^ (n - m) : ℤ) := by
              rw [Finset.sum_const, nsmul_eq_mul, hcardP_eq]
      exact le_of_mul_le_mul_left h1 hcardP_pos
    have hlarge_props : ∀ (a₀ : Fin n → ZMod 2) (S₀ : Submodule (ZMod 2) (Fin n → ZMod 2)),
        let v₀ : ℤ := ∑ x ∈ Finset.univ.filter (fun x => x - a₀ ∈ S₀), chi (f x)
        (2 ^ (n - m) : ℤ) < 2 * |v₀| →
        |v₀| = (2 ^ (n - m) : ℤ) ∧
        ∀ α ∈ perpSub S₀,
          chi (dotProduct α a₀) * (∑ x : Fin n → ZMod 2, chi (f x + dotProduct α x)) = v₀ := by
      intro a₀ S₀ v₀ hbig
      have : Fintype ↥S₀ := Fintype.ofFinite _
      have hv₀_eq : v₀ = ∑ x : ↥S₀, chi (f (a₀ + x.1)) := by
        dsimp only [v₀]
        refine Finset.sum_bij (fun x hx => ⟨x - a₀, (Finset.mem_filter.mp hx).2⟩) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro x₁ _ x₂ _ h
          have h1 : x₁ - a₀ = x₂ - a₀ := congrArg Subtype.val h
          exact sub_left_inj.mp h1
        · intro u _
          refine ⟨a₀ + u.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [u.2]⟩, ?_⟩
          apply Subtype.ext; simp
        · intro x _
          congr 1
          have : a₀ + (x - a₀) = x := by abel
          rw [this]
      have hpow := flat_charge_pow2 hf a₀ S₀
      rw [← hv₀_eq] at hpow
      have hcardP0_pos : (0 : ℤ) < (Nat.card ↥(perpSub S₀) : ℤ) := by
        rw [nat_card_subspace]; positivity
      have hcardP0_eq : ((Finset.univ.filter (fun α : Fin n → ZMod 2 => α ∈ perpSub S₀)).card : ℤ) =
          (Nat.card ↥(perpSub S₀) : ℤ) := by
        have : Fintype ↥(perpSub S₀) := Fintype.ofFinite _
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      have hleC0 : |v₀| ≤ (2 ^ (n - m) : ℤ) := by
        have h1 : (Nat.card ↥(perpSub S₀) : ℤ) * |v₀| ≤
            (Nat.card ↥(perpSub S₀) : ℤ) * (2 ^ (n - m) : ℤ) := by
          calc (Nat.card ↥(perpSub S₀) : ℤ) * |v₀|
              = |(Nat.card ↥(perpSub S₀) : ℤ) * v₀| := by rw [abs_mul, abs_of_pos hcardP0_pos]
            _ = |∑ α ∈ Finset.univ.filter (fun α => α ∈ perpSub S₀),
                  chi (dotProduct α a₀) * (∑ x : Fin n → ZMod 2, chi (f x + dotProduct α x))| := by
                rw [hflat_avg a₀ S₀]
            _ ≤ ∑ α ∈ Finset.univ.filter (fun α => α ∈ perpSub S₀),
                  |chi (dotProduct α a₀) * (∑ x : Fin n → ZMod 2, chi (f x + dotProduct α x))| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _α ∈ Finset.univ.filter (fun α => α ∈ perpSub S₀), (2 ^ (n - m) : ℤ) := by
                refine Finset.sum_le_sum (fun α _ => ?_)
                rw [abs_mul, chi_abs, one_mul]; exact hW_bound α
            _ = (Nat.card ↥(perpSub S₀) : ℤ) * (2 ^ (n - m) : ℤ) := by
                rw [Finset.sum_const, nsmul_eq_mul, hcardP0_eq]
        exact le_of_mul_le_mul_left h1 hcardP0_pos
      have habs_eq : |v₀| = (2 ^ (n - m) : ℤ) := by
        rcases hpow with h0 | ⟨r, hr⟩
        · rw [h0, abs_zero, mul_zero] at hbig
          have hpos : (0 : ℤ) < 2 ^ (n - m) := by positivity
          linarith
        · have hv_abs : |v₀| = (2 ^ r : ℤ) := by
            rw [← Int.natCast_natAbs, hr]; push_cast; rfl
          rw [hv_abs] at hbig hleC0 ⊢
          have hr_le : r ≤ n - m := by
            by_contra hgt
            have h1 : (2 : ℤ) ^ (n - m) < (2 : ℤ) ^ r := by
              exact_mod_cast Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega : n - m < r)
            linarith
          have hr_ge : n - m ≤ r := by
            by_contra hlt
            have h1 : 2 * (2 : ℤ) ^ r ≤ (2 : ℤ) ^ (n - m) := by
              rw [mul_comm, ← pow_succ]
              exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : r + 1 ≤ n - m)
            linarith
          have hr_eq : r = n - m := by omega
          rw [hr_eq]
      refine ⟨habs_eq, fun α hα => ?_⟩
      have hterm_bound : ∀ β ∈ Finset.univ.filter (fun α : Fin n → ZMod 2 => α ∈ perpSub S₀),
          |chi (dotProduct β a₀) * (∑ x : Fin n → ZMod 2, chi (f x + dotProduct β x))| ≤
          (2 ^ (n - m) : ℤ) := by
        intro β _
        rw [abs_mul, chi_abs, one_mul]
        exact hW_bound β
      have havg := hflat_avg a₀ S₀
      rw [← hcardP0_eq] at havg
      change ((Finset.univ.filter (fun α : Fin n → ZMod 2 => α ∈ perpSub S₀)).card : ℤ) * v₀ = _ at havg
      rcases eq_or_eq_neg_of_abs_eq habs_eq with hpos | hneg
      · rw [hpos] at havg ⊢
        exact sum_eq_card_mul_bound _ _ (2 ^ (n - m) : ℤ) hterm_bound havg.symm α
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα⟩)
      · rw [hneg] at havg ⊢
        have havg' : (∑ β ∈ Finset.univ.filter (fun α : Fin n → ZMod 2 => α ∈ perpSub S₀),
            chi (dotProduct β a₀) * (∑ x : Fin n → ZMod 2, chi (f x + dotProduct β x))) =
            -(((Finset.univ.filter (fun α : Fin n → ZMod 2 => α ∈ perpSub S₀)).card : ℤ) *
              (2 ^ (n - m) : ℤ)) := by linarith
        exact sum_eq_neg_card_mul_bound _ _ (2 ^ (n - m) : ℤ) hterm_bound havg' α
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα⟩)
    refine ⟨hleC, fun hbig => ?_⟩
    obtain ⟨habs_a, hall_a⟩ := hlarge_props a S hbig
    have hva_eq_tot : va = ∑ x : Fin n → ZMod 2, chi (f x) := by
      have h0 := hall_a 0 (perpSub S).zero_mem
      simp only [zero_dotProduct, chi_zero, one_mul, add_zero] at h0
      exact h0.symm
    refine ⟨habs_a, hva_eq_tot, fun b T hbig_b => ?_⟩
    let vb : ℤ := ∑ x ∈ Finset.univ.filter (fun x => x - b ∈ T), chi (f x)
    obtain ⟨_, hall_b⟩ := hlarge_props b T hbig_b
    have hvb_eq_tot : vb = ∑ x : Fin n → ZMod 2, chi (f x) := by
      have h0 := hall_b 0 (perpSub T).zero_mem
      simp only [zero_dotProduct, chi_zero, one_mul, add_zero] at h0
      exact h0.symm
    have hba_mem : b - a ∈ S ⊔ T := by
      rw [← perpSub_perpSub (S ⊔ T)]
      intro α hα
      have hαS : α ∈ perpSub S := fun u hu => hα u (Submodule.mem_sup_left hu)
      have hαT : α ∈ perpSub T := fun v hv => hα v (Submodule.mem_sup_right hv)
      have ea := hall_a α hαS
      have eb := hall_b α hαT
      change _ = va at ea
      change _ = vb at eb
      rw [hva_eq_tot] at ea
      rw [hvb_eq_tot] at eb
      have htot_ne : (∑ x : Fin n → ZMod 2, chi (f x)) ≠ 0 := by
        rw [← hva_eq_tot]
        intro h0
        change |va| = _ at habs_a
        rw [h0, abs_zero] at habs_a
        have hpos : (0 : ℤ) < 2 ^ (n - m) := by positivity
        linarith
      have hW_ne : (∑ x : Fin n → ZMod 2, chi (f x + dotProduct α x)) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at ea; exact htot_ne ea.symm
      have hchi_eq : chi (dotProduct α a) = chi (dotProduct α b) :=
        mul_right_cancel₀ hW_ne (ea.trans eb.symm)
      have hdot_eq : dotProduct α a = dotProduct α b := chi_inj hchi_eq
      rw [dotProduct_comm, dotProduct_sub, hdot_eq, sub_self]
    rcases Submodule.mem_sup.mp hba_mem with ⟨u, hu, v, hv, huv⟩
    refine ⟨a + u, by simp [hu], ?_⟩
    have hxv : a + u - b = -v := by
      have h1 : b - a = u + v := huv.symm
      funext i
      have h1i : b i - a i = u i + v i := congrFun h1 i
      change a i + u i - b i = -(v i)
      rw [zmod2_sub_eq_add] at h1i ⊢
      have hneg : -(v i) = v i := by
        rcases zmod2_cases (v i) with h | h <;> rw [h] <;> decide
      rw [hneg]
      have h2 : a i + u i + b i = (b i + a i) + u i := by ring
      rw [h2, h1i]
      have h3 : u i + v i + u i = v i + (u i + u i) := by ring
      rw [h3, zmod2_add_self, add_zero]
    rw [hxv]
    exact T.neg_mem hv
  have htree_to_aff := tree_to_aff_aux n f L H
  have haff_to_bound := aff_to_bound_aux n m f L H Rad c₁ lamR hcardX hcardX_split (by convert htotal_eq) hbal_iff (by convert h450)
  have hbound_to_tree :
      2 * 2 ^ m * H ≤
        Nat.card (Fin n → ZMod 2) *
          (2 ^ m + min (2 ^ m)
            (if Nat.card {x : Fin n → ZMod 2 // f x = 0} = Nat.card {x : Fin n → ZMod 2 // f x = 1}
              then L / 2 else (L + 1) / 2)) →
      ∃ (N J : Finset (List Bool))
        (q : List Bool → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (offset out : List Bool → ZMod 2),
        [] ∈ N ∧ J ⊆ N ∧
        (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
        (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
        (N \ J).card ≤ L ∧ H ≤ Nat.card {x : Fin n → ZMod 2 // ∃ p ∈ N \ J,
          (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step)
          ∧ f x = out p} := by
    intro hbound
    set t := min (2 ^ m)
      (if Nat.card {x : Fin n → ZMod 2 // f x = 0} = Nat.card {x : Fin n → ZMod 2 // f x = 1}
        then L / 2 else (L + 1) / 2)
    have hH_from_hits : ∀ hits : ℕ, (2 ^ n : ℤ) + (t : ℤ) * (2 ^ (n - m) : ℤ) ≤ 2 * (hits : ℤ) →
        H ≤ hits := by
      intro hits hge
      have hpos : (0 : ℤ) < 2 * (2 ^ m : ℤ) := by positivity
      have hZ : (2 * (2 ^ m : ℤ)) * (H : ℤ) ≤ (2 * (2 ^ m : ℤ)) * (hits : ℤ) := by
        have h1 : ((2 * 2 ^ m * H : ℕ) : ℤ) ≤ ((Nat.card (Fin n → ZMod 2) * (2 ^ m + t) : ℕ) : ℤ) := by
          exact_mod_cast hbound
        rw [hcardX] at h1
        push_cast at h1
        have hsplitZ : (2 ^ m : ℤ) * (2 ^ (n - m) : ℤ) = (2 ^ n : ℤ) := by exact_mod_cast hcardX_split
        have hr : (2 ^ n : ℤ) * ((2 ^ m : ℤ) + (t : ℤ)) =
            (2 ^ m : ℤ) * ((2 ^ n : ℤ) + (t : ℤ) * (2 ^ (n - m) : ℤ)) := by
          calc (2 ^ n : ℤ) * ((2 ^ m : ℤ) + (t : ℤ))
              = (2 ^ m : ℤ) * (2 ^ n : ℤ) + (t : ℤ) * (2 ^ n : ℤ) := by ring
            _ = (2 ^ m : ℤ) * (2 ^ n : ℤ) + (t : ℤ) * ((2 ^ m : ℤ) * (2 ^ (n - m) : ℤ)) := by rw [← hsplitZ]
            _ = (2 ^ m : ℤ) * ((2 ^ n : ℤ) + (t : ℤ) * (2 ^ (n - m) : ℤ)) := by ring
        have hmul : (2 ^ m : ℤ) * ((2 ^ n : ℤ) + (t : ℤ) * (2 ^ (n - m) : ℤ)) ≤
            (2 ^ m : ℤ) * (2 * (hits : ℤ)) :=
          mul_le_mul_of_nonneg_left hge (by positivity)
        have hl1 : 2 * (2 ^ m : ℤ) * (H : ℤ) = (2 * (2 ^ m : ℤ)) * (H : ℤ) := by ring
        have hr1 : (2 ^ m : ℤ) * (2 * (hits : ℤ)) = (2 * (2 ^ m : ℤ)) * (hits : ℤ) := by ring
        linarith only [h1, hr, hmul, hl1, hr1]
      exact_mod_cast le_of_mul_le_mul_left hZ hpos
    by_cases ht0 : t = 0
    · refine ⟨{[]}, ∅, fun _ => 0, fun _ => 0, fun _ => 0,
        Finset.mem_singleton_self _, Finset.empty_subset _, fun p b hp => by
          simp at hp, fun p hp => by simp at hp, by simp; omega, ?_⟩
      apply hH_from_hits
      rw [ht0]
      simp only [Nat.cast_zero, zero_mul, add_zero]
      have hbal : Nat.card {x : Fin n → ZMod 2 // f x = 0} =
          Nat.card {x : Fin n → ZMod 2 // f x = 1} := by
        by_contra hnot
        have h1 : 1 ≤ (L + 1) / 2 := by omega
        have h2 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by omega)
        have h3 : 1 ≤ t := by dsimp only [t]; rw [if_neg hnot]; exact le_min h2 h1
        omega
      have hsum_card : Nat.card {x : Fin n → ZMod 2 // f x = 0} +
          Nat.card {x : Fin n → ZMod 2 // f x = 1} = 2 ^ n := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
          Fintype.card_subtype]
        have h1 : Finset.univ.filter (fun x : Fin n → ZMod 2 => f x = 1) =
            Finset.univ.filter (fun x : Fin n → ZMod 2 => ¬ (f x = 0)) := by
          ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => h ▸ one_ne_zero, zmod2_eq_one_of_ne_zero⟩
        rw [h1, Finset.card_filter_add_card_filter_not]
        simp [ZMod.card 2]
      have hhit_eq : Nat.card {x : Fin n → ZMod 2 // ∃ p ∈ ({[]} : Finset (List Bool)) \ ∅,
          (∀ step : Fin p.length, decide ((0 : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) x = 0) = p.get step) ∧
          f x = 0} = Nat.card {x : Fin n → ZMod 2 // f x = 0} := by
        apply Nat.card_congr
        refine Equiv.subtypeEquivRight (fun x => by simp)
      rw [hhit_eq]
      have hnat : 2 ^ n ≤ 2 * Nat.card {x : Fin n → ZMod 2 // f x = 0} := by omega
      exact_mod_cast hnat
    · have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
      have htm : t ≤ 2 ^ m := min_le_left _ _
      by_cases hbal : Nat.card {x : Fin n → ZMod 2 // f x = 0} =
          Nat.card {x : Fin n → ZMod 2 // f x = 1}
      · have hlam_ne : ∃ r₀ : ↥Rad, lamR r₀ = 1 := by
          have hnot := hbal_iff.mp hbal
          by_contra hno
          apply hnot
          intro r
          by_contra hr
          exact hno ⟨r, zmod2_eq_one_of_ne_zero hr⟩
        rcases hlam_ne with ⟨r₀, hr₀⟩
        have h2t_le : 2 * t ≤ L := by
          have htL : t ≤ L / 2 := by
            dsimp only [t]; rw [if_pos hbal]; exact min_le_right _ _
          omega
        exact bound_to_tree_bal n m L H t f Rad hdim_symp hcoordE cB dB c₁ lamR hf_normal
          ht1 htm h2t_le r₀ hr₀ hH_from_hits
      · have hlam0 : ∀ r : ↥Rad, lamR r = 0 := by
          by_contra hnot; exact hbal (hbal_iff.mpr hnot)
        have h2t_le : 2 * t - 1 ≤ L := by
          have htL : t ≤ (L + 1) / 2 := by
            dsimp only [t]; rw [if_neg hbal]; exact min_le_right _ _
          omega
        exact bound_to_tree_imbal n m L H t f Rad hdim_symp hcoordE cB dB c₁ lamR hf_normal
          ht1 htm h2t_le hlam0 hH_from_hits
  exact ⟨⟨haff_to_bound, fun h => htree_to_aff (hbound_to_tree h)⟩,
    ⟨fun h => haff_to_bound (htree_to_aff h), hbound_to_tree⟩⟩

end PEqualNP.Outside.L_pcx_451_aux

theorem PEqualNP.Outside.L_pcx_451 :
  ∀ (n : ℕ),
    let F := ZMod 2
    let X := Fin n → F
    ∀ f : X → F,
      let B := fun u v : X => f (u+v)+f u+f v+f 0
      (∀ p u v : X, f (p+u+v)+f (p+u)+f (p+v)+f p=B u v) →
      let m := (n-(Nat.card {u : X // ∀ v : X, B u v=0}).log2)/2
      let bal := Nat.card {x : X // f x=0} = Nat.card {x : X // f x=1}
      ∀ L H : ℕ, 0<L →
        let K := 2^m
        let t := min K (if bal then L/2 else (L+1)/2)
        let bound := 2*K*H ≤ Nat.card X * (K+t)
        let affineCan := ∃ k : ℕ, k ≤ L ∧
          ∃ (a : Fin k → X) (S : Fin k → Submodule F X) (out : Fin k → F),
            (∀ x : X, ∃! j : Fin k, x-a j ∈ S j) ∧
            H ≤ Nat.card {x : X // ∃ j, x-a j ∈ S j ∧ f x=out j}
        let treeCan := ∃ (N J : Finset (List Bool))
          (q : List Bool → X →ₗ[F] F) (offset out : List Bool → F),
          [] ∈ N ∧ J ⊆ N ∧
          (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
          (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
          (N \ J).card ≤ L ∧ H ≤ Nat.card {x : X // ∃ p ∈ N \ J,
            (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step)
            ∧ f x=out p}
        (affineCan ↔ bound) ∧ (treeCan ↔ bound) := by
  intro n
  dsimp only
  intro f hf L H hL
  exact PEqualNP.Outside.L_pcx_451_aux.main_proof n f hf L H hL

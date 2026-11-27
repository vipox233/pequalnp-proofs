import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25694_aux

private abbrev B := ZMod 2

private def sign (t : B) : ℤ := if t = 0 then 1 else -1

private theorem sign_add (a b : B) : sign (a + b) = sign a * sign b := by
  fin_cases a <;> fin_cases b <;> rfl

private theorem sign_zero : sign 0 = 1 := rfl

private theorem sign_one : sign 1 = -1 := rfl

private def mixOp (k : ℕ) [NeZero k] (s : ℕ) : (ZMod k → B) →ₗ[B] (ZMod k → B) where
  toFun x i := x (i - (s : ZMod k)) + x i + x (i + (s : ZMod k))
  map_add' x y := by funext i; simp only [Pi.add_apply]; ring
  map_smul' c x := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private def edgeOp (k : ℕ) [NeZero k] (b : ZMod k → B) : (ZMod k → B) →ₗ[B] (ZMod k → B) where
  toFun w i := b (i - 2) * w (i - 1) + b (i - 1) * w (i + 1)
  map_add' x y := by funext i; simp only [Pi.add_apply]; ring
  map_smul' c x := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private theorem mixOp_symm (k : ℕ) [NeZero k] (s : ℕ) (u v : ZMod k → B) :
    dotProduct u (mixOp k s v) = dotProduct (mixOp k s u) v := by
  unfold dotProduct
  simp only [mixOp, LinearMap.coe_mk, AddHom.coe_mk, mul_add, add_mul, Finset.sum_add_distrib]
  have h1 : ∑ i : ZMod k, u i * v (i - (s : ZMod k)) = ∑ i : ZMod k, u (i + (s : ZMod k)) * v i := by
    refine Fintype.sum_equiv (Equiv.subRight (s : ZMod k)) _ _ fun i => ?_
    simp [sub_add_cancel]
  have h2 : ∑ i : ZMod k, u i * v (i + (s : ZMod k)) = ∑ i : ZMod k, u (i - (s : ZMod k)) * v i := by
    refine Fintype.sum_equiv (Equiv.addRight (s : ZMod k)) _ _ fun i => ?_
    simp [add_sub_cancel_right]
  rw [h1, h2]
  ring

private theorem zmod2_cases (a : B) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem mixOp_zero (k : ℕ) [NeZero k] : mixOp k 0 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext i
  simp only [mixOp, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe, id_eq, Nat.cast_zero,
    sub_zero, add_zero]
  rcases zmod2_cases (x i) with h | h <;> rw [h] <;> rfl

private theorem zmod2_add_self (a : B) : a + a = 0 := by
  fin_cases a <;> rfl

private theorem nl_polar (k : ℕ) [NeZero k] (b y z : ZMod k → B) :
    let nl := fun (w : ZMod k → B) (j : ZMod k) => w j + (1 + w (j + 1)) * w (j + 2)
    dotProduct b (nl (y + z)) + dotProduct b (nl y) + dotProduct b (nl z) =
      dotProduct y (edgeOp k b z) := by
  intro nl
  unfold dotProduct
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hterm : ∀ j : ZMod k,
      b j * nl (y + z) j + b j * nl y j + b j * nl z j =
        b j * y (j + 1) * z (j + 2) + b j * z (j + 1) * y (j + 2) := by
    intro j
    simp only [nl, Pi.add_apply]
    have h2 : ∀ a : B, a + a = 0 := zmod2_add_self
    have hcalc : b j * (y j + z j + (1 + (y (j + 1) + z (j + 1))) * (y (j + 2) + z (j + 2))) +
        b j * (y j + (1 + y (j + 1)) * y (j + 2)) +
        b j * (z j + (1 + z (j + 1)) * z (j + 2)) =
        (b j * y j + b j * y j) + (b j * z j + b j * z j) +
        (b j * y (j + 2) + b j * y (j + 2)) + (b j * z (j + 2) + b j * z (j + 2)) +
        (b j * y (j + 1) * y (j + 2) + b j * y (j + 1) * y (j + 2)) +
        (b j * z (j + 1) * z (j + 2) + b j * z (j + 1) * z (j + 2)) +
        (b j * y (j + 1) * z (j + 2) + b j * z (j + 1) * y (j + 2)) := by ring
    rw [hcalc]
    simp only [h2, zero_add]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib]
  have h1 : ∑ j : ZMod k, b j * y (j + 1) * z (j + 2) = ∑ i : ZMod k, y i * (b (i - 1) * z (i + 1)) := by
    refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod k)) _ _ fun j => ?_
    change b j * y (j + 1) * z (j + 2) = y (j + 1) * (b (j + 1 - 1) * z (j + 1 + 1))
    rw [add_sub_cancel_right]
    have e2 : j + 1 + 1 = j + 2 := by ring
    rw [e2]; ring
  have h2 : ∑ j : ZMod k, b j * z (j + 1) * y (j + 2) = ∑ i : ZMod k, y i * (b (i - 2) * z (i - 1)) := by
    refine Fintype.sum_equiv (Equiv.addRight (2 : ZMod k)) _ _ fun j => ?_
    change b j * z (j + 1) * y (j + 2) = y (j + 2) * (b (j + 2 - 2) * z (j + 2 - 1))
    rw [add_sub_cancel_right]
    have e1 : j + 2 - 1 = j + 1 := by ring
    rw [e1]; ring
  rw [h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [edgeOp, LinearMap.coe_mk, AddHom.coe_mk]
  ring

private theorem sum_sign_dot (k : ℕ) [NeZero k] (v : ZMod k → B) :
    ∑ x : ZMod k → B, sign (dotProduct x v) = if v = 0 then (2 ^ k : ℤ) else 0 := by
  by_cases hv : v = 0
  · subst hv
    simp only [↓reduceIte, dotProduct_zero, sign_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, ZMod.card, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  · simp only [hv, ↓reduceIte]
    have hex : ∃ i : ZMod k, v i = 1 := by
      by_contra h
      apply hv
      funext i
      generalize hvi : v i = z
      fin_cases z
      · rfl
      · exact absurd ⟨i, hvi⟩ h
    obtain ⟨i0, hi0⟩ := hex
    let e : (ZMod k → B) := Pi.single i0 1
    have hed : dotProduct e v = 1 := by
      simp [e, dotProduct, Pi.single_apply, hi0]
    have hshift : ∑ x : ZMod k → B, sign (dotProduct x v) =
        ∑ x : ZMod k → B, sign (dotProduct (x + e) v) :=
      (Fintype.sum_equiv (Equiv.addRight e) _ _ (fun _ => rfl)).symm
    have hneg : ∑ x : ZMod k → B, sign (dotProduct (x + e) v) =
        - ∑ x : ZMod k → B, sign (dotProduct x v) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [add_dotProduct, hed, sign_add, sign_one]
      ring
    linarith

private theorem sum_sign_subspace {k : ℕ} [NeZero k] (K : Submodule B (ZMod k → B))
    [Fintype K] (w : ZMod k → B) [Decidable (∀ u ∈ K, dotProduct w u = 0)] :
    ∑ u : K, sign (dotProduct w u.val) =
      if ∀ u ∈ K, dotProduct w u = 0 then (Fintype.card K : ℤ) else 0 := by
  by_cases hall : ∀ u ∈ K, dotProduct w u = 0
  · rw [if_pos hall]
    have h1 : ∀ u : K, sign (dotProduct w u.val) = 1 := fun u => by rw [hall u.val u.property]; rfl
    simp [h1]
  · rw [if_neg hall]
    have hex : ∃ u0 : K, dotProduct w u0.val = 1 := by
      by_contra h
      apply hall
      intro u hu
      generalize hwu : dotProduct w u = z
      fin_cases z
      · rfl
      · exact absurd ⟨⟨u, hu⟩, hwu⟩ h
    obtain ⟨u0, hu0⟩ := hex
    have hshift : ∑ u : K, sign (dotProduct w u.val) = ∑ u : K, sign (dotProduct w (u + u0).val) :=
      (Fintype.sum_equiv (Equiv.addRight u0) _ _ (fun _ => rfl)).symm
    have hneg : ∑ u : K, sign (dotProduct w (u + u0).val) = - ∑ u : K, sign (dotProduct w u.val) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      change sign (dotProduct w (u.val + u0.val)) = _
      rw [dotProduct_add, hu0, sign_add, sign_one]
      ring
    linarith

private theorem walsh_support_char (k : ℕ) [NeZero k] (s : ℕ) (b : ZMod k → B) :
    let V := ZMod k → B
    let nl := fun (y : V) (j : ZMod k) => y j + (1 + y (j + 1)) * y (j + 2)
    let coeff := fun (a : V) => ∑ x : V, sign (dotProduct a x + dotProduct b (nl (mixOp k s x)))
    let L : V →ₗ[B] V := (mixOp k s).comp ((edgeOp k b).comp (mixOp k s))
    (∃ base : V, ∀ a : V, coeff a ≠ 0 ↔ ∃ u : V, a = base + L u) ∧
    (Finset.univ.filter (fun a : V => coeff a ≠ 0)).card = 2 ^ Module.finrank B (LinearMap.range L) := by
  intro V nl coeff L
  classical
  let f : V → B := fun x => dotProduct b (nl (mixOp k s x))
  have haddV : ∀ x : V, x + x = 0 := fun x => by funext i; exact zmod2_add_self (x i)
  have hf_polar : ∀ x u : V, f (x + u) + f x + f u = dotProduct x (L u) := by
    intro x u
    dsimp only [f, L, LinearMap.comp_apply]
    rw [map_add, nl_polar k b (mixOp k s x) (mixOp k s u), mixOp_symm]
  have hL_symm : ∀ x u : V, dotProduct x (L u) = dotProduct u (L x) := by
    intro x u
    rw [← hf_polar x u, ← hf_polar u x, add_comm x u]
    ring
  let K : Submodule B V := LinearMap.ker L
  have : Fintype K := Fintype.ofFinite K
  let fK : K →ₗ[B] B := {
    toFun := fun u => f u.val
    map_add' := fun u v => by
      have hp := hf_polar u.val v.val
      have hv : L v.val = 0 := v.property
      rw [hv, dotProduct_zero] at hp
      have h1 : f (u.val + v.val) + (f u.val + f v.val) = 0 := by
        simpa [add_assoc] using hp
      have h2 := congrArg (· + (f u.val + f v.val)) h1
      rw [add_assoc, zmod2_add_self, add_zero, zero_add] at h2
      exact h2
    map_smul' := fun c u => by
      rcases zmod2_cases c with rfl | rfl
      · change f ((0 : B) • u.val) = (0 : B) * f u.val
        simp [f, nl, dotProduct]
      · change f ((1 : B) • u.val) = (1 : B) * f u.val
        simp
  }
  obtain ⟨gV, hgV⟩ := LinearMap.exists_extend fK
  let base : V := fun i => gV (Pi.single i 1)
  have hbase_dot : ∀ x : V, dotProduct base x = gV x := by
    intro x
    have hx : x = ∑ i : ZMod k, x i • Pi.single i (1 : B) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hx]
    rw [map_sum]
    unfold dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hbase_K : ∀ u ∈ K, dotProduct base u = f u := by
    intro u hu
    rw [hbase_dot u]
    have := LinearMap.congr_fun hgV ⟨u, hu⟩
    exact this
  have hsq : ∀ a : V, (coeff a) ^ 2 =
      (2 ^ k : ℤ) * ∑ u : K, sign (dotProduct (a + base) u.val) := by
    intro a
    rw [sq]
    dsimp only [coeff]
    change (∑ x : V, sign (dotProduct a x + f x)) * (∑ y : V, sign (dotProduct a y + f y)) = _
    rw [Finset.sum_mul]
    have h1 : ∑ x : V, sign (dotProduct a x + f x) * ∑ y : V, sign (dotProduct a y + f y) =
        ∑ x : V, ∑ u : V, sign (dotProduct a x + f x) * sign (dotProduct a (x + u) + f (x + u)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact (Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)).symm
    rw [h1, Finset.sum_comm]
    have h2 : ∀ u : V,
        ∑ x : V, sign (dotProduct a x + f x) * sign (dotProduct a (x + u) + f (x + u)) =
          sign (dotProduct a u + f u) * ∑ x : V, sign (dotProduct x (L u)) := by
      intro u
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← sign_add, ← sign_add]
      congr 1
      have hp := hf_polar x u
      have hfu : f x + f (x + u) = f u + dotProduct x (L u) := by
        have h3 := congrArg (· + f u) hp
        rw [add_assoc, zmod2_add_self, add_zero] at h3
        rw [add_comm (f x), h3, add_comm]
      rw [dotProduct_add]
      have hax : dotProduct a x + f x + (dotProduct a x + dotProduct a u + f (x + u)) =
          (dotProduct a x + dotProduct a x) + dotProduct a u + (f x + f (x + u)) := by ring
      rw [hax, zmod2_add_self, zero_add, hfu]
      ring
    rw [Finset.sum_congr rfl (fun u _ => h2 u)]
    simp_rw [show ∀ u : V, (∑ x : V, sign (dotProduct x (L u))) =
      if L u = 0 then (2 ^ k : ℤ) else 0 from fun u => sum_sign_dot k (L u)]
    have hsplit : ∑ u : V, sign (dotProduct a u + f u) * (if L u = 0 then (2 ^ k : ℤ) else 0) =
        (2 ^ k : ℤ) * ∑ u : V, if u ∈ K then sign (dotProduct (a + base) u) else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : u ∈ K
      · have hLu : L u = 0 := hu
        simp only [hu, hLu, ↓reduceIte]
        rw [add_dotProduct, hbase_K u hu, mul_comm]
      · have hLu : L u ≠ 0 := hu
        simp [hu, hLu]
    rw [hsplit]
    congr 1
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun (u : V) hu => (⟨u, (Finset.mem_filter.mp hu).2⟩ : K))
      (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => congrArg Subtype.val h)
      (fun u _ => ⟨u.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.property⟩, rfl⟩)
      (fun _ _ => rfl)
  let Ann : Submodule B V :=
    ⟨⟨⟨{w : V | ∀ u ∈ K, dotProduct w u = 0},
      fun ha hb u hu => by rw [add_dotProduct, ha u hu, hb u hu, add_zero]⟩,
      fun u _ => zero_dotProduct u⟩,
      fun c x hx u hu => by rw [smul_dotProduct, hx u hu, smul_zero]⟩
  have hrange_eq_ann : LinearMap.range L = Ann := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro w ⟨v, rfl⟩ u hu
      rw [dotProduct_comm, hL_symm u v, (show L u = 0 from hu), dotProduct_zero]
    · let ev : V →ₗ[B] (K →ₗ[B] B) := {
        toFun := fun w => {
          toFun := fun u => dotProduct w u.val
          map_add' := fun u v => dotProduct_add w u.val v.val
          map_smul' := fun c u => by change dotProduct w (c • u.val) = c * dotProduct w u.val; rw [dotProduct_smul, smul_eq_mul]
        }
        map_add' := fun w1 w2 => by ext u; exact add_dotProduct w1 w2 u.val
        map_smul' := fun c w => by ext u; change dotProduct (c • w) u.val = c * dotProduct w u.val; rw [smul_dotProduct, smul_eq_mul]
      }
      have hker_ev : LinearMap.ker ev = Ann := by
        ext w
        simp only [LinearMap.mem_ker, Ann, Submodule.mem_mk, AddSubmonoid.mem_mk,
          AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
        constructor
        · intro hw u hu
          have := LinearMap.congr_fun hw ⟨u, hu⟩
          exact this
        · intro hw
          ext u
          exact hw u.val u.property
      have hsurj_ev : Function.Surjective ev := by
        intro φ
        obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend φ
        refine ⟨fun i => ψ (Pi.single i 1), ?_⟩
        ext u
        have hdot : ∀ x : V, dotProduct (fun i => ψ (Pi.single i 1)) x = ψ x := by
          intro x
          have hx : x = ∑ i : ZMod k, x i • Pi.single i (1 : B) := by
            funext j; simp [Finset.sum_apply, Pi.single_apply]
          conv_rhs => rw [hx]
          rw [map_sum]
          unfold dotProduct
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul, smul_eq_mul, mul_comm]
        change dotProduct (fun i => ψ (Pi.single i 1)) u.val = φ u
        rw [hdot u.val]
        exact LinearMap.congr_fun hψ u
      have hrank1 := LinearMap.finrank_range_add_finrank_ker L
      change Module.finrank B (LinearMap.range L) + Module.finrank B K = _ at hrank1
      have hrank2 := LinearMap.finrank_range_add_finrank_ker ev
      have hrange_ev : LinearMap.range ev = ⊤ := LinearMap.range_eq_top.mpr hsurj_ev
      rw [hrange_ev, hker_ev, finrank_top, Module.finrank_linearMap, Module.finrank_self, mul_one] at hrank2
      omega
  have hiff : ∀ a : V, coeff a ≠ 0 ↔ ∃ u : V, a = base + L u := by
    intro a
    have hsq_a := hsq a
    rw [sum_sign_subspace K (a + base)] at hsq_a
    have hiff1 : coeff a ≠ 0 ↔ a + base ∈ Ann := by
      constructor
      · intro hne
        by_contra hnot
        have hnot' : ¬ (∀ u ∈ K, dotProduct (a + base) u = 0) := hnot
        rw [if_neg hnot', mul_zero] at hsq_a
        exact hne (sq_eq_zero_iff.mp hsq_a)
      · intro hmem h0
        have hmem' : ∀ u ∈ K, dotProduct (a + base) u = 0 := hmem
        rw [if_pos hmem', h0, zero_pow (by decide : 2 ≠ 0)] at hsq_a
        have hpos1 : (0 : ℤ) < 2 ^ k := by positivity
        have hpos2 : (0 : ℤ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
        linarith [mul_pos hpos1 hpos2]
    rw [hiff1, ← hrange_eq_ann, LinearMap.mem_range]
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨u, ?_⟩
      have h1 := congrArg (· + base) hu
      rw [add_assoc, haddV base, add_zero] at h1
      rw [← h1, add_comm]
    · rintro ⟨u, rfl⟩
      refine ⟨u, ?_⟩
      rw [add_comm base (L u), add_assoc, haddV base, add_zero]
  refine ⟨⟨base, hiff⟩, ?_⟩
  have hcard1 : (Finset.univ.filter (fun a : V => coeff a ≠ 0)).card =
      Fintype.card (LinearMap.range L) := by
    have hset : Finset.univ.filter (fun a : V => coeff a ≠ 0) =
        (Finset.univ : Finset (LinearMap.range L)).image (fun w => base + w.val) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hiff]
      constructor
      · rintro ⟨u, rfl⟩; exact ⟨⟨L u, ⟨u, rfl⟩⟩, rfl⟩
      · rintro ⟨⟨w, ⟨u, rfl⟩⟩, rfl⟩; exact ⟨u, rfl⟩
    rw [hset, Finset.card_image_of_injective]
    · simp
    · intro w1 w2 h
      exact Subtype.ext (add_left_cancel h)
  rw [hcard1]
  have hcard2 := Module.card_eq_pow_finrank (K := B) (V := LinearMap.range L)
  rw [ZMod.card] at hcard2
  exact hcard2

private theorem ker_comp_le {V : Type} [AddCommGroup V] [Module B V] [FiniteDimensional B V]
    (f g : V →ₗ[B] V) :
    Module.finrank B (LinearMap.ker (f.comp g)) ≤
      Module.finrank B (LinearMap.ker f) + Module.finrank B (LinearMap.ker g) := by
  let restr : LinearMap.ker (f.comp g) →ₗ[B] LinearMap.ker f := {
    toFun := fun x => ⟨g x.val, x.property⟩
    map_add' := fun x y => Subtype.ext (map_add g x.val y.val)
    map_smul' := fun c x => Subtype.ext (map_smul g c x.val)
  }
  have hrk := LinearMap.finrank_range_add_finrank_ker restr
  have h1 : Module.finrank B (LinearMap.range restr) ≤ Module.finrank B (LinearMap.ker f) :=
    Submodule.finrank_le _
  let emb : LinearMap.ker restr →ₗ[B] LinearMap.ker g := {
    toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
  }
  have hinj : Function.Injective emb := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : LinearMap.ker g => z.val) h))
  have h2 : Module.finrank B (LinearMap.ker restr) ≤ Module.finrank B (LinearMap.ker g) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  omega

private theorem mixOp_ker_le (k : ℕ) [NeZero k] (d : ℕ) :
    let g := Nat.gcd k d
    let h := if 3 ∣ k / g then 2 * g else 0
    Module.finrank B (LinearMap.ker (mixOp k d)) ≤ h := by
  intro g h
  have hk : 0 < k := NeZero.pos k
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d hk
  have hstep : ∀ x ∈ LinearMap.ker (mixOp k d), ∀ i : ZMod k,
      x (i + (d : ZMod k)) = x i + x (i - (d : ZMod k)) := by
    intro x hx i
    have hi : x (i - (d : ZMod k)) + x i + x (i + (d : ZMod k)) = 0 := congrFun hx i
    have h1 := congrArg (· + x (i + (d : ZMod k))) hi
    rw [add_assoc, zmod2_add_self, add_zero, zero_add] at h1
    rw [← h1, add_comm]
  have hper : ∀ x ∈ LinearMap.ker (mixOp k d), ∀ (t : ℕ) (i : ZMod k),
      x (i + (t : ZMod k) * (d : ZMod k)) =
        if t % 3 = 0 then x i
        else if t % 3 = 1 then x (i + (d : ZMod k))
        else x i + x (i + (d : ZMod k)) := by
    intro x hx t
    induction t using Nat.strong_induction_on with
    | ind t ih =>
      intro i
      match t with
      | 0 => simp
      | 1 => simp
      | t' + 2 =>
        have hst := hstep x hx (i + ((t' + 1 : ℕ) : ZMod k) * (d : ZMod k))
        have heq1 : i + ((t' + 2 : ℕ) : ZMod k) * (d : ZMod k) =
            i + ((t' + 1 : ℕ) : ZMod k) * (d : ZMod k) + (d : ZMod k) := by push_cast; ring
        have heq2 : i + ((t' + 1 : ℕ) : ZMod k) * (d : ZMod k) - (d : ZMod k) =
            i + (t' : ZMod k) * (d : ZMod k) := by push_cast; ring
        rw [heq1, hst, heq2, ih (t' + 1) (by omega) i, ih t' (by omega) i]
        have hm3 : t' % 3 = 0 ∨ t' % 3 = 1 ∨ t' % 3 = 2 := by omega
        rcases hm3 with h0 | h1 | h2
        · have m1 : (t' + 1) % 3 = 1 := by omega
          have m2 : (t' + 2) % 3 = 2 := by omega
          simp only [h0, m1, m2, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceIte]
          ring
        · have m1 : (t' + 1) % 3 = 2 := by omega
          have m2 : (t' + 2) % 3 = 0 := by omega
          simp only [h1, m1, m2, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceIte]
          rw [add_assoc, zmod2_add_self, add_zero]
        · have m1 : (t' + 1) % 3 = 0 := by omega
          have m2 : (t' + 2) % 3 = 1 := by omega
          simp only [h2, m1, m2, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceIte]
          rw [← add_assoc, zmod2_add_self, zero_add]
  have hLd_zero : ((k / g : ℕ) : ZMod k) * (d : ZMod k) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    refine ⟨d / g, ?_⟩
    have hgk : g * (k / g) = k := Nat.mul_div_cancel' (Nat.gcd_dvd_left k d)
    have hgd : g * (d / g) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right k d)
    have hmul : g * ((k / g) * d) = g * (k * (d / g)) := by
      calc g * ((k / g) * d) = (g * (k / g)) * d := by ring
        _ = k * d := by rw [hgk]
        _ = k * (g * (d / g)) := by rw [hgd]
        _ = g * (k * (d / g)) := by ring
    exact Nat.eq_of_mul_eq_mul_left hg_pos hmul
  by_cases hdiv3 : 3 ∣ k / g
  · simp only [h, hdiv3, ↓reduceIte]
    let φ : LinearMap.ker (mixOp k d) →ₗ[B] (Fin g → B × B) := {
      toFun := fun x j => (x.val (j.val : ZMod k), x.val ((j.val : ZMod k) + (d : ZMod k)))
      map_add' := fun x y => by funext j; rfl
      map_smul' := fun c x => by funext j; rfl
    }
    have hbez : ∃ b0 : ℕ, ((b0 : ℕ) : ZMod k) * (d : ZMod k) = (g : ZMod k) := by
      have hg_int : (g : ℤ) = (k : ℤ) * Nat.gcdA k d + (d : ℤ) * Nat.gcdB k d := Nat.gcd_eq_gcd_ab k d
      have hcast := congrArg (Int.cast : ℤ → ZMod k) hg_int
      simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul, ZMod.natCast_self, zero_mul, zero_add] at hcast
      let b0 : ℕ := ((Nat.gcdB k d % (k : ℤ) + (k : ℤ)) % (k : ℤ)).toNat
      refine ⟨b0, ?_⟩
      have hb0_eq : ((b0 : ℕ) : ZMod k) = (Nat.gcdB k d : ZMod k) := by
        have hnn : 0 ≤ (Nat.gcdB k d % (k : ℤ) + (k : ℤ)) % (k : ℤ) :=
          Int.emod_nonneg _ (by omega)
        have hcoe : (b0 : ℤ) = (Nat.gcdB k d % (k : ℤ) + (k : ℤ)) % (k : ℤ) := Int.toNat_of_nonneg hnn
        have : ((b0 : ℕ) : ZMod k) = ((b0 : ℤ) : ZMod k) := by simp
        rw [this, hcoe, ZMod.intCast_mod]
        simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_self, add_zero, ZMod.intCast_mod]
      rw [hb0_eq, mul_comm, ← hcast]
    obtain ⟨b0, hb0⟩ := hbez
    have hinj : Function.Injective φ := by
      intro x y hxy
      apply Subtype.ext
      funext i
      have hi_val : ((i.val : ℕ) : ZMod k) = i := ZMod.natCast_zmod_val i
      let j : Fin g := ⟨i.val % g, Nat.mod_lt i.val hg_pos⟩
      let q : ℕ := i.val / g
      have hi_decomp : i = (j.val : ZMod k) + ((q * b0 : ℕ) : ZMod k) * (d : ZMod k) := by
        have hnat : i.val = j.val + q * g := by
          dsimp [j, q]
          rw [Nat.mul_comm, Nat.add_comm]
          exact (Nat.div_add_mod i.val g).symm
        rw [← hi_val, hnat]
        push_cast
        rw [mul_assoc, hb0]
      have hj_eq : x.val (j.val : ZMod k) = y.val (j.val : ZMod k) ∧
          x.val ((j.val : ZMod k) + (d : ZMod k)) = y.val ((j.val : ZMod k) + (d : ZMod k)) := by
        have := congrFun hxy j
        exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
      rw [hi_decomp, hper x.val x.property (q * b0) (j.val : ZMod k),
        hper y.val y.property (q * b0) (j.val : ZMod k), hj_eq.1, hj_eq.2]
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_pi_fintype] at hle
    simp only [Module.finrank_prod, Module.finrank_self, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at hle
    omega
  · simp only [h, hdiv3, ↓reduceIte]
    have hbot : LinearMap.ker (mixOp k d) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hmod : (k / g) % 3 = 1 ∨ (k / g) % 3 = 2 := by
        have hne0 : (k / g) % 3 ≠ 0 := fun h0 => hdiv3 (Nat.dvd_of_mod_eq_zero h0)
        omega
      funext i
      have hloop : x i = x (i + ((k / g : ℕ) : ZMod k) * (d : ZMod k)) := by
        rw [hLd_zero, add_zero]
      rw [hper x hx (k / g) i] at hloop
      rcases hmod with hm1 | hm2
      · have hconst : ∀ j : ZMod k, x (j + (d : ZMod k)) = x j := by
          intro j
          have hj := hper x hx (k / g) j
          rw [hLd_zero, add_zero] at hj
          simp only [hm1, one_ne_zero, ↓reduceIte] at hj
          exact hj.symm
        have hstep_i := hstep x hx i
        have hprev : x (i - (d : ZMod k)) = x i := by
          have := hconst (i - (d : ZMod k))
          simpa [sub_add_cancel] using this.symm
        rw [hconst i, hprev, zmod2_add_self] at hstep_i
        exact hstep_i
      · have hzero_shift : ∀ j : ZMod k, x (j + (d : ZMod k)) = 0 := by
          intro j
          have hj := hper x hx (k / g) j
          rw [hLd_zero, add_zero] at hj
          simp only [hm2, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceIte] at hj
          have h1 := congrArg (· + x j) hj
          rw [zmod2_add_self, add_comm (x j), add_assoc, zmod2_add_self, add_zero] at h1
          exact h1.symm
        have := hzero_shift (i - (d : ZMod k))
        simpa [sub_add_cancel] using this
    rw [hbot, finrank_bot]

private def pathOp (n : ℕ) (e : ℕ → Bool) : (Fin n → B) →ₗ[B] (Fin n → B) where
  toFun v p :=
    (if h : 0 < p.val ∧ e (p.val - 1) = true then v ⟨p.val - 1, by omega⟩ else 0) +
    (if h : p.val + 1 < n ∧ e p.val = true then v ⟨p.val + 1, h.1⟩ else 0)
  map_add' x y := by
    funext p
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

private def scoreList : List Bool → ℕ
  | [] => 0
  | false :: rest => scoreList rest
  | true :: [] => 2
  | true :: _ :: rest => 2 + scoreList rest

private theorem pathOp_apply (n : ℕ) (e : ℕ → Bool) (v : Fin n → B) (p : Fin n) :
    pathOp n e v p =
      (if h : 0 < p.val ∧ e (p.val - 1) = true then v ⟨p.val - 1, by omega⟩ else 0) +
      (if h : p.val + 1 < n ∧ e p.val = true then v ⟨p.val + 1, h.1⟩ else 0) := rfl

private theorem pathOp_finrank (n : ℕ) : ∀ (e : ℕ → Bool),
    Module.finrank B (LinearMap.range (pathOp n e)) = scoreList ((List.range (n - 1)).map e) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro e
    have hrank := LinearMap.finrank_range_add_finrank_ker (pathOp n e)
    rw [Module.finrank_pi, Fintype.card_fin] at hrank
    match n with
    | 0 =>
      simp only [Nat.zero_sub, List.range_zero, List.map_nil, scoreList]
      omega
    | 1 =>
      simp only [Nat.sub_self, List.range_zero, List.map_nil, scoreList]
      have hker : LinearMap.ker (pathOp 1 e) = ⊤ := by
        rw [Submodule.eq_top_iff']
        intro v
        funext p
        rw [pathOp_apply]
        have hp : p.val = 0 := by omega
        simp [hp]
      rw [hker, finrank_top, Module.finrank_pi, Fintype.card_fin] at hrank
      omega
    | n' + 2 =>
      have hlist : (List.range (n' + 2 - 1)).map e = e 0 :: (List.range n').map (fun p => e (p + 1)) := by
        have h1 : n' + 2 - 1 = n' + 1 := by omega
        rw [h1, List.range_succ_eq_map, List.map_cons, List.map_map]
        rfl
      rw [hlist]
      cases he0 : e 0
      · simp only [scoreList]
        let e' : ℕ → Bool := fun p => e (p + 1)
        let eqv : LinearMap.ker (pathOp (n' + 2) e) ≃ₗ[B] (B × LinearMap.ker (pathOp (n' + 1) e')) := {
          toFun := fun v => (v.val 0, ⟨fun p => v.val ⟨p.val + 1, by omega⟩, by
            funext p
            have hv : pathOp (n' + 2) e v.val ⟨p.val + 1, by omega⟩ = 0 := congrFun v.property ⟨p.val + 1, by omega⟩
            rw [pathOp_apply] at hv ⊢
            dsimp only [e']
            have hL : (if h : 0 < p.val ∧ e (p.val - 1 + 1) = true then v.val ⟨p.val - 1 + 1, by omega⟩ else 0) =
                (if h : 0 < p.val + 1 ∧ e (p.val + 1 - 1) = true then v.val ⟨p.val + 1 - 1, by omega⟩ else 0) := by
              by_cases hp0 : p.val = 0
              · simp [hp0, he0]
              · have ha : p.val - 1 + 1 = p.val := by omega
                have hb : p.val + 1 - 1 = p.val := by omega
                have hc : 0 < p.val := by omega
                have hd : 0 < p.val + 1 := by omega
                simp only [hc, hd, ha, hb, true_and]
            have hR : (if h : p.val + 1 < n' + 1 ∧ e (p.val + 1) = true then v.val ⟨p.val + 1 + 1, by omega⟩ else 0) =
                (if h : p.val + 1 + 1 < n' + 2 ∧ e (p.val + 1) = true then v.val ⟨p.val + 1 + 1, by omega⟩ else 0) := by
              by_cases h1 : p.val + 1 < n' + 1 ∧ e (p.val + 1) = true
              · have h2 : p.val + 1 + 1 < n' + 2 ∧ e (p.val + 1) = true := ⟨by omega, h1.2⟩
                simp only [h1, h2, ↓reduceDIte]
              · have h2 : ¬ (p.val + 1 + 1 < n' + 2 ∧ e (p.val + 1) = true) := fun h => h1 ⟨by omega, h.2⟩
                simp only [h1, h2, ↓reduceDIte]
            rw [hL, hR]
            exact hv⟩)
          invFun := fun p => ⟨fun q => if hq : q.val = 0 then p.1 else p.2.val ⟨q.val - 1, by omega⟩, by
            funext q
            rw [pathOp_apply]
            by_cases hq0 : q.val = 0
            · simp [hq0, he0]
            · have hv : pathOp (n' + 1) e' p.2.val ⟨q.val - 1, by omega⟩ = 0 :=
                congrFun p.2.property ⟨q.val - 1, by omega⟩
              rw [pathOp_apply] at hv
              dsimp only [e'] at hv
              have hL : (if h : 0 < q.val ∧ e (q.val - 1) = true then
                  (if hq' : q.val - 1 = 0 then p.1 else p.2.val ⟨q.val - 1 - 1, by omega⟩) else 0) =
                  (if h : 0 < q.val - 1 ∧ e (q.val - 1 - 1 + 1) = true then p.2.val ⟨q.val - 1 - 1, by omega⟩ else 0) := by
                by_cases hq1 : q.val = 1
                · simp [hq1, he0]
                · have hne : q.val - 1 ≠ 0 := by omega
                  have ha : 0 < q.val := by omega
                  have hb : 0 < q.val - 1 := by omega
                  have hc : q.val - 1 - 1 + 1 = q.val - 1 := by omega
                  simp only [ha, hb, hc, hne, true_and, ↓reduceDIte]
              have hR : (if h : q.val + 1 < n' + 2 ∧ e q.val = true then
                  (if hq' : q.val + 1 = 0 then p.1 else p.2.val ⟨q.val + 1 - 1, by omega⟩) else 0) =
                  (if h : q.val - 1 + 1 < n' + 1 ∧ e (q.val - 1 + 1) = true then p.2.val ⟨q.val - 1 + 1, by omega⟩ else 0) := by
                have hc : q.val - 1 + 1 = q.val := by omega
                have hne : q.val + 1 ≠ 0 := by omega
                by_cases h1 : q.val + 1 < n' + 2 ∧ e q.val = true
                · have h2 : q.val - 1 + 1 < n' + 1 ∧ e (q.val - 1 + 1) = true := ⟨by omega, by rw [hc]; exact h1.2⟩
                  simp only [h1, h2, hne, ↓reduceDIte]
                  exact congrArg p.2.val (Fin.ext (by dsimp; omega))
                · have h2 : ¬ (q.val - 1 + 1 < n' + 1 ∧ e (q.val - 1 + 1) = true) := fun h => h1 ⟨by omega, by rw [← hc]; exact h.2⟩
                  simp only [h1, h2, ↓reduceDIte]
              rw [hL, hR]
              exact hv⟩
          left_inv := fun v => by
            apply Subtype.ext; funext q
            dsimp only
            by_cases hq0 : q.val = 0
            · simp only [hq0, ↓reduceDIte]; exact congrArg v.val (Fin.ext hq0.symm)
            · simp only [hq0, ↓reduceDIte]; exact congrArg v.val (Fin.ext (by dsimp; omega))
          right_inv := fun p => by
            ext
            · simp
            · rename_i q; dsimp only; simp
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
        }
        have hker_eq : Module.finrank B (LinearMap.ker (pathOp (n' + 2) e)) =
            1 + Module.finrank B (LinearMap.ker (pathOp (n' + 1) e')) := by
          rw [eqv.finrank_eq, Module.finrank_prod, Module.finrank_self]
        have ih' := ih (n' + 1) (by omega) e'
        have hrank' := LinearMap.finrank_range_add_finrank_ker (pathOp (n' + 1) e')
        rw [Module.finrank_pi, Fintype.card_fin] at hrank'
        have hlist' : n' + 1 - 1 = n' := by omega
        rw [hlist'] at ih'
        change Module.finrank B (LinearMap.range (pathOp (n' + 2) e)) = scoreList ((List.range n').map e')
        omega
      · match n' with
        | 0 =>
          simp only [List.range_zero, List.map_nil, scoreList]
          have hker : LinearMap.ker (pathOp 2 e) = ⊥ := by
            rw [Submodule.eq_bot_iff]
            intro v hv
            funext p
            have h0 : pathOp 2 e v ⟨0, by decide⟩ = 0 := congrFun hv ⟨0, by decide⟩
            have h1 : pathOp 2 e v ⟨1, by decide⟩ = 0 := congrFun hv ⟨1, by decide⟩
            rw [pathOp_apply] at h0 h1
            simp [he0] at h0 h1
            fin_cases p
            · exact h1
            · exact h0
          rw [hker, finrank_bot] at hrank
          omega
        | m' + 1 =>
          have hlist2 : (List.range (m' + 1)).map (fun p => e (p + 1)) =
              e 1 :: (List.range m').map (fun p => e (p + 2)) := by
            rw [List.range_succ_eq_map, List.map_cons, List.map_map]
            rfl
          rw [hlist2]
          simp only [scoreList]
          let e'' : ℕ → Bool := fun p => e (p + 2)
          let eqv : LinearMap.ker (pathOp (m' + 3) e) ≃ₗ[B] LinearMap.ker (pathOp (m' + 1) e'') := {
            toFun := fun v => ⟨fun p => v.val ⟨p.val + 2, by omega⟩, by
              have hv0 : pathOp (m' + 3) e v.val ⟨0, by omega⟩ = 0 := congrFun v.property ⟨0, by omega⟩
              rw [pathOp_apply] at hv0
              have hv1_zero : v.val ⟨1, by omega⟩ = 0 := by
                have h1lt : (0 : ℕ) + 1 < m' + 3 ∧ e 0 = true := ⟨by omega, he0⟩
                simp only [lt_self_iff_false, false_and, ↓reduceDIte, zero_add, h1lt] at hv0
                exact hv0
              funext p
              have hv : pathOp (m' + 3) e v.val ⟨p.val + 2, by omega⟩ = 0 :=
                congrFun v.property ⟨p.val + 2, by omega⟩
              rw [pathOp_apply] at hv ⊢
              dsimp only [e'']
              have hL : (if h : 0 < p.val ∧ e (p.val - 1 + 2) = true then v.val ⟨p.val - 1 + 2, by omega⟩ else 0) =
                  (if h : 0 < p.val + 2 ∧ e (p.val + 2 - 1) = true then v.val ⟨p.val + 2 - 1, by omega⟩ else 0) := by
                by_cases hp0 : p.val = 0
                · simp only [hp0, lt_self_iff_false, false_and, ↓reduceDIte]
                  symm
                  by_cases h1 : 0 < 0 + 2 ∧ e (0 + 2 - 1) = true
                  · simp only [h1, ↓reduceDIte]; exact hv1_zero
                  · simp only [h1, ↓reduceDIte]
                · have ha : 0 < p.val := by omega
                  have hb : 0 < p.val + 2 := by omega
                  have hc : p.val - 1 + 2 = p.val + 2 - 1 := by omega
                  by_cases he : e (p.val - 1 + 2) = true
                  · have h1 : 0 < p.val ∧ e (p.val - 1 + 2) = true := ⟨ha, he⟩
                    have h2 : 0 < p.val + 2 ∧ e (p.val + 2 - 1) = true := ⟨hb, by rw [← hc]; exact he⟩
                    simp only [h1, h2, ↓reduceDIte]
                    exact congrArg v.val (Fin.ext hc)
                  · have h1 : ¬ (0 < p.val ∧ e (p.val - 1 + 2) = true) := fun h => he h.2
                    have h2 : ¬ (0 < p.val + 2 ∧ e (p.val + 2 - 1) = true) := fun h => he (by rw [hc]; exact h.2)
                    simp only [h1, h2, ↓reduceDIte]
              have hR : (if h : p.val + 1 < m' + 1 ∧ e (p.val + 2) = true then v.val ⟨p.val + 1 + 2, by omega⟩ else 0) =
                  (if h : p.val + 2 + 1 < m' + 3 ∧ e (p.val + 2) = true then v.val ⟨p.val + 2 + 1, by omega⟩ else 0) := by
                by_cases h1 : p.val + 1 < m' + 1 ∧ e (p.val + 2) = true
                · have h2 : p.val + 2 + 1 < m' + 3 ∧ e (p.val + 2) = true := ⟨by omega, h1.2⟩
                  simp only [h1, h2]
                · have h2 : ¬ (p.val + 2 + 1 < m' + 3 ∧ e (p.val + 2) = true) := fun h => h1 ⟨by omega, h.2⟩
                  simp only [h1, h2, ↓reduceDIte]
              rw [hL, hR]
              exact hv⟩
            invFun := fun w => ⟨fun q =>
              if hq0 : q.val = 0 then (if e 1 = true then w.val ⟨0, by omega⟩ else 0)
              else if hq1 : q.val = 1 then 0
              else w.val ⟨q.val - 2, by omega⟩, by
              funext q
              rw [pathOp_apply]
              simp only [Pi.zero_apply]
              by_cases hq0 : q.val = 0
              · have h1lt : 1 < m' + 3 ∧ e 0 = true := ⟨by omega, he0⟩
                simp only [hq0, lt_self_iff_false, false_and, ↓reduceDIte, zero_add, h1lt,
                  one_ne_zero, and_self]
              · by_cases hq1 : q.val = 1
                · have hleft : 0 < (1 : ℕ) ∧ e (1 - 1) = true := ⟨by decide, he0⟩
                  simp only [hq1, hleft, ↓reduceDIte, Nat.sub_self]
                  by_cases he1 : e 1 = true
                  · have hright : (1 : ℕ) + 1 < m' + 3 ∧ e 1 = true := ⟨by omega, he1⟩
                    simp only [he1, ↓reduceIte, hright, ↓reduceDIte,
                      show (1 : ℕ) + 1 ≠ 0 by decide, show (1 : ℕ) + 1 ≠ 1 by decide]
                    exact zmod2_add_self _
                  · simp only [he1, Bool.false_eq_true, and_false, and_self, ↓reduceIte,
                      ↓reduceDIte, add_zero]
                · have hv : pathOp (m' + 1) e'' w.val ⟨q.val - 2, by omega⟩ = 0 :=
                    congrFun w.property ⟨q.val - 2, by omega⟩
                  rw [pathOp_apply] at hv
                  dsimp only [e''] at hv
                  have hL : (if h : 0 < q.val ∧ e (q.val - 1) = true then
                      (if hq0' : q.val - 1 = 0 then (if e 1 = true then w.val ⟨0, by omega⟩ else 0)
                       else if hq1' : q.val - 1 = 1 then 0
                       else w.val ⟨q.val - 1 - 2, by omega⟩) else 0) =
                      (if h : 0 < q.val - 2 ∧ e (q.val - 2 - 1 + 2) = true then w.val ⟨q.val - 2 - 1, by omega⟩ else 0) := by
                    by_cases hq2 : q.val = 2
                    · simp only [hq2, Nat.sub_self, lt_self_iff_false, false_and, ↓reduceDIte,
                        show (2 : ℕ) - 1 = 1 by rfl, one_ne_zero]
                      split_ifs <;> rfl
                    · have ha : 0 < q.val := by omega
                      have hb : 0 < q.val - 2 := by omega
                      have hc : q.val - 2 - 1 + 2 = q.val - 1 := by omega
                      have hne0 : q.val - 1 ≠ 0 := by omega
                      have hne1 : q.val - 1 ≠ 1 := by omega
                      by_cases he : e (q.val - 1) = true
                      · have h1 : 0 < q.val ∧ e (q.val - 1) = true := ⟨ha, he⟩
                        have h2 : 0 < q.val - 2 ∧ e (q.val - 2 - 1 + 2) = true := ⟨hb, by rw [hc]; exact he⟩
                        simp only [h1, h2, hne0, hne1, ↓reduceDIte]
                        exact congrArg w.val (Fin.ext (by dsimp; omega))
                      · have h1 : ¬ (0 < q.val ∧ e (q.val - 1) = true) := fun h => he h.2
                        have h2 : ¬ (0 < q.val - 2 ∧ e (q.val - 2 - 1 + 2) = true) := fun h => he (by rw [← hc]; exact h.2)
                        simp only [h1, h2, ↓reduceDIte]
                  have hR : (if h : q.val + 1 < m' + 3 ∧ e q.val = true then
                      (if hq0' : q.val + 1 = 0 then (if e 1 = true then w.val ⟨0, by omega⟩ else 0)
                       else if hq1' : q.val + 1 = 1 then 0
                       else w.val ⟨q.val + 1 - 2, by omega⟩) else 0) =
                      (if h : q.val - 2 + 1 < m' + 1 ∧ e (q.val - 2 + 2) = true then w.val ⟨q.val - 2 + 1, by omega⟩ else 0) := by
                    have hc : q.val - 2 + 2 = q.val := by omega
                    have hne0 : q.val + 1 ≠ 0 := by omega
                    have hne1 : q.val + 1 ≠ 1 := by omega
                    by_cases h1 : q.val + 1 < m' + 3 ∧ e q.val = true
                    · have h2 : q.val - 2 + 1 < m' + 1 ∧ e (q.val - 2 + 2) = true := ⟨by omega, by rw [hc]; exact h1.2⟩
                      simp only [h1, h2, hne0, hne1, ↓reduceDIte]
                      exact congrArg w.val (Fin.ext (by dsimp; omega))
                    · have h2 : ¬ (q.val - 2 + 1 < m' + 1 ∧ e (q.val - 2 + 2) = true) := fun h => h1 ⟨by omega, by rw [← hc]; exact h.2⟩
                      simp only [h1, h2, ↓reduceDIte]
                  rw [hL, hR]
                  exact hv⟩
            left_inv := fun v => by
              have hv0 : pathOp (m' + 3) e v.val ⟨0, by omega⟩ = 0 := congrFun v.property ⟨0, by omega⟩
              have hv1 : pathOp (m' + 3) e v.val ⟨1, by omega⟩ = 0 := congrFun v.property ⟨1, by omega⟩
              rw [pathOp_apply] at hv0 hv1
              have h0_lt : (0 : ℕ) + 1 < m' + 3 ∧ e 0 = true := ⟨by omega, he0⟩
              have hv_at1 : v.val ⟨1, by omega⟩ = 0 := by
                simp only [lt_self_iff_false, false_and, ↓reduceDIte, zero_add, h0_lt] at hv0
                exact hv0
              have h1_left : 0 < (1 : ℕ) ∧ e (1 - 1) = true := ⟨by decide, he0⟩
              apply Subtype.ext; funext q
              dsimp only
              by_cases hq0 : q.val = 0
              · simp only [hq0, ↓reduceDIte]
                have hqeq : q = ⟨0, by omega⟩ := Fin.ext hq0
                rw [hqeq]
                by_cases he1 : e 1 = true
                · have h1_right : (1 : ℕ) + 1 < m' + 3 ∧ e 1 = true := ⟨by omega, he1⟩
                  simp only [h1_left, h1_right, and_self, ↓reduceDIte] at hv1
                  simp only [he1, ↓reduceIte]
                  have h3 := congrArg (· + v.val ⟨2, by omega⟩) hv1
                  rw [add_assoc, zmod2_add_self, add_zero, zero_add] at h3
                  exact h3.symm
                · have h1_right : ¬ ((1 : ℕ) + 1 < m' + 3 ∧ e 1 = true) := fun h => he1 h.2
                  simp only [h1_left, h1_right, and_self, ↓reduceDIte, add_zero] at hv1
                  simp only [he1, ↓reduceIte]
                  exact hv1.symm
              · by_cases hq1 : q.val = 1
                · simp only [hq0, hq1, ↓reduceDIte]
                  have hqeq : q = ⟨1, by omega⟩ := Fin.ext hq1
                  rw [hqeq]; exact hv_at1.symm
                · simp only [hq0, hq1, ↓reduceDIte]
                  exact congrArg v.val (Fin.ext (by dsimp; omega))
            right_inv := fun w => by
              apply Subtype.ext; funext p
              dsimp only
              have ha : p.val + 2 ≠ 0 := by omega
              have hb : p.val + 2 ≠ 1 := by omega
              simp only [ha, hb, ↓reduceDIte]
              exact congrArg w.val (Fin.ext (by dsimp; omega))
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl
          }
          have hker_eq : Module.finrank B (LinearMap.ker (pathOp (m' + 3) e)) =
              Module.finrank B (LinearMap.ker (pathOp (m' + 1) e'')) := eqv.finrank_eq
          have ih'' := ih (m' + 1) (by omega) e''
          have hrank'' := LinearMap.finrank_range_add_finrank_ker (pathOp (m' + 1) e'')
          rw [Module.finrank_pi, Fintype.card_fin] at hrank''
          have hlist'' : m' + 1 - 1 = m' := by omega
          rw [hlist''] at ih''
          change Module.finrank B (LinearMap.range (pathOp (m' + 3) e)) +
            Module.finrank B (LinearMap.ker (pathOp (m' + 3) e)) = m' + 3 at hrank
          change Module.finrank B (LinearMap.range (pathOp (m' + 3) e)) =
            2 + scoreList ((List.range m').map e'')
          omega

private def runSum (l : List Bool) : ℕ :=
  ∑ p : Fin l.length,
    if l[p.val] = true ∧ (p.val = 0 ∨ l[p.val - 1]'(by omega) = false) then
      2 * (((l.drop p.val).takeWhile (fun b => b = true)).length + 1) / 2
    else 0

private def runSumExact (l : List Bool) : ℕ :=
  ∑ p : Fin l.length,
    if l[p.val] = true ∧ (p.val = 0 ∨ l[p.val - 1]'(by omega) = false) then
      2 * ((((l.drop p.val).takeWhile (fun b => b = true)).length + 1) / 2)
    else 0

private theorem scoreList_eq_runSumExact : ∀ l : List Bool, scoreList l = runSumExact l := by
  intro l
  have hcons_prev : ∀ (a : Bool) (xs : List Bool) (p : Fin xs.length), p.val ≠ 0 →
      (a :: xs)[p.val]'(by simp) = xs[p.val - 1]'(by omega) := by
    intro a xs p hp
    rcases p with ⟨k, hk⟩
    cases k with
    | zero => exact absurd rfl hp
    | succ m => rfl
  induction hlen : l.length using Nat.strong_induction_on generalizing l with
  | ind n ih =>
    match l with
    | [] => simp [scoreList, runSumExact]
    | false :: rest =>
      simp only [scoreList, runSumExact, List.length_cons]
      rw [Fin.sum_univ_succ]
      have hhead : (if (false :: rest)[(0 : Fin (rest.length + 1)).val] = true ∧
          ((0 : Fin (rest.length + 1)).val = 0 ∨ (false :: rest)[(0 : Fin (rest.length + 1)).val - 1] = false) then
          2 * (((((false :: rest).drop (0 : Fin (rest.length + 1)).val).takeWhile (fun b => b = true)).length + 1) / 2)
        else 0) = 0 := by simp
      rw [hhead, zero_add]
      rw [ih rest.length (by simp at hlen; omega) rest rfl]
      unfold runSumExact
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [Fin.val_succ, List.getElem_cons_succ, List.drop_succ_cons, Nat.add_sub_cancel,
        Nat.add_one_ne_zero, false_or]
      by_cases hp0 : p.val = 0
      · simp [hp0]
      · simp only [hp0, false_or, hcons_prev false rest p hp0]
    | true :: [] =>
      simp [scoreList, runSumExact]
    | true :: false :: rest =>
      simp only [scoreList, runSumExact, List.length_cons]
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      have h0 : (if (true :: false :: rest)[(0 : Fin (rest.length + 1 + 1)).val] = true ∧
          ((0 : Fin (rest.length + 1 + 1)).val = 0 ∨ (true :: false :: rest)[(0 : Fin (rest.length + 1 + 1)).val - 1] = false) then
          2 * (((((true :: false :: rest).drop (0 : Fin (rest.length + 1 + 1)).val).takeWhile (fun b => b = true)).length + 1) / 2)
        else 0) = 2 := by simp [List.takeWhile]
      have h1 : (if (true :: false :: rest)[((0 : Fin (rest.length + 1)).succ).val] = true ∧
          (((0 : Fin (rest.length + 1)).succ).val = 0 ∨ (true :: false :: rest)[((0 : Fin (rest.length + 1)).succ).val - 1] = false) then
          2 * (((((true :: false :: rest).drop ((0 : Fin (rest.length + 1)).succ).val).takeWhile (fun b => b = true)).length + 1) / 2)
        else 0) = 0 := by simp
      rw [h0, h1, zero_add, ih rest.length (by simp at hlen; omega) rest rfl]
      congr 1
      unfold runSumExact
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [Fin.val_succ, List.getElem_cons_succ, List.drop_succ_cons, Nat.add_sub_cancel,
        Nat.add_one_ne_zero, false_or]
      by_cases hp0 : p.val = 0
      · simp [hp0]
      · simp only [hp0, false_or, hcons_prev false rest p hp0]
    | true :: true :: rest =>
      simp only [scoreList, runSumExact, List.length_cons]
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      have h1 : (if (true :: true :: rest)[((0 : Fin (rest.length + 1)).succ).val] = true ∧
          (((0 : Fin (rest.length + 1)).succ).val = 0 ∨ (true :: true :: rest)[((0 : Fin (rest.length + 1)).succ).val - 1] = false) then
          2 * (((((true :: true :: rest).drop ((0 : Fin (rest.length + 1)).succ).val).takeWhile (fun b => b = true)).length + 1) / 2)
        else 0) = 0 := by simp
      rw [h1, zero_add, ih rest.length (by simp at hlen; omega) rest rfl]
      match rest with
      | [] =>
        simp [runSumExact, List.takeWhile]
      | false :: rest' =>
        have h0 : (if (true :: true :: false :: rest')[(0 : Fin (rest'.length + 1 + 1 + 1)).val] = true ∧
            ((0 : Fin (rest'.length + 1 + 1 + 1)).val = 0 ∨ (true :: true :: false :: rest')[(0 : Fin (rest'.length + 1 + 1 + 1)).val - 1] = false) then
            2 * (((((true :: true :: false :: rest').drop (0 : Fin (rest'.length + 1 + 1 + 1)).val).takeWhile (fun b => b = true)).length + 1) / 2)
          else 0) = 2 := by simp [List.takeWhile]
        rw [h0]
        congr 1
        unfold runSumExact
        simp only [List.length_cons]
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
        have hf0 : (if (false :: rest')[(0 : Fin (rest'.length + 1)).val] = true ∧
            ((0 : Fin (rest'.length + 1)).val = 0 ∨ (false :: rest')[(0 : Fin (rest'.length + 1)).val - 1] = false) then
            2 * (((((false :: rest').drop (0 : Fin (rest'.length + 1)).val).takeWhile (fun b => b = true)).length + 1) / 2)
          else 0) = 0 := by simp
        have hf1 : (if (true :: true :: false :: rest')[(Fin.succ (Fin.succ (0 : Fin (rest'.length + 1)))).val] = true ∧
            ((Fin.succ (Fin.succ (0 : Fin (rest'.length + 1)))).val = 0 ∨
              (true :: true :: false :: rest')[(Fin.succ (Fin.succ (0 : Fin (rest'.length + 1)))).val - 1]'(by simp only [Fin.val_succ, Fin.val_zero, List.length_cons]; omega) = false) then
            2 * (((((true :: true :: false :: rest').drop (Fin.succ (Fin.succ (0 : Fin (rest'.length + 1)))).val).takeWhile (fun b => b = true)).length + 1) / 2)
          else 0) = 0 := by
          simp only [Fin.val_succ, Fin.val_zero, List.getElem_cons_succ, List.getElem_cons_zero,
            Bool.false_eq_true, false_and, ↓reduceIte]
        rw [hf0, hf1, zero_add, zero_add]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp only [Fin.val_succ, List.getElem_cons_succ, List.drop_succ_cons, Nat.add_sub_cancel,
          Nat.add_one_ne_zero, false_or]
      | true :: rest' =>
        unfold runSumExact
        simp only [List.length_cons]
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
        have h0_eq : (if (true :: true :: true :: rest')[(0 : Fin (rest'.length + 1 + 1 + 1)).val] = true ∧
            ((0 : Fin (rest'.length + 1 + 1 + 1)).val = 0 ∨ (true :: true :: true :: rest')[(0 : Fin (rest'.length + 1 + 1 + 1)).val - 1] = false) then
            2 * (((((true :: true :: true :: rest').drop (0 : Fin (rest'.length + 1 + 1 + 1)).val).takeWhile (fun b => b = true)).length + 1) / 2)
          else 0) = 2 + 2 * (((((true :: rest').takeWhile (fun b => b = true)).length) + 1) / 2) := by
          simp only [Fin.val_zero, List.getElem_cons_zero, List.drop_zero, true_or, and_self, ↓reduceIte]
          have htw : ((true :: true :: true :: rest').takeWhile (fun b => b = true)).length =
              2 + ((true :: rest').takeWhile (fun b => b = true)).length := by
            simp [List.takeWhile]; omega
          rw [htw]
          omega
        have ht0_eq : (if (true :: rest')[(0 : Fin (rest'.length + 1)).val] = true ∧
            ((0 : Fin (rest'.length + 1)).val = 0 ∨ (true :: rest')[(0 : Fin (rest'.length + 1)).val - 1] = false) then
            2 * (((((true :: rest').drop (0 : Fin (rest'.length + 1)).val).takeWhile (fun b => b = true)).length + 1) / 2)
          else 0) = 2 * ((((true :: rest').takeWhile (fun b => b = true)).length + 1) / 2) := by
          simp
        have ht1_eq : (if (true :: true :: true :: rest')[(Fin.succ (Fin.succ (0 : Fin (rest'.length + 1)))).val] = true ∧
            ((Fin.succ (Fin.succ (0 : Fin (rest'.length + 1)))).val = 0 ∨
              (true :: true :: true :: rest')[(Fin.succ (Fin.succ (0 : Fin (rest'.length + 1)))).val - 1]'(by simp only [Fin.val_succ, Fin.val_zero, List.length_cons]; omega) = false) then
            2 * (((((true :: true :: true :: rest').drop (Fin.succ (Fin.succ (0 : Fin (rest'.length + 1)))).val).takeWhile (fun b => b = true)).length + 1) / 2)
          else 0) = 0 := by
          simp only [Fin.val_succ, Fin.val_zero, Nat.add_sub_cancel, List.getElem_cons_succ,
            List.getElem_cons_zero, Nat.add_one_ne_zero, Bool.true_eq_false, or_self, and_false,
            ↓reduceIte]
        rw [h0_eq, ht0_eq, ht1_eq, zero_add, Nat.add_assoc]
        congr 1
        congr 1
        refine Finset.sum_congr rfl fun p _ => ?_
        simp only [Fin.val_succ, List.getElem_cons_succ, List.drop_succ_cons, Nat.add_sub_cancel,
          Nat.add_one_ne_zero, false_or]

private theorem edgeOp_finrank (k : ℕ) [NeZero k] (b : ZMod k → B) :
    let run := fun (i : ZMod k) =>
      ((List.range k).takeWhile (fun offset => decide (b (i + (offset : ZMod k)) = 1))).length
    let r := if ∀ i : ZMod k, b i = 1 then k - Nat.gcd k 2 else
      ∑ i : ZMod k, if b i = 1 ∧ b (i - 1) = 0 then 2 * ((run i + 1) / 2) else 0
    Module.finrank B (LinearMap.range (edgeOp k b)) = r := by
  intro run r
  have hk : 0 < k := NeZero.pos k
  have hrank := LinearMap.finrank_range_add_finrank_ker (edgeOp k b)
  rw [Module.finrank_pi, ZMod.card] at hrank
  by_cases hall : ∀ i : ZMod k, b i = 1
  · have hr_val : r = k - Nat.gcd k 2 := by simp [r, hall]
    rw [hr_val]
    let g := Nat.gcd k 2
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left 2 hk
    have hstep : ∀ w ∈ LinearMap.ker (edgeOp k b), ∀ i : ZMod k, w (i + 2) = w i := by
      intro w hw i
      have hi := congrFun hw (i + 1)
      simp only [edgeOp, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, hall, one_mul] at hi
      have e1 : i + 1 - 1 = i := by ring
      have e2 : i + 1 + 1 = i + 2 := by ring
      rw [e1, e2] at hi
      have h1 := congrArg (· + w (i + 2)) hi
      rw [add_assoc, zmod2_add_self, add_zero, zero_add] at h1
      exact h1.symm
    have hstep_mul : ∀ w ∈ LinearMap.ker (edgeOp k b), ∀ (t : ℕ) (i : ZMod k),
        w (i + (t : ZMod k) * 2) = w i := by
      intro w hw t
      induction t with
      | zero => intro i; simp
      | succ t ih =>
        intro i
        have heq : i + ((t + 1 : ℕ) : ZMod k) * 2 = i + (t : ZMod k) * 2 + 2 := by push_cast; ring
        rw [heq, hstep w hw, ih]
    have hbez : ∃ b0 : ℕ, ((b0 : ℕ) : ZMod k) * (2 : ZMod k) = (g : ZMod k) := by
      have hg_int : (g : ℤ) = (k : ℤ) * Nat.gcdA k 2 + (2 : ℤ) * Nat.gcdB k 2 := Nat.gcd_eq_gcd_ab k 2
      have hcast := congrArg (Int.cast : ℤ → ZMod k) hg_int
      simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul, ZMod.natCast_self, zero_mul, zero_add,
        Int.cast_ofNat] at hcast
      let b0 : ℕ := ((Nat.gcdB k 2 % (k : ℤ) + (k : ℤ)) % (k : ℤ)).toNat
      refine ⟨b0, ?_⟩
      have hb0_eq : ((b0 : ℕ) : ZMod k) = (Nat.gcdB k 2 : ZMod k) := by
        have hnn : 0 ≤ (Nat.gcdB k 2 % (k : ℤ) + (k : ℤ)) % (k : ℤ) := Int.emod_nonneg _ (by omega)
        have hcoe : (b0 : ℤ) = (Nat.gcdB k 2 % (k : ℤ) + (k : ℤ)) % (k : ℤ) := Int.toNat_of_nonneg hnn
        have : ((b0 : ℕ) : ZMod k) = ((b0 : ℤ) : ZMod k) := by simp
        rw [this, hcoe, ZMod.intCast_mod]
        simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_self, add_zero, ZMod.intCast_mod]
      rw [hb0_eq, mul_comm, ← hcast]
    obtain ⟨b0, hb0⟩ := hbez
    have hmod_add2 : ∀ i : ZMod k, (i + 2).val % g = i.val % g := by
      intro i
      have hgk : g ∣ k := Nat.gcd_dvd_left k 2
      have hg2 : g ∣ 2 := Nat.gcd_dvd_right k 2
      have hval : (i + 2).val = (i.val + 2) % k := by
        have h1 : ((i.val + 2 : ℕ) : ZMod k) = i + 2 := by push_cast; rw [ZMod.natCast_zmod_val]
        rw [← h1, ZMod.val_natCast]
      rw [hval, Nat.mod_mod_of_dvd _ hgk, Nat.add_mod, Nat.mod_eq_zero_of_dvd hg2, Nat.add_zero,
        Nat.mod_mod]
    let eqv : LinearMap.ker (edgeOp k b) ≃ₗ[B] (Fin g → B) := {
      toFun := fun w j => w.val (j.val : ZMod k)
      invFun := fun c => ⟨fun i => c ⟨i.val % g, Nat.mod_lt i.val hg_pos⟩, by
        ext i
        simp only [edgeOp, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, hall, one_mul]
        have heq : (i + 1).val % g = (i - 1).val % g := by
          have : i + 1 = (i - 1) + 2 := by ring
          rw [this, hmod_add2]
        have hc : (⟨(i + 1).val % g, Nat.mod_lt _ hg_pos⟩ : Fin g) =
            ⟨(i - 1).val % g, Nat.mod_lt _ hg_pos⟩ := Fin.ext heq
        rw [hc]
        exact zmod2_add_self _⟩
      left_inv := fun w => by
        apply Subtype.ext
        funext i
        dsimp only
        have hi_val : ((i.val : ℕ) : ZMod k) = i := ZMod.natCast_zmod_val i
        have hi_decomp : i = ((i.val % g : ℕ) : ZMod k) + (((i.val / g) * b0 : ℕ) : ZMod k) * 2 := by
          have hnat : i.val = i.val % g + (i.val / g) * g := by
            rw [Nat.mul_comm, Nat.add_comm]; exact (Nat.div_add_mod i.val g).symm
          conv_lhs => rw [← hi_val, hnat]
          push_cast
          rw [mul_assoc, hb0]
        have h1 := hstep_mul w.val w.property ((i.val / g) * b0) ((i.val % g : ℕ) : ZMod k)
        rw [← hi_decomp] at h1
        exact h1.symm
      right_inv := fun c => by
        funext j
        dsimp only
        have hjlt : j.val < k := lt_of_lt_of_le j.isLt (Nat.gcd_le_left 2 hk)
        have hv : ((j.val : ℕ) : ZMod k).val = j.val := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hjlt]
        have hm : ((j.val : ℕ) : ZMod k).val % g = j.val := by rw [hv, Nat.mod_eq_of_lt j.isLt]
        exact congrArg c (Fin.ext hm)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
    }
    have hker_eq : Module.finrank B (LinearMap.ker (edgeOp k b)) = g := by
      rw [eqv.finrank_eq, Module.finrank_pi, Fintype.card_fin]
    omega
  · simp only [r, hall, ↓reduceIte]
    have hex0 : ∃ i0 : ZMod k, b i0 = 0 := by
      by_contra hno
      apply hall
      intro i
      rcases zmod2_cases (b i) with h | h
      · exact absurd ⟨i, h⟩ hno
      · exact h
    obtain ⟨i0, hi0⟩ := hex0
    let e : ℕ → Bool := fun p => decide (b (i0 + ((1 + p : ℕ) : ZMod k)) = 1)
    let ψ : (Fin k → B) ≃ₗ[B] (ZMod k → B) := {
      toFun := fun v i => v ⟨(i - i0 - 2).val, ZMod.val_lt _⟩
      invFun := fun w p => w (i0 + ((2 + p.val : ℕ) : ZMod k))
      left_inv := fun v => by
        funext p
        dsimp only
        have heq : i0 + ((2 + p.val : ℕ) : ZMod k) - i0 - 2 = (p.val : ZMod k) := by push_cast; ring
        have hval : (i0 + ((2 + p.val : ℕ) : ZMod k) - i0 - 2).val = p.val := by
          rw [heq, ZMod.val_natCast, Nat.mod_eq_of_lt p.isLt]
        exact congrArg v (Fin.ext hval)
      right_inv := fun w => by
        funext i
        dsimp only
        have hval : ((i - i0 - 2).val : ZMod k) = i - i0 - 2 := ZMod.natCast_zmod_val _
        have heq : i0 + ((2 + (i - i0 - 2).val : ℕ) : ZMod k) = i := by
          push_cast; rw [hval]; ring
        rw [heq]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
    }
    have hconj : ∀ v : Fin k → B, ψ.symm (edgeOp k b (ψ v)) = pathOp k e v := by
      intro v
      funext p
      simp only [ψ, LinearEquiv.coe_symm_mk, LinearEquiv.coe_mk, edgeOp, pathOp, LinearMap.coe_mk,
        AddHom.coe_mk]
      have hterm1 : b (i0 + ((2 + p.val : ℕ) : ZMod k) - 2) *
            v ⟨(i0 + ((2 + p.val : ℕ) : ZMod k) - 1 - i0 - 2).val, ZMod.val_lt _⟩ =
          if h : 0 < p.val ∧ e (p.val - 1) = true then v ⟨p.val - 1, by omega⟩ else 0 := by
        by_cases hp0 : p.val = 0
        · have heq : i0 + ((2 + p.val : ℕ) : ZMod k) - 2 = i0 := by rw [hp0]; push_cast; ring
          rw [heq, hi0, zero_mul]
          simp [hp0]
        · have hpos : 0 < p.val := by omega
          have heq1 : i0 + ((2 + p.val : ℕ) : ZMod k) - 2 = i0 + ((1 + (p.val - 1) : ℕ) : ZMod k) := by
            have : 1 + (p.val - 1) = p.val := by omega
            rw [this]; push_cast; ring
          have heq2 : i0 + ((2 + p.val : ℕ) : ZMod k) - 1 - i0 - 2 = ((p.val - 1 : ℕ) : ZMod k) := by
            have : 2 + p.val = 3 + (p.val - 1) := by omega
            rw [this]; push_cast; ring
          have hval : (i0 + ((2 + p.val : ℕ) : ZMod k) - 1 - i0 - 2).val = p.val - 1 := by
            rw [heq2, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
          rw [heq1]
          simp only [hpos, true_and, e, decide_eq_true_eq]
          rcases zmod2_cases (b (i0 + ((1 + (p.val - 1) : ℕ) : ZMod k))) with hb | hb
          · simp only [hb, zero_mul, zero_ne_one, ↓reduceDIte]
          · simp only [hb, one_mul, ↓reduceDIte]; exact congrArg v (Fin.ext hval)
      have hterm2 : b (i0 + ((2 + p.val : ℕ) : ZMod k) - 1) *
            v ⟨(i0 + ((2 + p.val : ℕ) : ZMod k) + 1 - i0 - 2).val, ZMod.val_lt _⟩ =
          if h : p.val + 1 < k ∧ e p.val = true then v ⟨p.val + 1, h.1⟩ else 0 := by
        by_cases hplast : p.val + 1 = k
        · have heq : i0 + ((2 + p.val : ℕ) : ZMod k) - 1 = i0 := by
            have : 2 + p.val = k + 1 := by omega
            rw [this]; push_cast; rw [ZMod.natCast_self]; ring
          rw [heq, hi0, zero_mul]
          have hnot : ¬ (p.val + 1 < k) := by omega
          simp [hnot]
        · have hlt : p.val + 1 < k := by omega
          have heq1 : i0 + ((2 + p.val : ℕ) : ZMod k) - 1 = i0 + ((1 + p.val : ℕ) : ZMod k) := by
            push_cast; ring
          have heq2 : i0 + ((2 + p.val : ℕ) : ZMod k) + 1 - i0 - 2 = ((p.val + 1 : ℕ) : ZMod k) := by
            push_cast; ring
          have hval : (i0 + ((2 + p.val : ℕ) : ZMod k) + 1 - i0 - 2).val = p.val + 1 := by
            rw [heq2, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
          rw [heq1]
          simp only [hlt, true_and, e, decide_eq_true_eq]
          rcases zmod2_cases (b (i0 + ((1 + p.val : ℕ) : ZMod k))) with hb | hb
          · simp only [hb, zero_mul, zero_ne_one, ↓reduceDIte]
          · simp only [hb, one_mul, ↓reduceDIte]; exact congrArg v (Fin.ext hval)
      rw [hterm1, hterm2]
    have hker_eq : Module.finrank B (LinearMap.ker (edgeOp k b)) =
        Module.finrank B (LinearMap.ker (pathOp k e)) := by
      let keqv : LinearMap.ker (pathOp k e) ≃ₗ[B] LinearMap.ker (edgeOp k b) := {
        toFun := fun v => ⟨ψ v.val, by
          have h0 : pathOp k e v.val = 0 := v.property
          have h1 : ψ.symm (edgeOp k b (ψ v.val)) = 0 := by rw [hconj v.val, h0]
          exact ψ.symm.injective (by simpa using h1)⟩
        invFun := fun w => ⟨ψ.symm w.val, by
          have h0 : edgeOp k b w.val = 0 := w.property
          change pathOp k e (ψ.symm w.val) = 0
          rw [← hconj (ψ.symm w.val), ψ.apply_symm_apply, h0, map_zero]⟩
        left_inv := fun v => Subtype.ext (ψ.symm_apply_apply v.val)
        right_inv := fun w => Subtype.ext (ψ.apply_symm_apply w.val)
        map_add' := fun x y => Subtype.ext (map_add ψ x.val y.val)
        map_smul' := fun c x => Subtype.ext (map_smul ψ c x.val)
      }
      exact keqv.finrank_eq.symm
    have hpath_rk := LinearMap.finrank_range_add_finrank_ker (pathOp k e)
    rw [Module.finrank_pi, Fintype.card_fin] at hpath_rk
    have hrange_eq : Module.finrank B (LinearMap.range (edgeOp k b)) =
        scoreList ((List.range (k - 1)).map e) := by
      have := pathOp_finrank k e
      omega
    rw [hrange_eq, scoreList_eq_runSumExact]
    let L := (List.range (k - 1)).map e
    have hLlen : L.length = k - 1 := by simp [L]
    have hsum_L : runSumExact L =
        ∑ p : Fin (k - 1),
          if b (i0 + ((1 + p.val : ℕ) : ZMod k)) = 1 ∧
              b (i0 + ((1 + p.val : ℕ) : ZMod k) - 1) = 0 then
            2 * ((run (i0 + ((1 + p.val : ℕ) : ZMod k)) + 1) / 2)
          else 0 := by
      unfold runSumExact
      refine Finset.sum_bij (fun (p : Fin L.length) _ => (⟨p.val, by omega⟩ : Fin (k - 1)))
        (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => Fin.ext (congrArg (fun x : Fin (k - 1) => x.val) h))
        (fun q _ => ⟨⟨q.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        (fun p _ => ?_)
      have hp_lt : p.val < k - 1 := by omega
      have hget : ∀ q (hq : q < L.length), L[q]'hq = e q := by
        intro q hq; simp [L]
      have hcond : (L[p.val] = true ∧ (p.val = 0 ∨ L[p.val - 1]'(by omega) = false)) ↔
          (b (i0 + ((1 + p.val : ℕ) : ZMod k)) = 1 ∧ b (i0 + ((1 + p.val : ℕ) : ZMod k) - 1) = 0) := by
        rw [hget p.val p.isLt]
        by_cases hp0 : p.val = 0
        · have heq : i0 + ((1 + p.val : ℕ) : ZMod k) - 1 = i0 := by rw [hp0]; push_cast; ring
          rw [heq, hi0]
          simp [hp0, e]
        · rw [hget (p.val - 1) (by omega)]
          have heq : i0 + ((1 + p.val : ℕ) : ZMod k) - 1 = i0 + ((1 + (p.val - 1) : ℕ) : ZMod k) := by
            have : 1 + p.val = 1 + (p.val - 1) + 1 := by omega
            rw [this]; push_cast; ring
          rw [heq]
          simp only [hp0, false_or, e, decide_eq_true_eq, decide_eq_false_iff_not]
          rcases zmod2_cases (b (i0 + ((1 + (p.val - 1) : ℕ) : ZMod k))) with hb | hb
          · simp only [hb, zero_ne_one, not_false_eq_true]
          · simp only [hb, not_true_eq_false, one_ne_zero]
      have htw_eq : ((L.drop p.val).takeWhile (fun b => b = true)).length =
          run (i0 + ((1 + p.val : ℕ) : ZMod k)) := by
        have hdrop : L.drop p.val = (List.range (k - 1 - p.val)).map (fun off => e (p.val + off)) := by
          apply List.ext_getElem
          · simp [L]
          · intro j h1 h2
            simp [L]
        rw [hdrop]
        dsimp only [run]
        have hdo : ∀ xs : List ℕ, (do let a ← xs; pure (a : ZMod k)) = xs.map (Nat.cast : ℕ → ZMod k) := by
          intro xs
          induction xs with
          | nil => rfl
          | cons a xs ih => exact congrArg (List.cons (a : ZMod k)) ih
        rw [hdo]
        have hrange_split : List.range k =
            List.range (k - 1 - p.val) ++ (k - 1 - p.val) :: (List.range p.val).map (fun j => k - p.val + j) := by
          apply List.ext_getElem
          · simp; omega
          · intro j h1 h2
            rw [List.getElem_range]
            by_cases hj : j < k - 1 - p.val
            · rw [List.getElem_append_left (by simp; exact hj), List.getElem_range]
            · rw [List.getElem_append_right (by simp; omega)]
              simp only [List.length_range]
              by_cases hjeq : j = k - 1 - p.val
              · subst hjeq
                simp only [Nat.sub_self, List.getElem_cons_zero]
              · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j - (k - 1 - p.val) ≠ 0)
                simp only [hm, List.getElem_cons_succ, List.getElem_map, List.getElem_range]
                omega
        rw [hrange_split, List.map_append, List.map_cons, List.takeWhile_append]
        have hpred : ∀ off : ℕ, decide (b (i0 + ((1 + p.val : ℕ) : ZMod k) + (off : ZMod k)) = 1) = e (p.val + off) := by
          intro off
          simp only [e]
          have heq : i0 + ((1 + p.val : ℕ) : ZMod k) + (off : ZMod k) =
              i0 + ((1 + (p.val + off) : ℕ) : ZMod k) := by push_cast; ring
          rw [heq]
        have hstop : decide (b (i0 + ((1 + p.val : ℕ) : ZMod k) + ((k - 1 - p.val : ℕ) : ZMod k)) = 1) = false := by
          have heq : i0 + ((1 + p.val : ℕ) : ZMod k) + ((k - 1 - p.val : ℕ) : ZMod k) = i0 := by
            have : (1 + p.val) + (k - 1 - p.val) = k := by omega
            rw [add_assoc, ← Nat.cast_add, this, ZMod.natCast_self, add_zero]
          rw [heq, hi0]
          decide
        have htail : (((k - 1 - p.val : ℕ) : ZMod k) :: ((List.range p.val).map (fun j => k - p.val + j)).map (Nat.cast : ℕ → ZMod k)).takeWhile
            (fun offset : ZMod k => decide (b (i0 + ((1 + p.val : ℕ) : ZMod k) + offset) = 1)) = [] := by
          simp only [List.takeWhile, hstop]
        rw [htail]
        have hmap_tw : ∀ {α : Type} (xs : List α) (f : α → Bool),
            ((xs.map f).takeWhile (fun b => b = true)).length = (xs.takeWhile f).length := by
          intro α xs f
          induction xs with
          | nil => rfl
          | cons a xs ih =>
            cases hfa : f a
            · simp only [List.map_cons, List.takeWhile, hfa, Bool.false_eq_true, decide_false]
              rfl
            · simp only [List.map_cons, List.takeWhile, hfa, decide_true, List.length_cons, ih]
        have htw_map_cast : ∀ (xs : List ℕ) (f : ZMod k → Bool),
            ((xs.map (Nat.cast : ℕ → ZMod k)).takeWhile f).length = (xs.takeWhile (fun (off : ℕ) => f (off : ZMod k))).length := by
          intro xs f
          induction xs with
          | nil => rfl
          | cons a xs ih =>
            cases hfa : f (a : ZMod k)
            · simp only [List.map_cons, List.takeWhile, hfa]
              rfl
            · simp only [List.map_cons, List.takeWhile, hfa, List.length_cons, ih]
        have htw_self : ∀ {α : Type} (l : List α) (f : α → Bool), l.all f = true → l.takeWhile f = l := by
          intro α l f
          induction l with
          | nil => intro _; rfl
          | cons a l ih =>
            intro h
            simp only [List.all_cons, Bool.and_eq_true] at h
            simp only [List.takeWhile, h.1, ih h.2]
        have hcongr : ∀ (xs : List ℕ) (f1 f2 : ℕ → Bool), (∀ a, f1 a = f2 a) →
            xs.takeWhile f1 = xs.takeWhile f2 := by
          intro xs f1 f2 hf
          induction xs with
          | nil => rfl
          | cons a xs ih => simp only [List.takeWhile, hf a, ih]
        split_ifs with hall_t
        · rw [List.append_nil, ← hall_t, hmap_tw, htw_map_cast]
          exact congrArg List.length (hcongr _ _ _ (fun off => (hpred off).symm))
        · rw [hmap_tw, htw_map_cast]
          exact congrArg List.length (hcongr _ _ _ (fun off => (hpred off).symm))
      by_cases hc : b (i0 + ((1 + p.val : ℕ) : ZMod k)) = 1 ∧ b (i0 + ((1 + p.val : ℕ) : ZMod k) - 1) = 0
      · have hc' : L[p.val] = true ∧ (p.val = 0 ∨ L[p.val - 1]'(by omega) = false) := hcond.mpr hc
        simp only [hc, hc', ↓reduceIte, htw_eq]
      · have hc' : ¬ (L[p.val] = true ∧ (p.val = 0 ∨ L[p.val - 1]'(by omega) = false)) := fun h => hc (hcond.mp h)
        simp only [hc, hc', ↓reduceIte]
    rw [hsum_L]
    have hsum_erase : ∑ i : ZMod k, (if b i = 1 ∧ b (i - 1) = 0 then 2 * ((run i + 1) / 2) else 0) =
        ∑ i ∈ (Finset.univ : Finset (ZMod k)).erase i0,
          if b i = 1 ∧ b (i - 1) = 0 then 2 * ((run i + 1) / 2) else 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
      simp [hi0]
    rw [hsum_erase]
    refine Finset.sum_bij (fun (p : Fin (k - 1)) _ => i0 + ((1 + p.val : ℕ) : ZMod k))
      (fun p _ => by
        rw [Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        intro heq
        have h0 : ((1 + p.val : ℕ) : ZMod k) = 0 := by
          have := congrArg (· - i0) heq
          simpa using this
        rw [ZMod.natCast_eq_zero_iff] at h0
        have hle := Nat.le_of_dvd (by omega) h0
        omega)
      (fun p1 _ p2 _ heq => by
        have hsub : ((1 + p1.val : ℕ) : ZMod k) = ((1 + p2.val : ℕ) : ZMod k) := add_left_cancel heq
        have hv1 : ((1 + p1.val : ℕ) : ZMod k).val = 1 + p1.val := by
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
        have hv2 : ((1 + p2.val : ℕ) : ZMod k).val = 1 + p2.val := by
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
        have := congrArg ZMod.val hsub
        rw [hv1, hv2] at this
        exact Fin.ext (by omega))
      (fun i hi => by
        rw [Finset.mem_erase] at hi
        have hne : i - i0 ≠ 0 := sub_ne_zero.mpr hi.1
        have hpos : 0 < (i - i0).val := by
          by_contra h0
          have hv0 : (i - i0).val = 0 := by omega
          apply hne
          rw [← ZMod.natCast_zmod_val (i - i0), hv0, Nat.cast_zero]
        have hlt : (i - i0).val < k := ZMod.val_lt _
        refine ⟨⟨(i - i0).val - 1, by omega⟩, Finset.mem_univ _, ?_⟩
        have h1 : 1 + ((i - i0).val - 1) = (i - i0).val := by omega
        dsimp only
        rw [h1, ZMod.natCast_zmod_val, add_sub_cancel])
      (fun _ _ => rfl)

private theorem solve_25694 (k : ℕ) [NeZero k] (d : ℕ) :
    let I := ZMod k
    let V := I → B
    let mix := fun (s : ℕ) (x : V) (i : I) => x (i - (s : I)) + x i + x (i + (s : I))
    let nl := fun (y : V) (j : I) => y j + (1 + y (j + 1)) * y (j + 2)
    let coeff := fun (s : ℕ) (a b : V) =>
      ∑ x : V, sign (dotProduct a x + dotProduct b (nl (mix s x)))
    let support := fun (s : ℕ) (b : V) => Finset.univ.filter (fun mask : V => coeff s mask b ≠ 0)
    let g := Nat.gcd k d
    let h := if 3 ∣ k / g then 2 * g else 0
    ∀ b : V,
      let edge := fun (w : V) (i : I) => b (i - 2) * w (i - 1) + b (i - 1) * w (i + 1)
      let run := fun (i : I) =>
        ((List.range k).takeWhile (fun offset => decide (b (i + (offset : I)) = 1))).length
      let r := if ∀ i : I, b i = 1 then k - Nat.gcd k 2 else
        ∑ i : I, if b i = 1 ∧ b (i - 1) = 0 then 2 * ((run i + 1) / 2) else 0
      (∃ base : V, ∀ a : V, a ∈ support d b ↔
        ∃ u : V, a = base + mix d (edge (mix d u))) ∧
      (support 0 b).card = 2 ^ r ∧
      (support d b).card ≤ 2 ^ r ∧ 2 ^ r ≤ 2 ^ (2 * h) * (support d b).card := by
  intro I V mix nl coeff support g h b edge run r
  have hw_d := walsh_support_char k d b
  have hw_0 := walsh_support_char k 0 b
  dsimp only at hw_d hw_0
  have hE_rk : Module.finrank B (LinearMap.range (edgeOp k b)) = r := edgeOp_finrank k b
  let Ld : V →ₗ[B] V := (mixOp k d).comp ((edgeOp k b).comp (mixOp k d))
  let L0 : V →ₗ[B] V := (mixOp k 0).comp ((edgeOp k b).comp (mixOp k 0))
  have hL0_eq : L0 = edgeOp k b := by
    dsimp only [L0]; rw [mixOp_zero]; ext x i; rfl
  have hsupp0 : (support 0 b).card = 2 ^ r := by
    have h0 : (support 0 b).card = 2 ^ Module.finrank B (LinearMap.range L0) := hw_0.2
    rw [h0, hL0_eq, hE_rk]
  have hsuppd : (support d b).card = 2 ^ Module.finrank B (LinearMap.range Ld) := hw_d.2
  have hrk_le : Module.finrank B (LinearMap.range Ld) ≤ r := by
    rw [← hE_rk]
    have hsub : LinearMap.range Ld ≤ Submodule.map (mixOp k d) (LinearMap.range (edgeOp k b)) := by
      rintro y ⟨u, rfl⟩
      exact ⟨edgeOp k b (mixOp k d u), ⟨mixOp k d u, rfl⟩, rfl⟩
    calc Module.finrank B (LinearMap.range Ld)
        ≤ Module.finrank B (Submodule.map (mixOp k d) (LinearMap.range (edgeOp k b))) :=
          Submodule.finrank_mono hsub
      _ ≤ Module.finrank B (LinearMap.range (edgeOp k b)) :=
          Submodule.finrank_map_le (mixOp k d) _
  have hrk_ge : r ≤ 2 * h + Module.finrank B (LinearMap.range Ld) := by
    have hkerM : Module.finrank B (LinearMap.ker (mixOp k d)) ≤ h := mixOp_ker_le k d
    have hk1 : Module.finrank B (LinearMap.ker Ld) ≤
        Module.finrank B (LinearMap.ker (mixOp k d)) +
          Module.finrank B (LinearMap.ker ((edgeOp k b).comp (mixOp k d))) :=
      ker_comp_le (mixOp k d) ((edgeOp k b).comp (mixOp k d))
    have hk2 := ker_comp_le (edgeOp k b) (mixOp k d)
    have hrk_Ld := LinearMap.finrank_range_add_finrank_ker Ld
    have hrk_E := LinearMap.finrank_range_add_finrank_ker (edgeOp k b)
    rw [Module.finrank_pi, ZMod.card] at hrk_Ld hrk_E
    omega
  refine ⟨?_, hsupp0, ?_, ?_⟩
  · obtain ⟨base, hbase⟩ := hw_d.1
    refine ⟨base, fun a => ?_⟩
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hbase a
  · rw [hsuppd]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hrk_le
  · rw [hsuppd, ← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hrk_ge

end PEqualNP.Outside.L_meta_25694_aux

theorem PEqualNP.Outside.L_meta_25694 : ∀ (k : ℕ) [NeZero k] (d : ℕ),
  let I := ZMod k
  let B := ZMod 2
  let V := I → B
  let sign := fun (t : B) => if t = 0 then (1 : ℤ) else -1
  let mix := fun (s : ℕ) (x : V) (i : I) => x (i-(s : I)) + x i + x (i+(s : I))
  let nl := fun (y : V) (j : I) => y j + (1+y (j+1))*y (j+2)
  let coeff := fun (s : ℕ) (a b : V) =>
    ∑ x : V, sign (dotProduct a x + dotProduct b (nl (mix s x)))
  let support := fun (s : ℕ) (b : V) => Finset.univ.filter (fun mask : V => coeff s mask b ≠ 0)
  let g := Nat.gcd k d
  let h := if 3 ∣ k/g then 2*g else 0
  ∀ b : V,
    let edge := fun (w : V) (i : I) => b (i-2)*w (i-1) + b (i-1)*w (i+1)
    let run := fun (i : I) =>
      ((List.range k).takeWhile (fun offset => decide (b (i+(offset : I)) = 1))).length
    let r := if ∀ i : I, b i = 1 then k - Nat.gcd k 2 else
      ∑ i : I, if b i = 1 ∧ b (i-1) = 0 then 2*((run i + 1)/2) else 0
    (∃ base : V, ∀ a : V, a ∈ support d b ↔
      ∃ u : V, a = base + mix d (edge (mix d u))) ∧
    (support 0 b).card = 2^r ∧
    (support d b).card ≤ 2^r ∧ 2^r ≤ 2^(2*h) * (support d b).card := by
  intro k _ d
  exact PEqualNP.Outside.L_meta_25694_aux.solve_25694 k d


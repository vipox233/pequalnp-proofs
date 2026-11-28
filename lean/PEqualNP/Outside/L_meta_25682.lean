import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25682_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private abbrev K := ZMod 2

/-! ### Section 1: `ZMod 2` Linear Algebra, `hits ↔ flat`, and Generator Kernel Fiber Size -/

private def b2z (b : Bool) : K := if b then 1 else 0
private def z2b (x : K) : Bool := decide (x ≠ 0)

private lemma z2_cases (x : K) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma z2_add_self (x : K) : x + x = 0 := by fin_cases x <;> rfl
private lemma z2_mul_self (x : K) : x * x = x := by fin_cases x <;> rfl
private lemma b2z_z2b (x : K) : b2z (z2b x) = x := by fin_cases x <;> rfl
private lemma z2b_b2z (b : Bool) : z2b (b2z b) = b := by cases b <;> rfl
private lemma z2b_add (a b : K) : z2b (a + b) = xor (z2b a) (z2b b) := by
  fin_cases a <;> fin_cases b <;> rfl
private lemma z2b_mul (a b : K) : z2b (a * b) = (z2b a && z2b b) := by
  fin_cases a <;> fin_cases b <;> rfl
private lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide
private lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide
private lemma b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by cases a <;> decide
private lemma b2z_injective : Function.Injective b2z := by
  intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

private def dot {m : ℕ} (a x : Fin m → K) : K :=
  ∑ g : Fin m, a g * x g

private lemma dot_comm {m : ℕ} (a x : Fin m → K) : dot a x = dot x a := by
  unfold dot
  refine Finset.sum_congr rfl fun g _ => mul_comm _ _

private lemma dot_add_right {m : ℕ} (a x y : Fin m → K) :
    dot a (x + y) = dot a x + dot a y := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma dot_add_left {m : ℕ} (a b x : Fin m → K) :
    dot (a + b) x = dot a x + dot b x := by
  rw [dot_comm, dot_add_right, dot_comm x a, dot_comm x b]

private lemma dot_smul_right {m : ℕ} (a : Fin m → K) (c : K) (x : Fin m → K) :
    dot a (c • x) = c * dot a x := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => by ring

private lemma dot_smul_left {m : ℕ} (c : K) (a x : Fin m → K) :
    dot (c • a) x = c * dot a x := by
  rw [dot_comm, dot_smul_right, dot_comm]

private lemma dot_zero_left {m : ℕ} (x : Fin m → K) : dot 0 x = 0 := by simp [dot]
private lemma dot_zero_right {m : ℕ} (a : Fin m → K) : dot a 0 = 0 := by simp [dot]

private def dotLin {m : ℕ} (a : Fin m → K) : (Fin m → K) →ₗ[K] K where
  toFun := dot a
  map_add' := dot_add_right a
  map_smul' c x := by simp [dot_smul_right]

private def ortho {m : ℕ} (S : Submodule K (Fin m → K)) : Submodule K (Fin m → K) :=
  { carrier := {x | ∀ v ∈ S, dot v x = 0}, zero_mem' := fun v _ => dot_zero_right v, add_mem' := fun hx hy v hv => by rw [dot_add_right, hx v hv, hy v hv, add_zero], smul_mem' := fun c _ hx v hv => by rw [dot_smul_right, hx v hv, mul_zero] }

private lemma finrank_ortho_add {m : ℕ} (U : Submodule K (Fin m → K)) :
    Module.finrank K U + Module.finrank K (ortho U) = m := by
  let r := Module.finrank K U
  let bU := Module.finBasis K U
  let Φ : (Fin m → K) →ₗ[K] (Fin r → K) :=
    { toFun := fun v i => dot v (bU i).1
      map_add' := fun v1 v2 => by funext i; exact dot_add_left v1 v2 (bU i).1
      map_smul' := fun c v => by funext i; simp [dot_smul_left] }
  have hker : LinearMap.ker Φ = ortho U := by
    ext v
    simp only [LinearMap.mem_ker, ortho, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
    constructor
    · intro hv x hx
      have hrep := bU.sum_repr ⟨x, hx⟩
      have hx_eq : x = ∑ i : Fin r, bU.repr ⟨x, hx⟩ i • (bU i).1 := by
        have h1 : (⟨x, hx⟩ : U).1 = (∑ i : Fin r, bU.repr ⟨x, hx⟩ i • bU i).1 :=
          congrArg Subtype.val hrep.symm
        simpa only [Submodule.coe_sum, SetLike.val_smul] using h1
      rw [dot_comm, hx_eq]
      simp only [dot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      calc ∑ g : Fin m, v g * (∑ i : Fin r, bU.repr ⟨x, hx⟩ i * (bU i).1 g)
          = ∑ g : Fin m, ∑ i : Fin r, bU.repr ⟨x, hx⟩ i * (v g * (bU i).1 g) := by
            refine Finset.sum_congr rfl fun g _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by ring
        _ = ∑ i : Fin r, bU.repr ⟨x, hx⟩ i * (∑ g : Fin m, v g * (bU i).1 g) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => by rw [← Finset.mul_sum]
        _ = ∑ i : Fin r, bU.repr ⟨x, hx⟩ i * Φ v i := rfl
        _ = 0 := by
            refine Finset.sum_eq_zero fun i _ => ?_
            have hi : Φ v i = 0 := congrFun hv i
            rw [hi, mul_zero]
    · intro hv
      funext i
      change dot v (bU i).1 = 0
      rw [dot_comm]
      exact hv (bU i).1 (bU i).2
  have hsurj : LinearMap.range Φ = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    obtain ⟨retract, hret⟩ := LinearMap.exists_leftInverse_of_injective U.subtype (Submodule.ker_subtype U)
    let ψ : U →ₗ[K] K := bU.constr K y
    let ψ' : (Fin m → K) →ₗ[K] K := ψ.comp retract
    let v : Fin m → K := fun g => ψ' (Pi.single g 1)
    refine ⟨v, ?_⟩
    funext i
    have hdot : ∀ x : Fin m → K, dot v x = ψ' x := fun x => by
      have hx : x = ∑ g : Fin m, x g • Pi.single g (1 : K) := by
        funext g; simp [Pi.single_apply]
      conv_rhs => rw [hx, map_sum]
      unfold dot
      refine Finset.sum_congr rfl fun g _ => ?_
      simp [v, smul_eq_mul, mul_comm]
    change dot v (bU i).1 = y i
    rw [hdot]
    have hret_i : retract (bU i).1 = bU i := LinearMap.congr_fun hret (bU i)
    simp only [ψ', LinearMap.comp_apply, hret_i, ψ, Module.Basis.constr_basis]
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hsurj, hker, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrn
  exact hrn

private lemma prod_affine_iff {m : ℕ} (a b : Fin m → K) (U : Submodule K (Fin m → K)) :
    (∃ (ell : (Fin m → K) →ₗ[K] K) (c : K), ∀ x ∈ U, dot a x * dot b x = ell x + c) ↔
    (∀ x ∈ U, dot a x = 0) ∨ (∀ x ∈ U, dot b x = 0) ∨ (∀ x ∈ U, dot (a + b) x = 0) := by
  constructor
  · rintro ⟨ell, c, h⟩
    have hc : c = 0 := by
      have h0 := h 0 U.zero_mem
      simpa [dot_zero_right] using h0.symm
    subst hc
    have hbil : ∀ x ∈ U, ∀ y ∈ U, dot a x * dot b y + dot a y * dot b x = 0 := by
      intro x hx y hy
      have hxy := h (x + y) (U.add_mem hx hy)
      have hx' := h x hx
      have hy' := h y hy
      rw [dot_add_right, dot_add_right, map_add, add_zero] at hxy
      rw [add_zero] at hx' hy'
      rw [← hx', ← hy'] at hxy
      linear_combination hxy
    by_contra hnone
    push Not at hnone
    rcases hnone with ⟨⟨x1, hx1, ha1⟩, ⟨x2, hx2, hb2⟩, ⟨x3, hx3, hab3⟩⟩
    have ha1' : dot a x1 = 1 := (z2_cases _).resolve_left ha1
    have hb2' : dot b x2 = 1 := (z2_cases _).resolve_left hb2
    rw [dot_add_left] at hab3
    rcases z2_cases (dot a x3) with ha3 | ha3 <;> rcases z2_cases (dot b x3) with hb3 | hb3
    · rw [ha3, hb3, add_zero] at hab3; exact hab3 rfl
    · have hc := hbil x3 hx3 x1 hx1
      rw [ha3, hb3, ha1'] at hc; simp at hc
    · have hc := hbil x3 hx3 x2 hx2
      rw [ha3, hb3, hb2'] at hc; simp at hc
    · rw [ha3, hb3, z2_add_self] at hab3; exact hab3 rfl
  · rintro (ha | hb | hab)
    · refine ⟨0, 0, fun x hx => by simp [ha x hx]⟩
    · refine ⟨0, 0, fun x hx => by simp [hb x hx]⟩
    · refine ⟨dotLin a, 0, fun x hx => ?_⟩
      have hsum : dot a x + dot b x = 0 := by rw [← dot_add_left]; exact hab x hx
      have heq : dot b x = dot a x := by
        have h2 := z2_add_self (dot a x)
        linear_combination hsum - h2
      simp only [dotLin, LinearMap.coe_mk, AddHom.coe_mk, add_zero, heq, z2_mul_self]

private def ixAux (k : ℕ) (hk : 0 < k) (pos : ℕ) : Fin k :=
  ⟨pos % k, Nat.mod_lt _ hk⟩

private def rotAux {k : ℕ} (hk : 0 < k) (s : ℕ) (w : Fin k → K) (j : Fin k) : K :=
  w (ixAux k hk (j.val + k - s % k))

private def mixedAux {k : ℕ} (hk : 0 < k) (d s : ℕ) (w name : Fin k → K) (mid : Fin k) : K :=
  let z := rotAux hk s w + name
  z mid + z (ixAux k hk (mid.val + d)) + z (ixAux k hk (mid.val + k - d % k))

private lemma rotAux_add {k : ℕ} (hk : 0 < k) (s : ℕ) (w1 w2 : Fin k → K) (j : Fin k) :
    rotAux hk s (w1 + w2) j = rotAux hk s w1 j + rotAux hk s w2 j := rfl

private lemma rotAux_smul {k : ℕ} (hk : 0 < k) (s : ℕ) (c : K) (w : Fin k → K) (j : Fin k) :
    rotAux hk s (c • w) j = c * rotAux hk s w j := rfl

private lemma rotAux_sum {k : ℕ} {ι : Type*} (hk : 0 < k) (s : ℕ) (S : Finset ι)
    (f : ι → Fin k → K) (j : Fin k) :
    rotAux hk s (∑ i ∈ S, f i) j = ∑ i ∈ S, rotAux hk s (f i) j := by
  simp [rotAux]

private lemma mixedAux_add_zero {k : ℕ} (hk : 0 < k) (d s : ℕ) (w1 w2 name : Fin k → K) (mid : Fin k) :
    mixedAux hk d s (w1 + w2) name mid = mixedAux hk d s w1 name mid + mixedAux hk d s w2 0 mid := by
  simp only [mixedAux, rotAux, Pi.add_apply, Pi.zero_apply, add_zero]
  ring

private lemma mixedAux_zero_sum {k m : ℕ} (hk : 0 < k) (d s : ℕ)
    (gen : Fin m → Fin k → K) (x : Fin m → K) (mid : Fin k) :
    mixedAux hk d s (∑ g : Fin m, x g • gen g) 0 mid =
      ∑ g : Fin m, x g * mixedAux hk d s (gen g) 0 mid := by
  simp only [mixedAux, rotAux, Pi.add_apply, Pi.zero_apply, add_zero, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]

private def probeAux {k t : ℕ} (hk : 0 < k) (site : Fin t → Fin k) (col : Fin t → Bool)
    (u v cr cc : Fin k → K) (raw : Fin k → K) (idx : Fin t) : K :=
  let spacing := if col idx then 2 else 1
  let start := if col idx then 3 else 1
  let injectAt := if col idx then 4 else 0
  let y := mixedAux hk spacing start raw (if col idx then v else u)
  let j := site idx
  y j + (1 + y (ixAux k hk (j.val + 1))) * y (ixAux k hk (j.val + 2)) +
    rotAux hk injectAt raw j + (if col idx then cc j else cr j)

private def operandAux {k m t : ℕ} (hk : 0 < k) (site : Fin t → Fin k) (col : Fin t → Bool)
    (gen : Fin m → Fin k → K) (p : Fin t) (offset : ℕ) (g : Fin m) : K :=
  let spacing := if col p then 2 else 1
  let start := if col p then 3 else 1
  mixedAux hk spacing start (gen g) 0 (ixAux k hk ((site p).val + offset))

private def probeLinAux {k m t : ℕ} (hk : 0 < k) (site : Fin t → Fin k) (col : Fin t → Bool)
    (base : Fin k → K) (gen : Fin m → Fin k → K) (u v : Fin k → K)
    (p : Fin t) (g : Fin m) : K :=
  let spacing := if col p then 2 else 1
  let start := if col p then 3 else 1
  let injectAt := if col p then 4 else 0
  let y0 := mixedAux hk spacing start base (if col p then v else u)
  let j := site p
  operandAux hk site col gen p 0 g +
    rotAux hk injectAt (gen g) j +
    (1 + y0 (ixAux k hk (j.val + 1))) * operandAux hk site col gen p 2 g +
    y0 (ixAux k hk (j.val + 2)) * operandAux hk site col gen p 1 g

private lemma probeAux_key_expand {k m t : ℕ} (hk : 0 < k) (site : Fin t → Fin k) (col : Fin t → Bool)
    (base : Fin k → K) (gen : Fin m → Fin k → K) (u v cr cc : Fin k → K)
    (x : Fin m → K) (p : Fin t) :
    probeAux hk site col u v cr cc (base + ∑ g : Fin m, x g • gen g) p =
      probeAux hk site col u v cr cc base p +
      dot (probeLinAux hk site col base gen u v p) x +
      dot (operandAux hk site col gen p 1) x * dot (operandAux hk site col gen p 2) x := by
  let sp := if col p then 2 else 1
  let st := if col p then 3 else 1
  let inj := if col p then 4 else 0
  let nm := if col p then v else u
  let y0 := mixedAux hk sp st base nm
  let j := site p
  have hy : ∀ off : ℕ,
      mixedAux hk sp st (base + ∑ g : Fin m, x g • gen g) nm (ixAux k hk (j.val + off)) =
        y0 (ixAux k hk (j.val + off)) + dot (operandAux hk site col gen p off) x := fun off => by
    rw [mixedAux_add_zero, mixedAux_zero_sum]
    congr 1
    unfold dot operandAux
    refine Finset.sum_congr rfl fun g _ => mul_comm _ _
  have hy0 : mixedAux hk sp st (base + ∑ g : Fin m, x g • gen g) nm j =
      y0 j + dot (operandAux hk site col gen p 0) x := by
    have hix : ixAux k hk (j.val + 0) = j := Fin.ext (by simp [ixAux, Nat.mod_eq_of_lt j.2])
    have h := hy 0
    rw [hix] at h
    exact h
  have hrot : rotAux hk inj (base + ∑ g : Fin m, x g • gen g) j =
      rotAux hk inj base j + ∑ g : Fin m, rotAux hk inj (gen g) j * x g := by
    rw [rotAux_add, rotAux_sum]
    congr 1
    refine Finset.sum_congr rfl fun g _ => by rw [rotAux_smul, mul_comm]
  have hlin : dot (probeLinAux hk site col base gen u v p) x =
      dot (operandAux hk site col gen p 0) x +
      (∑ g : Fin m, rotAux hk inj (gen g) j * x g) +
      (1 + y0 (ixAux k hk (j.val + 1))) * dot (operandAux hk site col gen p 2) x +
      y0 (ixAux k hk (j.val + 2)) * dot (operandAux hk site col gen p 1) x := by
    simp only [probeLinAux, dot, add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]
    rfl
  unfold probeAux
  dsimp only
  change mixedAux hk sp st (base + ∑ g, x g • gen g) nm j +
      (1 + mixedAux hk sp st (base + ∑ g, x g • gen g) nm (ixAux k hk (j.val + 1))) *
        mixedAux hk sp st (base + ∑ g, x g • gen g) nm (ixAux k hk (j.val + 2)) +
      rotAux hk inj (base + ∑ g, x g • gen g) j + (if col p then cc j else cr j) = _
  rw [hy0, hy 1, hy 2, hrot, hlin]
  ring

private lemma hits_iff_flat_aux {k m t q : ℕ} (hk : 0 < k) (site : Fin t → Fin k) (col : Fin t → Bool)
    (base : Fin k → K) (gen : Fin m → Fin k → K) (u v cr cc : Fin k → K) :
    let key := fun x : Fin m → K => base + ∑ g : Fin m, x g • gen g
    let hits := ∃ basis : Fin q → Fin m → K,
      let D := Submodule.span K (Set.range basis)
      ∀ j, operandAux hk site col gen j 1 ∈ D ∨ operandAux hk site col gen j 2 ∈ D ∨
        operandAux hk site col gen j 1 + operandAux hk site col gen j 2 ∈ D
    let flat := ∃ U : Submodule K (Fin m → K), m ≤ Module.finrank K U + q ∧
      ∀ (z : Fin m → K) (p : Fin t), ∃ (ell : (Fin m → K) →ₗ[K] K) (c : K),
        ∀ x ∈ U, probeAux hk site col u v cr cc (key (z + x)) p = ell x + c
    hits ↔ flat := by
  intro key hits flat
  have hexp_z : ∀ (z : Fin m → K) (p : Fin t),
      ∃ (ell0 : (Fin m → K) →ₗ[K] K) (c0 : K), ∀ x : Fin m → K,
        probeAux hk site col u v cr cc (key (z + x)) p =
          ell0 x + c0 + dot (operandAux hk site col gen p 1) x * dot (operandAux hk site col gen p 2) x := by
    intro z p
    have hkey_z : ∀ x, key (z + x) = key z + ∑ g : Fin m, x g • gen g := fun x => by
      simp only [key, Pi.add_apply, add_smul, Finset.sum_add_distrib, add_assoc]
    refine ⟨dotLin (probeLinAux hk site col (key z) gen u v p),
      probeAux hk site col u v cr cc (key z) p, fun x => ?_⟩
    rw [hkey_z x, probeAux_key_expand]
    simp only [dotLin, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  constructor
  · rintro ⟨basis, hcov⟩
    let D := Submodule.span K (Set.range basis)
    refine ⟨ortho D, ?_, fun z p => ?_⟩
    · have hfr := finrank_ortho_add D
      have hDle : Module.finrank K D ≤ q := by
        have h1 := finrank_span_le_card (R := K) (Set.range basis)
        have h2 : (Set.range basis).toFinset.card ≤ q := by
          calc (Set.range basis).toFinset.card
              = (Finset.univ.image basis).card := by congr 1; ext x; simp
            _ ≤ (Finset.univ : Finset (Fin q)).card := Finset.card_image_le
            _ = q := by simp
        dsimp only [D]; omega
      omega
    · obtain ⟨ell0, c0, he0⟩ := hexp_z z p
      have haff : (∀ x ∈ ortho D, dot (operandAux hk site col gen p 1) x = 0) ∨
          (∀ x ∈ ortho D, dot (operandAux hk site col gen p 2) x = 0) ∨
          (∀ x ∈ ortho D, dot (operandAux hk site col gen p 1 + operandAux hk site col gen p 2) x = 0) := by
        rcases hcov p with h1 | h2 | h3
        · exact Or.inl fun x hx => hx _ h1
        · exact Or.inr (Or.inl fun x hx => hx _ h2)
        · exact Or.inr (Or.inr fun x hx => hx _ h3)
      obtain ⟨ell1, c1, he1⟩ := (prod_affine_iff _ _ (ortho D)).mpr haff
      refine ⟨ell0 + ell1, c0 + c1, fun x hx => ?_⟩
      rw [he0 x, he1 x hx, LinearMap.add_apply]
      ring
  · rintro ⟨U, hUdim, hUaff⟩
    let D := ortho U
    have hfr := finrank_ortho_add U
    have hDle : Module.finrank K D ≤ q := by dsimp only [D]; omega
    let bD := Module.finBasis K D
    let basis : Fin q → Fin m → K := fun i =>
      if h : i.1 < Module.finrank K D then (bD ⟨i.1, h⟩).1 else 0
    have hDsub : D ≤ Submodule.span K (Set.range basis) := by
      intro v hv
      have hrep := bD.sum_repr ⟨v, hv⟩
      have hv_eq : v = ∑ i : Fin (Module.finrank K D), bD.repr ⟨v, hv⟩ i • (bD i).1 := by
        have h1 : (⟨v, hv⟩ : D).1 = (∑ i : Fin (Module.finrank K D), bD.repr ⟨v, hv⟩ i • bD i).1 :=
          congrArg Subtype.val hrep.symm
        simpa only [Submodule.coe_sum, SetLike.val_smul] using h1
      rw [hv_eq]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      refine ⟨⟨i.1, lt_of_lt_of_le i.2 hDle⟩, ?_⟩
      simp [basis, i.2]
    refine ⟨basis, fun p => ?_⟩
    obtain ⟨ell0, c0, he0⟩ := hexp_z 0 p
    obtain ⟨ell1, c1, he1⟩ := hUaff 0 p
    have hprod_aff : ∃ (ell : (Fin m → K) →ₗ[K] K) (c : K), ∀ x ∈ U,
        dot (operandAux hk site col gen p 1) x * dot (operandAux hk site col gen p 2) x = ell x + c := by
      refine ⟨ell1 - ell0, c1 - c0, fun x hx => ?_⟩
      have h1 := he0 x
      have h2 := he1 x hx
      rw [h1] at h2
      simp only [LinearMap.sub_apply]
      linear_combination h2
    rcases (prod_affine_iff _ _ U).mp hprod_aff with h1 | h2 | h3
    · exact Or.inl (hDsub (show operandAux hk site col gen p 1 ∈ D from fun x hx => by rw [dot_comm]; exact h1 x hx))
    · exact Or.inr (Or.inl (hDsub (show operandAux hk site col gen p 2 ∈ D from fun x hx => by rw [dot_comm]; exact h2 x hx)))
    · exact Or.inr (Or.inr (hDsub (show operandAux hk site col gen p 1 + operandAux hk site col gen p 2 ∈ D from fun x hx => by rw [dot_comm]; exact h3 x hx)))

-- Generator kernel fiber counting lemma:
-- #{x : X | ∀ p, probe (key x) p = wanted p} = count * 2 ^ (m - rank(gen))
private lemma fiber_card_eq_count_mul_ker {k m : ℕ}
    (base : Fin k → K) (gen : Fin m → Fin k → K)
    (P : (Fin k → K) → Prop) [DecidablePred P] :
    let key := fun x : Fin m → K => base + ∑ g : Fin m, x g • gen g
    let Lgen : (Fin m → K) →ₗ[K] (Fin k → K) :=
      { toFun := fun x => ∑ g : Fin m, x g • gen g
        map_add' := fun x y => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := fun c x => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, Finset.smul_sum] }
    ((Finset.univ : Finset (Fin m → K)).filter (fun x => P (key x))).card =
      Nat.card { raw : Fin k → K // raw ∈ Set.range key ∧ P raw } *
        2 ^ (m - Module.finrank K (LinearMap.range Lgen)) := by
  intro key Lgen
  classical
  have hker_dim : Module.finrank K (LinearMap.ker Lgen) = m - Module.finrank K (LinearMap.range Lgen) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker Lgen
    rw [Module.finrank_fin_fun] at hrn
    omega
  have hker_card : Fintype.card (LinearMap.ker Lgen) = 2 ^ (m - Module.finrank K (LinearMap.range Lgen)) := by
    rw [← hker_dim, Module.card_eq_pow_finrank (K := K) (V := LinearMap.ker Lgen), ZMod.card]
  let S_raw : Finset (Fin k → K) :=
    (Finset.univ.image key).filter P
  have hnat_card : Nat.card { raw : Fin k → K // raw ∈ Set.range key ∧ P raw } = S_raw.card := by
    rw [Nat.card_eq_fintype_card]
    symm
    refine Finset.card_bij (fun w hw => ⟨w, ?_⟩) ?_ ?_ ?_
    · obtain ⟨himg, hP⟩ := Finset.mem_filter.mp hw
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp himg
      exact ⟨⟨x, rfl⟩, hP⟩
    · intro _ _; exact Finset.mem_univ _
    · intro _ _ _ _ h; exact congrArg Subtype.val h
    · intro ⟨w, ⟨x, hx⟩, hP⟩ _
      exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩, hP⟩, rfl⟩
  rw [hnat_card, ← hker_card]
  have hfiber : ∀ w ∈ S_raw,
      ((Finset.univ : Finset (Fin m → K)).filter (fun x => P (key x) ∧ key x = w)).card =
        Fintype.card (LinearMap.ker Lgen) := by
    intro w hw
    obtain ⟨himg, hPw⟩ := Finset.mem_filter.mp hw
    obtain ⟨x0, _, hx0⟩ := Finset.mem_image.mp himg
    symm
    refine Finset.card_bij (fun z _ => x0 + z.1) ?_ ?_ ?_
    · intro z _
      have hk : key (x0 + z.1) = w := by
        have hz : Lgen z.1 = 0 := z.2
        have hsum : key (x0 + z.1) = key x0 + Lgen z.1 := by
          simp only [key, Lgen, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, add_smul,
            Finset.sum_add_distrib, add_assoc]
        rw [hsum, hz, add_zero, hx0]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk ▸ hPw, hk⟩
    · intro z1 _ z2 _ h
      exact Subtype.ext (add_left_cancel h)
    · intro x hx
      have hkx : key x = w := (Finset.mem_filter.mp hx).2.2
      have hdiff : x - x0 ∈ LinearMap.ker Lgen := by
        change Lgen (x - x0) = 0
        rw [map_sub]
        have heq : base + Lgen x = base + Lgen x0 := by
          change key x = key x0; rw [hkx, hx0]
        rw [add_left_cancel heq, sub_self]
      refine ⟨⟨x - x0, hdiff⟩, Finset.mem_univ _, add_sub_cancel x0 x⟩
  have hpart := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin m → K)).filter (fun x => P (key x)))
    (t := S_raw) (f := key) (fun x hx => Finset.mem_filter.mpr
      ⟨Finset.mem_image_of_mem key (Finset.mem_univ x), (Finset.mem_filter.mp hx).2⟩)
  rw [hpart]
  calc ∑ w ∈ S_raw, ((Finset.univ.filter (fun x => P (key x))).filter (fun x => key x = w)).card
      = ∑ w ∈ S_raw, ((Finset.univ.filter (fun x => P (key x) ∧ key x = w))).card := by
        refine Finset.sum_congr rfl fun w _ => ?_
        congr 1; ext x; simp
    _ = ∑ _w ∈ S_raw, Fintype.card (LinearMap.ker Lgen) := Finset.sum_congr rfl hfiber
    _ = S_raw.card * Fintype.card (LinearMap.ker Lgen) := by simp

/-! ### Section 2: Pure Boolean Algorithms (`PivotTable`, `AugPivotTable`, `fptSearch`, `totalCount`) -/

private abbrev Vec (m : ℕ) := Fin m → Bool

private def vecToK {m : ℕ} (v : Vec m) : Fin m → K := fun j => b2z (v j)
private def kToVec {m : ℕ} (v : Fin m → K) : Vec m := fun j => z2b (v j)

private lemma vecToK_kToVec {m : ℕ} (v : Fin m → K) : vecToK (kToVec v) = v := by
  funext j; exact b2z_z2b (v j)

private lemma kToVec_vecToK {m : ℕ} (v : Vec m) : kToVec (vecToK v) = v := by
  funext j; exact z2b_b2z (v j)

private def vecZero (m : ℕ) : Vec m := fun _ => false
private def vecXor {m : ℕ} (a b : Vec m) : Vec m := fun j => xor (a j) (b j)
private def vecIsZero {m : ℕ} (v : Vec m) : Bool := (List.finRange m).all fun j => !v j

private lemma vecToK_zero (m : ℕ) : vecToK (vecZero m) = 0 := by
  funext j; rfl

private lemma vecToK_xor {m : ℕ} (a b : Vec m) : vecToK (vecXor a b) = vecToK a + vecToK b := by
  funext j; exact b2z_xor (a j) (b j)

private lemma vecIsZero_iff {m : ℕ} (v : Vec m) : vecIsZero v = true ↔ vecToK v = 0 := by
  simp only [vecIsZero, List.all_eq_true, List.mem_finRange, true_implies, Bool.not_eq_true']
  constructor
  · intro h; funext j; simp [vecToK, h j, b2z]
  · intro h j
    have hj : b2z (v j) = 0 := congrFun h j
    cases hv : v j
    · rfl
    · rw [hv] at hj; exact absurd hj (by decide)

private structure PivotTable (m : ℕ) where
  hasPiv : Fin m → Bool
  row : Fin m → Vec m

private def PivotTable.empty (m : ℕ) : PivotTable m :=
  ⟨fun _ => false, fun _ => vecZero m⟩

private def PivotTable.WF {m : ℕ} (T : PivotTable m) : Prop :=
  ∀ j : Fin m,
    (T.hasPiv j = true → T.row j j = true ∧ ∀ i : Fin m, i < j → T.row j i = false) ∧
    (T.hasPiv j = false → T.row j = vecZero m)

private def PivotTable.span {m : ℕ} (T : PivotTable m) : Submodule K (Fin m → K) :=
  Submodule.span K {v | ∃ j : Fin m, T.hasPiv j = true ∧ v = vecToK (T.row j)}

private lemma PivotTable.empty_wf (m : ℕ) : (PivotTable.empty m).WF := by
  intro j; simp [PivotTable.empty]

private lemma PivotTable.empty_span (m : ℕ) : (PivotTable.empty m).span = ⊥ := by
  unfold PivotTable.span PivotTable.empty
  simp

private def reduceVecStep {m : ℕ} (T : PivotTable m) (v : Vec m) (j : Fin m) : Vec m :=
  if T.hasPiv j && v j then vecXor v (T.row j) else v

private def reduceVec {m : ℕ} (T : PivotTable m) (v : Vec m) : Vec m :=
  (List.finRange m).foldl (reduceVecStep T) v

private lemma foldl_reduceVec_inv {m : ℕ} (T : PivotTable m) (hT : T.WF) (v : Vec m) :
    ∀ k (_hk : k ≤ m),
      let w := ((List.finRange m).take k).foldl (reduceVecStep T) v
      vecToK w - vecToK v ∈ T.span ∧
      ∀ j : Fin m, j.1 < k → T.hasPiv j = true → w j = false := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [sub_self]
  | succ k ih =>
    intro hk
    have htake : (List.finRange m).take (k + 1) = (List.finRange m).take k ++ [⟨k, hk⟩] := by
      rw [List.take_succ_eq_append_getElem (by simp; omega)]
      simp
    obtain ⟨hspan, hzero⟩ := ih (by omega)
    set w0 := ((List.finRange m).take k).foldl (reduceVecStep T) v
    have hw_eq : ((List.finRange m).take (k + 1)).foldl (reduceVecStep T) v =
        reduceVecStep T w0 ⟨k, hk⟩ := by
      rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
    dsimp only
    rw [hw_eq]
    unfold reduceVecStep
    split_ifs with hcond
    · obtain ⟨hpiv, hw0k⟩ := Bool.and_eq_true_iff.mp hcond
      have hrow_wf := (hT ⟨k, hk⟩).1 hpiv
      constructor
      · have hmem_row : vecToK (T.row ⟨k, hk⟩) ∈ T.span :=
          Submodule.subset_span ⟨⟨k, hk⟩, hpiv, rfl⟩
        have hdiff : vecToK (vecXor w0 (T.row ⟨k, hk⟩)) - vecToK v =
            (vecToK w0 - vecToK v) + vecToK (T.row ⟨k, hk⟩) := by
          rw [vecToK_xor]; abel
        rw [hdiff]
        exact Submodule.add_mem _ hspan hmem_row
      · intro j hj hjp
        by_cases hjk : j.1 < k
        · have hjlt : j < ⟨k, hk⟩ := hjk
          simp [vecXor, hzero j hjk hjp, hrow_wf.2 j hjlt]
        · have hjeq : j = ⟨k, hk⟩ := Fin.ext (by dsimp only; omega)
          subst hjeq
          simp [vecXor, hw0k, hrow_wf.1]
    · constructor
      · exact hspan
      · intro j hj hjp
        by_cases hjk : j.1 < k
        · exact hzero j hjk hjp
        · have hjeq : j = ⟨k, hk⟩ := Fin.ext (by dsimp only; omega)
          subst hjeq
          simp only [Bool.and_eq_true, not_and] at hcond
          exact Bool.eq_false_iff.mpr (hcond hjp)

private lemma reduceVec_spec {m : ℕ} (T : PivotTable m) (hT : T.WF) (v : Vec m) :
    (vecToK (reduceVec T v) - vecToK v ∈ T.span) ∧
    (∀ j : Fin m, T.hasPiv j = true → reduceVec T v j = false) ∧
    (vecIsZero (reduceVec T v) = true ↔ vecToK v ∈ T.span) := by
  have hfull := foldl_reduceVec_inv T hT v m (le_refl m)
  have htake : (List.finRange m).take m = List.finRange m := List.take_of_length_le (by simp)
  rw [htake] at hfull
  change vecToK (reduceVec T v) - vecToK v ∈ T.span ∧
    ∀ j : Fin m, j.1 < m → T.hasPiv j = true → reduceVec T v j = false at hfull
  refine ⟨hfull.1, fun j hj => hfull.2 j j.2 hj, ?_⟩
  rw [vecIsZero_iff]
  constructor
  · intro h0
    have hmem := hfull.1
    rw [h0, zero_sub] at hmem
    simpa using Submodule.neg_mem _ hmem
  · intro hv_mem
    have hw_mem : vecToK (reduceVec T v) ∈ T.span := by
      have := Submodule.add_mem _ hfull.1 hv_mem
      simpa using this
    have honly0 : ∀ u ∈ T.span, (∀ j : Fin m, T.hasPiv j = true → u j = 0) → u = 0 := by
      intro u hu huz
      have hgen : ∀ u ∈ T.span, ∃ c : Fin m → K,
          (∀ j, T.hasPiv j = false → c j = 0) ∧ u = ∑ j : Fin m, c j • vecToK (T.row j) := by
        intro u hu
        refine Submodule.span_induction (p := fun u _ => ∃ c : Fin m → K,
          (∀ j, T.hasPiv j = false → c j = 0) ∧ u = ∑ j : Fin m, c j • vecToK (T.row j)) ?_ ?_ ?_ ?_ hu
        · rintro _ ⟨j, hj, rfl⟩
          refine ⟨Pi.single j 1, fun i hi => ?_, ?_⟩
          · by_cases hij : i = j
            · subst hij; rw [hj] at hi; exact absurd hi (by decide)
            · simp [hij]
          · rw [Finset.sum_eq_single j]
            · simp
            · intro i _ hij; simp [hij]
            · intro hnm; exact absurd (Finset.mem_univ j) hnm
        · exact ⟨0, fun _ _ => rfl, by simp⟩
        · rintro _ _ _ _ ⟨c1, hc1, rfl⟩ ⟨c2, hc2, rfl⟩
          exact ⟨c1 + c2, fun j hj => by simp [hc1 j hj, hc2 j hj], by
            simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
        · rintro a _ _ ⟨c1, hc1, rfl⟩
          exact ⟨a • c1, fun j hj => by simp [hc1 j hj], by
            simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]⟩
      obtain ⟨c, hc0, rfl⟩ := hgen u hu
      have hall_c0 : ∀ j : Fin m, c j = 0 := by
        intro j
        rcases j with ⟨jv, hjv⟩
        induction jv using Nat.strong_induction_on with
        | ind jv ih =>
          by_cases hp : T.hasPiv ⟨jv, hjv⟩ = true
          · have hzero_j := huz ⟨jv, hjv⟩ hp
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hzero_j
            have hsum_eq : ∑ i : Fin m, c i * vecToK (T.row i) ⟨jv, hjv⟩ = c ⟨jv, hjv⟩ := by
              rw [Finset.sum_eq_single ⟨jv, hjv⟩]
              · simp [vecToK, ((hT ⟨jv, hjv⟩).1 hp).1, b2z]
              · intro i _ hij
                by_cases hlt : i.1 < jv
                · rw [ih i.1 hlt i.2, zero_mul]
                · have hgt : (⟨jv, hjv⟩ : Fin m) < i := by
                    have hne : i.1 ≠ jv := fun h => hij (Fin.ext h)
                    exact Nat.lt_of_le_of_ne (by dsimp only; omega) hne.symm
                  by_cases hip : T.hasPiv i = true
                  · simp [vecToK, ((hT i).1 hip).2 ⟨jv, hjv⟩ hgt, b2z]
                  · rw [hc0 i (Bool.eq_false_iff.mpr hip), zero_mul]
              · intro hnm; exact absurd (Finset.mem_univ _) hnm
            rw [hsum_eq] at hzero_j
            exact hzero_j
          · exact hc0 ⟨jv, hjv⟩ (Bool.eq_false_iff.mpr hp)
      simp [hall_c0]
    exact honly0 _ hw_mem fun j hj => by simp [vecToK, hfull.2 j j.2 hj, b2z]

private def firstTrue {m : ℕ} (v : Vec m) : Fin m → Bool := fun j =>
  v j && (List.finRange m).all fun i => decide (i.1 < j.1) == false || !v i

private lemma firstTrue_spec {m : ℕ} (v : Vec m) (j : Fin m) :
    firstTrue v j = true ↔ v j = true ∧ ∀ i : Fin m, i < j → v i = false := by
  simp only [firstTrue, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, beq_iff_eq, decide_eq_false_iff_not, Bool.not_eq_true']
  constructor
  · rintro ⟨hvj, hall⟩
    refine ⟨hvj, fun i hij => ?_⟩
    rcases hall i with hnot | hfi
    · exact absurd hij hnot
    · exact hfi
  · rintro ⟨hvj, hall⟩
    refine ⟨hvj, fun i => ?_⟩
    by_cases hij : i < j
    · exact Or.inr (hall i hij)
    · exact Or.inl hij

private def insertVec {m : ℕ} (T : PivotTable m) (v : Vec m) : PivotTable m :=
  let w := reduceVec T v
  let ft := firstTrue w
  { hasPiv := fun j => T.hasPiv j || ft j
    row := fun j => if ft j then w else T.row j }

private lemma insertVec_spec {m : ℕ} (T : PivotTable m) (hT : T.WF) (v : Vec m) :
    (insertVec T v).WF ∧
    (insertVec T v).span = T.span ⊔ Submodule.span K {vecToK v} := by
  obtain ⟨hw_diff, hw_piv0, hw_zero_iff⟩ := reduceVec_spec T hT v
  have hft_not_piv : ∀ j : Fin m, firstTrue (reduceVec T v) j = true → T.hasPiv j = false := by
    intro j hj
    have hwj := ((firstTrue_spec (reduceVec T v) j).mp hj).1
    by_contra hp
    have hpt : T.hasPiv j = true := Bool.eq_true_of_not_eq_false hp
    rw [hw_piv0 j hpt] at hwj
    exact Bool.false_ne_true hwj
  have hwf : (insertVec T v).WF := by
    intro j
    constructor
    · intro hp
      simp only [insertVec, Bool.or_eq_true] at hp
      by_cases hft : firstTrue (reduceVec T v) j = true
      · simp only [insertVec, hft, ↓reduceIte]
        exact (firstTrue_spec (reduceVec T v) j).mp hft
      · have htp : T.hasPiv j = true := hp.resolve_right hft
        simp only [insertVec, hft]
        exact (hT j).1 htp
    · intro hpf
      simp only [insertVec, Bool.or_eq_false_iff] at hpf
      simp only [insertVec, hpf.2, Bool.false_eq_true, ↓reduceIte]
      exact (hT j).2 hpf.1
  have hsubT : T.span ≤ (insertVec T v).span := by
    rw [PivotTable.span, Submodule.span_le]
    rintro _ ⟨j, htp, rfl⟩
    have hft : firstTrue (reduceVec T v) j = false := by
      by_contra h
      rw [hft_not_piv j (Bool.eq_true_of_not_eq_false h)] at htp
      exact Bool.false_ne_true htp
    exact Submodule.subset_span ⟨j, by simp [insertVec, htp], by simp [insertVec, hft]⟩
  refine ⟨hwf, ?_⟩
  apply le_antisymm
  · rw [PivotTable.span, Submodule.span_le]
    rintro _ ⟨j, hp, rfl⟩
    by_cases hft : firstTrue (reduceVec T v) j = true
    · simp only [insertVec, hft, ↓reduceIte]
      have hw_eq : vecToK (reduceVec T v) = (vecToK (reduceVec T v) - vecToK v) + vecToK v := by abel
      rw [hw_eq]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hw_diff)
        (Submodule.mem_sup_right (Submodule.subset_span rfl))
    · simp only [insertVec, hft, Bool.false_eq_true, ↓reduceIte]
      have htp : T.hasPiv j = true := by
        simp only [insertVec, Bool.or_eq_true] at hp
        exact hp.resolve_right hft
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨j, htp, rfl⟩)
  · refine sup_le hsubT ?_
    rw [Submodule.span_le]
    intro u hu
    rw [Set.mem_singleton_iff] at hu; subst hu
    by_cases hw0 : vecToK (reduceVec T v) = 0
    · exact hsubT (hw_zero_iff.mp ((vecIsZero_iff _).mpr hw0))
    · have hex : ∃ j : Fin m, reduceVec T v j = true := by
        by_contra h; push Not at h
        apply hw0; funext j
        have hfj : reduceVec T v j = false := Bool.eq_false_iff.mpr (h j)
        simp [vecToK, hfj, b2z]
      let S := Finset.univ.filter (fun j : Fin m => reduceVec T v j = true)
      have hSne : S.Nonempty := by obtain ⟨j, hj⟩ := hex; exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
      let j0 := S.min' hSne
      have hj0_mem : reduceVec T v j0 = true := (Finset.mem_filter.mp (Finset.min'_mem S hSne)).2
      have hj0_min : ∀ i : Fin m, i < j0 → reduceVec T v i = false := by
        intro i hi
        by_contra h
        have hwi : reduceVec T v i = true := Bool.eq_true_of_not_eq_false h
        have hle := Finset.min'_le S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwi⟩)
        exact not_le_of_gt hi hle
      have hft0 : firstTrue (reduceVec T v) j0 = true := (firstTrue_spec _ j0).mpr ⟨hj0_mem, hj0_min⟩
      have hw_in : vecToK (reduceVec T v) ∈ (insertVec T v).span :=
        Submodule.subset_span ⟨j0, by simp [insertVec, hft0], by simp [insertVec, hft0]⟩
      have hv_eq : vecToK v = vecToK (reduceVec T v) - (vecToK (reduceVec T v) - vecToK v) := by abel
      rw [hv_eq]
      exact Submodule.sub_mem _ hw_in (hsubT hw_diff)

private lemma PivotTable.finrank_eq_count {m : ℕ} (T : PivotTable m) (hT : T.WF) :
    Module.finrank K T.span = ((Finset.univ : Finset (Fin m)).filter (fun j => T.hasPiv j = true)).card := by
  let P := (Finset.univ : Finset (Fin m)).filter (fun j => T.hasPiv j = true)
  let f : ↥P → Fin m → K := fun j => vecToK (T.row j.1)
  have hli : LinearIndependent K f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    rcases i with ⟨⟨iv, hiv⟩, hiP⟩
    induction iv using Nat.strong_induction_on with
    | ind iv ih =>
      have hip : T.hasPiv ⟨iv, hiv⟩ = true := (Finset.mem_filter.mp hiP).2
      have h0 : (∑ j : ↥P, c j • f j) ⟨iv, hiv⟩ = 0 := by rw [hc]; rfl
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f] at h0
      have hsum : ∑ j : ↥P, c j * vecToK (T.row j.1) ⟨iv, hiv⟩ = c ⟨⟨iv, hiv⟩, hiP⟩ := by
        rw [Finset.sum_eq_single ⟨⟨iv, hiv⟩, hiP⟩]
        · simp [vecToK, ((hT ⟨iv, hiv⟩).1 hip).1, b2z]
        · intro j _ hij
          by_cases hlt : j.1.1 < iv
          · rw [ih j.1.1 hlt j.1.2 j.2, zero_mul]
          · have hgt : (⟨iv, hiv⟩ : Fin m) < j.1 := by
              have hne : j.1.1 ≠ iv := fun h => hij (Subtype.ext (Fin.ext h))
              exact Nat.lt_of_le_of_ne (by dsimp only; omega) hne.symm
            have hjp : T.hasPiv j.1 = true := (Finset.mem_filter.mp j.2).2
            simp [vecToK, ((hT j.1).1 hjp).2 ⟨iv, hiv⟩ hgt, b2z]
        · intro hnm; exact absurd (Finset.mem_univ _) hnm
      rw [hsum] at h0
      exact h0
  have hsp : T.span = Submodule.span K (Set.range f) := by
    unfold PivotTable.span
    congr 1; ext v
    simp only [Set.mem_ofPred_eq, Set.mem_range, f]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩, rfl⟩
    · rintro ⟨⟨j, hj⟩, rfl⟩; exact ⟨j, (Finset.mem_filter.mp hj).2, rfl⟩
  rw [hsp, finrank_span_eq_card hli, Fintype.card_coe]

-- Augmented Pivot Table for solving linear equations over ZMod 2
private structure AugTable (m : ℕ) where
  piv : PivotTable m
  rhs : Fin m → Bool
  inc : Bool

private def AugTable.empty (m : ℕ) : AugTable m :=
  ⟨PivotTable.empty m, fun _ => false, false⟩

private def AugTable.Sols {m : ℕ} (A : AugTable m) : Set (Fin m → K) :=
  {x | A.inc = false ∧ ∀ j : Fin m, A.piv.hasPiv j = true → dot (vecToK (A.piv.row j)) x = b2z (A.rhs j)}

private def augReduceStep {m : ℕ} (A : AugTable m) (vr : Vec m × Bool) (j : Fin m) : Vec m × Bool :=
  if A.piv.hasPiv j && vr.1 j then (vecXor vr.1 (A.piv.row j), xor vr.2 (A.rhs j)) else vr

private def augReduce {m : ℕ} (A : AugTable m) (v : Vec m) (r : Bool) : Vec m × Bool :=
  (List.finRange m).foldl (augReduceStep A) (v, r)

private def augInsert {m : ℕ} (A : AugTable m) (v : Vec m) (r : Bool) : AugTable m :=
  let wr := augReduce A v r
  let w := wr.1
  let r' := wr.2
  let ft := firstTrue w
  let isZ := vecIsZero w
  { piv := { hasPiv := fun j => A.piv.hasPiv j || ft j
             row := fun j => if ft j then w else A.piv.row j }
    rhs := fun j => if ft j then r' else A.rhs j
    inc := A.inc || (isZ && r') }

private lemma augReduce_fst {m : ℕ} (A : AugTable m) (v : Vec m) (r : Bool) :
    (augReduce A v r).1 = reduceVec A.piv v := by
  unfold augReduce reduceVec
  have hgen : ∀ (l : List (Fin m)) (v : Vec m) (r : Bool),
      (l.foldl (augReduceStep A) (v, r)).1 = l.foldl (reduceVecStep A.piv) v := by
    intro l
    induction l with
    | nil => intros; rfl
    | cons j l ih =>
      intro v r
      simp only [List.foldl_cons, augReduceStep, reduceVecStep]
      split_ifs <;> exact ih _ _
  exact hgen _ v r

private lemma augReduce_sol_iff {m : ℕ} (A : AugTable m) (v : Vec m) (r : Bool)
    (x : Fin m → K) (hx : ∀ j : Fin m, A.piv.hasPiv j = true → dot (vecToK (A.piv.row j)) x = b2z (A.rhs j)) :
    dot (vecToK (augReduce A v r).1) x + b2z (augReduce A v r).2 = dot (vecToK v) x + b2z r := by
  unfold augReduce
  have hgen : ∀ (l : List (Fin m)) (v : Vec m) (r : Bool),
      dot (vecToK (l.foldl (augReduceStep A) (v, r)).1) x + b2z (l.foldl (augReduceStep A) (v, r)).2 =
        dot (vecToK v) x + b2z r := by
    intro l
    induction l with
    | nil => intros; rfl
    | cons j l ih =>
      intro v r
      simp only [List.foldl_cons, augReduceStep]
      split_ifs with hcond
      · rw [ih]
        obtain ⟨hpiv, _⟩ := Bool.and_eq_true_iff.mp hcond
        rw [vecToK_xor, dot_add_left, b2z_xor, hx j hpiv]
        have h2 := z2_add_self (b2z (A.rhs j))
        linear_combination h2
      · exact ih v r
  exact hgen _ v r

private lemma augInsert_spec {m : ℕ} (A : AugTable m) (hA : A.piv.WF) (v : Vec m) (r : Bool) :
    (augInsert A v r).piv.WF ∧
    (augInsert A v r).Sols = {x | x ∈ A.Sols ∧ dot (vecToK v) x = b2z r} := by
  have hpiv_eq : (augInsert A v r).piv = insertVec A.piv v := by
    simp only [augInsert, insertVec, augReduce_fst]
  have hwf : (augInsert A v r).piv.WF := by
    rw [hpiv_eq]; exact (insertVec_spec A.piv hA v).1
  refine ⟨hwf, ?_⟩
  have hw_eq : (augReduce A v r).1 = reduceVec A.piv v := augReduce_fst A v r
  obtain ⟨_, hw_piv0, _⟩ := reduceVec_spec A.piv hA v
  have hft_not_piv : ∀ j : Fin m, firstTrue (augReduce A v r).1 j = true → A.piv.hasPiv j = false := by
    intro j hj
    have hwj := ((firstTrue_spec (augReduce A v r).1 j).mp hj).1
    rw [hw_eq] at hwj
    by_contra hp
    rw [hw_piv0 j (Bool.eq_true_of_not_eq_false hp)] at hwj
    exact Bool.false_ne_true hwj
  ext x
  simp only [AugTable.Sols, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hinc', hall'⟩
    simp only [augInsert, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at hinc'
    have hAinc : A.inc = false := hinc'.1
    have hAall : ∀ j : Fin m, A.piv.hasPiv j = true → dot (vecToK (A.piv.row j)) x = b2z (A.rhs j) := by
      intro j hjp
      have hft : firstTrue (augReduce A v r).1 j = false := by
        by_contra h
        rw [hft_not_piv j (Bool.eq_true_of_not_eq_false h)] at hjp
        exact Bool.false_ne_true hjp
      have h1 := hall' j (by simp [augInsert, hjp])
      simpa [augInsert, hft] using h1
    refine ⟨⟨hAinc, hAall⟩, ?_⟩
    have hred := augReduce_sol_iff A v r x hAall
    by_cases hwz : vecIsZero (augReduce A v r).1 = true
    · have hw0 : vecToK (augReduce A v r).1 = 0 := (vecIsZero_iff _).mp hwz
      have hr'0 : (augReduce A v r).2 = false := by
        rcases hinc'.2 with hnz | hrf
        · rw [hwz] at hnz; exact absurd hnz (by decide)
        · exact hrf
      have h0 : dot (vecToK v) x + b2z r = 0 := by
        rw [← hred]; simp [hw0, hr'0, dot_zero_left, b2z]
      have h2 := z2_add_self (b2z r)
      linear_combination h0 - h2
    · have hwne : vecToK (augReduce A v r).1 ≠ 0 := fun h => hwz ((vecIsZero_iff _).mpr h)
      have hex : ∃ j : Fin m, (augReduce A v r).1 j = true := by
        by_contra h; push Not at h
        apply hwne; funext j; simp [vecToK, Bool.eq_false_iff.mpr (h j), b2z]
      let S := Finset.univ.filter (fun j : Fin m => (augReduce A v r).1 j = true)
      have hSne : S.Nonempty := by obtain ⟨j, hj⟩ := hex; exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
      let j0 := S.min' hSne
      have hft0 : firstTrue (augReduce A v r).1 j0 = true := (firstTrue_spec _ j0).mpr
        ⟨(Finset.mem_filter.mp (Finset.min'_mem S hSne)).2, fun i hi => by
          by_contra h
          exact not_le_of_gt hi (Finset.min'_le S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Bool.eq_true_of_not_eq_false h⟩))⟩
      have hj0 := hall' j0 (by simp [augInsert, hft0])
      simp only [augInsert, hft0, ↓reduceIte] at hj0
      have h0 : dot (vecToK v) x + b2z r = 0 := by
        rw [← hred, hj0, z2_add_self]
      have h2 := z2_add_self (b2z r)
      linear_combination h0 - h2
  · rintro ⟨⟨hAinc, hAall⟩, hvx⟩
    have hred := augReduce_sol_iff A v r x hAall
    have hwr_eq : dot (vecToK (augReduce A v r).1) x = b2z (augReduce A v r).2 := by
      have h0 : dot (vecToK (augReduce A v r).1) x + b2z (augReduce A v r).2 = 0 := by
        rw [hred, hvx, z2_add_self]
      have h2 := z2_add_self (b2z (augReduce A v r).2)
      linear_combination h0 - h2
    constructor
    · simp only [augInsert, hAinc, Bool.false_or, Bool.and_eq_false_iff]
      by_cases hwz : vecIsZero (augReduce A v r).1 = true
      · right
        have hw0 : vecToK (augReduce A v r).1 = 0 := (vecIsZero_iff _).mp hwz
        rw [hw0, dot_zero_left] at hwr_eq
        cases hr : (augReduce A v r).2
        · rfl
        · rw [hr] at hwr_eq; exact absurd hwr_eq (by decide)
      · exact Or.inl (Bool.eq_false_iff.mpr hwz)
    · intro j hjp
      by_cases hft : firstTrue (augReduce A v r).1 j = true
      · simp only [augInsert, hft, ↓reduceIte]; exact hwr_eq
      · simp only [augInsert, hft, Bool.false_eq_true, ↓reduceIte]
        simp only [augInsert, Bool.or_eq_true] at hjp
        exact hAall j (hjp.resolve_right hft)

-- Back-substitution on a WF AugTable: given free-variable values `free : Vec m`, produces a unique solution!
private def backSubStep {m : ℕ} (A : AugTable m) (free : Vec m) (j : Fin m) (cur : Vec m) : Vec m :=
  let tailDot := (List.finRange m).foldl (fun acc l =>
    if decide (j.1 < l.1) && A.piv.row j l && cur l then !acc else acc) false
  let val := if A.piv.hasPiv j then xor (A.rhs j) tailDot else free j
  fun i => if i = j then val else cur i

private def backSubWith {m : ℕ} (A : AugTable m) (free : Vec m) : Vec m :=
  (List.finRange m).foldr (backSubStep A free) (vecZero m)

private def backSub {m : ℕ} (A : AugTable m) : Vec m :=
  backSubWith A (vecZero m)

private lemma foldl_tailDot_eq {m : ℕ} (r cur : Vec m) (j : Fin m) :
    b2z ((List.finRange m).foldl (fun acc l =>
      if decide (j.1 < l.1) && r l && cur l then !acc else acc) false) =
    ∑ l : Fin m, if j < l then b2z (r l) * b2z (cur l) else 0 := by
  have hgen : ∀ (L : List (Fin m)) (init : Bool),
      L.Nodup →
      b2z (L.foldl (fun acc l => if decide (j.1 < l.1) && r l && cur l then !acc else acc) init) =
        b2z init + ∑ l ∈ L.toFinset, if j < l then b2z (r l) * b2z (cur l) else 0 := by
    intro L
    induction L with
    | nil => intro init _; simp
    | cons a L ih =>
      intro init hnd
      obtain ⟨haL, hndL⟩ := List.nodup_cons.mp hnd
      rw [List.foldl_cons, ih _ hndL, List.toFinset_cons,
        Finset.sum_insert (by simpa using haL)]
      have hterm : b2z (if decide (j.1 < a.1) && r a && cur a then !init else init) =
          b2z init + (if j < a then b2z (r a) * b2z (cur a) else 0) := by
        by_cases hja : j < a
        · have hja' : j.1 < a.1 := hja
          cases hra : r a <;> cases hca : cur a <;> cases init <;> simp [hja, hja', b2z, z2_add_self]
        · have hja' : ¬ j.1 < a.1 := hja
          simp [hja, hja']
      rw [hterm]; ring
  have h1 := hgen (List.finRange m) false (List.nodup_finRange m)
  have hto : (List.finRange m).toFinset = Finset.univ := by ext x; simp
  rw [hto] at h1
  simpa [b2z] using h1

private lemma backSubWith_spec {m : ℕ} (A : AugTable m) (hA : A.piv.WF) (free : Vec m) :
    (∀ j : Fin m, A.piv.hasPiv j = false → backSubWith A free j = free j) ∧
    (∀ j : Fin m, A.piv.hasPiv j = true →
      dot (vecToK (A.piv.row j)) (vecToK (backSubWith A free)) = b2z (A.rhs j)) := by
  have hgen : ∀ (k : ℕ) (hk : k ≤ m),
      let w := ((List.finRange m).drop (m - k)).foldr (backSubStep A free) (vecZero m)
      (∀ j : Fin m, m - k ≤ j.1 → A.piv.hasPiv j = false → w j = free j) ∧
      (∀ j : Fin m, m - k ≤ j.1 → A.piv.hasPiv j = true →
        dot (vecToK (A.piv.row j)) (vecToK w) = b2z (A.rhs j)) ∧
      (∀ j : Fin m, j.1 < m - k → w j = false) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hdrop : (List.finRange m).drop (m - 0) = [] := by simp
      simp only [hdrop, List.foldr_nil]
      exact ⟨fun j hj => by omega, fun j hj => by omega, fun j _ => rfl⟩
    | succ k ih =>
      intro hk
      have hlt : m - (k + 1) < m := by omega
      have hdrop : (List.finRange m).drop (m - (k + 1)) =
          ⟨m - (k + 1), hlt⟩ :: (List.finRange m).drop (m - k) := by
        rw [List.drop_eq_getElem_cons (by simp; omega)]
        simp [show m - (k + 1) + 1 = m - k by omega]
      obtain ⟨ih_free, ih_piv, ih_zero⟩ := ih (by omega)
      set j0 : Fin m := ⟨m - (k + 1), hlt⟩
      set w0 := ((List.finRange m).drop (m - k)).foldr (backSubStep A free) (vecZero m)
      have hw_eq : ((List.finRange m).drop (m - (k + 1))).foldr (backSubStep A free) (vecZero m) =
          backSubStep A free j0 w0 := by
        rw [hdrop, List.foldr_cons]
      dsimp only
      rw [hw_eq]
      have hge_eq : ∀ i : Fin m, j0 < i → backSubStep A free j0 w0 i = w0 i := fun i hi => by
        have hne : i ≠ j0 := ne_of_gt hi
        simp [backSubStep, hne]
      refine ⟨?_, ?_, ?_⟩
      · intro j hj hjp
        by_cases hjj0 : j = j0
        · subst hjj0; simp [backSubStep, hjp]
        · have hjgt : m - k ≤ j.1 := by
            have : j.1 ≠ m - (k + 1) := fun h => hjj0 (Fin.ext h)
            omega
          rw [hge_eq j (by show j0.1 < j.1; dsimp only [j0]; omega)]
          exact ih_free j hjgt hjp
      · intro j hj hjp
        by_cases hjj0 : j = j0
        · subst hjj0
          have hrow := (hA j0).1 hjp
          have hdot_split : dot (vecToK (A.piv.row j0)) (vecToK (backSubStep A free j0 w0)) =
              b2z (backSubStep A free j0 w0 j0) +
              ∑ l : Fin m, if j0 < l then b2z (A.piv.row j0 l) * b2z (w0 l) else 0 := by
            unfold dot
            have hpart := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin m))
              (fun l => j0 < l) (fun l => vecToK (A.piv.row j0) l * vecToK (backSubStep A free j0 w0) l)
            rw [← hpart, add_comm]
            congr 1
            · rw [Finset.sum_eq_single j0]
              · simp [vecToK, hrow.1, b2z]
              · intro l hl hne
                have hnotlt : ¬ j0 < l := (Finset.mem_filter.mp hl).2
                have hlt' : l < j0 := lt_of_le_of_ne (not_lt.mp hnotlt) hne
                simp [vecToK, hrow.2 l hlt', b2z]
              · intro hnm
                have hmem0 : j0 ∈ (Finset.univ : Finset (Fin m)).filter (fun l => ¬ j0 < l) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ j0, lt_irrefl j0⟩
                exact absurd hmem0 hnm
            · rw [Finset.sum_filter]
              refine Finset.sum_congr rfl fun l _ => ?_
              split_ifs with hlt'
              · rw [vecToK, vecToK, hge_eq l hlt']
              · rfl
          rw [hdot_split]
          have hval : b2z (backSubStep A free j0 w0 j0) =
              b2z (A.rhs j0) + ∑ l : Fin m, if j0 < l then b2z (A.piv.row j0 l) * b2z (w0 l) else 0 := by
            simp only [backSubStep, ↓reduceIte, hjp, b2z_xor, foldl_tailDot_eq]
          rw [hval, add_assoc, z2_add_self, add_zero]
        · have hjgt : m - k ≤ j.1 := by
            have : j.1 ≠ m - (k + 1) := fun h => hjj0 (Fin.ext h)
            omega
          have hrow := (hA j).1 hjp
          have hdot_eq : dot (vecToK (A.piv.row j)) (vecToK (backSubStep A free j0 w0)) =
              dot (vecToK (A.piv.row j)) (vecToK w0) := by
            unfold dot
            refine Finset.sum_congr rfl fun l _ => ?_
            by_cases hlj0 : l = j0
            · subst hlj0
              have hj0lt : j0 < j := by show j0.1 < j.1; dsimp only [j0]; omega
              simp [vecToK, hrow.2 j0 hj0lt, b2z]
            · simp [vecToK, backSubStep, hlj0]
          rw [hdot_eq]
          exact ih_piv j hjgt hjp
      · intro j hj
        have hne : j ≠ j0 := fun h => by have := congrArg Fin.val h; dsimp [j0] at this; omega
        simp only [backSubStep, hne, ↓reduceIte]
        exact ih_zero j (by omega)
  have hfull := hgen m (le_refl m)
  have hdrop0 : (List.finRange m).drop (m - m) = List.finRange m := by simp
  rw [hdrop0, Nat.sub_self] at hfull
  exact ⟨fun j hp => hfull.1 j (Nat.zero_le _) hp, fun j hp => hfull.2.1 j (Nat.zero_le _) hp⟩

private lemma augTable_card_sols {m : ℕ} (A : AugTable m) (hA : A.piv.WF) :
    letI := Classical.decPred (fun x : Fin m → K => x ∈ A.Sols)
    ((Finset.univ : Finset (Fin m → K)).filter (fun x => x ∈ A.Sols)).card =
      if A.inc then 0
      else 2 ^ (m - ((Finset.univ : Finset (Fin m)).filter (fun j => A.piv.hasPiv j = true)).card) := by
  classical
  by_cases hinc : A.inc = true
  · simp only [hinc, ↓reduceIte]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    have h1 := hx.1
    rw [hinc] at h1
    exact Bool.false_ne_true h1.symm
  · have hincf : A.inc = false := Bool.eq_false_iff.mpr hinc
    simp only [hincf, Bool.false_eq_true, ↓reduceIte]
    let FreeIdx := (Finset.univ : Finset (Fin m)).filter (fun j => A.piv.hasPiv j = false)
    have hcard_free : FreeIdx.card =
        m - ((Finset.univ : Finset (Fin m)).filter (fun j => A.piv.hasPiv j = true)).card := by
      have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
        (p := fun j => A.piv.hasPiv j = true)
      have hfeq : FreeIdx = (Finset.univ : Finset (Fin m)).filter (fun j => ¬ A.piv.hasPiv j = true) := by
        ext j; simp [FreeIdx]
      rw [← hfeq, Finset.card_univ, Fintype.card_fin] at htot
      omega
    rw [← hcard_free]
    have hpow : 2 ^ FreeIdx.card = (Finset.univ : Finset (↥FreeIdx → Bool)).card := by
      simp
    rw [hpow]
    symm
    refine Finset.card_bij
      (fun (f : ↥FreeIdx → Bool) _ =>
        vecToK (backSubWith A (fun j => if h : j ∈ FreeIdx then f ⟨j, h⟩ else false))) ?_ ?_ ?_
    · intro f _
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hincf, fun j hjp => ?_⟩
      exact (backSubWith_spec A hA _).2 j hjp
    · intro f1 _ f2 _ heq
      funext ⟨j, hj⟩
      have hjp : A.piv.hasPiv j = false := (Finset.mem_filter.mp hj).2
      have hj1 := (backSubWith_spec A hA (fun j => if h : j ∈ FreeIdx then f1 ⟨j, h⟩ else false)).1 j hjp
      have hj2 := (backSubWith_spec A hA (fun j => if h : j ∈ FreeIdx then f2 ⟨j, h⟩ else false)).1 j hjp
      have hbj : b2z (backSubWith A (fun j => if h : j ∈ FreeIdx then f1 ⟨j, h⟩ else false) j) =
          b2z (backSubWith A (fun j => if h : j ∈ FreeIdx then f2 ⟨j, h⟩ else false) j) :=
        congrFun heq j
      have hbe := b2z_injective hbj
      rw [hj1, hj2] at hbe
      simpa [hj] using hbe
    · intro x hx
      have hxsol := (Finset.mem_filter.mp hx).2
      let f : ↥FreeIdx → Bool := fun j => z2b (x j.1)
      refine ⟨f, Finset.mem_univ _, ?_⟩
      let w := backSubWith A (fun j => if h : j ∈ FreeIdx then f ⟨j, h⟩ else false)
      have hspec := backSubWith_spec A hA (fun j => if h : j ∈ FreeIdx then f ⟨j, h⟩ else false)
      -- Show vecToK w = x by downward induction on j from m - 1 down to 0
      funext j
      rcases j with ⟨jv, hjv⟩
      suffices hdown : ∀ d : ℕ, d ≤ m → ∀ j : Fin m, m - d ≤ j.1 → vecToK w j = x j by
        exact hdown m (le_refl m) ⟨jv, hjv⟩ (by omega)
      intro d
      induction d with
      | zero => intro _ j hj; omega
      | succ d ih =>
        intro hd j hj
        by_cases hgt : m - d ≤ j.1
        · exact ih (by omega) j hgt
        · have hjeq : j.1 = m - (d + 1) := by omega
          by_cases hjp : A.piv.hasPiv j = true
          · have h1 := hspec.2 j hjp
            have h2 := hxsol.2 j hjp
            have hrow := (hA j).1 hjp
            have hdiff : dot (vecToK (A.piv.row j)) (vecToK w) - dot (vecToK (A.piv.row j)) x = 0 := by
              rw [h1, h2, sub_self]
            have hsum_eq : dot (vecToK (A.piv.row j)) (vecToK w) - dot (vecToK (A.piv.row j)) x =
                vecToK w j - x j := by
              unfold dot
              rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
              · simp [vecToK, hrow.1, b2z]
              · intro l _ hlj
                by_cases hlt : l < j
                · simp [vecToK, hrow.2 l hlt, b2z]
                · have hlgt : m - d ≤ l.1 := by
                    have hne : l.1 ≠ j.1 := fun h => hlj (Fin.ext h)
                    have : j.1 ≤ l.1 := not_lt.mp hlt
                    omega
                  rw [ih (by omega) l hlgt, sub_self]
              · intro hnm; exact absurd (Finset.mem_univ j) hnm
            rw [hsum_eq] at hdiff
            exact sub_eq_zero.mp hdiff
          · have hjf : A.piv.hasPiv j = false := Bool.eq_false_iff.mpr hjp
            have hjmem : j ∈ FreeIdx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjf⟩
            have hwj := hspec.1 j hjf
            simp only [vecToK, w, hwj, hjmem, ↓reduceDIte, f, b2z_z2b]

-- One-hot count of true flags in `f : Fin len → Bool`
private def oneHotStep {len : ℕ} (oh : Fin (len + 1) → Bool) (flag : Bool) : Fin (len + 1) → Bool :=
  fun r => if flag then (if h : 0 < r.1 then oh ⟨r.1 - 1, by omega⟩ else false) else oh r

private def oneHotCount {len : ℕ} (f : Fin len → Bool) : Fin (len + 1) → Bool :=
  (List.finRange len).foldl (fun oh j => oneHotStep oh (f j)) (fun r => decide (r.1 = 0))

private lemma oneHotCount_spec {len : ℕ} (f : Fin len → Bool) (r : Fin (len + 1)) :
    oneHotCount f r = decide (r.1 = ((Finset.univ : Finset (Fin len)).filter (fun j => f j = true)).card) := by
  have hgen : ∀ (k : ℕ) (hk : k ≤ len) (r : Fin (len + 1)),
      ((List.finRange len).take k).foldl (fun oh j => oneHotStep oh (f j)) (fun r => decide (r.1 = 0)) r =
        decide (r.1 = ((Finset.univ : Finset (Fin len)).filter (fun j => j.1 < k ∧ f j = true)).card) := by
    intro k
    induction k with
    | zero =>
      intro _ r
      simp
    | succ k ih =>
      intro hk r
      have htake : (List.finRange len).take (k + 1) = (List.finRange len).take k ++ [⟨k, hk⟩] := by
        rw [List.take_succ_eq_append_getElem (by simp; omega)]
        simp
      set oh0 := ((List.finRange len).take k).foldl (fun oh j => oneHotStep oh (f j)) (fun r => decide (r.1 = 0))
      rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set S0 := (Finset.univ : Finset (Fin len)).filter (fun j => j.1 < k ∧ f j = true)
      set S1 := (Finset.univ : Finset (Fin len)).filter (fun j => j.1 < k + 1 ∧ f j = true)
      change oneHotStep oh0 (f ⟨k, hk⟩) r = decide (r.1 = S1.card)
      unfold oneHotStep
      by_cases hfk : f ⟨k, hk⟩ = true
      · have hS1 : S1 = insert ⟨k, hk⟩ S0 := by
          ext j
          simp only [S1, S0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · rintro ⟨h1, h2⟩
            by_cases hjk : j.1 < k
            · exact Or.inr ⟨hjk, h2⟩
            · exact Or.inl (Fin.ext (by dsimp only; omega))
          · rintro (rfl | ⟨h1, h2⟩)
            · exact ⟨by dsimp only; omega, hfk⟩
            · exact ⟨by omega, h2⟩
        have hnotmem : (⟨k, hk⟩ : Fin len) ∉ S0 := by simp [S0]
        have hcard : S1.card = S0.card + 1 := by rw [hS1, Finset.card_insert_of_notMem hnotmem]
        simp only [hfk, ↓reduceIte, hcard]
        split_ifs with hr
        · rw [ih (by omega) ⟨r.1 - 1, by omega⟩]
          have : r.1 - 1 = S0.card ↔ r.1 = S0.card + 1 := by omega
          simp [this]
        · have hr0 : r.1 = 0 := by omega
          simp [hr0]
      · have hfkf : f ⟨k, hk⟩ = false := Bool.eq_false_iff.mpr hfk
        have hS1 : S1 = S0 := by
          ext j
          simp only [S1, S0, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨?_, h2⟩
            by_contra hge
            have hjeq : j = ⟨k, hk⟩ := Fin.ext (by dsimp only; omega)
            subst hjeq; rw [hfkf] at h2; exact Bool.false_ne_true h2
          · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
        simp only [hfkf, Bool.false_eq_true, ↓reduceIte, hS1]
        exact ih (by omega) r
  have hfull := hgen len (le_refl len) r
  have htake : (List.finRange len).take len = List.finRange len := List.take_of_length_le (by simp)
  rw [htake] at hfull
  unfold oneHotCount
  rw [hfull]
  congr 1; congr 1; congr 1
  ext j; simp

-- Pure FPT 3-way branching search!
private def probeCovered {m : ℕ} (T : PivotTable m) (a b : Vec m) : Bool :=
  vecIsZero (reduceVec T a) || vecIsZero (reduceVec T b) || vecIsZero (reduceVec T (vecXor a b))

private lemma probeCovered_iff {m : ℕ} (T : PivotTable m) (hT : T.WF) (a b : Vec m) :
    probeCovered T a b = true ↔
      vecToK a ∈ T.span ∨ vecToK b ∈ T.span ∨ vecToK a + vecToK b ∈ T.span := by
  simp only [probeCovered, Bool.or_eq_true, (reduceVec_spec T hT _).2.2, vecToK_xor, or_assoc]

private def pickFirstUncovered {m t : ℕ} (cov : Fin t → Bool) (a b : Fin t → Vec m) : Vec m × Vec m :=
  let ft := firstTrue (fun p => !cov p)
  (List.finRange t).foldl (fun acc p => if ft p then (a p, b p) else acc) (vecZero m, vecZero m)

private lemma pickFirstUncovered_spec {m t : ℕ} (cov : Fin t → Bool) (a b : Fin t → Vec m)
    (hnotall : ∃ p : Fin t, cov p = false) :
    ∃ p : Fin t, cov p = false ∧ pickFirstUncovered cov a b = (a p, b p) := by
  let S := Finset.univ.filter (fun p : Fin t => cov p = false)
  have hSne : S.Nonempty := by obtain ⟨p, hp⟩ := hnotall; exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
  let p0 := S.min' hSne
  have hp0_f : cov p0 = false := (Finset.mem_filter.mp (Finset.min'_mem S hSne)).2
  have hft0 : firstTrue (fun p => !cov p) p0 = true := (firstTrue_spec _ p0).mpr
    ⟨by simp [hp0_f], fun i hi => by
      by_contra h
      have hci : cov i = false := by simpa using h
      exact not_le_of_gt hi (Finset.min'_le S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hci⟩))⟩
  have hft_uniq : ∀ p : Fin t, firstTrue (fun p => !cov p) p = true → p = p0 := by
    intro p hp
    obtain ⟨hpf, hmin⟩ := (firstTrue_spec _ p).mp hp
    have hpcf : cov p = false := by simpa using hpf
    have hle : p0 ≤ p := Finset.min'_le S p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpcf⟩)
    by_contra hne
    have hlt : p0 < p := lt_of_le_of_ne hle (Ne.symm hne)
    have h0 := hmin p0 hlt
    simp [hp0_f] at h0
  refine ⟨p0, hp0_f, ?_⟩
  unfold pickFirstUncovered
  have hgen : ∀ (L : List (Fin t)) (init : Vec m × Vec m),
      (p0 ∈ L → L.foldl (fun acc p => if firstTrue (fun p => !cov p) p then (a p, b p) else acc) init = (a p0, b p0)) ∧
      (p0 ∉ L → L.foldl (fun acc p => if firstTrue (fun p => !cov p) p then (a p, b p) else acc) init = init) := by
    intro L
    induction L with
    | nil => intro init; exact ⟨by simp, fun _ => rfl⟩
    | cons x L ih =>
      intro init
      by_cases hx : x = p0
      · subst hx
        constructor
        · intro _
          rw [List.foldl_cons, ite_eq_left_iff.mpr (fun h => absurd hft0 h)]
          by_cases hm : p0 ∈ L
          · exact (ih _).1 hm
          · exact (ih _).2 hm
        · intro hnm; exact absurd List.mem_cons_self hnm
      · have hftx : firstTrue (fun p => !cov p) x = false := by
          by_contra h; exact hx (hft_uniq x (Bool.eq_true_of_not_eq_false h))
        constructor
        · intro hm
          rw [List.foldl_cons, ite_eq_right_iff.mpr (by simp [hftx])]
          exact (ih init).1 ((List.mem_cons.mp hm).resolve_left (Ne.symm hx))
        · intro hnm
          rw [List.foldl_cons, ite_eq_right_iff.mpr (by simp [hftx])]
          exact (ih init).2 (fun h => hnm (List.mem_cons_of_mem _ h))
  exact (hgen (List.finRange t) _).1 (List.mem_finRange p0)

private def fptSearch {m t : ℕ} (a b : Fin t → Vec m) :
    (rem : ℕ) → PivotTable m → Bool × PivotTable m × (Fin rem → Vec m)
  | 0, T =>
    let allCov := (List.finRange t).all fun p => probeCovered T (a p) (b p)
    (allCov, T, Fin.elim0)
  | rem + 1, T =>
    let cov : Fin t → Bool := fun p => probeCovered T (a p) (b p)
    let allCov := (List.finRange t).all cov
    let ab := pickFirstUncovered cov a b
    let v1 := ab.1
    let v2 := ab.2
    let v3 := vecXor v1 v2
    let r1 := fptSearch a b rem (insertVec T v1)
    let r2 := fptSearch a b rem (insertVec T v2)
    let r3 := fptSearch a b rem (insertVec T v3)
    if allCov then (true, T, fun _ => vecZero m)
    else if r1.1 then (true, r1.2.1, Fin.cons v1 r1.2.2)
    else if r2.1 then (true, r2.2.1, Fin.cons v2 r2.2.2)
    else (r3.1, r3.2.1, Fin.cons v3 r3.2.2)

private lemma fptSearch_sound {m t : ℕ} (a b : Fin t → Vec m) :
    ∀ (rem : ℕ) (T : PivotTable m), T.WF →
      let res := fptSearch a b rem T
      res.1 = true →
      res.2.1.WF ∧
      res.2.1.span = T.span ⊔ Submodule.span K (Set.range (fun i => vecToK (res.2.2 i))) ∧
      ∀ p : Fin t, vecToK (a p) ∈ res.2.1.span ∨ vecToK (b p) ∈ res.2.1.span ∨
        vecToK (a p) + vecToK (b p) ∈ res.2.1.span := by
  intro rem
  induction rem with
  | zero =>
    intro T hT res hok
    dsimp only [res, fptSearch] at hok ⊢
    refine ⟨hT, ?_, ?_⟩
    · have hemp : Set.range (fun i : Fin 0 => vecToK (Fin.elim0 (α := Vec m) i)) = ∅ := by
        ext x; simp
      rw [hemp, Submodule.span_empty, sup_bot_eq]
    · intro p
      have hp : probeCovered T (a p) (b p) = true :=
        (List.all_eq_true.mp hok) p (List.mem_finRange p)
      exact (probeCovered_iff T hT (a p) (b p)).mp hp
  | succ rem ih =>
    intro T hT res hok
    dsimp only [res, fptSearch] at hok ⊢
    set cov : Fin t → Bool := fun p => probeCovered T (a p) (b p)
    set allCov := (List.finRange t).all cov
    set ab := pickFirstUncovered cov a b
    set v1 := ab.1
    set v2 := ab.2
    set v3 := vecXor v1 v2
    set r1 := fptSearch a b rem (insertVec T v1)
    set r2 := fptSearch a b rem (insertVec T v2)
    set r3 := fptSearch a b rem (insertVec T v3)
    have hrange_cons : ∀ (v : Vec m) (vs : Fin rem → Vec m),
        Submodule.span K (Set.range (fun i => vecToK (Fin.cons (α := fun _ => Vec m) v vs i))) =
          Submodule.span K {vecToK v} ⊔ Submodule.span K (Set.range (fun i => vecToK (vs i))) := by
      intro v vs
      rw [← Submodule.span_union]
      congr 1; ext x
      simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        refine Fin.cases ?_ ?_ i
        · exact Or.inl rfl
        · intro j; exact Or.inr ⟨j, rfl⟩
      · rintro (rfl | ⟨j, rfl⟩)
        · exact ⟨0, rfl⟩
        · exact ⟨j.succ, rfl⟩
    split_ifs at hok ⊢ with hac hr1 hr2
    · refine ⟨hT, ?_, ?_⟩
      · have h0 : Submodule.span K (Set.range (fun _ : Fin (rem + 1) => vecToK (vecZero m))) = ⊥ := by
          rw [Submodule.span_eq_bot]; rintro _ ⟨_, rfl⟩; exact vecToK_zero m
        rw [h0, sup_bot_eq]
      · intro p
        have hp : probeCovered T (a p) (b p) = true := (List.all_eq_true.mp hac) p (List.mem_finRange p)
        exact (probeCovered_iff T hT (a p) (b p)).mp hp
    · obtain ⟨hins_wf, hins_sp⟩ := insertVec_spec T hT v1
      obtain ⟨hwf1, hsp1, hcov1⟩ := ih (insertVec T v1) hins_wf hr1
      refine ⟨hwf1, ?_, hcov1⟩
      rw [hsp1, hins_sp, hrange_cons, sup_assoc]
    · obtain ⟨hins_wf, hins_sp⟩ := insertVec_spec T hT v2
      obtain ⟨hwf2, hsp2, hcov2⟩ := ih (insertVec T v2) hins_wf hr2
      refine ⟨hwf2, ?_, hcov2⟩
      rw [hsp2, hins_sp, hrange_cons, sup_assoc]
    · obtain ⟨hins_wf, hins_sp⟩ := insertVec_spec T hT v3
      obtain ⟨hwf3, hsp3, hcov3⟩ := ih (insertVec T v3) hins_wf hok
      refine ⟨hwf3, ?_, hcov3⟩
      rw [hsp3, hins_sp, hrange_cons, sup_assoc]

private lemma fptSearch_complete {m t : ℕ} (a b : Fin t → Vec m) :
    ∀ (rem : ℕ) (T : PivotTable m), T.WF →
      ∀ D : Submodule K (Fin m → K),
        T.span ≤ D →
        Module.finrank K D ≤ Module.finrank K T.span + rem →
        (∀ p : Fin t, vecToK (a p) ∈ D ∨ vecToK (b p) ∈ D ∨ vecToK (a p) + vecToK (b p) ∈ D) →
        (fptSearch a b rem T).1 = true := by
  intro rem
  induction rem with
  | zero =>
    intro T hT D hTD hdim hDcov
    dsimp only [fptSearch]
    rw [List.all_eq_true]
    intro p _
    rw [probeCovered_iff T hT]
    have hTeq : T.span = D :=
      Submodule.eq_of_le_of_finrank_eq hTD (le_antisymm (Submodule.finrank_mono hTD) (by omega))
    rw [hTeq]
    exact hDcov p
  | succ rem ih =>
    intro T hT D hTD hdim hDcov
    dsimp only [fptSearch]
    set cov : Fin t → Bool := fun p => probeCovered T (a p) (b p)
    set allCov := (List.finRange t).all cov
    by_cases hac : allCov = true
    · simp [hac]
    · have hnotall : ∃ p : Fin t, cov p = false := by
        by_contra hall; push Not at hall
        apply hac
        rw [List.all_eq_true]
        intro p _; exact Bool.eq_true_of_not_eq_false (hall p)
      obtain ⟨p0, hp0f, hpick⟩ := pickFirstUncovered_spec cov a b hnotall
      have hnotcov : ¬ (vecToK (a p0) ∈ T.span ∨ vecToK (b p0) ∈ T.span ∨ vecToK (a p0) + vecToK (b p0) ∈ T.span) := by
        intro h
        dsimp only [cov] at hp0f
        rw [(probeCovered_iff T hT (a p0) (b p0)).mpr h] at hp0f
        exact Bool.false_ne_true hp0f.symm
      have hstrict : ∀ v : Vec m, vecToK v ∈ D → vecToK v ∉ T.span →
          (fptSearch a b rem (insertVec T v)).1 = true := by
        intro v hvD hvnot
        obtain ⟨hins_wf, hins_sp⟩ := insertVec_spec T hT v
        have hleD : (insertVec T v).span ≤ D := by
          rw [hins_sp]; exact sup_le hTD (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvD))
        have hlt : T.span < (insertVec T v).span := by
          rw [hins_sp]
          exact lt_of_le_of_ne le_sup_left fun heq => hvnot (heq ▸ Submodule.mem_sup_right (Submodule.subset_span rfl))
        have hfr_gt : Module.finrank K T.span < Module.finrank K (insertVec T v).span :=
          Submodule.finrank_lt_finrank_of_lt hlt
        exact ih (insertVec T v) hins_wf D hleD (by omega) hDcov
      simp only [hac, Bool.false_eq_true, ↓reduceIte, hpick]
      rcases hDcov p0 with h1 | h2 | h3
      · have hr1 := hstrict (a p0) h1 (fun h => hnotcov (Or.inl h))
        simp [hr1]
      · have hr2 := hstrict (b p0) h2 (fun h => hnotcov (Or.inr (Or.inl h)))
        simp only [hr2, ↓reduceIte]
        split_ifs <;> rfl
      · have hv3 : vecToK (vecXor (a p0) (b p0)) ∈ D := by rw [vecToK_xor]; exact h3
        have hv3n : vecToK (vecXor (a p0) (b p0)) ∉ T.span := by rw [vecToK_xor]; exact fun h => hnotcov (Or.inr (Or.inr h))
        have hr3 := hstrict (vecXor (a p0) (b p0)) hv3 hv3n
        split_ifs
        · rfl
        · rfl
        · exact hr3

private lemma fptSearch_iff_hits {m t q : ℕ} (a b : Fin t → Vec m) :
    let d := min q (min m t)
    (fptSearch a b d (PivotTable.empty m)).1 = true ↔
      ∃ basis : Fin q → Fin m → K,
        let D := Submodule.span K (Set.range basis)
        ∀ p : Fin t, vecToK (a p) ∈ D ∨ vecToK (b p) ∈ D ∨ vecToK (a p) + vecToK (b p) ∈ D := by
  intro d
  constructor
  · intro hok
    obtain ⟨_, hsp, hcov⟩ := fptSearch_sound a b d (PivotTable.empty m) (PivotTable.empty_wf m) hok
    rw [PivotTable.empty_span, bot_sup_eq] at hsp
    let res := (fptSearch a b d (PivotTable.empty m)).2.2
    have hdq : d ≤ q := min_le_left _ _
    let basis : Fin q → Fin m → K := fun i =>
      if h : i.1 < d then vecToK (res ⟨i.1, h⟩) else 0
    refine ⟨basis, fun p => ?_⟩
    have hsub : (fptSearch a b d (PivotTable.empty m)).2.1.span ≤ Submodule.span K (Set.range basis) := by
      rw [hsp, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Submodule.subset_span ⟨⟨i.1, lt_of_lt_of_le i.2 hdq⟩, ?_⟩
      simp [basis, i.2, res]
    rcases hcov p with h1 | h2 | h3
    · exact Or.inl (hsub h1)
    · exact Or.inr (Or.inl (hsub h2))
    · exact Or.inr (Or.inr (hsub h3))
  · rintro ⟨basis, hcov⟩
    let D0 := Submodule.span K (Set.range basis)
    -- Shrink D0 to D1 spanned by at most one witness per probe p : Fin t
    have hex_w : ∀ p : Fin t, ∃ v : Fin m → K, v ∈ D0 ∧
        (v = vecToK (a p) ∨ v = vecToK (b p) ∨ v = vecToK (a p) + vecToK (b p)) := by
      intro p
      rcases hcov p with h1 | h2 | h3
      · exact ⟨_, h1, Or.inl rfl⟩
      · exact ⟨_, h2, Or.inr (Or.inl rfl)⟩
      · exact ⟨_, h3, Or.inr (Or.inr rfl)⟩
    let pick : Fin t → Fin m → K := fun p => Classical.choose (hex_w p)
    let D1 := Submodule.span K (Set.range pick)
    have hD1le : D1 ≤ D0 := Submodule.span_le.mpr (by
      rintro _ ⟨p, rfl⟩; exact (Classical.choose_spec (hex_w p)).1)
    have hD1cov : ∀ p : Fin t, vecToK (a p) ∈ D1 ∨ vecToK (b p) ∈ D1 ∨ vecToK (a p) + vecToK (b p) ∈ D1 := by
      intro p
      have hp_mem : pick p ∈ D1 := Submodule.subset_span ⟨p, rfl⟩
      rcases (Classical.choose_spec (hex_w p)).2 with h1 | h2 | h3
      · exact Or.inl (h1 ▸ hp_mem)
      · exact Or.inr (Or.inl (h2 ▸ hp_mem))
      · exact Or.inr (Or.inr (h3 ▸ hp_mem))
    have hD1_le_q : Module.finrank K D1 ≤ q := by
      have h1 : Module.finrank K D1 ≤ Module.finrank K D0 := Submodule.finrank_mono hD1le
      have h2 := finrank_span_le_card (R := K) (Set.range basis)
      have h3 : (Set.range basis).toFinset.card ≤ q := by
        calc (Set.range basis).toFinset.card = (Finset.univ.image basis).card := by congr 1; ext x; simp
          _ ≤ (Finset.univ : Finset (Fin q)).card := Finset.card_image_le
          _ = q := by simp
      dsimp only [D0] at h1; omega
    have hD1_le_m : Module.finrank K D1 ≤ m := by
      have := Submodule.finrank_le D1
      rw [Module.finrank_fin_fun] at this
      exact this
    have hD1_le_t : Module.finrank K D1 ≤ t := by
      have h2 := finrank_span_le_card (R := K) (Set.range pick)
      have h3 : (Set.range pick).toFinset.card ≤ t := by
        calc (Set.range pick).toFinset.card = (Finset.univ.image pick).card := by congr 1; ext x; simp
          _ ≤ (Finset.univ : Finset (Fin t)).card := Finset.card_image_le
          _ = t := by simp
      dsimp only [D1]; omega
    have hD1_le_d : Module.finrank K D1 ≤ d := le_min hD1_le_q (le_min hD1_le_m hD1_le_t)
    refine fptSearch_complete a b d (PivotTable.empty m) (PivotTable.empty_wf m) D1
      (by rw [PivotTable.empty_span]; exact bot_le) ?_ hD1cov
    rw [PivotTable.empty_span, finrank_bot, zero_add]
    exact hD1_le_d

-- Binary arithmetic helpers for Stage 2
private def bitsToNat {w : ℕ} (b : Fin w → Bool) : ℕ :=
  ∑ i : Fin w, if b i then 2 ^ i.1 else 0

private lemma bitsToNat_lt {w : ℕ} (b : Fin w → Bool) : bitsToNat b < 2 ^ w := by
  induction w with
  | zero => simp [bitsToNat]
  | succ w ih =>
    unfold bitsToNat
    rw [Fin.sum_univ_castSucc]
    have h1 := ih (fun i => b i.castSucc)
    unfold bitsToNat at h1
    have hlast : (if b (Fin.last w) = true then 2 ^ (Fin.last w).1 else 0) ≤ 2 ^ w := by
      split_ifs <;> simp
    have hpow : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by ring
    dsimp only at h1
    simp only [Fin.val_castSucc]
    omega

private lemma bitsToNat_succ {w : ℕ} (b : Fin (w + 1) → Bool) :
    bitsToNat b = (if b 0 then 1 else 0) + 2 * bitsToNat (fun i : Fin w => b i.succ) := by
  unfold bitsToNat
  rw [Fin.sum_univ_succ]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [pow_succ, mul_comm]

private lemma bitsToNat_testBit {w : ℕ} (b : Fin w → Bool) (j : ℕ) :
    (bitsToNat b).testBit j = if h : j < w then b ⟨j, h⟩ else false := by
  induction w generalizing j with
  | zero => simp [bitsToNat]
  | succ w ih =>
    rw [bitsToNat_succ]
    cases j with
    | zero =>
      simp only [Nat.zero_lt_succ, ↓reduceDIte]
      cases hb0 : b 0
      · simp [Nat.testBit_zero, hb0]
      · simp [Nat.testBit_zero, hb0]
    | succ j =>
      have hdiv : ((if b 0 then 1 else 0) + 2 * bitsToNat (fun i : Fin w => b i.succ)) / 2 =
          bitsToNat (fun i : Fin w => b i.succ) := by
        cases b 0 <;> simp
        omega
      rw [Nat.testBit_succ, hdiv, ih (fun i => b i.succ) j]
      by_cases hj : j < w
      · have hj' : j + 1 < w + 1 := by omega
        simp [hj, hj', Fin.succ]
      · have hj' : ¬ j + 1 < w + 1 := by omega
        simp [hj, hj']

private def addBitsCarry : (w : ℕ) → (Fin w → Bool) → (Fin w → Bool) → Bool → (Fin w → Bool) × Bool
  | 0, _, _, c => (Fin.elim0, c)
  | w + 1, a, b, c =>
    let s0 := xor (xor (a 0) (b 0)) c
    let c1 := (a 0 && b 0) || (c && xor (a 0) (b 0))
    let rest := addBitsCarry w (fun i => a i.succ) (fun i => b i.succ) c1
    (Fin.cons (α := fun _ => Bool) s0 rest.1, rest.2)

private def addBits {w : ℕ} (a b : Fin w → Bool) : Fin w → Bool :=
  (addBitsCarry w a b false).1

private lemma addBitsCarry_spec : ∀ (w : ℕ) (a b : Fin w → Bool) (c : Bool),
    let res := addBitsCarry w a b c
    bitsToNat res.1 + (if res.2 then 2 ^ w else 0) =
      bitsToNat a + bitsToNat b + (if c then 1 else 0) := by
  intro w
  induction w with
  | zero => intro a b c; simp [addBitsCarry, bitsToNat]
  | succ w ih =>
    intro a b c
    dsimp only [addBitsCarry]
    set s0 := xor (xor (a 0) (b 0)) c
    set c1 := (a 0 && b 0) || (c && xor (a 0) (b 0))
    have hstep := ih (fun i => a i.succ) (fun i => b i.succ) c1
    have hfa := bitsToNat_succ a
    have hfb := bitsToNat_succ b
    have hfr : bitsToNat (Fin.cons (α := fun _ => Bool) s0 (addBitsCarry w (fun i => a i.succ) (fun i => b i.succ) c1).1) =
        (if s0 then 1 else 0) + 2 * bitsToNat (addBitsCarry w (fun i => a i.succ) (fun i => b i.succ) c1).1 := by
      simpa only [Fin.cons_zero, Fin.cons_succ] using
        bitsToNat_succ (Fin.cons (α := fun _ => Bool) s0 (addBitsCarry w (fun i => a i.succ) (fun i => b i.succ) c1).1)
    have hbit : (if s0 then 1 else 0) + 2 * (if c1 then 1 else 0) =
        (if a 0 then 1 else 0) + (if b 0 then 1 else 0) + (if c then 1 else 0) := by
      have aux : ∀ x y z : Bool,
          (if xor (xor x y) z then 1 else 0) + 2 * (if (x && y) || (z && xor x y) then 1 else 0) =
            (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) := by decide
      exact aux (a 0) (b 0) c
    have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := by ring
    rw [hfr, hfa, hfb, hpow]
    have hmul : 2 * (bitsToNat (addBitsCarry w (fun i => a i.succ) (fun i => b i.succ) c1).1 +
        if (addBitsCarry w (fun i => a i.succ) (fun i => b i.succ) c1).2 then 2 ^ w else 0) =
        2 * (bitsToNat (fun i => a i.succ) + bitsToNat (fun i => b i.succ) + if c1 then 1 else 0) :=
      congrArg (2 * ·) hstep
    cases hco : (addBitsCarry w (fun i => a i.succ) (fun i => b i.succ) c1).2 <;>
      simp only [hco, Bool.false_eq_true, ↓reduceIte] at hmul ⊢ <;> omega

private lemma addBits_spec {w : ℕ} (a b : Fin w → Bool) (hlt : bitsToNat a + bitsToNat b < 2 ^ w) :
    bitsToNat (addBits a b) = bitsToNat a + bitsToNat b := by
  have h := addBitsCarry_spec w a b false
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at h
  cases hc : (addBitsCarry w a b false).2
  · simp [addBits, hc] at h ⊢; exact h
  · rw [hc] at h; simp at h; omega

private def vecDot {m : ℕ} (a x : Vec m) : Bool :=
  (List.finRange m).foldl (fun acc j => if a j && x j then !acc else acc) false

private lemma vecDot_spec {m : ℕ} (a x : Vec m) :
    b2z (vecDot a x) = dot (vecToK a) (vecToK x) := by
  unfold vecDot dot
  have hgen : ∀ (L : List (Fin m)) (init : Bool), L.Nodup →
      b2z (L.foldl (fun acc j => if a j && x j then !acc else acc) init) =
        b2z init + ∑ j ∈ L.toFinset, vecToK a j * vecToK x j := by
    intro L
    induction L with
    | nil => intro init _; simp
    | cons j0 L ih =>
      intro init hnd
      obtain ⟨hj0, hndL⟩ := List.nodup_cons.mp hnd
      rw [List.foldl_cons, ih _ hndL, List.toFinset_cons, Finset.sum_insert (by simpa using hj0)]
      have hterm : b2z (if a j0 && x j0 then !init else init) = b2z init + vecToK a j0 * vecToK x j0 := by
        cases ha : a j0 <;> cases hx : x j0 <;> cases init <;> simp [vecToK, ha, hx, b2z, z2_add_self]
      rw [hterm]; ring
  have h1 := hgen (List.finRange m) false (List.nodup_finRange m)
  have hto : (List.finRange m).toFinset = Finset.univ := by ext j; simp
  rw [hto] at h1
  simpa [b2z] using h1

private def finishCell {m t : ℕ} (Tfound : PivotTable m) (a b L : Fin t → Vec m)
    (baseP wanted : Fin t → Bool) (A_cell : AugTable m) : Fin (m + 1) → Bool :=
  let z := backSub A_cell
  let A_sol := (List.finRange t).foldl (fun A p =>
    let isA := vecIsZero (reduceVec Tfound (a p))
    let isB := vecIsZero (reduceVec Tfound (b p))
    let dA := vecDot (a p) z
    let dB := vecDot (b p) z
    let dAB := xor dA dB
    let qLin : Vec m :=
      if isA then (fun g => dA && b p g)
      else if isB then (fun g => dB && a p g)
      else (fun g => !dAB && a p g)
    augInsert A (vecXor (L p) qLin) (xor (wanted p) (baseP p))) A_cell
  let oh := oneHotCount A_sol.piv.hasPiv
  fun idx => !A_sol.inc && oh ⟨m - idx.1, by omega⟩

private lemma finishCell_spec {m t : ℕ} (Tfound : PivotTable m) (hTf : Tfound.WF)
    (a b L : Fin t → Vec m) (baseP wanted : Fin t → Bool)
    (hcov : ∀ p : Fin t, vecToK (a p) ∈ Tfound.span ∨ vecToK (b p) ∈ Tfound.span ∨
      vecToK (a p) + vecToK (b p) ∈ Tfound.span)
    (A_cell : AugTable m) (hAc : A_cell.piv.WF)
    (hcell_ortho : ∀ x ∈ A_cell.Sols, ∀ y ∈ A_cell.Sols, ∀ v ∈ Tfound.span, dot v x = dot v y) :
    letI := Classical.decPred (fun x : Fin m → K => x ∈ A_cell.Sols)
    bitsToNat (finishCell Tfound a b L baseP wanted A_cell) =
      ((Finset.univ : Finset (Fin m → K)).filter (fun x => x ∈ A_cell.Sols ∧
        ∀ p : Fin t, b2z (baseP p) + dot (vecToK (L p)) x +
          dot (vecToK (a p)) x * dot (vecToK (b p)) x = b2z (wanted p))).card := by
  classical
  set z := backSub A_cell
  let stepFn : AugTable m → Fin t → AugTable m := fun A p =>
    let isA := vecIsZero (reduceVec Tfound (a p))
    let isB := vecIsZero (reduceVec Tfound (b p))
    let dA := vecDot (a p) z
    let dB := vecDot (b p) z
    let dAB := xor dA dB
    let qLin : Vec m :=
      if isA then (fun g => dA && b p g)
      else if isB then (fun g => dB && a p g)
      else (fun g => !dAB && a p g)
    augInsert A (vecXor (L p) qLin) (xor (wanted p) (baseP p))
  -- Key equivalence on x ∈ A_cell.Sols (when A_cell.inc = false, z ∈ A_cell.Sols!)
  have hz_sol : A_cell.inc = false → vecToK z ∈ A_cell.Sols := fun hinc =>
    ⟨hinc, fun j hjp => (backSubWith_spec A_cell hAc (vecZero m)).2 j hjp⟩
  have hprobe_eq : ∀ (x : Fin m → K), x ∈ A_cell.Sols → ∀ p : Fin t,
      let isA := vecIsZero (reduceVec Tfound (a p))
      let isB := vecIsZero (reduceVec Tfound (b p))
      let dA := vecDot (a p) z
      let dB := vecDot (b p) z
      let dAB := xor dA dB
      let qLin : Vec m :=
        if isA then (fun g => dA && b p g)
        else if isB then (fun g => dB && a p g)
        else (fun g => !dAB && a p g)
      (dot (vecToK (vecXor (L p) qLin)) x = b2z (xor (wanted p) (baseP p))) ↔
        (b2z (baseP p) + dot (vecToK (L p)) x +
          dot (vecToK (a p)) x * dot (vecToK (b p)) x = b2z (wanted p)) := by
    intro x hx p
    have hz : vecToK z ∈ A_cell.Sols := hz_sol hx.1
    have hdot_scale : ∀ (c : Bool) (u : Vec m),
        dot (vecToK (fun g => c && u g)) x = b2z c * dot (vecToK u) x := fun c u => by
      unfold dot vecToK
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => by rw [b2z_and, mul_assoc]
    have hquad :
        let isA := vecIsZero (reduceVec Tfound (a p))
        let isB := vecIsZero (reduceVec Tfound (b p))
        let dA := vecDot (a p) z
        let dB := vecDot (b p) z
        let dAB := xor dA dB
        let qLin : Vec m :=
          if isA then (fun g => dA && b p g)
          else if isB then (fun g => dB && a p g)
          else (fun g => !dAB && a p g)
        dot (vecToK qLin) x = dot (vecToK (a p)) x * dot (vecToK (b p)) x := by
      dsimp only
      split_ifs with hA hB
      · have hAmem : vecToK (a p) ∈ Tfound.span := (reduceVec_spec Tfound hTf (a p)).2.2.mp hA
        have heqA : dot (vecToK (a p)) x = b2z (vecDot (a p) z) := by
          rw [vecDot_spec]; exact hcell_ortho x hx (vecToK z) hz _ hAmem
        rw [hdot_scale, heqA]
      · have hBmem : vecToK (b p) ∈ Tfound.span := (reduceVec_spec Tfound hTf (b p)).2.2.mp hB
        have heqB : dot (vecToK (b p)) x = b2z (vecDot (b p) z) := by
          rw [vecDot_spec]; exact hcell_ortho x hx (vecToK z) hz _ hBmem
        rw [hdot_scale, heqB, mul_comm]
      · have hABmem : vecToK (a p) + vecToK (b p) ∈ Tfound.span := by
          rcases hcov p with h1 | h2 | h3
          · exact absurd ((reduceVec_spec Tfound hTf (a p)).2.2.mpr h1) hA
          · exact absurd ((reduceVec_spec Tfound hTf (b p)).2.2.mpr h2) hB
          · exact h3
        have heqAB : dot (vecToK (a p)) x + dot (vecToK (b p)) x =
            b2z (xor (vecDot (a p) z) (vecDot (b p) z)) := by
          rw [← dot_add_left, b2z_xor, vecDot_spec, vecDot_spec, ← dot_add_left]
          exact hcell_ortho x hx (vecToK z) hz _ hABmem
        have hb_eq : dot (vecToK (b p)) x =
            dot (vecToK (a p)) x + b2z (xor (vecDot (a p) z) (vecDot (b p) z)) := by
          have h2 := z2_add_self (dot (vecToK (a p)) x)
          linear_combination heqAB - h2
        rw [hdot_scale, b2z_not, hb_eq, mul_add, z2_mul_self]
        ring
    dsimp only
    rw [vecToK_xor, dot_add_left, hquad, b2z_xor]
    have h2b := z2_add_self (b2z (baseP p))
    constructor
    · intro h; linear_combination h + h2b
    · intro h; linear_combination h - h2b
  -- Fold invariant over the t probe steps
  have hfold : ∀ (k : ℕ) (_hk : k ≤ t),
      let A_k := ((List.finRange t).take k).foldl stepFn A_cell
      A_k.piv.WF ∧
      A_k.Sols = {x | x ∈ A_cell.Sols ∧ ∀ p : Fin t, p.1 < k →
        b2z (baseP p) + dot (vecToK (L p)) x +
          dot (vecToK (a p)) x * dot (vecToK (b p)) x = b2z (wanted p)} := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [hAc]
    | succ k ih =>
      intro hk
      have htake : (List.finRange t).take (k + 1) = (List.finRange t).take k ++ [⟨k, hk⟩] := by
        rw [List.take_succ_eq_append_getElem (by simp; omega)]
        simp
      obtain ⟨hwf_k, hsol_k⟩ := ih (by omega)
      set A_k := ((List.finRange t).take k).foldl stepFn A_cell
      have hstep_eq : ((List.finRange t).take (k + 1)).foldl stepFn A_cell = stepFn A_k ⟨k, hk⟩ := by
        rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
      dsimp only
      rw [hstep_eq]
      obtain ⟨hwf_next, hsol_next⟩ := augInsert_spec A_k hwf_k _ _
      refine ⟨hwf_next, ?_⟩
      rw [hsol_next, hsol_k]
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨hxA, hall⟩, hnew⟩
        refine ⟨hxA, fun p hp => ?_⟩
        by_cases hpk : p.1 < k
        · exact hall p hpk
        · have hpeq : p = ⟨k, hk⟩ := Fin.ext (by dsimp only; omega)
          subst hpeq
          exact (hprobe_eq x hxA ⟨k, hk⟩).mp hnew
      · rintro ⟨hxA, hall⟩
        exact ⟨⟨hxA, fun p hp => hall p (by omega)⟩, (hprobe_eq x hxA ⟨k, hk⟩).mpr (hall ⟨k, hk⟩ (by dsimp only; omega))⟩
  have hfull := hfold t (le_refl t)
  have htake : (List.finRange t).take t = List.finRange t := List.take_of_length_le (by simp)
  rw [htake] at hfull
  set A_sol := (List.finRange t).foldl stepFn A_cell
  have hcard_sol := augTable_card_sols A_sol hfull.1
  have hsol_eq : ((Finset.univ : Finset (Fin m → K)).filter (fun x => x ∈ A_sol.Sols)).card =
      ((Finset.univ : Finset (Fin m → K)).filter (fun x => x ∈ A_cell.Sols ∧
        ∀ p : Fin t, b2z (baseP p) + dot (vecToK (L p)) x +
          dot (vecToK (a p)) x * dot (vecToK (b p)) x = b2z (wanted p))).card := by
    congr 1; ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hfull.2, Set.mem_ofPred_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun p => h2 p p.2⟩, fun ⟨h1, h2⟩ => ⟨h1, fun p _ => h2 p⟩⟩
  rw [← hsol_eq, hcard_sol]
  unfold finishCell
  dsimp only [bitsToNat]
  change (∑ idx : Fin (m + 1), if (!A_sol.inc && oneHotCount A_sol.piv.hasPiv ⟨m - idx.1, _⟩) = true then 2 ^ idx.1 else 0) = _
  set rk := ((Finset.univ : Finset (Fin m)).filter (fun j => A_sol.piv.hasPiv j = true)).card
  have hrk_le : rk ≤ m := by
    have := Finset.card_le_univ ((Finset.univ : Finset (Fin m)).filter (fun j => A_sol.piv.hasPiv j = true))
    simpa [rk] using this
  cases hinc : A_sol.inc
  · simp only [Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    rw [Finset.sum_eq_single ⟨m - rk, by omega⟩]
    · rw [oneHotCount_spec]
      have heq : m - (m - rk) = rk := by omega
      simp only [heq, rk, decide_true, ↓reduceIte]
    · intro idx _ hne
      rw [oneHotCount_spec]
      have hne' : m - idx.1 ≠ rk := by
        intro heq; apply hne; exact Fin.ext (by dsimp only; omega)
      have hne'' : ¬ m - idx.1 = ((Finset.univ : Finset (Fin m)).filter (fun j => A_sol.piv.hasPiv j = true)).card := hne'
      simp only [hne'', decide_false, Bool.false_eq_true, ↓reduceIte]
    · intro hnm; exact absurd (Finset.mem_univ _) hnm
  · simp

private def sumCells {m t : ℕ} (Tfound : PivotTable m) (a b L : Fin t → Vec m)
    (baseP wanted : Fin t → Bool) :
    (rem : ℕ) → (Fin rem → Vec m) → AugTable m → Fin (m + 1) → Bool
  | 0, _, A_cell => finishCell Tfound a b L baseP wanted A_cell
  | r + 1, found, A_cell =>
    let b0 := sumCells Tfound a b L baseP wanted r (fun i => found i.succ) (augInsert A_cell (found 0) false)
    let b1 := sumCells Tfound a b L baseP wanted r (fun i => found i.succ) (augInsert A_cell (found 0) true)
    addBits b0 b1

private lemma sumCells_spec {m t : ℕ} (Tfound : PivotTable m) (hTf : Tfound.WF)
    (a b L : Fin t → Vec m) (baseP wanted : Fin t → Bool)
    (hcov : ∀ p : Fin t, vecToK (a p) ∈ Tfound.span ∨ vecToK (b p) ∈ Tfound.span ∨
      vecToK (a p) + vecToK (b p) ∈ Tfound.span) :
    ∀ (rem : ℕ) (found : Fin rem → Vec m) (A_cell : AugTable m),
      A_cell.piv.WF →
      Tfound.span ≤ A_cell.piv.span ⊔ Submodule.span K (Set.range (fun i => vecToK (found i))) →
      letI := Classical.decPred (fun x : Fin m → K => x ∈ A_cell.Sols)
      bitsToNat (sumCells Tfound a b L baseP wanted rem found A_cell) =
        ((Finset.univ : Finset (Fin m → K)).filter (fun x => x ∈ A_cell.Sols ∧
          ∀ p : Fin t, b2z (baseP p) + dot (vecToK (L p)) x +
            dot (vecToK (a p)) x * dot (vecToK (b p)) x = b2z (wanted p))).card := by
  intro rem
  induction rem with
  | zero =>
    intro found A_cell hAc hspan
    classical
    have hemp : Submodule.span K (Set.range (fun i : Fin 0 => vecToK (found i))) = ⊥ := by
      rw [Submodule.span_eq_bot]; rintro _ ⟨i, _⟩; exact i.elim0
    rw [hemp, sup_bot_eq] at hspan
    have hortho : ∀ x ∈ A_cell.Sols, ∀ y ∈ A_cell.Sols, ∀ v ∈ Tfound.span, dot v x = dot v y := by
      intro x hx y hy v hv
      have hvA : v ∈ A_cell.piv.span := hspan hv
      refine Submodule.span_induction (p := fun v _ => dot v x = dot v y) ?_ ?_ ?_ ?_ hvA
      · rintro _ ⟨j, hj, rfl⟩; rw [hx.2 j hj, hy.2 j hj]
      · simp [dot_zero_left]
      · intro u1 u2 _ _ h1 h2; rw [dot_add_left, dot_add_left, h1, h2]
      · intro c u _ h1; rw [dot_smul_left, dot_smul_left, h1]
    exact finishCell_spec Tfound hTf a b L baseP wanted hcov A_cell hAc hortho
  | succ r ih =>
    intro found A_cell hAc hspan
    classical
    dsimp only [sumCells]
    obtain ⟨hwf0, hsol0⟩ := augInsert_spec A_cell hAc (found 0) false
    obtain ⟨hwf1, hsol1⟩ := augInsert_spec A_cell hAc (found 0) true
    have hsp_split : Submodule.span K (Set.range (fun i : Fin (r + 1) => vecToK (found i))) =
        Submodule.span K {vecToK (found 0)} ⊔ Submodule.span K (Set.range (fun i : Fin r => vecToK (found i.succ))) := by
      rw [← Submodule.span_union]
      congr 1; ext v
      simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        refine Fin.cases (Or.inl rfl) (fun j => Or.inr ⟨j, rfl⟩) i
      · rintro (rfl | ⟨j, rfl⟩)
        · exact ⟨0, rfl⟩
        · exact ⟨j.succ, rfl⟩
    have hpiv0 : (augInsert A_cell (found 0) false).piv = insertVec A_cell.piv (found 0) := by
      simp only [augInsert, insertVec, augReduce_fst]
    have hpiv1 : (augInsert A_cell (found 0) true).piv = insertVec A_cell.piv (found 0) := by
      simp only [augInsert, insertVec, augReduce_fst]
    have hsp0 : Tfound.span ≤ (augInsert A_cell (found 0) false).piv.span ⊔
        Submodule.span K (Set.range (fun i : Fin r => vecToK (found i.succ))) := by
      rw [hpiv0, (insertVec_spec A_cell.piv hAc (found 0)).2, sup_assoc, ← hsp_split]
      exact hspan
    have hsp1 : Tfound.span ≤ (augInsert A_cell (found 0) true).piv.span ⊔
        Submodule.span K (Set.range (fun i : Fin r => vecToK (found i.succ))) := by
      rw [hpiv1, (insertVec_spec A_cell.piv hAc (found 0)).2, sup_assoc, ← hsp_split]
      exact hspan
    have ih0 := ih (fun i => found i.succ) (augInsert A_cell (found 0) false) hwf0 hsp0
    have ih1 := ih (fun i => found i.succ) (augInsert A_cell (found 0) true) hwf1 hsp1
    let S := (Finset.univ : Finset (Fin m → K)).filter (fun x => x ∈ A_cell.Sols ∧
      ∀ p : Fin t, b2z (baseP p) + dot (vecToK (L p)) x +
        dot (vecToK (a p)) x * dot (vecToK (b p)) x = b2z (wanted p))
    have hS0 : bitsToNat (sumCells Tfound a b L baseP wanted r (fun i => found i.succ) (augInsert A_cell (found 0) false)) =
        (S.filter (fun x => dot (vecToK (found 0)) x = 0)).card := by
      rw [ih0]; refine congrArg Finset.card ?_; ext x
      rw [Finset.mem_filter, Finset.mem_filter]
      dsimp only [S]
      rw [Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, hsol0, Set.mem_ofPred_eq, b2z,
        Bool.false_eq_true, ↓reduceIte]
      exact ⟨fun ⟨⟨hxA, hd⟩, hpr⟩ => ⟨⟨hxA, hpr⟩, hd⟩, fun ⟨⟨hxA, hpr⟩, hd⟩ => ⟨⟨hxA, hd⟩, hpr⟩⟩
    have hS1 : bitsToNat (sumCells Tfound a b L baseP wanted r (fun i => found i.succ) (augInsert A_cell (found 0) true)) =
        (S.filter (fun x => ¬ dot (vecToK (found 0)) x = 0)).card := by
      rw [ih1]; refine congrArg Finset.card ?_; ext x
      rw [Finset.mem_filter, Finset.mem_filter]
      dsimp only [S]
      rw [Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, hsol1, Set.mem_ofPred_eq, b2z, ↓reduceIte]
      exact ⟨fun ⟨⟨hxA, h1⟩, hpr⟩ => ⟨⟨hxA, hpr⟩, by rw [h1]; exact one_ne_zero⟩,
        fun ⟨⟨hxA, hpr⟩, hne⟩ => ⟨⟨hxA, (z2_cases _).resolve_left hne⟩, hpr⟩⟩
    have hpart : (S.filter (fun x => dot (vecToK (found 0)) x = 0)).card +
        (S.filter (fun x => ¬ dot (vecToK (found 0)) x = 0)).card = S.card :=
      Finset.card_filter_add_card_filter_not (p := fun x => dot (vecToK (found 0)) x = 0) (s := S)
    have hSle : S.card ≤ 2 ^ m := by
      calc S.card ≤ (Finset.univ : Finset (Fin m → K)).card := Finset.card_le_univ S
        _ = 2 ^ m := by simp [K, ZMod.card]
    have hsum_eq : bitsToNat (sumCells Tfound a b L baseP wanted r (fun i => found i.succ) (augInsert A_cell (found 0) false)) +
        bitsToNat (sumCells Tfound a b L baseP wanted r (fun i => found i.succ) (augInsert A_cell (found 0) true)) = S.card := by
      rw [hS0, hS1, hpart]
    have hlt : bitsToNat (sumCells Tfound a b L baseP wanted r (fun i => found i.succ) (augInsert A_cell (found 0) false)) +
        bitsToNat (sumCells Tfound a b L baseP wanted r (fun i => found i.succ) (augInsert A_cell (found 0) true)) < 2 ^ (m + 1) := by
      rw [hsum_eq]
      have : 2 ^ m < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self m)
      omega
    rw [addBits_spec _ _ hlt, hsum_eq]

private def genRankTable {k m : ℕ} (genV : Fin m → Vec k) : PivotTable k :=
  (List.finRange m).foldl (fun T g => insertVec T (genV g)) (PivotTable.empty k)

private lemma genRankTable_spec {k m : ℕ} (gen : Fin m → Fin k → K) :
    let T := genRankTable (fun g => kToVec (gen g))
    let Lgen : (Fin m → K) →ₗ[K] (Fin k → K) :=
      { toFun := fun x => ∑ g : Fin m, x g • gen g
        map_add' := fun x y => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := fun c x => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, Finset.smul_sum] }
    T.WF ∧
    ((Finset.univ : Finset (Fin k)).filter (fun j => T.hasPiv j = true)).card =
      Module.finrank K (LinearMap.range Lgen) := by
  intro T Lgen
  have hfold : ∀ (r : ℕ) (_hr : r ≤ m),
      let Tr := ((List.finRange m).take r).foldl (fun T g => insertVec T (kToVec (gen g))) (PivotTable.empty k)
      Tr.WF ∧ Tr.span = Submodule.span K {v | ∃ g : Fin m, g.1 < r ∧ v = gen g} := by
    intro r
    induction r with
    | zero =>
      intro _
      simp [PivotTable.empty_wf, PivotTable.empty_span]
    | succ r ih =>
      intro hr
      have htake : (List.finRange m).take (r + 1) = (List.finRange m).take r ++ [⟨r, hr⟩] := by
        rw [List.take_succ_eq_append_getElem (by simp; omega)]
        simp
      obtain ⟨hwf, hsp⟩ := ih (by omega)
      set Tr := ((List.finRange m).take r).foldl (fun T g => insertVec T (kToVec (gen g))) (PivotTable.empty k)
      have heq : ((List.finRange m).take (r + 1)).foldl (fun T g => insertVec T (kToVec (gen g))) (PivotTable.empty k) =
          insertVec Tr (kToVec (gen ⟨r, hr⟩)) := by
        rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
      dsimp only
      rw [heq]
      obtain ⟨hwf', hsp'⟩ := insertVec_spec Tr hwf (kToVec (gen ⟨r, hr⟩))
      refine ⟨hwf', ?_⟩
      rw [hsp', hsp, vecToK_kToVec, ← Submodule.span_union]
      congr 1; ext v
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro (⟨g, hgr, rfl⟩ | rfl)
        · exact ⟨g, by omega, rfl⟩
        · exact ⟨⟨r, hr⟩, by dsimp only; omega, rfl⟩
      · rintro ⟨g, hgr, rfl⟩
        by_cases hlt : g.1 < r
        · exact Or.inl ⟨g, hlt, rfl⟩
        · exact Or.inr (congrArg gen (Fin.ext (by dsimp only; omega)))
  have hfull := hfold m (le_refl m)
  have htake : (List.finRange m).take m = List.finRange m := List.take_of_length_le (by simp)
  rw [htake] at hfull
  change T.WF ∧ T.span = Submodule.span K {v | ∃ g : Fin m, g.1 < m ∧ v = gen g} at hfull
  refine ⟨hfull.1, ?_⟩
  rw [← PivotTable.finrank_eq_count T hfull.1, hfull.2]
  refine congrArg (fun S : Submodule K (Fin k → K) => Module.finrank K S) ?_
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨g, _, rfl⟩
    refine ⟨Pi.single g 1, ?_⟩
    simp only [Lgen, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single g]
    · simp
    · intro i _ hig; simp [hig]
    · intro hnm; exact absurd (Finset.mem_univ g) hnm
  · rintro _ ⟨x, rfl⟩
    simp only [Lgen, LinearMap.coe_mk, AddHom.coe_mk]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, g.2, rfl⟩)

private def shiftRightBits {k m : ℕ} (totalX : Fin (m + 1) → Bool)
    (ohGen : Fin (k + 1) → Bool) (o : Fin (k + 1)) : Bool :=
  (List.finRange (k + 1)).foldl (fun acc r =>
    acc || (ohGen r && if h : o.1 + (m - r.1) < m + 1 then totalX ⟨o.1 + (m - r.1), h⟩ else false)) false

private lemma shiftRightBits_spec {k m : ℕ} (totalX : Fin (m + 1) → Bool)
    (ohGen : Fin (k + 1) → Bool) (rk count : ℕ)
    (hrk_k : rk ≤ k) (_hrk_m : rk ≤ m)
    (hoh : ∀ r : Fin (k + 1), ohGen r = decide (r.1 = rk))
    (hcnt : bitsToNat totalX = count * 2 ^ (m - rk))
    (o : Fin (k + 1)) :
    shiftRightBits totalX ohGen o = count.testBit o.1 := by
  let f : Fin (k + 1) → Bool := fun r =>
    ohGen r && if h : o.1 + (m - r.1) < m + 1 then totalX ⟨o.1 + (m - r.1), h⟩ else false
  have hfold_or : ∀ (L : List (Fin (k + 1))) (init : Bool),
      L.foldl (fun acc r => acc || f r) init = true ↔ init = true ∨ ∃ r ∈ L, f r = true := by
    intro L
    induction L with
    | nil => intro init; simp
    | cons r L ih =>
      intro init
      rw [List.foldl_cons, ih]
      simp only [Bool.or_eq_true, List.mem_cons]
      constructor
      · rintro ((hi | hfr) | ⟨r', hr', hfr'⟩)
        · exact Or.inl hi
        · exact Or.inr ⟨r, Or.inl rfl, hfr⟩
        · exact Or.inr ⟨r', Or.inr hr', hfr'⟩
      · rintro (hi | ⟨r', rfl | hr', hfr'⟩)
        · exact Or.inl (Or.inl hi)
        · exact Or.inl (Or.inr hfr')
        · exact Or.inr ⟨r', hr', hfr'⟩
  have hres : shiftRightBits totalX ohGen o = f ⟨rk, by omega⟩ := by
    apply Bool.eq_iff_iff.mpr
    unfold shiftRightBits
    change (List.finRange (k + 1)).foldl (fun acc r => acc || f r) false = true ↔ f ⟨rk, by omega⟩ = true
    rw [hfold_or]
    simp only [Bool.false_eq_true, false_or, List.mem_finRange, true_and]
    constructor
    · rintro ⟨r, hr⟩
      have hoh_r : ohGen r = true := (Bool.and_eq_true_iff.mp hr).1
      rw [hoh r, decide_eq_true_eq] at hoh_r
      have hreq : r = ⟨rk, by omega⟩ := Fin.ext hoh_r
      rwa [← hreq]
    · intro h; exact ⟨⟨rk, by omega⟩, h⟩
  rw [hres]
  have htb_shift : ∀ (a d pos : ℕ), (a * 2 ^ d).testBit (pos + d) = a.testBit pos := by
    intro a d
    induction d with
    | zero => intro pos; simp
    | succ d ih =>
      intro pos
      have h1 : a * 2 ^ (d + 1) = 2 * (a * 2 ^ d) := by ring
      have h2 : pos + (d + 1) = (pos + d) + 1 := by omega
      rw [h1, h2, Nat.testBit_succ, Nat.mul_div_right _ (by decide), ih pos]
  have htb : (bitsToNat totalX).testBit (o.1 + (m - rk)) = count.testBit o.1 := by
    rw [hcnt, htb_shift]
  rw [← htb, bitsToNat_testBit]
  simp only [f, hoh ⟨rk, by omega⟩, decide_true, Bool.true_and]

-- ============================================================================
-- Section 3: Fan-in-Two Circuit Compiler
-- ============================================================================

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private def wiresOf (g : List Gate) (x : List Bool) : List Bool :=
  (Circuit.mk g 0).wires x

private def val (g : List Gate) (x : List Bool) (w : ℕ) : Bool :=
  (wiresOf g x).getD w false

private def Extends (g1 g2 : List Gate) : Prop :=
  ∃ rest, g2 = g1 ++ rest

private def GoodCircuit (n : ℕ) (g : List Gate) : Prop :=
  FanInTwo ⟨g, 0⟩ ∧ ReadsBack n ⟨g, 0⟩

private lemma Extends.refl (g : List Gate) : Extends g g :=
  ⟨[], (List.append_nil g).symm⟩

private lemma Extends.trans {g1 g2 g3 : List Gate} (h1 : Extends g1 g2) (h2 : Extends g2 g3) :
    Extends g1 g3 := by
  rcases h1 with ⟨r1, rfl⟩
  rcases h2 with ⟨r2, rfl⟩
  exact ⟨r1 ++ r2, List.append_assoc _ _ _⟩

private lemma Extends.len_le {g1 g2 : List Gate} (h : Extends g1 g2) :
    g1.length ≤ g2.length := by
  rcases h with ⟨r, rfl⟩
  simp

private lemma GoodCircuit.nil (n : ℕ) : GoodCircuit n [] := by
  constructor
  · intro g hg; simp at hg
  · intro j hj; simp at hj

private lemma wiresOf_length (g : List Gate) (x : List Bool) :
    (wiresOf g x).length = x.length + g.length := by
  unfold wiresOf Circuit.wires
  dsimp only
  induction g generalizing x with
  | nil => simp
  | cons gt gs ih =>
    rw [List.foldl_cons, ih]
    simp
    omega

private lemma wiresOf_append_exists (g1 g2 : List Gate) (x : List Bool) :
    ∃ rest, wiresOf (g1 ++ g2) x = wiresOf g1 x ++ rest := by
  unfold wiresOf Circuit.wires
  dsimp only
  rw [List.foldl_append]
  generalize g1.foldl (fun w gt => w ++ [gt.op.eval (gt.inputs.map fun i => w.getD i false)]) x = w0
  induction g2 generalizing w0 with
  | nil => exact ⟨[], by simp⟩
  | cons gt gs ih =>
    rw [List.foldl_cons]
    obtain ⟨rest, hr⟩ := ih (w0 ++ [gt.op.eval (gt.inputs.map fun i => w0.getD i false)])
    exact ⟨gt.op.eval (gt.inputs.map fun i => w0.getD i false) :: rest, by simpa [List.append_assoc] using hr⟩

private lemma list_getD_append_left {α : Type} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma val_of_extends {n : ℕ} {g1 g2 : List Gate} {x : List Bool} {w : ℕ}
    (hx : x.length = n) (hext : Extends g1 g2) (hw : w < n + g1.length) :
    val g2 x w = val g1 x w := by
  rcases hext with ⟨rest, rfl⟩
  obtain ⟨wrest, hwr⟩ := wiresOf_append_exists g1 rest x
  unfold val
  rw [hwr, list_getD_append_left]
  rw [wiresOf_length, hx]
  exact hw

private lemma val_input {n : ℕ} (g : List Gate) {x : List Bool} {w : ℕ}
    (hx : x.length = n) (hw : w < n) :
    val g x w = x.getD w false := by
  have hext : Extends [] g := ⟨g, rfl⟩
  have h1 := val_of_extends hx hext (by simpa using hw)
  simpa [val, wiresOf, Circuit.wires] using h1

private def addGate (n : ℕ) (g : List Gate) (op : GateOp) (ins : List ℕ) : List Gate × ℕ :=
  let bound := n + g.length
  let ins' := (ins.take 2).map (fun i => if i < bound then i else 0)
  (g ++ [⟨op, ins'⟩], bound)

private lemma addGate_spec {n : ℕ} (_hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (op : GateOp) (ins : List ℕ)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : ins.length ≤ 2) (hins : ∀ i ∈ ins, i < n + g.length) :
    let res := addGate n g op ins
    GoodCircuit n res.1 ∧
    Extends g res.1 ∧
    res.1.length = g.length + 1 ∧
    res.2 = n + g.length ∧
    res.2 < n + res.1.length ∧
    ∀ x : List Bool, x.length = n → val res.1 x res.2 = op.eval (ins.map (val g x)) := by
  dsimp only [addGate]
  have htake : ins.take 2 = ins := List.take_of_length_le hlen
  have hmap : (ins.take 2).map (fun i => if i < n + g.length then i else 0) = ins := by
    rw [htake]
    have : ∀ l : List ℕ, (∀ i ∈ l, i < n + g.length) →
        l.map (fun i => if i < n + g.length then i else 0) = l := by
      intro l hl
      induction l with
      | nil => rfl
      | cons a l ih =>
        have ha : a < n + g.length := hl a List.mem_cons_self
        simp only [List.map_cons, ha, ↓reduceIte, ih fun i hi => hl i (List.mem_cons_of_mem _ hi)]
    exact this ins hins
  refine ⟨⟨?_, ?_⟩, ⟨[⟨op, (ins.take 2).map (fun i => if i < n + g.length then i else 0)⟩], rfl⟩,
    by simp, rfl, by simp, ?_⟩
  · intro gt hgt
    simp only [List.mem_append, List.mem_singleton] at hgt
    rcases hgt with h1 | rfl
    · exact hg.1 gt h1
    · exact ⟨hop, by simp [hmap, hlen]⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < g.length
    · have hget : gateAt ⟨g ++ [⟨op, (ins.take 2).map (fun i => if i < n + g.length then i else 0)⟩], 0⟩ j =
          gateAt ⟨g, 0⟩ j := by
        unfold gateAt
        exact list_getD_append_left g _ j _ hlt
      rw [hget] at hi
      exact hg.2 j hlt i hi
    · have hjeq : j = g.length := by omega
      subst hjeq
      have hget : gateAt ⟨g ++ [⟨op, (ins.take 2).map (fun i => if i < n + g.length then i else 0)⟩], 0⟩ g.length =
          ⟨op, (ins.take 2).map (fun i => if i < n + g.length then i else 0)⟩ := by
        unfold gateAt
        simp [List.getD_eq_getElem?_getD]
      rw [hget] at hi
      dsimp only at hi
      rw [hmap] at hi
      exact hins i hi
  · intro x hx
    unfold val wiresOf Circuit.wires
    dsimp only
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hmap]
    have hlen_w : (wiresOf g x).length = n + g.length := by rw [wiresOf_length, hx]
    change (wiresOf g x ++ [op.eval (ins.map fun i => (wiresOf g x).getD i false)]).getD (n + g.length) false = _
    rw [← hlen_w, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
    rfl

-- Seven basic fan-in-2 gate builders
private def cFalse (n : ℕ) (g : List Gate) : List Gate × ℕ :=
  addGate n g GateOp.or []

private def cTrue (n : ℕ) (g : List Gate) : List Gate × ℕ :=
  addGate n g GateOp.and []

private def cNot (n : ℕ) (g : List Gate) (a : ℕ) : List Gate × ℕ :=
  addGate n g GateOp.not [a]

private def cAnd (n : ℕ) (g : List Gate) (a b : ℕ) : List Gate × ℕ :=
  addGate n g GateOp.and [a, b]

private def cOr (n : ℕ) (g : List Gate) (a b : ℕ) : List Gate × ℕ :=
  addGate n g GateOp.or [a, b]

private def cXor (n : ℕ) (g : List Gate) (a b : ℕ) : List Gate × ℕ :=
  let r1 := cOr n g a b
  let r2 := cAnd n r1.1 a b
  let r3 := cNot n r2.1 r2.2
  cAnd n r3.1 r1.2 r3.2

private def cMux (n : ℕ) (g : List Gate) (sel a b : ℕ) : List Gate × ℕ :=
  let r1 := cNot n g sel
  let r2 := cAnd n r1.1 sel a
  let r3 := cAnd n r2.1 r1.2 b
  cOr n r3.1 r2.2 r3.2

private lemma cFalse_spec {n : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g) :
    let r := cFalse n g
    GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + 1 ∧ r.2 < n + r.1.length ∧
    ∀ x, x.length = n → val r.1 x r.2 = false := by
  dsimp only [cFalse]
  have h := addGate_spec hn g hg GateOp.or [] (by simp) (by simp) (by simp)
  exact ⟨h.1, h.2.1, by have := h.2.2.1; omega, h.2.2.2.2.1, fun x hx => by simpa [GateOp.eval] using h.2.2.2.2.2 x hx⟩

private lemma cTrue_spec {n : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g) :
    let r := cTrue n g
    GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + 1 ∧ r.2 < n + r.1.length ∧
    ∀ x, x.length = n → val r.1 x r.2 = true := by
  dsimp only [cTrue]
  have h := addGate_spec hn g hg GateOp.and [] (by simp) (by simp) (by simp)
  exact ⟨h.1, h.2.1, by have := h.2.2.1; omega, h.2.2.2.2.1, fun x hx => by simpa [GateOp.eval] using h.2.2.2.2.2 x hx⟩

private lemma cNot_spec {n : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (a : ℕ) (ha : a < n + g.length) :
    let r := cNot n g a
    GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + 1 ∧ r.2 < n + r.1.length ∧
    ∀ x, x.length = n → val r.1 x r.2 = !(val g x a) := by
  dsimp only [cNot]
  have h := addGate_spec hn g hg GateOp.not [a] (by simp) (by simp) (by simpa using ha)
  exact ⟨h.1, h.2.1, by have := h.2.2.1; omega, h.2.2.2.2.1, fun x hx => by simpa [GateOp.eval] using h.2.2.2.2.2 x hx⟩

private lemma cAnd_spec {n : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (a b : ℕ) (ha : a < n + g.length) (hb : b < n + g.length) :
    let r := cAnd n g a b
    GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + 1 ∧ r.2 < n + r.1.length ∧
    ∀ x, x.length = n → val r.1 x r.2 = (val g x a && val g x b) := by
  dsimp only [cAnd]
  have h := addGate_spec hn g hg GateOp.and [a, b] (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)
  exact ⟨h.1, h.2.1, by have := h.2.2.1; omega, h.2.2.2.2.1, fun x hx => by simpa [GateOp.eval] using h.2.2.2.2.2 x hx⟩

private lemma cOr_spec {n : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (a b : ℕ) (ha : a < n + g.length) (hb : b < n + g.length) :
    let r := cOr n g a b
    GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + 1 ∧ r.2 < n + r.1.length ∧
    ∀ x, x.length = n → val r.1 x r.2 = (val g x a || val g x b) := by
  dsimp only [cOr]
  have h := addGate_spec hn g hg GateOp.or [a, b] (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)
  exact ⟨h.1, h.2.1, by have := h.2.2.1; omega, h.2.2.2.2.1, fun x hx => by simpa [GateOp.eval] using h.2.2.2.2.2 x hx⟩

private lemma cXor_spec {n : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (a b : ℕ) (ha : a < n + g.length) (hb : b < n + g.length) :
    let r := cXor n g a b
    GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + 4 ∧ r.2 < n + r.1.length ∧
    ∀ x, x.length = n → val r.1 x r.2 = xor (val g x a) (val g x b) := by
  dsimp only [cXor]
  have h1 := cOr_spec hn g hg a b ha hb
  set r1 := cOr n g a b
  have h1le := h1.2.1.len_le
  have h2 := cAnd_spec hn r1.1 h1.1 a b (by omega) (by omega)
  set r2 := cAnd n r1.1 a b
  have h2le := h2.2.1.len_le
  have h3 := cNot_spec hn r2.1 h2.1 r2.2 h2.2.2.2.1
  set r3 := cNot n r2.1 r2.2
  have h3le := h3.2.1.len_le
  have h4 := cAnd_spec hn r3.1 h3.1 r1.2 r3.2 (by have a1 := h1.2.2.2.1; omega) h3.2.2.2.1
  refine ⟨h4.1, ((h1.2.1.trans h2.2.1).trans h3.2.1).trans h4.2.1,
    by have a1 := h1.2.2.1; have a2 := h2.2.2.1; have a3 := h3.2.2.1; have a4 := h4.2.2.1; omega,
    h4.2.2.2.1, fun x hx => ?_⟩
  rw [h4.2.2.2.2 x hx]
  have e1 : val r3.1 x r1.2 = (val g x a || val g x b) := by
    rw [val_of_extends hx (h2.2.1.trans h3.2.1) h1.2.2.2.1, h1.2.2.2.2 x hx]
  have e2 : val r3.1 x r3.2 = !(val g x a && val g x b) := by
    rw [h3.2.2.2.2 x hx, h2.2.2.2.2 x hx, val_of_extends hx h1.2.1 ha, val_of_extends hx h1.2.1 hb]
  rw [e1, e2]
  cases val g x a <;> cases val g x b <;> rfl

private lemma cMux_spec {n : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (sel a b : ℕ) (hs : sel < n + g.length) (ha : a < n + g.length) (hb : b < n + g.length) :
    let r := cMux n g sel a b
    GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + 4 ∧ r.2 < n + r.1.length ∧
    ∀ x, x.length = n → val r.1 x r.2 = if val g x sel then val g x a else val g x b := by
  dsimp only [cMux]
  have h1 := cNot_spec hn g hg sel hs
  set r1 := cNot n g sel
  have h1le := h1.2.1.len_le
  have h2 := cAnd_spec hn r1.1 h1.1 sel a (by omega) (by omega)
  set r2 := cAnd n r1.1 sel a
  have h2le := h2.2.1.len_le
  have h3 := cAnd_spec hn r2.1 h2.1 r1.2 b (by have a1 := h1.2.2.2.1; omega) (by omega)
  set r3 := cAnd n r2.1 r1.2 b
  have h3le := h3.2.1.len_le
  have h4 := cOr_spec hn r3.1 h3.1 r2.2 r3.2 (by have a2 := h2.2.2.2.1; omega) h3.2.2.2.1
  refine ⟨h4.1, ((h1.2.1.trans h2.2.1).trans h3.2.1).trans h4.2.1,
    by have a1 := h1.2.2.1; have a2 := h2.2.2.1; have a3 := h3.2.2.1; have a4 := h4.2.2.1; omega,
    h4.2.2.2.1, fun x hx => ?_⟩
  rw [h4.2.2.2.2 x hx]
  have e2 : val r3.1 x r2.2 = (val g x sel && val g x a) := by
    rw [val_of_extends hx h3.2.1 h2.2.2.2.1, h2.2.2.2.2 x hx, val_of_extends hx h1.2.1 hs, val_of_extends hx h1.2.1 ha]
  have e3 : val r3.1 x r3.2 = (!(val g x sel) && val g x b) := by
    rw [h3.2.2.2.2 x hx, val_of_extends hx h2.2.1 h1.2.2.2.1, h1.2.2.2.2 x hx,
      val_of_extends hx (h1.2.1.trans h2.2.1) hb]
  rw [e2, e3]
  cases val g x sel <;> cases val g x a <;> cases val g x b <;> rfl

-- Generic circuit combinators: cBuildFin and cFoldl
private def cBuildFin {α : Type} : (len : ℕ) → (List Gate → Fin len → List Gate × α) → List Gate → List Gate × (Fin len → α)
  | 0, _, g => (g, Fin.elim0)
  | len + 1, f, g =>
    let r0 := f g 0
    let rest := cBuildFin len (fun g' i => f g' i.succ) r0.1
    (rest.1, Fin.cons (α := fun _ => α) r0.2 rest.2)

private lemma cBuildFin_spec {n : ℕ} {α β : Type}
    (ValidA : ℕ → α → Prop)
    (hValid_mono : ∀ {L1 L2 a}, L1 ≤ L2 → ValidA L1 a → ValidA L2 a)
    (evalA : List Gate → List Bool → α → β)
    (heval_ext : ∀ {g1 g2 x a}, x.length = n → Extends g1 g2 → ValidA (n + g1.length) a → evalA g2 x a = evalA g1 x a)
    (len B : ℕ) (f : List Gate → Fin len → List Gate × α)
    (target : List Bool → Fin len → β)
    (g0 : List Gate) (hg0 : GoodCircuit n g0)
    (hstep : ∀ (g : List Gate) (i : Fin len), GoodCircuit n g → Extends g0 g →
      let r := f g i
      GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + B ∧
      ValidA (n + r.1.length) r.2 ∧ ∀ x, x.length = n → evalA r.1 x r.2 = target x i) :
    let res := cBuildFin len f g0
    GoodCircuit n res.1 ∧ Extends g0 res.1 ∧ res.1.length ≤ g0.length + len * B ∧
    (∀ i : Fin len, ValidA (n + res.1.length) (res.2 i)) ∧
    ∀ x, x.length = n → ∀ i : Fin len, evalA res.1 x (res.2 i) = target x i := by
  induction len generalizing g0 with
  | zero =>
    dsimp only [cBuildFin]
    refine ⟨hg0, Extends.refl g0, by simp, fun i => i.elim0, fun _ _ i => i.elim0⟩
  | succ len ih =>
    dsimp only [cBuildFin]
    have h0 := hstep g0 0 hg0 (Extends.refl g0)
    have hrest := ih (fun g' i => f g' i.succ) (fun x i => target x i.succ) (f g0 0).1 h0.1
      (fun g i hg hext => hstep g i.succ hg (h0.2.1.trans hext))
    have hlen_le : (cBuildFin len (fun g' i => f g' i.succ) (f g0 0).1).1.length ≤ g0.length + (len + 1) * B := by
      have h1 := h0.2.2.1
      have h2 := hrest.2.2.1
      have hmul : (len + 1) * B = len * B + B := by ring
      omega
    refine ⟨hrest.1, h0.2.1.trans hrest.2.1, hlen_le, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => hrest.2.2.2.1 j) i
      exact hValid_mono (by have := hrest.2.1.len_le; omega) h0.2.2.2.1
    · intro x hx i
      refine Fin.cases ?_ (fun j => hrest.2.2.2.2 x hx j) i
      simp only [Fin.cons_zero]
      rw [heval_ext hx hrest.2.1 h0.2.2.2.1, h0.2.2.2.2 x hx]

private def cFoldl {α S : Type} (step : List Gate → S → α → List Gate × S) :
    List α → List Gate → S → List Gate × S
  | [], g, s => (g, s)
  | a :: L, g, s =>
    let r := step g s a
    cFoldl step L r.1 r.2

private lemma cFoldl_spec {n : ℕ} {α S T : Type}
    (ValidS : ℕ → S → Prop)
    (evalS : List Gate → List Bool → S → T)
    (step : List Gate → S → α → List Gate × S)
    (pureStep : List Bool → T → α → T)
    (B : ℕ) (L : List α) (g0 : List Gate) (s0 : S)
    (hg0 : GoodCircuit n g0) (hs0 : ValidS (n + g0.length) s0)
    (hstep : ∀ (g : List Gate) (s : S) (a : α), a ∈ L → GoodCircuit n g → Extends g0 g → ValidS (n + g.length) s →
      let r := step g s a
      GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + B ∧
      ValidS (n + r.1.length) r.2 ∧ ∀ x, x.length = n → evalS r.1 x r.2 = pureStep x (evalS g x s) a) :
    let res := cFoldl step L g0 s0
    GoodCircuit n res.1 ∧ Extends g0 res.1 ∧ res.1.length ≤ g0.length + L.length * B ∧
    ValidS (n + res.1.length) res.2 ∧
    ∀ x, x.length = n → evalS res.1 x res.2 = L.foldl (pureStep x) (evalS g0 x s0) := by
  induction L generalizing g0 s0 with
  | nil =>
    dsimp only [cFoldl]
    exact ⟨hg0, Extends.refl g0, by simp, hs0, fun _ _ => rfl⟩
  | cons a L ih =>
    dsimp only [cFoldl]
    have h0 := hstep g0 s0 a List.mem_cons_self hg0 (Extends.refl g0) hs0
    have hrest := ih (step g0 s0 a).1 (step g0 s0 a).2 h0.1 h0.2.2.2.1
      (fun g s a' ha' hg hext hs => hstep g s a' (List.mem_cons_of_mem _ ha') hg (h0.2.1.trans hext) hs)
    have hlen_le : (cFoldl step L (step g0 s0 a).1 (step g0 s0 a).2).1.length ≤ g0.length + (a :: L).length * B := by
      have h1 := h0.2.2.1
      have h2 := hrest.2.2.1
      simp only [List.length_cons]
      have hmul : (L.length + 1) * B = L.length * B + B := by ring
      omega
    refine ⟨hrest.1, h0.2.1.trans hrest.2.1, hlen_le, hrest.2.2.2.1, fun x hx => ?_⟩
    rw [hrest.2.2.2.2 x hx, h0.2.2.2.2 x hx, List.foldl_cons]

-- Wire representations & evaluators
private abbrev VecW (m : ℕ) := Fin m → ℕ

private def ValidVec {m : ℕ} (L : ℕ) (v : VecW m) : Prop := ∀ j, v j < L

private def evalVec {m : ℕ} (g : List Gate) (x : List Bool) (v : VecW m) : Vec m :=
  fun j => val g x (v j)

private lemma ValidVec.mono {m L1 L2 : ℕ} {v : VecW m} (hL : L1 ≤ L2) (hv : ValidVec L1 v) :
    ValidVec L2 v := fun j => lt_of_lt_of_le (hv j) hL

private lemma evalVec_of_extends {n m : ℕ} {g1 g2 : List Gate} {x : List Bool} {v : VecW m}
    (hx : x.length = n) (hext : Extends g1 g2) (hv : ValidVec (n + g1.length) v) :
    evalVec g2 x v = evalVec g1 x v := by
  funext j; exact val_of_extends hx hext (hv j)

private structure PivotW (m : ℕ) where
  hasPiv : Fin m → ℕ
  row : Fin m → VecW m

private def ValidPivot {m : ℕ} (L : ℕ) (T : PivotW m) : Prop :=
  (∀ j, T.hasPiv j < L) ∧ (∀ j, ValidVec L (T.row j))

private def evalPivot {m : ℕ} (g : List Gate) (x : List Bool) (T : PivotW m) : PivotTable m :=
  ⟨fun j => val g x (T.hasPiv j), fun j => evalVec g x (T.row j)⟩

private lemma ValidPivot.mono {m L1 L2 : ℕ} {T : PivotW m} (hL : L1 ≤ L2) (hT : ValidPivot L1 T) :
    ValidPivot L2 T := ⟨fun j => lt_of_lt_of_le (hT.1 j) hL, fun j => (hT.2 j).mono hL⟩

private lemma evalPivot_of_extends {n m : ℕ} {g1 g2 : List Gate} {x : List Bool} {T : PivotW m}
    (hx : x.length = n) (hext : Extends g1 g2) (hT : ValidPivot (n + g1.length) T) :
    evalPivot g2 x T = evalPivot g1 x T := by
  cases T
  simp only [evalPivot, PivotTable.mk.injEq]
  exact ⟨funext fun j => val_of_extends hx hext (hT.1 j),
    funext fun j => evalVec_of_extends hx hext (hT.2 j)⟩

private structure AugW (m : ℕ) where
  piv : PivotW m
  rhs : Fin m → ℕ
  inc : ℕ

private def ValidAug {m : ℕ} (L : ℕ) (A : AugW m) : Prop :=
  ValidPivot L A.piv ∧ (∀ j, A.rhs j < L) ∧ A.inc < L

private def evalAug {m : ℕ} (g : List Gate) (x : List Bool) (A : AugW m) : AugTable m :=
  ⟨evalPivot g x A.piv, fun j => val g x (A.rhs j), val g x A.inc⟩

private lemma ValidAug.mono {m L1 L2 : ℕ} {A : AugW m} (hL : L1 ≤ L2) (hA : ValidAug L1 A) :
    ValidAug L2 A := ⟨hA.1.mono hL, fun j => lt_of_lt_of_le (hA.2.1 j) hL, lt_of_lt_of_le hA.2.2 hL⟩

private lemma evalAug_of_extends {n m : ℕ} {g1 g2 : List Gate} {x : List Bool} {A : AugW m}
    (hx : x.length = n) (hext : Extends g1 g2) (hA : ValidAug (n + g1.length) A) :
    evalAug g2 x A = evalAug g1 x A := by
  cases A
  simp only [evalAug, AugTable.mk.injEq]
  exact ⟨evalPivot_of_extends hx hext hA.1, funext fun j => val_of_extends hx hext (hA.2.1 j),
    val_of_extends hx hext hA.2.2⟩

-- Vector circuit builders
private def cVecZero (n m : ℕ) (g : List Gate) : List Gate × VecW m :=
  cBuildFin m (fun g' _ => cFalse n g') g

private lemma cVecZero_spec {n m : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g) :
    let r := cVecZero n m g
    GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + m ∧
    ValidVec (n + r.1.length) r.2 ∧
    ∀ x, x.length = n → evalVec r.1 x r.2 = vecZero m := by
  dsimp only [cVecZero]
  have h := cBuildFin_spec (n := n) (fun L w => w < L) (fun hL hw => lt_of_lt_of_le hw hL)
    val (fun hx hext hw => val_of_extends hx hext hw) m 1 (fun g' _ => cFalse n g') (fun _ _ => false) g hg
    (fun g' _ hg' _ => cFalse_spec hn g' hg')
  exact ⟨h.1, h.2.1, by simpa using h.2.2.1, h.2.2.2.1, fun x hx => funext fun j => h.2.2.2.2 x hx j⟩

private def cVecXor (n m : ℕ) (g : List Gate) (a b : VecW m) : List Gate × VecW m :=
  cBuildFin m (fun g' j => cXor n g' (a j) (b j)) g

private lemma cVecXor_spec {n m : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (a b : VecW m) (ha : ValidVec (n + g.length) a) (hb : ValidVec (n + g.length) b) :
    let r := cVecXor n m g a b
    GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + 4 * m ∧
    ValidVec (n + r.1.length) r.2 ∧
    ∀ x, x.length = n → evalVec r.1 x r.2 = vecXor (evalVec g x a) (evalVec g x b) := by
  dsimp only [cVecXor]
  have h := cBuildFin_spec (n := n) (fun L w => w < L) (fun hL hw => lt_of_lt_of_le hw hL)
    val (fun hx hext hw => val_of_extends hx hext hw) m 4 (fun g' j => cXor n g' (a j) (b j))
    (fun x j => xor (val g x (a j)) (val g x (b j))) g hg (fun g' j hg' hext => by
      have hle := hext.len_le
      have h1 := cXor_spec hn g' hg' (a j) (b j) (by have := ha j; omega) (by have := hb j; omega)
      exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, fun x hx => by
        rw [h1.2.2.2.2 x hx, val_of_extends hx hext (ha j), val_of_extends hx hext (hb j)]⟩)
  exact ⟨h.1, h.2.1, by have := h.2.2.1; omega, h.2.2.2.1, fun x hx => funext fun j => h.2.2.2.2 x hx j⟩

private def cVecAndScalar (n m : ℕ) (g : List Gate) (s : ℕ) (v : VecW m) : List Gate × VecW m :=
  cBuildFin m (fun g' j => cAnd n g' s (v j)) g

private lemma cVecAndScalar_spec {n m : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (s : ℕ) (v : VecW m) (hs : s < n + g.length) (hv : ValidVec (n + g.length) v) :
    let r := cVecAndScalar n m g s v
    GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + m ∧
    ValidVec (n + r.1.length) r.2 ∧
    ∀ x, x.length = n → evalVec r.1 x r.2 = fun j => val g x s && evalVec g x v j := by
  dsimp only [cVecAndScalar]
  have h := cBuildFin_spec (n := n) (fun L w => w < L) (fun hL hw => lt_of_lt_of_le hw hL)
    val (fun hx hext hw => val_of_extends hx hext hw) m 1 (fun g' j => cAnd n g' s (v j))
    (fun x j => val g x s && val g x (v j)) g hg (fun g' j hg' hext => by
      have hle := hext.len_le
      have h1 := cAnd_spec hn g' hg' s (v j) (by omega) (by have := hv j; omega)
      exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, fun x hx => by
        rw [h1.2.2.2.2 x hx, val_of_extends hx hext hs, val_of_extends hx hext (hv j)]⟩)
  exact ⟨h.1, h.2.1, by simpa using h.2.2.1, h.2.2.2.1, fun x hx => funext fun j => h.2.2.2.2 x hx j⟩

private def cVecMux (n m : ℕ) (g : List Gate) (sel : ℕ) (a b : VecW m) : List Gate × VecW m :=
  cBuildFin m (fun g' j => cMux n g' sel (a j) (b j)) g

private lemma cVecMux_spec {n m : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (sel : ℕ) (a b : VecW m) (hs : sel < n + g.length)
    (ha : ValidVec (n + g.length) a) (hb : ValidVec (n + g.length) b) :
    let r := cVecMux n m g sel a b
    GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + 4 * m ∧
    ValidVec (n + r.1.length) r.2 ∧
    ∀ x, x.length = n → evalVec r.1 x r.2 = if val g x sel then evalVec g x a else evalVec g x b := by
  dsimp only [cVecMux]
  have h := cBuildFin_spec (n := n) (fun L w => w < L) (fun hL hw => lt_of_lt_of_le hw hL)
    val (fun hx hext hw => val_of_extends hx hext hw) m 4 (fun g' j => cMux n g' sel (a j) (b j))
    (fun x j => if val g x sel then val g x (a j) else val g x (b j)) g hg (fun g' j hg' hext => by
      have hle := hext.len_le
      have h1 := cMux_spec hn g' hg' sel (a j) (b j) (by omega) (by have := ha j; omega) (by have := hb j; omega)
      exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, fun x hx => by
        rw [h1.2.2.2.2 x hx, val_of_extends hx hext hs, val_of_extends hx hext (ha j), val_of_extends hx hext (hb j)]⟩)
  refine ⟨h.1, h.2.1, by have := h.2.2.1; omega, h.2.2.2.1, fun x hx => funext fun j => ?_⟩
  rw [evalVec, h.2.2.2.2 x hx j]
  cases val g x sel <;> rfl

private lemma list_all_eq_foldl_and {α : Type} (L : List α) (f : α → Bool) :
    L.all f = L.foldl (fun acc a => acc && f a) true := by
  have hgen : ∀ (init : Bool), (init && L.all f) = L.foldl (fun acc a => acc && f a) init := by
    induction L with
    | nil => intro init; simp
    | cons a L ih =>
      intro init
      rw [List.all_cons, List.foldl_cons, ← ih, Bool.and_assoc]
  simpa using hgen true

private def cVecIsZero (n m : ℕ) (g : List Gate) (v : VecW m) : List Gate × ℕ :=
  let r0 := cTrue n g
  cFoldl (fun g' acc j =>
    let r1 := cNot n g' (v j)
    cAnd n r1.1 acc r1.2) (List.finRange m) r0.1 r0.2

private lemma cVecIsZero_spec {n m : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (v : VecW m) (hv : ValidVec (n + g.length) v) :
    let r := cVecIsZero n m g v
    GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + (2 * m + 1) ∧
    r.2 < n + r.1.length ∧
    ∀ x, x.length = n → val r.1 x r.2 = vecIsZero (evalVec g x v) := by
  dsimp only [cVecIsZero]
  have h0 := cTrue_spec hn g hg
  have h0le := h0.2.1.len_le
  have hf := cFoldl_spec (n := n) (fun L w => w < L) val
    (fun g' acc j => let r1 := cNot n g' (v j); cAnd n r1.1 acc r1.2)
    (fun x acc j => acc && !(val g x (v j)))
    2 (List.finRange m) (cTrue n g).1 (cTrue n g).2 h0.1 h0.2.2.2.1 (fun g' acc j _ hg' hext hacc => by
      have hle := hext.len_le
      have h1 := cNot_spec hn g' hg' (v j) (by have := hv j; omega)
      have h1le := h1.2.1.len_le
      have h2 := cAnd_spec hn (cNot n g' (v j)).1 h1.1 acc (cNot n g' (v j)).2 (by omega) h1.2.2.2.1
      refine ⟨h2.1, h1.2.1.trans h2.2.1, by dsimp only; have a1 := h1.2.2.1; have a2 := h2.2.2.1; omega, h2.2.2.2.1, fun x hx => ?_⟩
      rw [h2.2.2.2.2 x hx, val_of_extends hx h1.2.1 hacc, h1.2.2.2.2 x hx,
        val_of_extends hx (h0.2.1.trans hext) (hv j)])
  refine ⟨hf.1, h0.2.1.trans hf.2.1, by have a0 := h0.2.2.1; have af := hf.2.2.1; simp at af; omega, hf.2.2.2.1, fun x hx => ?_⟩
  rw [hf.2.2.2.2 x hx, h0.2.2.2.2 x hx]
  unfold vecIsZero evalVec
  exact (list_all_eq_foldl_and (List.finRange m) (fun j => !(val g x (v j)))).symm

private def cVecDot (n m : ℕ) (g : List Gate) (a b : VecW m) : List Gate × ℕ :=
  let r0 := cFalse n g
  cFoldl (fun g' acc j =>
    let r1 := cAnd n g' (a j) (b j)
    cXor n r1.1 acc r1.2) (List.finRange m) r0.1 r0.2

private lemma cVecDot_spec {n m : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (a b : VecW m) (ha : ValidVec (n + g.length) a) (hb : ValidVec (n + g.length) b) :
    let r := cVecDot n m g a b
    GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + (5 * m + 1) ∧
    r.2 < n + r.1.length ∧
    ∀ x, x.length = n → val r.1 x r.2 = vecDot (evalVec g x a) (evalVec g x b) := by
  dsimp only [cVecDot]
  have h0 := cFalse_spec hn g hg
  have h0le := h0.2.1.len_le
  have hf := cFoldl_spec (n := n) (fun L w => w < L) val
    (fun g' acc j => let r1 := cAnd n g' (a j) (b j); cXor n r1.1 acc r1.2)
    (fun x acc j => if val g x (a j) && val g x (b j) then !acc else acc)
    5 (List.finRange m) (cFalse n g).1 (cFalse n g).2 h0.1 h0.2.2.2.1 (fun g' acc j _ hg' hext hacc => by
      have hle := hext.len_le
      have h1 := cAnd_spec hn g' hg' (a j) (b j) (by have := ha j; omega) (by have := hb j; omega)
      have h1le := h1.2.1.len_le
      have h2 := cXor_spec hn (cAnd n g' (a j) (b j)).1 h1.1 acc (cAnd n g' (a j) (b j)).2 (by omega) h1.2.2.2.1
      refine ⟨h2.1, h1.2.1.trans h2.2.1, by dsimp only; have a1 := h1.2.2.1; have a2 := h2.2.2.1; omega, h2.2.2.2.1, fun x hx => ?_⟩
      rw [h2.2.2.2.2 x hx, val_of_extends hx h1.2.1 hacc, h1.2.2.2.2 x hx,
        val_of_extends hx (h0.2.1.trans hext) (ha j), val_of_extends hx (h0.2.1.trans hext) (hb j)]
      cases val g' x acc <;> cases val g x (a j) <;> cases val g x (b j) <;> rfl)
  refine ⟨hf.1, h0.2.1.trans hf.2.1, by have a0 := h0.2.2.1; have af := hf.2.2.1; simp at af; omega, hf.2.2.2.1, fun x hx => ?_⟩
  rw [hf.2.2.2.2 x hx, h0.2.2.2.2 x hx]
  rfl

private def cFirstTrue (n m : ℕ) (g : List Gate) (v : VecW m) : List Gate × VecW m :=
  cBuildFin m (fun g' j =>
    let r0 := cTrue n g'
    let rf := cFoldl (fun g'' acc i =>
      if i.1 < j.1 then
        let r1 := cNot n g'' (v i)
        cAnd n r1.1 acc r1.2
      else (g'', acc)) (List.finRange m) r0.1 r0.2
    cAnd n rf.1 (v j) rf.2) g

private lemma cFirstTrue_spec {n m : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (v : VecW m) (hv : ValidVec (n + g.length) v) :
    let r := cFirstTrue n m g v
    GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + m * (2 * m + 2) ∧
    ValidVec (n + r.1.length) r.2 ∧
    ∀ x, x.length = n → evalVec r.1 x r.2 = firstTrue (evalVec g x v) := by
  dsimp only [cFirstTrue]
  have h := cBuildFin_spec (n := n) (fun L w => w < L) (fun hL hw => lt_of_lt_of_le hw hL)
    val (fun hx hext hw => val_of_extends hx hext hw) m (2 * m + 2)
    (fun g' j =>
      let r0 := cTrue n g'
      let rf := cFoldl (fun g'' acc i =>
        if i.1 < j.1 then let r1 := cNot n g'' (v i); cAnd n r1.1 acc r1.2 else (g'', acc)) (List.finRange m) r0.1 r0.2
      cAnd n rf.1 (v j) rf.2)
    (fun x j => firstTrue (evalVec g x v) j) g hg (fun g' j hg' hext => by
      dsimp only
      have h0 := cTrue_spec hn g' hg'
      set r0 := cTrue n g'
      have hf := cFoldl_spec (n := n) (fun L w => w < L) val
        (fun g'' acc i => if i.1 < j.1 then let r1 := cNot n g'' (v i); cAnd n r1.1 acc r1.2 else (g'', acc))
        (fun x acc i => acc && (decide (i.1 < j.1) == false || !(val g x (v i))))
        2 (List.finRange m) r0.1 r0.2 h0.1 h0.2.2.2.1 (fun g'' acc i _ hg'' hext' hacc => by
          by_cases hij : i.1 < j.1
          · simp only [hij, ↓reduceIte]
            have hle := (hext.trans (h0.2.1.trans hext')).len_le
            have h1 := cNot_spec hn g'' hg'' (v i) (by have := hv i; omega)
            have h1le := h1.2.1.len_le
            have h2 := cAnd_spec hn (cNot n g'' (v i)).1 h1.1 acc (cNot n g'' (v i)).2 (by omega) h1.2.2.2.1
            refine ⟨h2.1, h1.2.1.trans h2.2.1, by have a1 := h1.2.2.1; have a2 := h2.2.2.1; omega, h2.2.2.2.1, fun x hx => ?_⟩
            rw [h2.2.2.2.2 x hx, val_of_extends hx h1.2.1 hacc, h1.2.2.2.2 x hx,
              val_of_extends hx (hext.trans (h0.2.1.trans hext')) (hv i)]
            simp
          · simp only [hij, ↓reduceIte]
            refine ⟨hg'', Extends.refl g'', by omega, hacc, fun x _ => by simp⟩)
      set rf := cFoldl (fun g'' acc i => if i.1 < j.1 then let r1 := cNot n g'' (v i); cAnd n r1.1 acc r1.2 else (g'', acc))
        (List.finRange m) r0.1 r0.2
      have hle_all := (hext.trans (h0.2.1.trans hf.2.1)).len_le
      have hand := cAnd_spec hn rf.1 hf.1 (v j) rf.2 (by have av := hv j; omega) hf.2.2.2.1
      refine ⟨hand.1, (h0.2.1.trans hf.2.1).trans hand.2.1,
        by have a0 := h0.2.2.1; have af := hf.2.2.1; have aa := hand.2.2.1; simp only [List.length_finRange] at af; omega,
        hand.2.2.2.1, fun x hx => ?_⟩
      rw [hand.2.2.2.2 x hx, val_of_extends hx (hext.trans (h0.2.1.trans hf.2.1)) (hv j),
        hf.2.2.2.2 x hx, h0.2.2.2.2 x hx]
      unfold firstTrue evalVec
      rw [list_all_eq_foldl_and])
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun x hx => funext fun j => h.2.2.2.2 x hx j⟩

-- PivotTable and AugTable circuit builders
private def cPivotEmpty (n m : ℕ) (g : List Gate) : List Gate × PivotW m :=
  let r1 := cVecZero n m g
  let r2 := cBuildFin m (fun g' _ => cVecZero n m g') r1.1
  (r2.1, ⟨r1.2, r2.2⟩)

private lemma cPivotEmpty_spec {n m : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g) :
    let r := cPivotEmpty n m g
    GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + (m * m + m) ∧
    ValidPivot (n + r.1.length) r.2 ∧
    ∀ x, x.length = n → evalPivot r.1 x r.2 = PivotTable.empty m := by
  dsimp only [cPivotEmpty]
  have h1 := cVecZero_spec hn (m := m) g hg
  have h2 := cBuildFin_spec (n := n) ValidVec (fun hL hv => hv.mono hL) evalVec
    (fun hx hext hv => evalVec_of_extends hx hext hv) m m (fun g' _ => cVecZero n m g')
    (fun _ _ => vecZero m) (cVecZero n m g).1 h1.1 (fun g' _ hg' _ => cVecZero_spec hn g' hg')
  have h2le := h2.2.1.len_le
  refine ⟨h2.1, h1.2.1.trans h2.2.1, by have a1 := h1.2.2.1; have a2 := h2.2.2.1; omega,
    ⟨h1.2.2.2.1.mono (by omega), h2.2.2.2.1⟩, fun x hx => ?_⟩
  unfold evalPivot PivotTable.empty
  congr 1
  · exact funext fun j => by rw [val_of_extends hx h2.2.1 (h1.2.2.2.1 j)]; exact congrFun (h1.2.2.2.2 x hx) j
  · exact funext fun j => h2.2.2.2.2 x hx j

private def cAugEmpty (n m : ℕ) (g : List Gate) : List Gate × AugW m :=
  let r1 := cPivotEmpty n m g
  let r2 := cVecZero n m r1.1
  let r3 := cFalse n r2.1
  (r3.1, ⟨r1.2, r2.2, r3.2⟩)

private lemma cAugEmpty_spec {n m : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g) :
    let r := cAugEmpty n m g
    GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + (m * m + 2 * m + 1) ∧
    ValidAug (n + r.1.length) r.2 ∧
    ∀ x, x.length = n → evalAug r.1 x r.2 = AugTable.empty m := by
  dsimp only [cAugEmpty]
  have h1 := cPivotEmpty_spec hn (m := m) g hg
  have h2 := cVecZero_spec hn (m := m) _ h1.1
  have h3 := cFalse_spec hn _ h2.1
  have h2le := h2.2.1.len_le
  have h3le := h3.2.1.len_le
  refine ⟨h3.1, (h1.2.1.trans h2.2.1).trans h3.2.1,
    by have a1 := h1.2.2.1; have a2 := h2.2.2.1; have a3 := h3.2.2.1; omega,
    ⟨h1.2.2.2.1.mono (by omega), h2.2.2.2.1.mono (by omega), h3.2.2.2.1⟩, fun x hx => ?_⟩
  unfold evalAug AugTable.empty
  congr 1
  · rw [evalPivot_of_extends hx (h2.2.1.trans h3.2.1) h1.2.2.2.1, h1.2.2.2.2 x hx]
  · exact funext fun j => by rw [val_of_extends hx h3.2.1 (h2.2.2.2.1 j)]; exact congrFun (h2.2.2.2.2 x hx) j
  · exact h3.2.2.2.2 x hx

private def cPivotMux (n m : ℕ) (g : List Gate) (sel : ℕ) (T1 T2 : PivotW m) : List Gate × PivotW m :=
  let r1 := cVecMux n m g sel T1.hasPiv T2.hasPiv
  let r2 := cBuildFin m (fun g' j => cVecMux n m g' sel (T1.row j) (T2.row j)) r1.1
  (r2.1, ⟨r1.2, r2.2⟩)

private lemma cPivotMux_spec {n m : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (sel : ℕ) (T1 T2 : PivotW m) (hs : sel < n + g.length)
    (hT1 : ValidPivot (n + g.length) T1) (hT2 : ValidPivot (n + g.length) T2) :
    let r := cPivotMux n m g sel T1 T2
    GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + (4 * m * m + 4 * m) ∧
    ValidPivot (n + r.1.length) r.2 ∧
    ∀ x, x.length = n → evalPivot r.1 x r.2 = if val g x sel then evalPivot g x T1 else evalPivot g x T2 := by
  dsimp only [cPivotMux]
  have h1 := cVecMux_spec hn g hg sel T1.hasPiv T2.hasPiv hs hT1.1 hT2.1
  have h2 := cBuildFin_spec (n := n) ValidVec (fun hL hv => hv.mono hL) evalVec
    (fun hx hext hv => evalVec_of_extends hx hext hv) m (4 * m)
    (fun g' j => cVecMux n m g' sel (T1.row j) (T2.row j))
    (fun x j => if val g x sel then evalVec g x (T1.row j) else evalVec g x (T2.row j))
    (cVecMux n m g sel T1.hasPiv T2.hasPiv).1 h1.1 (fun g' j hg' hext => by
      have hle := (h1.2.1.trans hext).len_le
      have hm := cVecMux_spec hn g' hg' sel (T1.row j) (T2.row j) (by omega)
        ((hT1.2 j).mono (by omega)) ((hT2.2 j).mono (by omega))
      refine ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, fun x hx => ?_⟩
      rw [hm.2.2.2.2 x hx, val_of_extends hx (h1.2.1.trans hext) hs,
        evalVec_of_extends hx (h1.2.1.trans hext) (hT1.2 j),
        evalVec_of_extends hx (h1.2.1.trans hext) (hT2.2 j)])
  have h2le := h2.2.1.len_le
  refine ⟨h2.1, h1.2.1.trans h2.2.1,
    by have a1 := h1.2.2.1; have a2 := h2.2.2.1; have hm : m * (4 * m) = 4 * m * m := by ring
       omega,
    ⟨h1.2.2.2.1.mono (by omega), h2.2.2.2.1⟩, fun x hx => ?_⟩
  cases hsel : val g x sel
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold evalPivot
    congr 1
    · exact funext fun j => by
        rw [val_of_extends hx h2.2.1 (h1.2.2.2.1 j)]
        have := congrFun (h1.2.2.2.2 x hx) j
        simpa [hsel, evalVec] using this
    · exact funext fun j => by simpa [hsel] using h2.2.2.2.2 x hx j
  · simp only [↓reduceIte]
    unfold evalPivot
    congr 1
    · exact funext fun j => by
        rw [val_of_extends hx h2.2.1 (h1.2.2.2.1 j)]
        have := congrFun (h1.2.2.2.2 x hx) j
        simpa [hsel, evalVec] using this
    · exact funext fun j => by simpa [hsel] using h2.2.2.2.2 x hx j

private def cReduceVec (n m : ℕ) (g : List Gate) (T : PivotW m) (v : VecW m) : List Gate × VecW m :=
  cFoldl (fun g' cur j =>
    let r1 := cAnd n g' (T.hasPiv j) (cur j)
    let r2 := cVecXor n m r1.1 cur (T.row j)
    cVecMux n m r2.1 r1.2 r2.2 cur) (List.finRange m) g v

private lemma cReduceVec_spec {n m : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (T : PivotW m) (v : VecW m) (hT : ValidPivot (n + g.length) T) (hv : ValidVec (n + g.length) v) :
    let r := cReduceVec n m g T v
    GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + m * (8 * m + 1) ∧
    ValidVec (n + r.1.length) r.2 ∧
    ∀ x, x.length = n → evalVec r.1 x r.2 = reduceVec (evalPivot g x T) (evalVec g x v) := by
  dsimp only [cReduceVec]
  have hf := cFoldl_spec (n := n) ValidVec evalVec
    (fun g' cur j =>
      let r1 := cAnd n g' (T.hasPiv j) (cur j)
      let r2 := cVecXor n m r1.1 cur (T.row j)
      cVecMux n m r2.1 r1.2 r2.2 cur)
    (fun x cur j => reduceVecStep (evalPivot g x T) cur j)
    (8 * m + 1) (List.finRange m) g v hg hv (fun g' cur j _ hg' hext hcur => by
      dsimp only
      have hle := hext.len_le
      have h1 := cAnd_spec hn g' hg' (T.hasPiv j) (cur j) (by have := hT.1 j; omega) (hcur j)
      set r1 := cAnd n g' (T.hasPiv j) (cur j)
      have h1le := h1.2.1.len_le
      have h2 := cVecXor_spec hn r1.1 h1.1 cur (T.row j) (hcur.mono (by omega)) ((hT.2 j).mono (by omega))
      set r2 := cVecXor n m r1.1 cur (T.row j)
      have h2le := h2.2.1.len_le
      have h3 := cVecMux_spec hn r2.1 h2.1 r1.2 r2.2 cur (by have a1 := h1.2.2.2.1; omega) h2.2.2.2.1 (hcur.mono (by omega))
      refine ⟨h3.1, (h1.2.1.trans h2.2.1).trans h3.2.1,
        by have a1 := h1.2.2.1; have a2 := h2.2.2.1; have a3 := h3.2.2.1; omega, h3.2.2.2.1, fun x hx => ?_⟩
      rw [h3.2.2.2.2 x hx, val_of_extends hx h2.2.1 h1.2.2.2.1, h1.2.2.2.2 x hx,
        val_of_extends hx hext (hT.1 j), h2.2.2.2.2 x hx,
        evalVec_of_extends hx h1.2.1 hcur, evalVec_of_extends hx (hext.trans h1.2.1) (hT.2 j),
        evalVec_of_extends hx (h1.2.1.trans h2.2.1) hcur]
      rfl)
  exact ⟨hf.1, hf.2.1, by simpa using hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩

private def cInsertVec (n m : ℕ) (g : List Gate) (T : PivotW m) (v : VecW m) : List Gate × PivotW m :=
  let rw1 := cReduceVec n m g T v
  let rft := cFirstTrue n m rw1.1 rw1.2
  let rhp := cBuildFin m (fun g' j => cOr n g' (T.hasPiv j) (rft.2 j)) rft.1
  let rrow := cBuildFin m (fun g' j => cVecMux n m g' (rft.2 j) rw1.2 (T.row j)) rhp.1
  (rrow.1, ⟨rhp.2, rrow.2⟩)

private lemma cInsertVec_spec {n m : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (T : PivotW m) (v : VecW m) (hT : ValidPivot (n + g.length) T) (hv : ValidVec (n + g.length) v) :
    let r := cInsertVec n m g T v
    GoodCircuit n r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + (14 * m * m + 4 * m) ∧
    ValidPivot (n + r.1.length) r.2 ∧
    ∀ x, x.length = n → evalPivot r.1 x r.2 = insertVec (evalPivot g x T) (evalVec g x v) := by
  dsimp only [cInsertVec]
  have h1 := cReduceVec_spec hn g hg T v hT hv
  set rw1 := cReduceVec n m g T v
  have h2 := cFirstTrue_spec hn rw1.1 h1.1 rw1.2 h1.2.2.2.1
  set rft := cFirstTrue n m rw1.1 rw1.2
  have h3 := cBuildFin_spec (n := n) (fun L w => w < L) (fun hL hw => lt_of_lt_of_le hw hL)
    val (fun hx hext hw => val_of_extends hx hext hw) m 1
    (fun g' j => cOr n g' (T.hasPiv j) (rft.2 j))
    (fun x j => (evalPivot g x T).hasPiv j || firstTrue (reduceVec (evalPivot g x T) (evalVec g x v)) j)
    rft.1 h2.1 (fun g' j hg' hext => by
      have hle1 := ((h1.2.1.trans h2.2.1).trans hext).len_le
      have hle2 := hext.len_le
      have ho := cOr_spec hn g' hg' (T.hasPiv j) (rft.2 j) (by have aT := hT.1 j; omega) (by have aft := h2.2.2.2.1 j; omega)
      refine ⟨ho.1, ho.2.1, ho.2.2.1, ho.2.2.2.1, fun x hx => ?_⟩
      rw [ho.2.2.2.2 x hx, val_of_extends hx ((h1.2.1.trans h2.2.1).trans hext) (hT.1 j),
        val_of_extends hx hext (h2.2.2.2.1 j)]
      have hft := congrFun (h2.2.2.2.2 x hx) j
      rw [h1.2.2.2.2 x hx] at hft
      exact congrArg (val g x (T.hasPiv j) || ·) hft)
  set rhp := cBuildFin m (fun g' j => cOr n g' (T.hasPiv j) (rft.2 j)) rft.1
  have h4 := cBuildFin_spec (n := n) ValidVec (fun hL hv => hv.mono hL) evalVec
    (fun hx hext hv => evalVec_of_extends hx hext hv) m (4 * m)
    (fun g' j => cVecMux n m g' (rft.2 j) rw1.2 (T.row j))
    (fun x j => if firstTrue (reduceVec (evalPivot g x T) (evalVec g x v)) j
      then reduceVec (evalPivot g x T) (evalVec g x v) else (evalPivot g x T).row j)
    rhp.1 h3.1 (fun g' j hg' hext => by
      have hle0 := (((h1.2.1.trans h2.2.1).trans h3.2.1).trans hext).len_le
      have hle1 := ((h2.2.1.trans h3.2.1).trans hext).len_le
      have hle2 := (h3.2.1.trans hext).len_le
      have hm := cVecMux_spec hn g' hg' (rft.2 j) rw1.2 (T.row j) (by have aft := h2.2.2.2.1 j; omega)
        (h1.2.2.2.1.mono (by omega)) ((hT.2 j).mono (by omega))
      refine ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, fun x hx => ?_⟩
      rw [hm.2.2.2.2 x hx, val_of_extends hx (h3.2.1.trans hext) (h2.2.2.2.1 j),
        evalVec_of_extends hx ((h2.2.1.trans h3.2.1).trans hext) h1.2.2.2.1,
        evalVec_of_extends hx (((h1.2.1.trans h2.2.1).trans h3.2.1).trans hext) (hT.2 j)]
      have hft := congrFun (h2.2.2.2.2 x hx) j
      rw [h1.2.2.2.2 x hx] at hft ⊢
      exact congrArg (fun b => if b then reduceVec (evalPivot g x T) (evalVec g x v) else evalVec g x (T.row j)) hft)
  have h4le := h4.2.1.len_le
  refine ⟨h4.1, ((h1.2.1.trans h2.2.1).trans h3.2.1).trans h4.2.1, ?_,
    ⟨fun j => by dsimp only [PivotW.hasPiv]; have a3 := h3.2.2.2.1 j; omega, h4.2.2.2.1⟩, fun x hx => ?_⟩
  · have a1 := h1.2.2.1; have a2 := h2.2.2.1; have a3 := h3.2.2.1; have a4 := h4.2.2.1
    have eq1 : m * (8 * m + 1) + m * (2 * m + 2) + m * 1 + m * (4 * m) = 14 * m * m + 4 * m := by ring
    omega
  unfold evalPivot insertVec
  congr 1
  · exact funext fun j => by rw [val_of_extends hx h4.2.1 (h3.2.2.2.1 j)]; exact h3.2.2.2.2 x hx j
  · exact funext fun j => h4.2.2.2.2 x hx j

private def cAugReduce (n m : ℕ) (g : List Gate) (A : AugW m) (v : VecW m) (r : ℕ) : List Gate × (VecW m × ℕ) :=
  cFoldl (fun g' cur j =>
    let r1 := cAnd n g' (A.piv.hasPiv j) (cur.1 j)
    let r2 := cVecXor n m r1.1 cur.1 (A.piv.row j)
    let r3 := cVecMux n m r2.1 r1.2 r2.2 cur.1
    let r4 := cXor n r3.1 cur.2 (A.rhs j)
    let r5 := cMux n r4.1 r1.2 r4.2 cur.2
    (r5.1, (r3.2, r5.2))) (List.finRange m) g (v, r)

private lemma cAugReduce_spec {n m : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (A : AugW m) (v : VecW m) (r : ℕ)
    (hA : ValidAug (n + g.length) A) (hv : ValidVec (n + g.length) v) (hr : r < n + g.length) :
    let res := cAugReduce n m g A v r
    GoodCircuit n res.1 ∧ Extends g res.1 ∧ res.1.length ≤ g.length + m * (8 * m + 9) ∧
    (ValidVec (n + res.1.length) res.2.1 ∧ res.2.2 < n + res.1.length) ∧
    ∀ x, x.length = n → (evalVec res.1 x res.2.1, val res.1 x res.2.2) =
      augReduce (evalAug g x A) (evalVec g x v) (val g x r) := by
  dsimp only [cAugReduce]
  have hf := cFoldl_spec (n := n)
    (fun L (p : VecW m × ℕ) => ValidVec L p.1 ∧ p.2 < L)
    (fun g' x (p : VecW m × ℕ) => (evalVec g' x p.1, val g' x p.2))
    (fun g' cur j =>
      let r1 := cAnd n g' (A.piv.hasPiv j) (cur.1 j)
      let r2 := cVecXor n m r1.1 cur.1 (A.piv.row j)
      let r3 := cVecMux n m r2.1 r1.2 r2.2 cur.1
      let r4 := cXor n r3.1 cur.2 (A.rhs j)
      let r5 := cMux n r4.1 r1.2 r4.2 cur.2
      (r5.1, (r3.2, r5.2)))
    (fun x cur j => augReduceStep (evalAug g x A) cur j)
    (8 * m + 9) (List.finRange m) g (v, r) hg ⟨hv, hr⟩ (fun g' cur j _ hg' hext hcur => by
      dsimp only
      have hle := hext.len_le
      have h1 := cAnd_spec hn g' hg' (A.piv.hasPiv j) (cur.1 j) (by have := hA.1.1 j; omega) (hcur.1 j)
      set r1 := cAnd n g' (A.piv.hasPiv j) (cur.1 j)
      have h1le := h1.2.1.len_le
      have h2 := cVecXor_spec hn r1.1 h1.1 cur.1 (A.piv.row j) (hcur.1.mono (by omega)) ((hA.1.2 j).mono (by omega))
      set r2 := cVecXor n m r1.1 cur.1 (A.piv.row j)
      have h2le := h2.2.1.len_le
      have h3 := cVecMux_spec hn r2.1 h2.1 r1.2 r2.2 cur.1 (by have a1 := h1.2.2.2.1; omega) h2.2.2.2.1 (hcur.1.mono (by omega))
      set r3 := cVecMux n m r2.1 r1.2 r2.2 cur.1
      have h3le := h3.2.1.len_le
      have h4 := cXor_spec hn r3.1 h3.1 cur.2 (A.rhs j) (by have ac := hcur.2; omega) (by have ar := hA.2.1 j; omega)
      set r4 := cXor n r3.1 cur.2 (A.rhs j)
      have h4le := h4.2.1.len_le
      have h5 := cMux_spec hn r4.1 h4.1 r1.2 r4.2 cur.2 (by have a1 := h1.2.2.2.1; omega) h4.2.2.2.1 (by have ac := hcur.2; omega)
      set r5 := cMux n r4.1 r1.2 r4.2 cur.2
      have h5le := h5.2.1.len_le
      refine ⟨h5.1, (((h1.2.1.trans h2.2.1).trans h3.2.1).trans h4.2.1).trans h5.2.1,
        by have a1 := h1.2.2.1; have a2 := h2.2.2.1; have a3 := h3.2.2.1; have a4 := h4.2.2.1; have a5 := h5.2.2.1; omega,
        ⟨h3.2.2.2.1.mono (by omega), h5.2.2.2.1⟩, fun x hx => ?_⟩
      have hv3 : evalVec r5.1 x r3.2 =
          if val g x (A.piv.hasPiv j) && val g' x (cur.1 j)
          then vecXor (evalVec g' x cur.1) (evalVec g x (A.piv.row j)) else evalVec g' x cur.1 := by
        rw [evalVec_of_extends hx (h4.2.1.trans h5.2.1) h3.2.2.2.1, h3.2.2.2.2 x hx,
          val_of_extends hx h2.2.1 h1.2.2.2.1, h1.2.2.2.2 x hx, val_of_extends hx hext (hA.1.1 j),
          h2.2.2.2.2 x hx, evalVec_of_extends hx h1.2.1 hcur.1,
          evalVec_of_extends hx (hext.trans h1.2.1) (hA.1.2 j),
          evalVec_of_extends hx (h1.2.1.trans h2.2.1) hcur.1]
      have hv5 : val r5.1 x r5.2 =
          if val g x (A.piv.hasPiv j) && val g' x (cur.1 j)
          then xor (val g' x cur.2) (val g x (A.rhs j)) else val g' x cur.2 := by
        rw [h5.2.2.2.2 x hx, val_of_extends hx ((h2.2.1.trans h3.2.1).trans h4.2.1) h1.2.2.2.1,
          h1.2.2.2.2 x hx, val_of_extends hx hext (hA.1.1 j),
          h4.2.2.2.2 x hx, val_of_extends hx ((h1.2.1.trans h2.2.1).trans h3.2.1) hcur.2,
          val_of_extends hx (hext.trans ((h1.2.1.trans h2.2.1).trans h3.2.1)) (hA.2.1 j),
          val_of_extends hx (((h1.2.1.trans h2.2.1).trans h3.2.1).trans h4.2.1) hcur.2]
      rw [hv3, hv5]
      unfold augReduceStep evalAug evalPivot evalVec
      cases val g x (A.piv.hasPiv j) && val g' x (cur.1 j) <;> rfl)
  exact ⟨hf.1, hf.2.1, by simpa using hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩

private def cAugInsert (n m : ℕ) (g : List Gate) (A : AugW m) (v : VecW m) (r : ℕ) : List Gate × AugW m :=
  let rwr := cAugReduce n m g A v r
  let rft := cFirstTrue n m rwr.1 rwr.2.1
  let riz := cVecIsZero n m rft.1 rwr.2.1
  let rhp := cBuildFin m (fun g' j => cOr n g' (A.piv.hasPiv j) (rft.2 j)) riz.1
  let rrow := cBuildFin m (fun g' j => cVecMux n m g' (rft.2 j) rwr.2.1 (A.piv.row j)) rhp.1
  let rrhs := cBuildFin m (fun g' j => cMux n g' (rft.2 j) rwr.2.2 (A.rhs j)) rrow.1
  let rand := cAnd n rrhs.1 riz.2 rwr.2.2
  let rinc := cOr n rand.1 A.inc rand.2
  (rinc.1, ⟨⟨rhp.2, rrow.2⟩, rrhs.2, rinc.2⟩)

private lemma cAugInsert_spec {n m : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (A : AugW m) (v : VecW m) (r : ℕ)
    (hA : ValidAug (n + g.length) A) (hv : ValidVec (n + g.length) v) (hr : r < n + g.length) :
    let res := cAugInsert n m g A v r
    GoodCircuit n res.1 ∧ Extends g res.1 ∧ res.1.length ≤ g.length + (14 * m * m + 18 * m + 3) ∧
    ValidAug (n + res.1.length) res.2 ∧
    ∀ x, x.length = n → evalAug res.1 x res.2 = augInsert (evalAug g x A) (evalVec g x v) (val g x r) := by
  dsimp only [cAugInsert]
  have h1 := cAugReduce_spec hn g hg A v r hA hv hr
  set rwr := cAugReduce n m g A v r
  have h2 := cFirstTrue_spec hn rwr.1 h1.1 rwr.2.1 h1.2.2.2.1.1
  set rft := cFirstTrue n m rwr.1 rwr.2.1
  have h2le := h2.2.1.len_le
  have h3 := cVecIsZero_spec hn rft.1 h2.1 rwr.2.1 (h1.2.2.2.1.1.mono (by omega))
  set riz := cVecIsZero n m rft.1 rwr.2.1
  have e01 := h1.2.1
  have e02 := e01.trans h2.2.1
  have e03 := e02.trans h3.2.1
  have h4 := cBuildFin_spec (n := n) (fun L w => w < L) (fun hL hw => lt_of_lt_of_le hw hL)
    val (fun hx hext hw => val_of_extends hx hext hw) m 1
    (fun g' j => cOr n g' (A.piv.hasPiv j) (rft.2 j))
    (fun x j => (evalAug g x A).piv.hasPiv j || firstTrue (augReduce (evalAug g x A) (evalVec g x v) (val g x r)).1 j)
    riz.1 h3.1 (fun g' j hg' hext => by
      have hle0 := (e03.trans hext).len_le
      have hle2 := (h3.2.1.trans hext).len_le
      have ho := cOr_spec hn g' hg' (A.piv.hasPiv j) (rft.2 j) (by have aA := hA.1.1 j; omega) (by have aft := h2.2.2.2.1 j; omega)
      refine ⟨ho.1, ho.2.1, ho.2.2.1, ho.2.2.2.1, fun x hx => ?_⟩
      rw [ho.2.2.2.2 x hx, val_of_extends hx (e03.trans hext) (hA.1.1 j),
        val_of_extends hx (h3.2.1.trans hext) (h2.2.2.2.1 j)]
      have hft := congrFun (h2.2.2.2.2 x hx) j
      have hwr := congrArg Prod.fst (h1.2.2.2.2 x hx)
      dsimp only at hwr
      rw [hwr] at hft
      exact congrArg (val g x (A.piv.hasPiv j) || ·) hft)
  set rhp := cBuildFin m (fun g' j => cOr n g' (A.piv.hasPiv j) (rft.2 j)) riz.1
  have e04 := e03.trans h4.2.1
  have h5 := cBuildFin_spec (n := n) ValidVec (fun hL hv => hv.mono hL) evalVec
    (fun hx hext hv => evalVec_of_extends hx hext hv) m (4 * m)
    (fun g' j => cVecMux n m g' (rft.2 j) rwr.2.1 (A.piv.row j))
    (fun x j => if firstTrue (augReduce (evalAug g x A) (evalVec g x v) (val g x r)).1 j
      then (augReduce (evalAug g x A) (evalVec g x v) (val g x r)).1 else (evalAug g x A).piv.row j)
    rhp.1 h4.1 (fun g' j hg' hext => by
      have hle0 := (e04.trans hext).len_le
      have hle1 := (((h2.2.1.trans h3.2.1).trans h4.2.1).trans hext).len_le
      have hle2 := ((h3.2.1.trans h4.2.1).trans hext).len_le
      have hm := cVecMux_spec hn g' hg' (rft.2 j) rwr.2.1 (A.piv.row j) (by have aft := h2.2.2.2.1 j; omega)
        (h1.2.2.2.1.1.mono (by omega)) ((hA.1.2 j).mono (by omega))
      refine ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, fun x hx => ?_⟩
      rw [hm.2.2.2.2 x hx, val_of_extends hx ((h3.2.1.trans h4.2.1).trans hext) (h2.2.2.2.1 j),
        evalVec_of_extends hx (((h2.2.1.trans h3.2.1).trans h4.2.1).trans hext) h1.2.2.2.1.1,
        evalVec_of_extends hx (e04.trans hext) (hA.1.2 j)]
      have hft := congrFun (h2.2.2.2.2 x hx) j
      have hwr := congrArg Prod.fst (h1.2.2.2.2 x hx)
      dsimp only at hwr
      rw [hwr] at hft ⊢
      exact congrArg (fun b => if b then (augReduce (evalAug g x A) (evalVec g x v) (val g x r)).1 else evalVec g x (A.piv.row j)) hft)
  set rrow := cBuildFin m (fun g' j => cVecMux n m g' (rft.2 j) rwr.2.1 (A.piv.row j)) rhp.1
  have e05 := e04.trans h5.2.1
  have h6 := cBuildFin_spec (n := n) (fun L w => w < L) (fun hL hw => lt_of_lt_of_le hw hL)
    val (fun hx hext hw => val_of_extends hx hext hw) m 4
    (fun g' j => cMux n g' (rft.2 j) rwr.2.2 (A.rhs j))
    (fun x j => if firstTrue (augReduce (evalAug g x A) (evalVec g x v) (val g x r)).1 j
      then (augReduce (evalAug g x A) (evalVec g x v) (val g x r)).2 else (evalAug g x A).rhs j)
    rrow.1 h5.1 (fun g' j hg' hext => by
      have hle0 := (e05.trans hext).len_le
      have hle1 := ((((h2.2.1.trans h3.2.1).trans h4.2.1).trans h5.2.1).trans hext).len_le
      have hle2 := (((h3.2.1.trans h4.2.1).trans h5.2.1).trans hext).len_le
      have hm := cMux_spec hn g' hg' (rft.2 j) rwr.2.2 (A.rhs j) (by have aft := h2.2.2.2.1 j; omega)
        (by have awr := h1.2.2.2.1.2; omega) (by have aA := hA.2.1 j; omega)
      refine ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, fun x hx => ?_⟩
      rw [hm.2.2.2.2 x hx, val_of_extends hx (((h3.2.1.trans h4.2.1).trans h5.2.1).trans hext) (h2.2.2.2.1 j),
        val_of_extends hx ((((h2.2.1.trans h3.2.1).trans h4.2.1).trans h5.2.1).trans hext) h1.2.2.2.1.2,
        val_of_extends hx (e05.trans hext) (hA.2.1 j)]
      have hft := congrFun (h2.2.2.2.2 x hx) j
      have hwr1 := congrArg Prod.fst (h1.2.2.2.2 x hx)
      have hwr2 := congrArg Prod.snd (h1.2.2.2.2 x hx)
      dsimp only at hwr1 hwr2
      rw [hwr1] at hft; rw [hwr2]
      exact congrArg (fun b => if b then (augReduce (evalAug g x A) (evalVec g x v) (val g x r)).2 else val g x (A.rhs j)) hft)
  set rrhs := cBuildFin m (fun g' j => cMux n g' (rft.2 j) rwr.2.2 (A.rhs j)) rrow.1
  have e06 := e05.trans h6.2.1
  have e16 := (((h2.2.1.trans h3.2.1).trans h4.2.1).trans h5.2.1).trans h6.2.1
  have e36 := (h4.2.1.trans h5.2.1).trans h6.2.1
  have h7 := cAnd_spec hn rrhs.1 h6.1 riz.2 rwr.2.2 (by have a36 := e36.len_le; have a3 := h3.2.2.2.1; omega)
    (by have a16 := e16.len_le; have a1 := h1.2.2.2.1.2; omega)
  set rand := cAnd n rrhs.1 riz.2 rwr.2.2
  have h8 := cOr_spec hn rand.1 h7.1 A.inc rand.2 (by have a07 := (e06.trans h7.2.1).len_le; have aA := hA.2.2; omega) h7.2.2.2.1
  have hlen : (cOr n rand.1 A.inc rand.2).1.length ≤ g.length + (14 * m * m + 18 * m + 3) := by
    have a1 := h1.2.2.1; have a2 := h2.2.2.1; have a3 := h3.2.2.1
    have a4 := h4.2.2.1; have a5 := h5.2.2.1; have a6 := h6.2.2.1
    have a7 := h7.2.2.1; have a8 := h8.2.2.1
    have eq1 : m * (8 * m + 9) + m * (2 * m + 2) + (2 * m + 1) + m * 1 + m * (4 * m) + m * 4 + 1 + 1 =
        14 * m * m + 18 * m + 3 := by ring
    omega
  have e48 := ((h5.2.1.trans h6.2.1).trans h7.2.1).trans h8.2.1
  have e58 := (h6.2.1.trans h7.2.1).trans h8.2.1
  have e68 := h7.2.1.trans h8.2.1
  refine ⟨h8.1, e06.trans e68, hlen,
    ⟨⟨fun j => by dsimp only [AugW.piv, PivotW.hasPiv]; have a48 := e48.len_le; have a4 := h4.2.2.2.1 j; omega,
      fun j => (h5.2.2.2.1 j).mono (by have a58 := e58.len_le; omega)⟩,
     fun j => by dsimp only [AugW.rhs]; have a68 := e68.len_le; have a6 := h6.2.2.2.1 j; omega, h8.2.2.2.1⟩, fun x hx => ?_⟩
  unfold evalAug evalPivot augInsert
  congr 1
  · congr 1
    · exact funext fun j => by rw [val_of_extends hx e48 (h4.2.2.2.1 j)]; exact h4.2.2.2.2 x hx j
    · exact funext fun j => by rw [evalVec_of_extends hx e58 (h5.2.2.2.1 j)]; exact h5.2.2.2.2 x hx j
  · exact funext fun j => by rw [val_of_extends hx e68 (h6.2.2.2.1 j)]; exact h6.2.2.2.2 x hx j
  · rw [h8.2.2.2.2 x hx, val_of_extends hx (e06.trans h7.2.1) hA.2.2,
      h7.2.2.2.2 x hx, val_of_extends hx e36 h3.2.2.2.1, h3.2.2.2.2 x hx,
      evalVec_of_extends hx h2.2.1 h1.2.2.2.1.1,
      val_of_extends hx e16 h1.2.2.2.1.2]
    have hwr1 := congrArg Prod.fst (h1.2.2.2.2 x hx)
    have hwr2 := congrArg Prod.snd (h1.2.2.2.2 x hx)
    dsimp only at hwr1 hwr2
    rw [hwr1, hwr2]
    rfl

private lemma foldr_eq_foldl_reverse {α β : Type} (f : α → β → β) (init : β) (L : List α) :
    L.foldr f init = L.reverse.foldl (fun acc a => f a acc) init := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.foldr_cons, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]

private def cBackSubWith (n m : ℕ) (g : List Gate) (A : AugW m) (free : VecW m) : List Gate × VecW m :=
  let r0 := cVecZero n m g
  cFoldl (fun g' cur j =>
    let rt0 := cFalse n g'
    let rtd := cFoldl (fun g'' acc l =>
      if j.1 < l.1 then
        let r1 := cAnd n g'' (A.piv.row j l) (cur l)
        cXor n r1.1 acc r1.2
      else (g'', acc)) (List.finRange m) rt0.1 rt0.2
    let rx := cXor n rtd.1 (A.rhs j) rtd.2
    let rv := cMux n rx.1 (A.piv.hasPiv j) rx.2 (free j)
    (rv.1, fun i => if i = j then rv.2 else cur i)) (List.finRange m).reverse r0.1 r0.2

private lemma cBackSubWith_spec {n m : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (A : AugW m) (free : VecW m)
    (hA : ValidAug (n + g.length) A) (hfree : ValidVec (n + g.length) free) :
    let res := cBackSubWith n m g A free
    GoodCircuit n res.1 ∧ Extends g res.1 ∧ res.1.length ≤ g.length + (m * (5 * m + 9) + m) ∧
    ValidVec (n + res.1.length) res.2 ∧
    ∀ x, x.length = n → evalVec res.1 x res.2 = backSubWith (evalAug g x A) (evalVec g x free) := by
  dsimp only [cBackSubWith]
  have h0 := cVecZero_spec hn (m := m) g hg
  have hf := cFoldl_spec (n := n) ValidVec evalVec
    (fun g' cur j =>
      let rt0 := cFalse n g'
      let rtd := cFoldl (fun g'' acc l =>
        if j.1 < l.1 then let r1 := cAnd n g'' (A.piv.row j l) (cur l); cXor n r1.1 acc r1.2 else (g'', acc))
        (List.finRange m) rt0.1 rt0.2
      let rx := cXor n rtd.1 (A.rhs j) rtd.2
      let rv := cMux n rx.1 (A.piv.hasPiv j) rx.2 (free j)
      (rv.1, fun i => if i = j then rv.2 else cur i))
    (fun x cur j => backSubStep (evalAug g x A) (evalVec g x free) j cur)
    (5 * m + 9) (List.finRange m).reverse (cVecZero n m g).1 (cVecZero n m g).2 h0.1 h0.2.2.2.1
    (fun g' cur j _ hg' hext hcur => by
      dsimp only
      have ht0 := cFalse_spec hn g' hg'
      have htd := cFoldl_spec (n := n) (fun L w => w < L) val
        (fun g'' acc l =>
          if j.1 < l.1 then let r1 := cAnd n g'' (A.piv.row j l) (cur l); cXor n r1.1 acc r1.2 else (g'', acc))
        (fun x acc l => if decide (j.1 < l.1) && (evalAug g x A).piv.row j l && evalVec g' x cur l then !acc else acc)
        5 (List.finRange m) (cFalse n g').1 (cFalse n g').2 ht0.1 ht0.2.2.2.1 (fun g'' acc l _ hg'' hext' hacc => by
          by_cases hjl : j.1 < l.1
          · simp only [hjl, ↓reduceIte]
            have hle0 := ((h0.2.1.trans hext).trans (ht0.2.1.trans hext')).len_le
            have hle1 := (ht0.2.1.trans hext').len_le
            have h1 := cAnd_spec hn g'' hg'' (A.piv.row j l) (cur l)
              (by have := hA.1.2 j l; omega) (by have := hcur l; omega)
            have h1le := h1.2.1.len_le
            have h2 := cXor_spec hn (cAnd n g'' (A.piv.row j l) (cur l)).1 h1.1 acc (cAnd n g'' (A.piv.row j l) (cur l)).2 (by omega) h1.2.2.2.1
            refine ⟨h2.1, h1.2.1.trans h2.2.1, by have a1 := h1.2.2.1; have a2 := h2.2.2.1; omega, h2.2.2.2.1, fun x hx => ?_⟩
            rw [h2.2.2.2.2 x hx, val_of_extends hx h1.2.1 hacc, h1.2.2.2.2 x hx,
              val_of_extends hx ((h0.2.1.trans hext).trans (ht0.2.1.trans hext')) (hA.1.2 j l),
              val_of_extends hx (ht0.2.1.trans hext') (hcur l)]
            simp only [decide_true, Bool.true_and, evalAug, evalPivot, evalVec]
            cases val g'' x acc <;> cases val g x (A.piv.row j l) <;> cases val g' x (cur l) <;> rfl
          · simp only [hjl, ↓reduceIte]
            refine ⟨hg'', Extends.refl g'', by omega, hacc, fun x _ => by simp⟩)
      set rtd := cFoldl (fun g'' acc l =>
        if j.1 < l.1 then let r1 := cAnd n g'' (A.piv.row j l) (cur l); cXor n r1.1 acc r1.2 else (g'', acc))
        (List.finRange m) (cFalse n g').1 (cFalse n g').2
      have e0td := (h0.2.1.trans hext).trans (ht0.2.1.trans htd.2.1)
      have hrx := cXor_spec hn rtd.1 htd.1 (A.rhs j) rtd.2 (by have ae := e0td.len_le; have aA := hA.2.1 j; omega) htd.2.2.2.1
      set rx := cXor n rtd.1 (A.rhs j) rtd.2
      have hrv := cMux_spec hn rx.1 hrx.1 (A.piv.hasPiv j) rx.2 (free j)
        (by have ae := (e0td.trans hrx.2.1).len_le; have aA := hA.1.1 j; omega)
        hrx.2.2.2.1 (by have ae := (e0td.trans hrx.2.1).len_le; have af := hfree j; omega)
      have e_step := ((ht0.2.1.trans htd.2.1).trans hrx.2.1).trans hrv.2.1
      refine ⟨hrv.1, e_step, ?_, fun i => ?_, fun x hx => funext fun i => ?_⟩
      · have a1 := ht0.2.2.1; have a2 := htd.2.2.1; have a3 := hrx.2.2.1; have a4 := hrv.2.2.1
        simp only [List.length_finRange] at a2; omega
      · by_cases hij : i = j
        · simp only [hij, ↓reduceIte]; exact hrv.2.2.2.1
        · simp only [hij, ↓reduceIte]; have ae := e_step.len_le; have ac := hcur i; omega
      · by_cases hij : i = j
        · subst hij
          simp only [evalVec, ↓reduceIte, backSubStep]
          rw [hrv.2.2.2.2 x hx, val_of_extends hx (e0td.trans hrx.2.1) (hA.1.1 i),
            hrx.2.2.2.2 x hx, val_of_extends hx e0td (hA.2.1 i),
            htd.2.2.2.2 x hx, ht0.2.2.2.2 x hx,
            val_of_extends hx (e0td.trans hrx.2.1) (hfree i)]
          rfl
        · simp only [evalVec, hij, ↓reduceIte, backSubStep]
          exact val_of_extends hx e_step (hcur i))
  refine ⟨hf.1, h0.2.1.trans hf.2.1,
    by have a0 := h0.2.2.1; have af := hf.2.2.1; simp only [List.length_reverse, List.length_finRange] at af; omega,
    hf.2.2.2.1, fun x hx => ?_⟩
  rw [hf.2.2.2.2 x hx, h0.2.2.2.2 x hx]
  unfold backSubWith
  exact (foldr_eq_foldl_reverse _ _ _).symm

private def cBackSub (n m : ℕ) (g : List Gate) (A : AugW m) : List Gate × VecW m :=
  let r0 := cVecZero n m g
  cBackSubWith n m r0.1 A r0.2

private lemma cBackSub_spec {n m : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (A : AugW m) (hA : ValidAug (n + g.length) A) :
    let res := cBackSub n m g A
    GoodCircuit n res.1 ∧ Extends g res.1 ∧ res.1.length ≤ g.length + (m * (5 * m + 9) + 2 * m) ∧
    ValidVec (n + res.1.length) res.2 ∧
    ∀ x, x.length = n → evalVec res.1 x res.2 = backSub (evalAug g x A) := by
  dsimp only [cBackSub]
  have h0 := cVecZero_spec hn (m := m) g hg
  have h1 := cBackSubWith_spec hn (cVecZero n m g).1 h0.1 A (cVecZero n m g).2 (hA.mono (by have := h0.2.1.len_le; omega)) h0.2.2.2.1
  refine ⟨h1.1, h0.2.1.trans h1.2.1, by have a0 := h0.2.2.1; have a1 := h1.2.2.1; omega, h1.2.2.2.1, fun x hx => ?_⟩
  rw [h1.2.2.2.2 x hx, evalAug_of_extends hx h0.2.1 hA, h0.2.2.2.2 x hx]
  rfl

-- One-hot counter circuit
private def cOneHotStep (n len : ℕ) (g : List Gate) (oh : VecW (len + 1)) (flag : ℕ) : List Gate × VecW (len + 1) :=
  cBuildFin (len + 1) (fun g'' r =>
    if h : 0 < r.1 then cMux n g'' flag (oh ⟨r.1 - 1, by omega⟩) (oh r)
    else cMux n (cFalse n g'').1 flag (cFalse n g'').2 (oh r)) g

private def cOneHotCount (n len : ℕ) (g : List Gate) (f : VecW len) : List Gate × (Fin (len + 1) → ℕ) :=
  let r0 := cBuildFin (len + 1) (fun g' r => if r.1 = 0 then cTrue n g' else cFalse n g') g
  cFoldl (fun g' oh j => cOneHotStep n len g' oh (f j)) (List.finRange len) r0.1 r0.2

private lemma cOneHotCount_spec {n len : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (f : VecW len) (hfv : ValidVec (n + g.length) f) :
    let res := cOneHotCount n len g f
    GoodCircuit n res.1 ∧ Extends g res.1 ∧ res.1.length ≤ g.length + ((len + 1) + len * ((len + 1) * 5)) ∧
    ValidVec (n + res.1.length) res.2 ∧
    ∀ x, x.length = n → evalVec res.1 x res.2 = oneHotCount (evalVec g x f) := by
  dsimp only [cOneHotCount]
  have h0 := cBuildFin_spec (n := n) (fun L w => w < L) (fun hL hw => lt_of_lt_of_le hw hL)
    val (fun hx hext hw => val_of_extends hx hext hw) (len + 1) 1
    (fun g' r => if r.1 = 0 then cTrue n g' else cFalse n g') (fun _ r => decide (r.1 = 0)) g hg
    (fun g' r hg' _ => by
      by_cases hr : r.1 = 0
      · simp only [hr, ↓reduceIte, decide_true]; exact cTrue_spec hn g' hg'
      · simp only [hr, ↓reduceIte, decide_false]; exact cFalse_spec hn g' hg')
  set r0 := cBuildFin (len + 1) (fun g' r => if r.1 = 0 then cTrue n g' else cFalse n g') g
  have hf := cFoldl_spec (n := n) ValidVec evalVec
    (fun g' oh j => cOneHotStep n len g' oh (f j))
    (fun x oh j => oneHotStep oh (val g x (f j)))
    ((len + 1) * 5) (List.finRange len) r0.1 r0.2 h0.1 h0.2.2.2.1 (fun g' oh j _ hg' hext hoh => by
      dsimp only [cOneHotStep]
      have hb := cBuildFin_spec (n := n) (fun L w => w < L) (fun hL hw => lt_of_lt_of_le hw hL)
        val (fun hx hext' hw => val_of_extends hx hext' hw) (len + 1) 5
        (fun g'' r =>
          if h : 0 < r.1 then cMux n g'' (f j) (oh ⟨r.1 - 1, by omega⟩) (oh r)
          else cMux n (cFalse n g'').1 (f j) (cFalse n g'').2 (oh r))
        (fun x r => oneHotStep (evalVec g' x oh) (val g x (f j)) r)
        g' hg' (fun g'' r hg'' hext'' => by
          have hle0 := ((h0.2.1.trans hext).trans hext'').len_le
          have hle1 := hext''.len_le
          by_cases hr : 0 < r.1
          · simp only [hr, ↓reduceDIte]
            have hm := cMux_spec hn g'' hg'' (f j) (oh ⟨r.1 - 1, by omega⟩) (oh r)
              (by have := hfv j; omega) (by have := hoh ⟨r.1 - 1, by omega⟩; omega) (by have := hoh r; omega)
            refine ⟨hm.1, hm.2.1, by have am := hm.2.2.1; omega, hm.2.2.2.1, fun x hx => ?_⟩
            rw [hm.2.2.2.2 x hx, val_of_extends hx ((h0.2.1.trans hext).trans hext'') (hfv j),
              val_of_extends hx hext'' (hoh ⟨r.1 - 1, by omega⟩), val_of_extends hx hext'' (hoh r)]
            simp [oneHotStep, hr, evalVec]
          · simp only [hr, ↓reduceDIte]
            have hfl := cFalse_spec hn g'' hg''
            have hflle := hfl.2.1.len_le
            have hm := cMux_spec hn (cFalse n g'').1 hfl.1 (f j) (cFalse n g'').2 (oh r)
              (by have := hfv j; omega) hfl.2.2.2.1 (by have := hoh r; omega)
            refine ⟨hm.1, hfl.2.1.trans hm.2.1, by have af := hfl.2.2.1; have am := hm.2.2.1; omega, hm.2.2.2.1, fun x hx => ?_⟩
            rw [hm.2.2.2.2 x hx, val_of_extends hx (((h0.2.1.trans hext).trans hext'').trans hfl.2.1) (hfv j),
              hfl.2.2.2.2 x hx, val_of_extends hx (hext''.trans hfl.2.1) (hoh r)]
            simp [oneHotStep, hr, evalVec])
      exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, fun x hx => funext fun r => hb.2.2.2.2 x hx r⟩)
  refine ⟨hf.1, h0.2.1.trans hf.2.1, ?_, hf.2.2.2.1, fun x hx => ?_⟩
  · have a0 : r0.1.length ≤ g.length + (len + 1) := by simpa using h0.2.2.1
    have af : (cFoldl (fun g' oh j => cOneHotStep n len g' oh (f j)) (List.finRange len) r0.1 r0.2).1.length ≤
        r0.1.length + len * ((len + 1) * 5) := by
      simpa [List.length_finRange] using hf.2.2.1
    exact le_trans af (by omega)
  · rw [hf.2.2.2.2 x hx]
    have h0e : evalVec (cBuildFin (len + 1) _ g).1 x (cBuildFin (len + 1) _ g).2 = fun r => decide (r.1 = 0) :=
      funext fun r => h0.2.2.2.2 x hx r
    rw [h0e]
    rfl

-- Ripple-carry adder circuit
private def cAddBitsCarry (n : ℕ) : (w : ℕ) → List Gate → VecW w → VecW w → ℕ → List Gate × (VecW w × ℕ)
  | 0, g, _, _, c => (g, (Fin.elim0, c))
  | w + 1, g, a, b, c =>
    let r1 := cXor n g (a 0) (b 0)
    let r2 := cXor n r1.1 r1.2 c
    let r3 := cAnd n r2.1 (a 0) (b 0)
    let r4 := cAnd n r3.1 c r1.2
    let r5 := cOr n r4.1 r3.2 r4.2
    let rest := cAddBitsCarry n w r5.1 (fun i => a i.succ) (fun i => b i.succ) r5.2
    (rest.1, (Fin.cons (α := fun _ => ℕ) r2.2 rest.2.1, rest.2.2))

private lemma cAddBitsCarry_spec {n : ℕ} (hn : 0 < n) :
    ∀ (w : ℕ) (g : List Gate) (hg : GoodCircuit n g) (a b : VecW w) (c : ℕ),
      ValidVec (n + g.length) a → ValidVec (n + g.length) b → c < n + g.length →
      let res := cAddBitsCarry n w g a b c
      GoodCircuit n res.1 ∧ Extends g res.1 ∧ res.1.length ≤ g.length + 11 * w ∧
      (ValidVec (n + res.1.length) res.2.1 ∧ res.2.2 < n + res.1.length) ∧
      ∀ x, x.length = n →
        (evalVec res.1 x res.2.1, val res.1 x res.2.2) =
          addBitsCarry w (evalVec g x a) (evalVec g x b) (val g x c) := by
  intro w
  induction w with
  | zero =>
    intro g hg a b c _ _ hc
    dsimp only [cAddBitsCarry]
    refine ⟨hg, Extends.refl g, by simp, ⟨fun i => i.elim0, hc⟩, fun x _ => ?_⟩
    exact Prod.ext (funext fun i => i.elim0) rfl
  | succ w ih =>
    intro g hg a b c ha hb hc
    dsimp only [cAddBitsCarry]
    have h1 := cXor_spec hn g hg (a 0) (b 0) (ha 0) (hb 0)
    set r1 := cXor n g (a 0) (b 0)
    have h1le := h1.2.1.len_le
    have h2 := cXor_spec hn r1.1 h1.1 r1.2 c h1.2.2.2.1 (by omega)
    set r2 := cXor n r1.1 r1.2 c
    have h2le := h2.2.1.len_le
    have h3 := cAnd_spec hn r2.1 h2.1 (a 0) (b 0) (by have a0 := ha 0; omega) (by have b0 := hb 0; omega)
    set r3 := cAnd n r2.1 (a 0) (b 0)
    have h3le := h3.2.1.len_le
    have h4 := cAnd_spec hn r3.1 h3.1 c r1.2 (by omega) (by have a1 := h1.2.2.2.1; omega)
    set r4 := cAnd n r3.1 c r1.2
    have h4le := h4.2.1.len_le
    have h5 := cOr_spec hn r4.1 h4.1 r3.2 r4.2 (by have a3 := h3.2.2.2.1; omega) h4.2.2.2.1
    set r5 := cOr n r4.1 r3.2 r4.2
    have e05 := (((h1.2.1.trans h2.2.1).trans h3.2.1).trans h4.2.1).trans h5.2.1
    have h05le := e05.len_le
    have hrest := ih r5.1 h5.1 (fun i => a i.succ) (fun i => b i.succ) r5.2
      (fun i => by dsimp only; have ai := ha i.succ; omega) (fun i => by dsimp only; have bi := hb i.succ; omega) h5.2.2.2.1
    set rest := cAddBitsCarry n w r5.1 (fun i => a i.succ) (fun i => b i.succ) r5.2
    have hrest_le := hrest.2.1.len_le
    have e2rest := ((h3.2.1.trans h4.2.1).trans h5.2.1).trans hrest.2.1
    refine ⟨hrest.1, e05.trans hrest.2.1,
      by have a1 := h1.2.2.1; have a2 := h2.2.2.1; have a3 := h3.2.2.1; have a4 := h4.2.2.1; have a5 := h5.2.2.1; have ar := hrest.2.2.1; omega,
      ⟨fun i => Fin.cases (by simp only [Fin.cons_zero]; have ae := e2rest.len_le; have a2 := h2.2.2.2.1; omega)
        (fun j => hrest.2.2.2.1.1 j) i, hrest.2.2.2.1.2⟩,
      fun x hx => ?_⟩
    have hs0 : val rest.1 x r2.2 =
        xor (xor (val g x (a 0)) (val g x (b 0))) (val g x c) := by
      rw [val_of_extends hx e2rest h2.2.2.2.1, h2.2.2.2.2 x hx, h1.2.2.2.2 x hx, val_of_extends hx h1.2.1 hc]
    have hc1 : val r5.1 x r5.2 =
        ((val g x (a 0) && val g x (b 0)) || (val g x c && xor (val g x (a 0)) (val g x (b 0)))) := by
      rw [h5.2.2.2.2 x hx, val_of_extends hx h4.2.1 h3.2.2.2.1, h3.2.2.2.2 x hx,
        val_of_extends hx (h1.2.1.trans h2.2.1) (ha 0), val_of_extends hx (h1.2.1.trans h2.2.1) (hb 0),
        h4.2.2.2.2 x hx, val_of_extends hx ((h1.2.1.trans h2.2.1).trans h3.2.1) hc,
        val_of_extends hx (h2.2.1.trans h3.2.1) h1.2.2.2.1, h1.2.2.2.2 x hx]
    have hre := hrest.2.2.2.2 x hx
    rw [hc1] at hre
    have hae : evalVec r5.1 x (fun i => a i.succ) = fun i => evalVec g x a i.succ :=
      funext fun i => val_of_extends hx e05 (ha i.succ)
    have hbe : evalVec r5.1 x (fun i => b i.succ) = fun i => evalVec g x b i.succ :=
      funext fun i => val_of_extends hx e05 (hb i.succ)
    rw [hae, hbe] at hre
    apply Prod.ext
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [evalVec, addBitsCarry] using hs0
      · simpa [evalVec, addBitsCarry] using congrFun (congrArg Prod.fst hre) j
    · simpa [evalVec, addBitsCarry] using congrArg Prod.snd hre

private def cAddBits (n w : ℕ) (g : List Gate) (a b : VecW w) : List Gate × VecW w :=
  let r0 := cFalse n g
  let r1 := cAddBitsCarry n w r0.1 a b r0.2
  (r1.1, r1.2.1)

private lemma cAddBits_spec {n w : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (a b : VecW w) (ha : ValidVec (n + g.length) a) (hb : ValidVec (n + g.length) b) :
    let res := cAddBits n w g a b
    GoodCircuit n res.1 ∧ Extends g res.1 ∧ res.1.length ≤ g.length + (11 * w + 1) ∧
    ValidVec (n + res.1.length) res.2 ∧
    ∀ x, x.length = n → evalVec res.1 x res.2 = addBits (evalVec g x a) (evalVec g x b) := by
  dsimp only [cAddBits]
  have h0 := cFalse_spec hn g hg
  have h0le := h0.2.1.len_le
  have h1 := cAddBitsCarry_spec hn w (cFalse n g).1 h0.1 a b (cFalse n g).2 (ha.mono (by omega)) (hb.mono (by omega)) h0.2.2.2.1
  refine ⟨h1.1, h0.2.1.trans h1.2.1, by have a0 := h0.2.2.1; have a1 := h1.2.2.1; omega, h1.2.2.2.1.1, fun x hx => ?_⟩
  have he := congrArg Prod.fst (h1.2.2.2.2 x hx)
  rw [evalVec_of_extends hx h0.2.1 ha, evalVec_of_extends hx h0.2.1 hb, h0.2.2.2.2 x hx] at he
  exact he

-- ============================================================================
-- Section 3C: High-Level Search, Cell Counting, Generator Rank & Shift Circuits
-- ============================================================================

private def cProbeCovered (n m : ℕ) (g : List Gate) (T : PivotW m) (a b : VecW m) : List Gate × ℕ :=
  let r1 := cReduceVec n m g T a
  let r2 := cVecIsZero n m r1.1 r1.2
  let r3 := cReduceVec n m r2.1 T b
  let r4 := cVecIsZero n m r3.1 r3.2
  let r5 := cVecXor n m r4.1 a b
  let r6 := cReduceVec n m r5.1 T r5.2
  let r7 := cVecIsZero n m r6.1 r6.2
  let r8 := cOr n r7.1 r2.2 r4.2
  cOr n r8.1 r8.2 r7.2

private lemma cProbeCovered_spec {n m : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (T : PivotW m) (a b : VecW m)
    (hT : ValidPivot (n + g.length) T) (ha : ValidVec (n + g.length) a) (hb : ValidVec (n + g.length) b) :
    let res := cProbeCovered n m g T a b
    GoodCircuit n res.1 ∧ Extends g res.1 ∧ res.1.length ≤ g.length + (24 * m * m + 13 * m + 5) ∧
    res.2 < n + res.1.length ∧
    ∀ x, x.length = n → val res.1 x res.2 = probeCovered (evalPivot g x T) (evalVec g x a) (evalVec g x b) := by
  dsimp only [cProbeCovered]
  have h1 := cReduceVec_spec hn g hg T a hT ha
  set r1 := cReduceVec n m g T a
  have h2 := cVecIsZero_spec hn r1.1 h1.1 r1.2 h1.2.2.2.1
  set r2 := cVecIsZero n m r1.1 r1.2
  have e02 := h1.2.1.trans h2.2.1
  have h3 := cReduceVec_spec hn r2.1 h2.1 T b (hT.mono (by have := e02.len_le; omega)) (hb.mono (by have := e02.len_le; omega))
  set r3 := cReduceVec n m r2.1 T b
  have h4 := cVecIsZero_spec hn r3.1 h3.1 r3.2 h3.2.2.2.1
  set r4 := cVecIsZero n m r3.1 r3.2
  have e04 := e02.trans (h3.2.1.trans h4.2.1)
  have h5 := cVecXor_spec hn r4.1 h4.1 a b (ha.mono (by have := e04.len_le; omega)) (hb.mono (by have := e04.len_le; omega))
  set r5 := cVecXor n m r4.1 a b
  have e05 := e04.trans h5.2.1
  have h6 := cReduceVec_spec hn r5.1 h5.1 T r5.2 (hT.mono (by have := e05.len_le; omega)) h5.2.2.2.1
  set r6 := cReduceVec n m r5.1 T r5.2
  have h7 := cVecIsZero_spec hn r6.1 h6.1 r6.2 h6.2.2.2.1
  set r7 := cVecIsZero n m r6.1 r6.2
  have e27 := (((h3.2.1.trans h4.2.1).trans h5.2.1).trans h6.2.1).trans h7.2.1
  have e47 := (h5.2.1.trans h6.2.1).trans h7.2.1
  have h8 := cOr_spec hn r7.1 h7.1 r2.2 r4.2 (by have a1 := e27.len_le; have a2 := h2.2.2.2.1; omega)
    (by have a1 := e47.len_le; have a2 := h4.2.2.2.1; omega)
  set r8 := cOr n r7.1 r2.2 r4.2
  have h9 := cOr_spec hn r8.1 h8.1 r8.2 r7.2 h8.2.2.2.1 (by have a1 := h8.2.1.len_le; have a2 := h7.2.2.2.1; omega)
  refine ⟨h9.1, (e05.trans (h6.2.1.trans h7.2.1)).trans (h8.2.1.trans h9.2.1), ?_, h9.2.2.2.1, fun x hx => ?_⟩
  · have a1 := h1.2.2.1; have a2 := h2.2.2.1; have a3 := h3.2.2.1; have a4 := h4.2.2.1
    have a5 := h5.2.2.1; have a6 := h6.2.2.1; have a7 := h7.2.2.1; have a8 := h8.2.2.1; have a9 := h9.2.2.1
    have eq1 : m * (8 * m + 1) + (2 * m + 1) + m * (8 * m + 1) + (2 * m + 1) + 4 * m + m * (8 * m + 1) + (2 * m + 1) + 1 + 1 =
        24 * m * m + 13 * m + 5 := by ring
    omega
  · rw [h9.2.2.2.2 x hx, h8.2.2.2.2 x hx, val_of_extends hx e27 h2.2.2.2.1, val_of_extends hx e47 h4.2.2.2.1,
      val_of_extends hx h8.2.1 h7.2.2.2.1, h2.2.2.2.2 x hx, h1.2.2.2.2 x hx, h4.2.2.2.2 x hx, h3.2.2.2.2 x hx,
      evalPivot_of_extends hx e02 hT, evalVec_of_extends hx e02 hb,
      h7.2.2.2.2 x hx, h6.2.2.2.2 x hx, evalPivot_of_extends hx e05 hT, h5.2.2.2.2 x hx,
      evalVec_of_extends hx e04 ha, evalVec_of_extends hx e04 hb]
    rfl

private def cPickFirstUncovered (n m t : ℕ) (g : List Gate) (cov : VecW t) (a b : Fin t → VecW m) :
    List Gate × (VecW m × VecW m) :=
  let rnc := cBuildFin t (fun g' p => cNot n g' (cov p)) g
  let rft := cFirstTrue n t rnc.1 rnc.2
  let rz1 := cVecZero n m rft.1
  let rz2 := cVecZero n m rz1.1
  cFoldl (fun g' acc p =>
    let ra := cVecMux n m g' (rft.2 p) (a p) acc.1
    let rb := cVecMux n m ra.1 (rft.2 p) (b p) acc.2
    (rb.1, (ra.2, rb.2))) (List.finRange t) rz2.1 (rz1.2, rz2.2)

private lemma cPickFirstUncovered_spec {n m t : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (cov : VecW t) (a b : Fin t → VecW m)
    (hcov : ValidVec (n + g.length) cov)
    (ha : ∀ p, ValidVec (n + g.length) (a p)) (hb : ∀ p, ValidVec (n + g.length) (b p)) :
    let res := cPickFirstUncovered n m t g cov a b
    GoodCircuit n res.1 ∧ Extends g res.1 ∧
    res.1.length ≤ g.length + (t + t * (2 * t + 2) + 2 * m + t * (8 * m)) ∧
    (ValidVec (n + res.1.length) res.2.1 ∧ ValidVec (n + res.1.length) res.2.2) ∧
    ∀ x, x.length = n →
      (evalVec res.1 x res.2.1, evalVec res.1 x res.2.2) =
        pickFirstUncovered (evalVec g x cov) (fun p => evalVec g x (a p)) (fun p => evalVec g x (b p)) := by
  dsimp only [cPickFirstUncovered]
  have hnc := cBuildFin_spec (n := n) (fun L w => w < L) (fun hL hw => lt_of_lt_of_le hw hL)
    val (fun hx hext hw => val_of_extends hx hext hw) t 1
    (fun g' p => cNot n g' (cov p)) (fun x p => !(val g x (cov p))) g hg (fun g' p hg' hext => by
      have h1 := cNot_spec hn g' hg' (cov p) (by have ae := hext.len_le; have ac := hcov p; omega)
      refine ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, fun x hx => by
        rw [h1.2.2.2.2 x hx, val_of_extends hx hext (hcov p)]⟩)
  set rnc := cBuildFin t (fun g' p => cNot n g' (cov p)) g
  have hft := cFirstTrue_spec hn rnc.1 hnc.1 rnc.2 hnc.2.2.2.1
  set rft := cFirstTrue n t rnc.1 rnc.2
  have hz1 := cVecZero_spec hn (m := m) rft.1 hft.1
  set rz1 := cVecZero n m rft.1
  have hz2 := cVecZero_spec hn (m := m) rz1.1 hz1.1
  set rz2 := cVecZero n m rz1.1
  have e0z := ((hnc.2.1.trans hft.2.1).trans hz1.2.1).trans hz2.2.1
  have eftz := hz1.2.1.trans hz2.2.1
  have hf := cFoldl_spec (n := n)
    (fun L (p : VecW m × VecW m) => ValidVec L p.1 ∧ ValidVec L p.2)
    (fun g' x (p : VecW m × VecW m) => (evalVec g' x p.1, evalVec g' x p.2))
    (fun g' acc p =>
      let ra := cVecMux n m g' (rft.2 p) (a p) acc.1
      let rb := cVecMux n m ra.1 (rft.2 p) (b p) acc.2
      (rb.1, (ra.2, rb.2)))
    (fun x acc p => if firstTrue (fun q => !(evalVec g x cov q)) p then (evalVec g x (a p), evalVec g x (b p)) else acc)
    (8 * m) (List.finRange t) rz2.1 (rz1.2, rz2.2) hz2.1
    ⟨hz1.2.2.2.1.mono (by have := hz2.2.1.len_le; omega), hz2.2.2.2.1⟩
    (fun g' acc p _ hg' hext hacc => by
      dsimp only
      have ha1 := cVecMux_spec hn g' hg' (rft.2 p) (a p) acc.1
        (by have ae := (eftz.trans hext).len_le; have aft := hft.2.2.2.1 p; omega)
        ((ha p).mono (by have ae := (e0z.trans hext).len_le; omega)) hacc.1
      set ra := cVecMux n m g' (rft.2 p) (a p) acc.1
      have hb1 := cVecMux_spec hn ra.1 ha1.1 (rft.2 p) (b p) acc.2
        (by have ae := ((eftz.trans hext).trans ha1.2.1).len_le; have aft := hft.2.2.2.1 p; omega)
        ((hb p).mono (by have ae := ((e0z.trans hext).trans ha1.2.1).len_le; omega))
        (hacc.2.mono (by have ae := ha1.2.1.len_le; omega))
      set rb := cVecMux n m ra.1 (rft.2 p) (b p) acc.2
      refine ⟨hb1.1, ha1.2.1.trans hb1.2.1,
        by have a1 := ha1.2.2.1; have a2 := hb1.2.2.1; omega,
        ⟨ha1.2.2.2.1.mono (by have ae := hb1.2.1.len_le; omega), hb1.2.2.2.1⟩, fun x hx => ?_⟩
      have hft_p : val g' x (rft.2 p) = firstTrue (fun q => !(evalVec g x cov q)) p := by
        rw [val_of_extends hx (eftz.trans hext) (hft.2.2.2.1 p)]
        have h1 := congrFun (hft.2.2.2.2 x hx) p
        have h2 : evalVec rnc.1 x rnc.2 = fun q => !(evalVec g x cov q) := funext fun q => hnc.2.2.2.2 x hx q
        rw [h2] at h1
        exact h1
      have hpa : evalVec rb.1 x ra.2 =
          if firstTrue (fun q => !(evalVec g x cov q)) p then evalVec g x (a p) else evalVec g' x acc.1 := by
        rw [evalVec_of_extends hx hb1.2.1 ha1.2.2.2.1, ha1.2.2.2.2 x hx, hft_p,
          evalVec_of_extends hx (e0z.trans hext) (ha p)]
      have hpb : evalVec rb.1 x rb.2 =
          if firstTrue (fun q => !(evalVec g x cov q)) p then evalVec g x (b p) else evalVec g' x acc.2 := by
        rw [hb1.2.2.2.2 x hx, val_of_extends hx ha1.2.1 (by have ae := (eftz.trans hext).len_le; have aft := hft.2.2.2.1 p; omega),
          hft_p, evalVec_of_extends hx ((e0z.trans hext).trans ha1.2.1) (hb p),
          evalVec_of_extends hx ha1.2.1 hacc.2]
      rw [hpa, hpb]
      cases firstTrue (fun q => !(evalVec g x cov q)) p <;> rfl)
  refine ⟨hf.1, e0z.trans hf.2.1, ?_, hf.2.2.2.1, fun x hx => ?_⟩
  · have a1 := hnc.2.2.1; have a2 := hft.2.2.1; have a3 := hz1.2.2.1; have a4 := hz2.2.2.1; have a5 := hf.2.2.1
    simp only [List.length_finRange, mul_one] at a1 a5
    omega
  · rw [hf.2.2.2.2 x hx, evalVec_of_extends hx hz2.2.1 hz1.2.2.2.1, hz1.2.2.2.2 x hx, hz2.2.2.2.2 x hx]
    rfl

private def cVecListMux (n m len : ℕ) (g : List Gate) (sel : ℕ) (f1 f2 : Fin len → VecW m) :
    List Gate × (Fin len → VecW m) :=
  cBuildFin len (fun g' i => cVecMux n m g' sel (f1 i) (f2 i)) g

private lemma cVecListMux_spec {n m len : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (sel : ℕ) (f1 f2 : Fin len → VecW m)
    (hs : sel < n + g.length) (hf1 : ∀ i, ValidVec (n + g.length) (f1 i)) (hf2 : ∀ i, ValidVec (n + g.length) (f2 i)) :
    let res := cVecListMux n m len g sel f1 f2
    GoodCircuit n res.1 ∧ Extends g res.1 ∧ res.1.length ≤ g.length + len * (4 * m) ∧
    (∀ i, ValidVec (n + res.1.length) (res.2 i)) ∧
    ∀ x, x.length = n → ∀ i, evalVec res.1 x (res.2 i) =
      if val g x sel then evalVec g x (f1 i) else evalVec g x (f2 i) := by
  dsimp only [cVecListMux]
  exact cBuildFin_spec (n := n) ValidVec (fun hL hv => hv.mono hL) evalVec
    (fun hx hext hv => evalVec_of_extends hx hext hv) len (4 * m)
    (fun g' i => cVecMux n m g' sel (f1 i) (f2 i))
    (fun x i => if val g x sel then evalVec g x (f1 i) else evalVec g x (f2 i)) g hg
    (fun g' i hg' hext => by
      have ae := hext.len_le
      have hm := cVecMux_spec hn g' hg' sel (f1 i) (f2 i) (by omega) ((hf1 i).mono (by omega)) ((hf2 i).mono (by omega))
      refine ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, fun x hx => ?_⟩
      rw [hm.2.2.2.2 x hx, val_of_extends hx hext hs,
        evalVec_of_extends hx hext (hf1 i), evalVec_of_extends hx hext (hf2 i)])

-- Stage 1: FPT 3-way branching search circuit
private def cFptCombine (n m rem : ℕ) (g : List Gate) (allCov : ℕ) (T : PivotW m)
    (v1 v2 v3 : VecW m)
    (r1 r2 r3 : ℕ × PivotW m × (Fin rem → VecW m)) :
    List Gate × (ℕ × PivotW m × (Fin (rem + 1) → VecW m)) :=
  let rzeros := cBuildFin (rem + 1) (fun g' _ => cVecZero n m g') g
  let ok23 := cOr n rzeros.1 r2.1 r3.1
  let ok123 := cOr n ok23.1 r1.1 ok23.2
  let okAll := cOr n ok123.1 allCov ok123.2
  let T23 := cPivotMux n m okAll.1 r2.1 r2.2.1 r3.2.1
  let T123 := cPivotMux n m T23.1 r1.1 r1.2.1 T23.2
  let TAll := cPivotMux n m T123.1 allCov T T123.2
  let f1 : Fin (rem + 1) → VecW m := Fin.cons (α := fun _ => VecW m) v1 r1.2.2
  let f2 : Fin (rem + 1) → VecW m := Fin.cons (α := fun _ => VecW m) v2 r2.2.2
  let f3 : Fin (rem + 1) → VecW m := Fin.cons (α := fun _ => VecW m) v3 r3.2.2
  let F23 := cVecListMux n m (rem + 1) TAll.1 r2.1 f2 f3
  let F123 := cVecListMux n m (rem + 1) F23.1 r1.1 f1 F23.2
  let FAll := cVecListMux n m (rem + 1) F123.1 allCov rzeros.2 F123.2
  (FAll.1, (okAll.2, TAll.2, FAll.2))

private lemma cFptCombine_spec {n m rem : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (allCov : ℕ) (T : PivotW m) (v1 v2 v3 : VecW m)
    (r1 r2 r3 : ℕ × PivotW m × (Fin rem → VecW m))
    (hac : allCov < n + g.length) (hT : ValidPivot (n + g.length) T)
    (hv1 : ValidVec (n + g.length) v1) (hv2 : ValidVec (n + g.length) v2) (hv3 : ValidVec (n + g.length) v3)
    (hr1 : r1.1 < n + g.length ∧ ValidPivot (n + g.length) r1.2.1 ∧ ∀ i, ValidVec (n + g.length) (r1.2.2 i))
    (hr2 : r2.1 < n + g.length ∧ ValidPivot (n + g.length) r2.2.1 ∧ ∀ i, ValidVec (n + g.length) (r2.2.2 i))
    (hr3 : r3.1 < n + g.length ∧ ValidPivot (n + g.length) r3.2.1 ∧ ∀ i, ValidVec (n + g.length) (r3.2.2 i)) :
    let res := cFptCombine n m rem g allCov T v1 v2 v3 r1 r2 r3
    GoodCircuit n res.1 ∧ Extends g res.1 ∧
    res.1.length ≤ g.length + ((rem + 1) * m + 3 + 3 * (4 * m * m + 4 * m) + 3 * ((rem + 1) * (4 * m))) ∧
    (res.2.1 < n + res.1.length ∧ ValidPivot (n + res.1.length) res.2.2.1 ∧
      ∀ i, ValidVec (n + res.1.length) (res.2.2.2 i)) ∧
    ∀ x, x.length = n →
      (val res.1 x res.2.1, evalPivot res.1 x res.2.2.1, fun i => evalVec res.1 x (res.2.2.2 i)) =
        if val g x allCov then (true, evalPivot g x T, fun _ => vecZero m)
        else if val g x r1.1 then (true, evalPivot g x r1.2.1, Fin.cons (α := fun _ => Vec m) (evalVec g x v1) (fun i => evalVec g x (r1.2.2 i)))
        else if val g x r2.1 then (true, evalPivot g x r2.2.1, Fin.cons (α := fun _ => Vec m) (evalVec g x v2) (fun i => evalVec g x (r2.2.2 i)))
        else (val g x r3.1, evalPivot g x r3.2.1, Fin.cons (α := fun _ => Vec m) (evalVec g x v3) (fun i => evalVec g x (r3.2.2 i))) := by
  dsimp only [cFptCombine]
  have hzeros := cBuildFin_spec (n := n) ValidVec (fun hL hv => hv.mono hL) evalVec
    (fun hx hext hv => evalVec_of_extends hx hext hv) (rem + 1) m
    (fun g' _ => cVecZero n m g') (fun _ _ => vecZero m) g hg (fun g' _ hg' _ => cVecZero_spec hn g' hg')
  set rzeros := cBuildFin (rem + 1) (fun g' _ => cVecZero n m g') g
  have hok23 := cOr_spec hn rzeros.1 hzeros.1 r2.1 r3.1
    (by have ae := hzeros.2.1.len_le; have a2 := hr2.1; omega)
    (by have ae := hzeros.2.1.len_le; have a3 := hr3.1; omega)
  set ok23 := cOr n rzeros.1 r2.1 r3.1
  have hok123 := cOr_spec hn ok23.1 hok23.1 r1.1 ok23.2
    (by have ae := (hzeros.2.1.trans hok23.2.1).len_le; have a1 := hr1.1; omega) hok23.2.2.2.1
  set ok123 := cOr n ok23.1 r1.1 ok23.2
  have hokAll := cOr_spec hn ok123.1 hok123.1 allCov ok123.2
    (by have ae := ((hzeros.2.1.trans hok23.2.1).trans hok123.2.1).len_le; omega) hok123.2.2.2.1
  set okAll := cOr n ok123.1 allCov ok123.2
  have e0_ok := ((hzeros.2.1.trans hok23.2.1).trans hok123.2.1).trans hokAll.2.1
  have hT23 := cPivotMux_spec hn okAll.1 hokAll.1 r2.1 r2.2.1 r3.2.1
    (by have ae := e0_ok.len_le; have a2 := hr2.1; omega)
    (hr2.2.1.mono (by have := e0_ok.len_le; omega))
    (hr3.2.1.mono (by have := e0_ok.len_le; omega))
  set T23 := cPivotMux n m okAll.1 r2.1 r2.2.1 r3.2.1
  have hT123 := cPivotMux_spec hn T23.1 hT23.1 r1.1 r1.2.1 T23.2
    (by have ae := (e0_ok.trans hT23.2.1).len_le; have a1 := hr1.1; omega)
    (hr1.2.1.mono (by have := (e0_ok.trans hT23.2.1).len_le; omega)) hT23.2.2.2.1
  set T123 := cPivotMux n m T23.1 r1.1 r1.2.1 T23.2
  have hTAll := cPivotMux_spec hn T123.1 hT123.1 allCov T T123.2
    (by have ae := ((e0_ok.trans hT23.2.1).trans hT123.2.1).len_le; omega)
    (hT.mono (by have := ((e0_ok.trans hT23.2.1).trans hT123.2.1).len_le; omega)) hT123.2.2.2.1
  set TAll := cPivotMux n m T123.1 allCov T T123.2
  have e0_T := e0_ok.trans ((hT23.2.1.trans hT123.2.1).trans hTAll.2.1)
  let f1 : Fin (rem + 1) → VecW m := Fin.cons (α := fun _ => VecW m) v1 r1.2.2
  let f2 : Fin (rem + 1) → VecW m := Fin.cons (α := fun _ => VecW m) v2 r2.2.2
  let f3 : Fin (rem + 1) → VecW m := Fin.cons (α := fun _ => VecW m) v3 r3.2.2
  have hf1_v : ∀ i, ValidVec (n + TAll.1.length) (f1 i) := fun i =>
    Fin.cases (hv1.mono (by have := e0_T.len_le; omega)) (fun j => (hr1.2.2 j).mono (by have := e0_T.len_le; omega)) i
  have hf2_v : ∀ i, ValidVec (n + TAll.1.length) (f2 i) := fun i =>
    Fin.cases (hv2.mono (by have := e0_T.len_le; omega)) (fun j => (hr2.2.2 j).mono (by have := e0_T.len_le; omega)) i
  have hf3_v : ∀ i, ValidVec (n + TAll.1.length) (f3 i) := fun i =>
    Fin.cases (hv3.mono (by have := e0_T.len_le; omega)) (fun j => (hr3.2.2 j).mono (by have := e0_T.len_le; omega)) i
  have hF23 := cVecListMux_spec hn TAll.1 hTAll.1 r2.1 f2 f3
    (by have ae := e0_T.len_le; have a2 := hr2.1; omega) hf2_v hf3_v
  set F23 := cVecListMux n m (rem + 1) TAll.1 r2.1 f2 f3
  have hF123 := cVecListMux_spec hn F23.1 hF23.1 r1.1 f1 F23.2
    (by have ae := (e0_T.trans hF23.2.1).len_le; have a1 := hr1.1; omega)
    (fun i => (hf1_v i).mono (by have := hF23.2.1.len_le; omega)) hF23.2.2.2.1
  set F123 := cVecListMux n m (rem + 1) F23.1 r1.1 f1 F23.2
  have ez_T := (((hok23.2.1.trans hok123.2.1).trans hokAll.2.1).trans hT23.2.1).trans (hT123.2.1.trans hTAll.2.1)
  have hFAll := cVecListMux_spec hn F123.1 hF123.1 allCov rzeros.2 F123.2
    (by have ae := ((e0_T.trans hF23.2.1).trans hF123.2.1).len_le; omega)
    (fun i => (hzeros.2.2.2.1 i).mono (by have := ((ez_T.trans hF23.2.1).trans hF123.2.1).len_le; omega)) hF123.2.2.2.1
  set FAll := cVecListMux n m (rem + 1) F123.1 allCov rzeros.2 F123.2
  have eT_F := (hF23.2.1.trans hF123.2.1).trans hFAll.2.1
  have eok_F := ((hT23.2.1.trans hT123.2.1).trans hTAll.2.1).trans eT_F
  refine ⟨hFAll.1, e0_T.trans eT_F, ?_,
    ⟨by have ae := eok_F.len_le; have ao := hokAll.2.2.2.1; omega,
     hTAll.2.2.2.1.mono (by have := eT_F.len_le; omega), hFAll.2.2.2.1⟩, fun x hx => ?_⟩
  · have a1 := hzeros.2.2.1; have a2 := hok23.2.2.1; have a3 := hok123.2.2.1; have a4 := hokAll.2.2.1
    have a5 := hT23.2.2.1; have a6 := hT123.2.2.1; have a7 := hTAll.2.2.1
    have a8 := hF23.2.2.1; have a9 := hF123.2.2.1; have a10 := hFAll.2.2.1
    omega
  · have hok_e : val FAll.1 x okAll.2 = (val g x allCov || val g x r1.1 || val g x r2.1 || val g x r3.1) := by
      rw [val_of_extends hx eok_F hokAll.2.2.2.1, hokAll.2.2.2.2 x hx,
        val_of_extends hx ((hzeros.2.1.trans hok23.2.1).trans hok123.2.1) hac,
        hok123.2.2.2.2 x hx, val_of_extends hx (hzeros.2.1.trans hok23.2.1) hr1.1,
        hok23.2.2.2.2 x hx, val_of_extends hx hzeros.2.1 hr2.1, val_of_extends hx hzeros.2.1 hr3.1]
      simp [Bool.or_assoc]
    have hT_e : evalPivot FAll.1 x TAll.2 =
        if val g x allCov then evalPivot g x T else if val g x r1.1 then evalPivot g x r1.2.1
        else if val g x r2.1 then evalPivot g x r2.2.1 else evalPivot g x r3.2.1 := by
      rw [evalPivot_of_extends hx eT_F hTAll.2.2.2.1, hTAll.2.2.2.2 x hx,
        val_of_extends hx ((e0_ok.trans hT23.2.1).trans hT123.2.1) hac,
        evalPivot_of_extends hx ((e0_ok.trans hT23.2.1).trans hT123.2.1) hT,
        hT123.2.2.2.2 x hx, val_of_extends hx (e0_ok.trans hT23.2.1) hr1.1,
        evalPivot_of_extends hx (e0_ok.trans hT23.2.1) hr1.2.1,
        hT23.2.2.2.2 x hx, val_of_extends hx e0_ok hr2.1,
        evalPivot_of_extends hx e0_ok hr2.2.1, evalPivot_of_extends hx e0_ok hr3.2.1]
    have hf1_e : ∀ i, evalVec TAll.1 x (f1 i) = Fin.cons (α := fun _ => Vec m) (evalVec g x v1) (fun j => evalVec g x (r1.2.2 j)) i := fun i =>
      Fin.cases (evalVec_of_extends hx e0_T hv1) (fun j => evalVec_of_extends hx e0_T (hr1.2.2 j)) i
    have hf2_e : ∀ i, evalVec TAll.1 x (f2 i) = Fin.cons (α := fun _ => Vec m) (evalVec g x v2) (fun j => evalVec g x (r2.2.2 j)) i := fun i =>
      Fin.cases (evalVec_of_extends hx e0_T hv2) (fun j => evalVec_of_extends hx e0_T (hr2.2.2 j)) i
    have hf3_e : ∀ i, evalVec TAll.1 x (f3 i) = Fin.cons (α := fun _ => Vec m) (evalVec g x v3) (fun j => evalVec g x (r3.2.2 j)) i := fun i =>
      Fin.cases (evalVec_of_extends hx e0_T hv3) (fun j => evalVec_of_extends hx e0_T (hr3.2.2 j)) i
    have hF_e : (fun i => evalVec FAll.1 x (FAll.2 i)) =
        if val g x allCov then (fun _ => vecZero m)
        else if val g x r1.1 then Fin.cons (α := fun _ => Vec m) (evalVec g x v1) (fun j => evalVec g x (r1.2.2 j))
        else if val g x r2.1 then Fin.cons (α := fun _ => Vec m) (evalVec g x v2) (fun j => evalVec g x (r2.2.2 j))
        else Fin.cons (α := fun _ => Vec m) (evalVec g x v3) (fun j => evalVec g x (r3.2.2 j)) := by
      funext i
      rw [hFAll.2.2.2.2 x hx i, val_of_extends hx ((e0_T.trans hF23.2.1).trans hF123.2.1) hac,
        evalVec_of_extends hx ((ez_T.trans hF23.2.1).trans hF123.2.1) (hzeros.2.2.2.1 i), hzeros.2.2.2.2 x hx i,
        hF123.2.2.2.2 x hx i, val_of_extends hx (e0_T.trans hF23.2.1) hr1.1,
        evalVec_of_extends hx hF23.2.1 (hf1_v i), hf1_e i,
        hF23.2.2.2.2 x hx i, val_of_extends hx e0_T hr2.1, hf2_e i, hf3_e i]
      cases val g x allCov <;> cases val g x r1.1 <;> cases val g x r2.1 <;> rfl
    rw [hok_e, hT_e, hF_e]
    cases val g x allCov <;> cases val g x r1.1 <;> cases val g x r2.1 <;> rfl

private def cFptSearch (n m t : ℕ) (a b : Fin t → VecW m) :
    (rem : ℕ) → List Gate → PivotW m → List Gate × (ℕ × PivotW m × (Fin rem → VecW m))
  | 0, g, T =>
    let rcov := cBuildFin t (fun g' p => cProbeCovered n m g' T (a p) (b p)) g
    let r0 := cTrue n rcov.1
    let rall := cFoldl (fun g' acc p => cAnd n g' acc (rcov.2 p)) (List.finRange t) r0.1 r0.2
    (rall.1, (rall.2, T, Fin.elim0))
  | rem + 1, g, T =>
    let rcov := cBuildFin t (fun g' p => cProbeCovered n m g' T (a p) (b p)) g
    let r0 := cTrue n rcov.1
    let rall := cFoldl (fun g' acc p => cAnd n g' acc (rcov.2 p)) (List.finRange t) r0.1 r0.2
    let rab := cPickFirstUncovered n m t rall.1 rcov.2 a b
    let rv3 := cVecXor n m rab.1 rab.2.1 rab.2.2
    let rT1 := cInsertVec n m rv3.1 T rab.2.1
    let res1 := cFptSearch n m t a b rem rT1.1 rT1.2
    let rT2 := cInsertVec n m res1.1 T rab.2.2
    let res2 := cFptSearch n m t a b rem rT2.1 rT2.2
    let rT3 := cInsertVec n m res2.1 T rv3.2
    let res3 := cFptSearch n m t a b rem rT3.1 rT3.2
    cFptCombine n m rem res3.1 rall.2 T rab.2.1 rab.2.2 rv3.2 res1.2 res2.2 res3.2

private def fptNodeBound (m t d : ℕ) : ℕ := 256 * (m + t + d + 2) ^ 3

private lemma cFptSearch_spec {n m t d : ℕ} (hn : 0 < n) (a b : Fin t → VecW m) :
    ∀ (rem : ℕ), rem ≤ d → ∀ (g : List Gate), GoodCircuit n g → ∀ (T : PivotW m),
      ValidPivot (n + g.length) T →
      (∀ p, ValidVec (n + g.length) (a p)) → (∀ p, ValidVec (n + g.length) (b p)) →
      let res := cFptSearch n m t a b rem g T
      GoodCircuit n res.1 ∧ Extends g res.1 ∧
      res.1.length + fptNodeBound m t d ≤ g.length + 2 * 3 ^ rem * fptNodeBound m t d ∧
      (res.2.1 < n + res.1.length ∧ ValidPivot (n + res.1.length) res.2.2.1 ∧
        ∀ i, ValidVec (n + res.1.length) (res.2.2.2 i)) ∧
      ∀ x, x.length = n →
        (val res.1 x res.2.1, evalPivot res.1 x res.2.2.1, fun i => evalVec res.1 x (res.2.2.2 i)) =
          fptSearch (fun p => evalVec g x (a p)) (fun p => evalVec g x (b p)) rem (evalPivot g x T) := by
  intro rem
  induction rem with
  | zero =>
    intro _ g hg T hT ha hb
    dsimp only [cFptSearch]
    have hcov := cBuildFin_spec (n := n) (fun L w => w < L) (fun hL hw => lt_of_lt_of_le hw hL)
      val (fun hx hext hw => val_of_extends hx hext hw) t (24 * m * m + 13 * m + 5)
      (fun g' p => cProbeCovered n m g' T (a p) (b p))
      (fun x p => probeCovered (evalPivot g x T) (evalVec g x (a p)) (evalVec g x (b p))) g hg
      (fun g' p hg' hext => by
        have ae := hext.len_le
        have hp := cProbeCovered_spec hn g' hg' T (a p) (b p) (hT.mono (by omega))
          ((ha p).mono (by omega)) ((hb p).mono (by omega))
        refine ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, fun x hx => ?_⟩
        rw [hp.2.2.2.2 x hx, evalPivot_of_extends hx hext hT,
          evalVec_of_extends hx hext (ha p), evalVec_of_extends hx hext (hb p)])
    set rcov := cBuildFin t (fun g' p => cProbeCovered n m g' T (a p) (b p)) g
    have h0 := cTrue_spec hn rcov.1 hcov.1
    set r0 := cTrue n rcov.1
    have hall := cFoldl_spec (n := n) (fun L w => w < L) val
      (fun g' acc p => cAnd n g' acc (rcov.2 p))
      (fun x acc p => acc && probeCovered (evalPivot g x T) (evalVec g x (a p)) (evalVec g x (b p)))
      1 (List.finRange t) r0.1 r0.2 h0.1 h0.2.2.2.1 (fun g' acc p _ hg' hext hacc => by
        have ae := (h0.2.1.trans hext).len_le
        have h1 := cAnd_spec hn g' hg' acc (rcov.2 p) hacc (by have ac := hcov.2.2.2.1 p; omega)
        refine ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, fun x hx => ?_⟩
        rw [h1.2.2.2.2 x hx, val_of_extends hx (h0.2.1.trans hext) (hcov.2.2.2.1 p), hcov.2.2.2.2 x hx p])
    have eall := (hcov.2.1.trans h0.2.1).trans hall.2.1
    refine ⟨hall.1, eall, ?_, ⟨hall.2.2.2.1, hT.mono (by have := eall.len_le; omega), fun i => i.elim0⟩, fun x hx => ?_⟩
    · have a1 := hcov.2.2.1; have a2 := h0.2.2.1; have a3 := hall.2.2.1
      simp only [List.length_finRange, mul_one] at a3
      have hB : t * (24 * m * m + 13 * m + 5) + 1 + t ≤ fptNodeBound m t d := by
        unfold fptNodeBound
        set S := m + t + d + 2
        have hS1 : 1 ≤ S := by omega
        have hSm : m ≤ S := by omega
        have hSt : t ≤ S := by omega
        nlinarith [sq_nonneg S, mul_le_mul hSm hSm (Nat.zero_le m) (Nat.zero_le S),
          mul_le_mul hSt (mul_le_mul hSm hSm (Nat.zero_le m) (Nat.zero_le S)) (Nat.zero_le _) (Nat.zero_le S),
          mul_le_mul hSt hSm (Nat.zero_le m) (Nat.zero_le S)]
      simp only [pow_zero, mul_one]
      omega
    · dsimp only [fptSearch]
      rw [hall.2.2.2.2 x hx, h0.2.2.2.2 x hx, evalPivot_of_extends hx eall hT, list_all_eq_foldl_and]
      exact Prod.ext rfl (Prod.ext rfl (funext fun i => i.elim0))
  | succ rem ih =>
    intro hrem g hg T hT ha hb
    dsimp only [cFptSearch]
    have hcov := cBuildFin_spec (n := n) (fun L w => w < L) (fun hL hw => lt_of_lt_of_le hw hL)
      val (fun hx hext hw => val_of_extends hx hext hw) t (24 * m * m + 13 * m + 5)
      (fun g' p => cProbeCovered n m g' T (a p) (b p))
      (fun x p => probeCovered (evalPivot g x T) (evalVec g x (a p)) (evalVec g x (b p))) g hg
      (fun g' p hg' hext => by
        have ae := hext.len_le
        have hp := cProbeCovered_spec hn g' hg' T (a p) (b p) (hT.mono (by omega))
          ((ha p).mono (by omega)) ((hb p).mono (by omega))
        refine ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, fun x hx => ?_⟩
        rw [hp.2.2.2.2 x hx, evalPivot_of_extends hx hext hT,
          evalVec_of_extends hx hext (ha p), evalVec_of_extends hx hext (hb p)])
    set rcov := cBuildFin t (fun g' p => cProbeCovered n m g' T (a p) (b p)) g
    have h0 := cTrue_spec hn rcov.1 hcov.1
    set r0 := cTrue n rcov.1
    have hall := cFoldl_spec (n := n) (fun L w => w < L) val
      (fun g' acc p => cAnd n g' acc (rcov.2 p))
      (fun x acc p => acc && probeCovered (evalPivot g x T) (evalVec g x (a p)) (evalVec g x (b p)))
      1 (List.finRange t) r0.1 r0.2 h0.1 h0.2.2.2.1 (fun g' acc p _ hg' hext hacc => by
        have ae := (h0.2.1.trans hext).len_le
        have h1 := cAnd_spec hn g' hg' acc (rcov.2 p) hacc (by have ac := hcov.2.2.2.1 p; omega)
        refine ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, fun x hx => ?_⟩
        rw [h1.2.2.2.2 x hx, val_of_extends hx (h0.2.1.trans hext) (hcov.2.2.2.1 p), hcov.2.2.2.2 x hx p])
    set rall := cFoldl (fun g' acc p => cAnd n g' acc (rcov.2 p)) (List.finRange t) r0.1 r0.2
    have e0_all := (hcov.2.1.trans h0.2.1).trans hall.2.1
    have ecov_all := h0.2.1.trans hall.2.1
    have hab := cPickFirstUncovered_spec hn rall.1 hall.1 rcov.2 a b
      (fun p => by have ae := ecov_all.len_le; have ac := hcov.2.2.2.1 p; omega)
      (fun p => (ha p).mono (by have := e0_all.len_le; omega))
      (fun p => (hb p).mono (by have := e0_all.len_le; omega))
    set rab := cPickFirstUncovered n m t rall.1 rcov.2 a b
    have hv3 := cVecXor_spec hn rab.1 hab.1 rab.2.1 rab.2.2 hab.2.2.2.1.1 hab.2.2.2.1.2
    set rv3 := cVecXor n m rab.1 rab.2.1 rab.2.2
    have e0_v3 := (e0_all.trans hab.2.1).trans hv3.2.1
    have hT1 := cInsertVec_spec hn rv3.1 hv3.1 T rab.2.1
      (hT.mono (by have := e0_v3.len_le; omega)) (hab.2.2.2.1.1.mono (by have := hv3.2.1.len_le; omega))
    set rT1 := cInsertVec n m rv3.1 T rab.2.1
    have e0_T1 := e0_v3.trans hT1.2.1
    have hres1 := ih (by omega) rT1.1 hT1.1 rT1.2 hT1.2.2.2.1
      (fun p => (ha p).mono (by have := e0_T1.len_le; omega))
      (fun p => (hb p).mono (by have := e0_T1.len_le; omega))
    set res1 := cFptSearch n m t a b rem rT1.1 rT1.2
    have e0_r1 := e0_T1.trans hres1.2.1
    have eab_r1 := (hv3.2.1.trans hT1.2.1).trans hres1.2.1
    have hT2 := cInsertVec_spec hn res1.1 hres1.1 T rab.2.2
      (hT.mono (by have := e0_r1.len_le; omega)) (hab.2.2.2.1.2.mono (by have := eab_r1.len_le; omega))
    set rT2 := cInsertVec n m res1.1 T rab.2.2
    have e0_T2 := e0_r1.trans hT2.2.1
    have hres2 := ih (by omega) rT2.1 hT2.1 rT2.2 hT2.2.2.2.1
      (fun p => (ha p).mono (by have := e0_T2.len_le; omega))
      (fun p => (hb p).mono (by have := e0_T2.len_le; omega))
    set res2 := cFptSearch n m t a b rem rT2.1 rT2.2
    have e0_r2 := e0_T2.trans hres2.2.1
    have ev3_r2 := ((hT1.2.1.trans hres1.2.1).trans hT2.2.1).trans hres2.2.1
    have hT3 := cInsertVec_spec hn res2.1 hres2.1 T rv3.2
      (hT.mono (by have := e0_r2.len_le; omega)) (hv3.2.2.2.1.mono (by have := ev3_r2.len_le; omega))
    set rT3 := cInsertVec n m res2.1 T rv3.2
    have e0_T3 := e0_r2.trans hT3.2.1
    have hres3 := ih (by omega) rT3.1 hT3.1 rT3.2 hT3.2.2.2.1
      (fun p => (ha p).mono (by have := e0_T3.len_le; omega))
      (fun p => (hb p).mono (by have := e0_T3.len_le; omega))
    set res3 := cFptSearch n m t a b rem rT3.1 rT3.2
    have er2_r3 := hT3.2.1.trans hres3.2.1
    have er1_r3 := (hT2.2.1.trans hres2.2.1).trans er2_r3
    have ev3_r3 := ev3_r2.trans er2_r3
    have eab_r3 := eab_r1.trans er1_r3
    have eall_r3 := hab.2.1.trans eab_r3
    have e0_r3 := e0_all.trans eall_r3
    have hcomb := cFptCombine_spec hn res3.1 hres3.1 rall.2 T rab.2.1 rab.2.2 rv3.2 res1.2 res2.2 res3.2
      (by have ae := eall_r3.len_le; have aa := hall.2.2.2.1; omega)
      (hT.mono (by have := e0_r3.len_le; omega))
      (hab.2.2.2.1.1.mono (by have := eab_r3.len_le; omega))
      (hab.2.2.2.1.2.mono (by have := eab_r3.len_le; omega))
      (hv3.2.2.2.1.mono (by have := ev3_r3.len_le; omega))
      ⟨by have ae := er1_r3.len_le; have a1 := hres1.2.2.2.1.1; omega,
       hres1.2.2.2.1.2.1.mono (by have := er1_r3.len_le; omega),
       fun i => (hres1.2.2.2.1.2.2 i).mono (by have := er1_r3.len_le; omega)⟩
      ⟨by have ae := er2_r3.len_le; have a2 := hres2.2.2.2.1.1; omega,
       hres2.2.2.2.1.2.1.mono (by have := er2_r3.len_le; omega),
       fun i => (hres2.2.2.2.1.2.2 i).mono (by have := er2_r3.len_le; omega)⟩
      hres3.2.2.2.1
    refine ⟨hcomb.1, e0_r3.trans hcomb.2.1, ?_, hcomb.2.2.2.1, fun x hx => ?_⟩
    · have a1 := hcov.2.2.1; have a2 := h0.2.2.1; have a3 := hall.2.2.1; have a4 := hab.2.2.1
      have a5 := hv3.2.2.1; have a6 := hT1.2.2.1; have a7 := hres1.2.2.1
      have a8 := hT2.2.2.1; have a9 := hres2.2.2.1; have a10 := hT3.2.2.1; have a11 := hres3.2.2.1
      have a12 := hcomb.2.2.1
      simp only [List.length_finRange, mul_one] at a3
      have hov : t * (24 * m * m + 13 * m + 5) + 1 + t + (t + t * (2 * t + 2) + 2 * m + t * (8 * m)) + 4 * m +
          3 * (14 * m * m + 4 * m) + ((rem + 1) * m + 3 + 3 * (4 * m * m + 4 * m) + 3 * ((rem + 1) * (4 * m))) ≤
          fptNodeBound m t d := by
        unfold fptNodeBound
        set S := m + t + d + 2
        have hS1 : 1 ≤ S := by omega
        have hSm : m ≤ S := by omega
        have hSt : t ≤ S := by omega
        have hSr : rem + 1 ≤ S := by omega
        nlinarith [sq_nonneg S,
          mul_le_mul hSm hSm (Nat.zero_le m) (Nat.zero_le S),
          mul_le_mul hSt hSt (Nat.zero_le t) (Nat.zero_le S),
          mul_le_mul hSt hSm (Nat.zero_le m) (Nat.zero_le S),
          mul_le_mul hSr hSm (Nat.zero_le m) (Nat.zero_le S),
          mul_le_mul hSt (mul_le_mul hSm hSm (Nat.zero_le m) (Nat.zero_le S)) (Nat.zero_le _) (Nat.zero_le S)]
      have hpow : 2 * 3 ^ (rem + 1) * fptNodeBound m t d =
          2 * 3 ^ rem * fptNodeBound m t d + 2 * 3 ^ rem * fptNodeBound m t d + 2 * 3 ^ rem * fptNodeBound m t d := by ring
      rw [hpow]
      omega
    · rw [hcomb.2.2.2.2 x hx, val_of_extends hx eall_r3 hall.2.2.2.1, evalPivot_of_extends hx e0_r3 hT,
        evalVec_of_extends hx eab_r3 hab.2.2.2.1.1, evalVec_of_extends hx eab_r3 hab.2.2.2.1.2,
        evalVec_of_extends hx ev3_r3 hv3.2.2.2.1,
        val_of_extends hx er1_r3 hres1.2.2.2.1.1, evalPivot_of_extends hx er1_r3 hres1.2.2.2.1.2.1,
        val_of_extends hx er2_r3 hres2.2.2.2.1.1, evalPivot_of_extends hx er2_r3 hres2.2.2.2.1.2.1]
      have hf1' : (fun i => evalVec res3.1 x (res1.2.2.2 i)) = fun i => evalVec res1.1 x (res1.2.2.2 i) :=
        funext fun i => evalVec_of_extends hx er1_r3 (hres1.2.2.2.1.2.2 i)
      have hf2' : (fun i => evalVec res3.1 x (res2.2.2.2 i)) = fun i => evalVec res2.1 x (res2.2.2.2 i) :=
        funext fun i => evalVec_of_extends hx er2_r3 (hres2.2.2.2.1.2.2 i)
      rw [hf1', hf2']
      let aE : Fin t → Vec m := fun p => evalVec g x (a p)
      let bE : Fin t → Vec m := fun p => evalVec g x (b p)
      let TE : PivotTable m := evalPivot g x T
      have hcov_e : evalVec rcov.1 x rcov.2 = fun p => probeCovered TE (aE p) (bE p) :=
        funext fun p => hcov.2.2.2.2 x hx p
      have hall_e : val rall.1 x rall.2 = (List.finRange t).all (fun p => probeCovered TE (aE p) (bE p)) := by
        rw [hall.2.2.2.2 x hx, h0.2.2.2.2 x hx, list_all_eq_foldl_and]
      have hab_e : (evalVec rab.1 x rab.2.1, evalVec rab.1 x rab.2.2) =
          pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE := by
        rw [hab.2.2.2.2 x hx, evalVec_of_extends hx ecov_all hcov.2.2.2.1, hcov_e]
        have hae : (fun p => evalVec rall.1 x (a p)) = aE := funext fun p => evalVec_of_extends hx e0_all (ha p)
        have hbe : (fun p => evalVec rall.1 x (b p)) = bE := funext fun p => evalVec_of_extends hx e0_all (hb p)
        rw [hae, hbe]
      have hv1_e : evalVec rab.1 x rab.2.1 = (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).1 :=
        congrArg Prod.fst hab_e
      have hv2_e : evalVec rab.1 x rab.2.2 = (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).2 :=
        congrArg Prod.snd hab_e
      have hv3_e : evalVec rv3.1 x rv3.2 = vecXor (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).1
          (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).2 := by
        rw [hv3.2.2.2.2 x hx, hv1_e, hv2_e]
      have hres1_e : (val res1.1 x res1.2.1, evalPivot res1.1 x res1.2.2.1, fun i => evalVec res1.1 x (res1.2.2.2 i)) =
          fptSearch aE bE rem (insertVec TE (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).1) := by
        rw [hres1.2.2.2.2 x hx, hT1.2.2.2.2 x hx, evalPivot_of_extends hx e0_v3 hT,
          evalVec_of_extends hx hv3.2.1 hab.2.2.2.1.1, hv1_e]
        have hae : (fun p => evalVec rT1.1 x (a p)) = aE := funext fun p => evalVec_of_extends hx e0_T1 (ha p)
        have hbe : (fun p => evalVec rT1.1 x (b p)) = bE := funext fun p => evalVec_of_extends hx e0_T1 (hb p)
        rw [hae, hbe]
      have hres2_e : (val res2.1 x res2.2.1, evalPivot res2.1 x res2.2.2.1, fun i => evalVec res2.1 x (res2.2.2.2 i)) =
          fptSearch aE bE rem (insertVec TE (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).2) := by
        rw [hres2.2.2.2.2 x hx, hT2.2.2.2.2 x hx, evalPivot_of_extends hx e0_r1 hT,
          evalVec_of_extends hx eab_r1 hab.2.2.2.1.2, hv2_e]
        have hae : (fun p => evalVec rT2.1 x (a p)) = aE := funext fun p => evalVec_of_extends hx e0_T2 (ha p)
        have hbe : (fun p => evalVec rT2.1 x (b p)) = bE := funext fun p => evalVec_of_extends hx e0_T2 (hb p)
        rw [hae, hbe]
      have hres3_e : (val res3.1 x res3.2.1, evalPivot res3.1 x res3.2.2.1, fun i => evalVec res3.1 x (res3.2.2.2 i)) =
          fptSearch aE bE rem (insertVec TE (vecXor (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).1
            (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).2)) := by
        rw [hres3.2.2.2.2 x hx, hT3.2.2.2.2 x hx, evalPivot_of_extends hx e0_r2 hT,
          evalVec_of_extends hx ev3_r2 hv3.2.2.2.1, hv3_e]
        have hae : (fun p => evalVec rT3.1 x (a p)) = aE := funext fun p => evalVec_of_extends hx e0_T3 (ha p)
        have hbe : (fun p => evalVec rT3.1 x (b p)) = bE := funext fun p => evalVec_of_extends hx e0_T3 (hb p)
        rw [hae, hbe]
      have hr1_1 : val res1.1 x res1.2.1 = (fptSearch aE bE rem (insertVec TE (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).1)).1 :=
        congrArg Prod.fst hres1_e
      have hr1_2 : evalPivot res1.1 x res1.2.2.1 = (fptSearch aE bE rem (insertVec TE (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).1)).2.1 :=
        congrArg (fun p => p.2.1) hres1_e
      have hr1_3 : (fun i => evalVec res1.1 x (res1.2.2.2 i)) = (fptSearch aE bE rem (insertVec TE (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).1)).2.2 :=
        congrArg (fun p => p.2.2) hres1_e
      have hr2_1 : val res2.1 x res2.2.1 = (fptSearch aE bE rem (insertVec TE (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).2)).1 :=
        congrArg Prod.fst hres2_e
      have hr2_2 : evalPivot res2.1 x res2.2.2.1 = (fptSearch aE bE rem (insertVec TE (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).2)).2.1 :=
        congrArg (fun p => p.2.1) hres2_e
      have hr2_3 : (fun i => evalVec res2.1 x (res2.2.2.2 i)) = (fptSearch aE bE rem (insertVec TE (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).2)).2.2 :=
        congrArg (fun p => p.2.2) hres2_e
      have hr3_1 : val res3.1 x res3.2.1 = (fptSearch aE bE rem (insertVec TE (vecXor (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).1
          (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).2))).1 :=
        congrArg Prod.fst hres3_e
      have hr3_2 : evalPivot res3.1 x res3.2.2.1 = (fptSearch aE bE rem (insertVec TE (vecXor (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).1
          (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).2))).2.1 :=
        congrArg (fun p => p.2.1) hres3_e
      have hr3_3 : (fun i => evalVec res3.1 x (res3.2.2.2 i)) = (fptSearch aE bE rem (insertVec TE (vecXor (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).1
          (pickFirstUncovered (fun p => probeCovered TE (aE p) (bE p)) aE bE).2))).2.2 :=
        congrArg (fun p => p.2.2) hres3_e
      rw [hall_e, hv1_e, hv2_e, hv3_e, hr1_1, hr1_2, hr1_3, hr2_1, hr2_2, hr2_3, hr3_1, hr3_2, hr3_3]
      rfl

-- Stage 2: Cell finish & recursive sum circuit
private def cFinishCell (n m t : ℕ) (g : List Gate) (Tfound : PivotW m) (a b L : Fin t → VecW m)
    (baseP wanted : Fin t → ℕ) (A_cell : AugW m) : List Gate × VecW (m + 1) :=
  let rz := cBackSub n m g A_cell
  let rAsol := cFoldl (fun g' A p =>
    let r1 := cReduceVec n m g' Tfound (a p)
    let risA := cVecIsZero n m r1.1 r1.2
    let r2 := cReduceVec n m risA.1 Tfound (b p)
    let risB := cVecIsZero n m r2.1 r2.2
    let rdA := cVecDot n m risB.1 (a p) rz.2
    let rdB := cVecDot n m rdA.1 (b p) rz.2
    let rdAB := cXor n rdB.1 rdA.2 rdB.2
    let rndAB := cNot n rdAB.1 rdAB.2
    let rq1 := cVecAndScalar n m rndAB.1 rdA.2 (b p)
    let rq2 := cVecAndScalar n m rq1.1 rdB.2 (a p)
    let rq3 := cVecAndScalar n m rq2.1 rndAB.2 (a p)
    let rq23 := cVecMux n m rq3.1 risB.2 rq2.2 rq3.2
    let rqLin := cVecMux n m rq23.1 risA.2 rq1.2 rq23.2
    let rv := cVecXor n m rqLin.1 (L p) rqLin.2
    let rrhs := cXor n rv.1 (wanted p) (baseP p)
    cAugInsert n m rrhs.1 A rv.2 rrhs.2) (List.finRange t) rz.1 A_cell
  let roh := cOneHotCount n m rAsol.1 rAsol.2.piv.hasPiv
  let rninc := cNot n roh.1 rAsol.2.inc
  cBuildFin (m + 1) (fun g' idx => cAnd n g' rninc.2 (roh.2 ⟨m - idx.1, by omega⟩)) rninc.1

private def cellNodeBound (m t : ℕ) : ℕ := 128 * (m + t + 2) ^ 3

private lemma cFinishCell_spec {n m t : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (Tfound : PivotW m) (a b L : Fin t → VecW m) (baseP wanted : Fin t → ℕ) (A_cell : AugW m)
    (hTf : ValidPivot (n + g.length) Tfound)
    (ha : ∀ p, ValidVec (n + g.length) (a p)) (hb : ∀ p, ValidVec (n + g.length) (b p))
    (hL : ∀ p, ValidVec (n + g.length) (L p))
    (hbp : ∀ p, baseP p < n + g.length) (hw : ∀ p, wanted p < n + g.length)
    (hAc : ValidAug (n + g.length) A_cell) :
    let res := cFinishCell n m t g Tfound a b L baseP wanted A_cell
    GoodCircuit n res.1 ∧ Extends g res.1 ∧ res.1.length ≤ g.length + cellNodeBound m t ∧
    ValidVec (n + res.1.length) res.2 ∧
    ∀ x, x.length = n → evalVec res.1 x res.2 =
      finishCell (evalPivot g x Tfound) (fun p => evalVec g x (a p)) (fun p => evalVec g x (b p))
        (fun p => evalVec g x (L p)) (fun p => val g x (baseP p)) (fun p => val g x (wanted p))
        (evalAug g x A_cell) := by
  dsimp only [cFinishCell]
  have hz := cBackSub_spec hn g hg A_cell hAc
  set rz := cBackSub n m g A_cell
  have hfold := cFoldl_spec (n := n) ValidAug evalAug
    (fun g' A p =>
      let r1 := cReduceVec n m g' Tfound (a p)
      let risA := cVecIsZero n m r1.1 r1.2
      let r2 := cReduceVec n m risA.1 Tfound (b p)
      let risB := cVecIsZero n m r2.1 r2.2
      let rdA := cVecDot n m risB.1 (a p) rz.2
      let rdB := cVecDot n m rdA.1 (b p) rz.2
      let rdAB := cXor n rdB.1 rdA.2 rdB.2
      let rndAB := cNot n rdAB.1 rdAB.2
      let rq1 := cVecAndScalar n m rndAB.1 rdA.2 (b p)
      let rq2 := cVecAndScalar n m rq1.1 rdB.2 (a p)
      let rq3 := cVecAndScalar n m rq2.1 rndAB.2 (a p)
      let rq23 := cVecMux n m rq3.1 risB.2 rq2.2 rq3.2
      let rqLin := cVecMux n m rq23.1 risA.2 rq1.2 rq23.2
      let rv := cVecXor n m rqLin.1 (L p) rqLin.2
      let rrhs := cXor n rv.1 (wanted p) (baseP p)
      cAugInsert n m rrhs.1 A rv.2 rrhs.2)
    (fun x A p =>
      let isA := vecIsZero (reduceVec (evalPivot g x Tfound) (evalVec g x (a p)))
      let isB := vecIsZero (reduceVec (evalPivot g x Tfound) (evalVec g x (b p)))
      let dA := vecDot (evalVec g x (a p)) (backSub (evalAug g x A_cell))
      let dB := vecDot (evalVec g x (b p)) (backSub (evalAug g x A_cell))
      let dAB := xor dA dB
      let qLin : Vec m :=
        if isA then (fun q => dA && evalVec g x (b p) q)
        else if isB then (fun q => dB && evalVec g x (a p) q)
        else (fun q => !dAB && evalVec g x (a p) q)
      augInsert A (vecXor (evalVec g x (L p)) qLin) (xor (val g x (wanted p)) (val g x (baseP p))))
    (30 * m * m + 49 * m + 16) (List.finRange t) rz.1 A_cell hz.1
    (hAc.mono (by have := hz.2.1.len_le; omega)) (fun g' A p _ hg' hext hA => by
      dsimp only
      have e0g := hz.2.1.trans hext
      have h1 := cReduceVec_spec hn g' hg' Tfound (a p) (hTf.mono (by have := e0g.len_le; omega)) ((ha p).mono (by have := e0g.len_le; omega))
      set r1 := cReduceVec n m g' Tfound (a p)
      have hisA := cVecIsZero_spec hn r1.1 h1.1 r1.2 h1.2.2.2.1
      set risA := cVecIsZero n m r1.1 r1.2
      have eg_isA := h1.2.1.trans hisA.2.1
      have h2 := cReduceVec_spec hn risA.1 hisA.1 Tfound (b p)
        (hTf.mono (by have := (e0g.trans eg_isA).len_le; omega)) ((hb p).mono (by have := (e0g.trans eg_isA).len_le; omega))
      set r2 := cReduceVec n m risA.1 Tfound (b p)
      have hisB := cVecIsZero_spec hn r2.1 h2.1 r2.2 h2.2.2.2.1
      set risB := cVecIsZero n m r2.1 r2.2
      have eg_isB := eg_isA.trans (h2.2.1.trans hisB.2.1)
      have hdA := cVecDot_spec hn risB.1 hisB.1 (a p) rz.2
        ((ha p).mono (by have := (e0g.trans eg_isB).len_le; omega)) (hz.2.2.2.1.mono (by have := (hext.trans eg_isB).len_le; omega))
      set rdA := cVecDot n m risB.1 (a p) rz.2
      have eg_dA := eg_isB.trans hdA.2.1
      have hdB := cVecDot_spec hn rdA.1 hdA.1 (b p) rz.2
        ((hb p).mono (by have := (e0g.trans eg_dA).len_le; omega)) (hz.2.2.2.1.mono (by have := (hext.trans eg_dA).len_le; omega))
      set rdB := cVecDot n m rdA.1 (b p) rz.2
      have hdAB := cXor_spec hn rdB.1 hdB.1 rdA.2 rdB.2 (by have ae := hdB.2.1.len_le; have ad := hdA.2.2.2.1; omega) hdB.2.2.2.1
      set rdAB := cXor n rdB.1 rdA.2 rdB.2
      have hndAB := cNot_spec hn rdAB.1 hdAB.1 rdAB.2 hdAB.2.2.2.1
      set rndAB := cNot n rdAB.1 rdAB.2
      have edA_nd := (hdB.2.1.trans hdAB.2.1).trans hndAB.2.1
      have eg_nd := eg_dA.trans edA_nd
      have hq1 := cVecAndScalar_spec hn rndAB.1 hndAB.1 rdA.2 (b p)
        (by have ae := edA_nd.len_le; have ad := hdA.2.2.2.1; omega) ((hb p).mono (by have := (e0g.trans eg_nd).len_le; omega))
      set rq1 := cVecAndScalar n m rndAB.1 rdA.2 (b p)
      have hq2 := cVecAndScalar_spec hn rq1.1 hq1.1 rdB.2 (a p)
        (by have ae := ((hdAB.2.1.trans hndAB.2.1).trans hq1.2.1).len_le; have ad := hdB.2.2.2.1; omega)
        ((ha p).mono (by have := ((e0g.trans eg_nd).trans hq1.2.1).len_le; omega))
      set rq2 := cVecAndScalar n m rq1.1 rdB.2 (a p)
      have hq3 := cVecAndScalar_spec hn rq2.1 hq2.1 rndAB.2 (a p)
        (by have ae := (hq1.2.1.trans hq2.2.1).len_le; have ad := hndAB.2.2.2.1; omega)
        ((ha p).mono (by have := (((e0g.trans eg_nd).trans hq1.2.1).trans hq2.2.1).len_le; omega))
      set rq3 := cVecAndScalar n m rq2.1 rndAB.2 (a p)
      have eisB_q3 := (((hdA.2.1.trans edA_nd).trans hq1.2.1).trans hq2.2.1).trans hq3.2.1
      have hq23 := cVecMux_spec hn rq3.1 hq3.1 risB.2 rq2.2 rq3.2
        (by have ae := eisB_q3.len_le; have ab := hisB.2.2.2.1; omega)
        (hq2.2.2.2.1.mono (by have := hq3.2.1.len_le; omega)) hq3.2.2.2.1
      set rq23 := cVecMux n m rq3.1 risB.2 rq2.2 rq3.2
      have eisA_q23 := ((h2.2.1.trans hisB.2.1).trans eisB_q3).trans hq23.2.1
      have hqLin := cVecMux_spec hn rq23.1 hq23.1 risA.2 rq1.2 rq23.2
        (by have ae := eisA_q23.len_le; have aa := hisA.2.2.2.1; omega)
        (hq1.2.2.2.1.mono (by have := ((hq2.2.1.trans hq3.2.1).trans hq23.2.1).len_le; omega)) hq23.2.2.2.1
      set rqLin := cVecMux n m rq23.1 risA.2 rq1.2 rq23.2
      have eg_qLin := eg_isA.trans (eisA_q23.trans hqLin.2.1)
      have hv := cVecXor_spec hn rqLin.1 hqLin.1 (L p) rqLin.2
        ((hL p).mono (by have := (e0g.trans eg_qLin).len_le; omega)) hqLin.2.2.2.1
      set rv := cVecXor n m rqLin.1 (L p) rqLin.2
      have hrhs := cXor_spec hn rv.1 hv.1 (wanted p) (baseP p)
        (by have ae := ((e0g.trans eg_qLin).trans hv.2.1).len_le; have aw := hw p; omega)
        (by have ae := ((e0g.trans eg_qLin).trans hv.2.1).len_le; have ab := hbp p; omega)
      set rrhs := cXor n rv.1 (wanted p) (baseP p)
      have eg_rhs := (eg_qLin.trans hv.2.1).trans hrhs.2.1
      have hins := cAugInsert_spec hn rrhs.1 hrhs.1 A rv.2 rrhs.2
        (hA.mono (by have := eg_rhs.len_le; omega)) (hv.2.2.2.1.mono (by have := hrhs.2.1.len_le; omega)) hrhs.2.2.2.1
      refine ⟨hins.1, eg_rhs.trans hins.2.1, ?_, hins.2.2.2.1, fun x hx => ?_⟩
      · have b1 := h1.2.2.1; have b2 := hisA.2.2.1; have b3 := h2.2.2.1; have b4 := hisB.2.2.1
        have b5 := hdA.2.2.1; have b6 := hdB.2.2.1; have b7 := hdAB.2.2.1; have b8 := hndAB.2.2.1
        have b9 := hq1.2.2.1; have b10 := hq2.2.2.1; have b11 := hq3.2.2.1; have b12 := hq23.2.2.1
        have b13 := hqLin.2.2.1; have b14 := hv.2.2.1; have b15 := hrhs.2.2.1; have b16 := hins.2.2.1
        have eq1 : m * (8 * m + 1) + (2 * m + 1) + m * (8 * m + 1) + (2 * m + 1) + (5 * m + 1) + (5 * m + 1) +
            4 + 1 + m + m + m + 4 * m + 4 * m + 4 * m + 4 + (14 * m * m + 18 * m + 3) =
            30 * m * m + 49 * m + 16 := by ring
        omega
      · rw [hins.2.2.2.2 x hx, evalAug_of_extends hx eg_rhs hA, evalVec_of_extends hx hrhs.2.1 hv.2.2.2.1,
          hv.2.2.2.2 x hx, evalVec_of_extends hx (e0g.trans eg_qLin) (hL p),
          hrhs.2.2.2.2 x hx, val_of_extends hx ((e0g.trans eg_qLin).trans hv.2.1) (hw p),
          val_of_extends hx ((e0g.trans eg_qLin).trans hv.2.1) (hbp p)]
        have eisA_v : val risA.1 x risA.2 = vecIsZero (reduceVec (evalPivot g x Tfound) (evalVec g x (a p))) := by
          rw [hisA.2.2.2.2 x hx, h1.2.2.2.2 x hx, evalPivot_of_extends hx e0g hTf, evalVec_of_extends hx e0g (ha p)]
        have eisB_v : val risB.1 x risB.2 = vecIsZero (reduceVec (evalPivot g x Tfound) (evalVec g x (b p))) := by
          rw [hisB.2.2.2.2 x hx, h2.2.2.2.2 x hx, evalPivot_of_extends hx (e0g.trans eg_isA) hTf,
            evalVec_of_extends hx (e0g.trans eg_isA) (hb p)]
        have edA_v : val rdA.1 x rdA.2 = vecDot (evalVec g x (a p)) (backSub (evalAug g x A_cell)) := by
          rw [hdA.2.2.2.2 x hx, evalVec_of_extends hx (e0g.trans eg_isB) (ha p),
            evalVec_of_extends hx (hext.trans eg_isB) hz.2.2.2.1, hz.2.2.2.2 x hx]
        have edB_v : val rdB.1 x rdB.2 = vecDot (evalVec g x (b p)) (backSub (evalAug g x A_cell)) := by
          rw [hdB.2.2.2.2 x hx, evalVec_of_extends hx (e0g.trans eg_dA) (hb p),
            evalVec_of_extends hx (hext.trans eg_dA) hz.2.2.2.1, hz.2.2.2.2 x hx]
        have endAB_v : val rndAB.1 x rndAB.2 = !(xor (vecDot (evalVec g x (a p)) (backSub (evalAug g x A_cell)))
            (vecDot (evalVec g x (b p)) (backSub (evalAug g x A_cell)))) := by
          rw [hndAB.2.2.2.2 x hx, hdAB.2.2.2.2 x hx, val_of_extends hx hdB.2.1 hdA.2.2.2.1, edA_v, edB_v]
        have eq1_v : evalVec rq1.1 x rq1.2 = fun q => vecDot (evalVec g x (a p)) (backSub (evalAug g x A_cell)) && evalVec g x (b p) q := by
          rw [hq1.2.2.2.2 x hx, val_of_extends hx edA_nd hdA.2.2.2.1, edA_v, evalVec_of_extends hx (e0g.trans eg_nd) (hb p)]
        have eq2_v : evalVec rq2.1 x rq2.2 = fun q => vecDot (evalVec g x (b p)) (backSub (evalAug g x A_cell)) && evalVec g x (a p) q := by
          rw [hq2.2.2.2.2 x hx, val_of_extends hx ((hdAB.2.1.trans hndAB.2.1).trans hq1.2.1) hdB.2.2.2.1, edB_v,
            evalVec_of_extends hx ((e0g.trans eg_nd).trans hq1.2.1) (ha p)]
        have eq3_v : evalVec rq3.1 x rq3.2 = fun q => !(xor (vecDot (evalVec g x (a p)) (backSub (evalAug g x A_cell)))
            (vecDot (evalVec g x (b p)) (backSub (evalAug g x A_cell)))) && evalVec g x (a p) q := by
          rw [hq3.2.2.2.2 x hx, val_of_extends hx (hq1.2.1.trans hq2.2.1) hndAB.2.2.2.1, endAB_v,
            evalVec_of_extends hx (((e0g.trans eg_nd).trans hq1.2.1).trans hq2.2.1) (ha p)]
        have eqLin_v : evalVec rqLin.1 x rqLin.2 =
            if vecIsZero (reduceVec (evalPivot g x Tfound) (evalVec g x (a p))) then
              (fun q => vecDot (evalVec g x (a p)) (backSub (evalAug g x A_cell)) && evalVec g x (b p) q)
            else if vecIsZero (reduceVec (evalPivot g x Tfound) (evalVec g x (b p))) then
              (fun q => vecDot (evalVec g x (b p)) (backSub (evalAug g x A_cell)) && evalVec g x (a p) q)
            else (fun q => !(xor (vecDot (evalVec g x (a p)) (backSub (evalAug g x A_cell)))
              (vecDot (evalVec g x (b p)) (backSub (evalAug g x A_cell)))) && evalVec g x (a p) q) := by
          rw [hqLin.2.2.2.2 x hx, val_of_extends hx eisA_q23 hisA.2.2.2.1, eisA_v,
            evalVec_of_extends hx ((hq2.2.1.trans hq3.2.1).trans hq23.2.1) hq1.2.2.2.1, eq1_v,
            hq23.2.2.2.2 x hx, val_of_extends hx eisB_q3 hisB.2.2.2.1, eisB_v,
            evalVec_of_extends hx hq3.2.1 hq2.2.2.2.1, eq2_v, eq3_v]
        rw [eqLin_v])
  set rAsol := cFoldl _ (List.finRange t) rz.1 A_cell
  have hoh := cOneHotCount_spec hn rAsol.1 hfold.1 rAsol.2.piv.hasPiv hfold.2.2.2.1.1.1
  set roh := cOneHotCount n m rAsol.1 rAsol.2.piv.hasPiv
  have hninc := cNot_spec hn roh.1 hoh.1 rAsol.2.inc (by have ae := hoh.2.1.len_le; have ai := hfold.2.2.2.1.2.2; omega)
  set rninc := cNot n roh.1 rAsol.2.inc
  have hout := cBuildFin_spec (n := n) (fun L w => w < L) (fun hL hw => lt_of_lt_of_le hw hL)
    val (fun hx hext hw => val_of_extends hx hext hw) (m + 1) 1
    (fun g' idx => cAnd n g' rninc.2 (roh.2 ⟨m - idx.1, by omega⟩))
    (fun x idx => !((evalAug rAsol.1 x rAsol.2).inc) && oneHotCount (evalAug rAsol.1 x rAsol.2).piv.hasPiv ⟨m - idx.1, by omega⟩)
    rninc.1 hninc.1 (fun g' idx hg' hext => by
      have ha1 := cAnd_spec hn g' hg' rninc.2 (roh.2 ⟨m - idx.1, by omega⟩)
        (by have ae := hext.len_le; have an := hninc.2.2.2.1; omega)
        (by have ae := (hninc.2.1.trans hext).len_le; have ao := hoh.2.2.2.1 ⟨m - idx.1, by omega⟩; omega)
      refine ⟨ha1.1, ha1.2.1, ha1.2.2.1, ha1.2.2.2.1, fun x hx => ?_⟩
      rw [ha1.2.2.2.2 x hx, val_of_extends hx hext hninc.2.2.2.1, hninc.2.2.2.2 x hx,
        val_of_extends hx hoh.2.1 hfold.2.2.2.1.2.2,
        val_of_extends hx (hninc.2.1.trans hext) (hoh.2.2.2.1 ⟨m - idx.1, by omega⟩)]
      have ho := congrFun (hoh.2.2.2.2 x hx) ⟨m - idx.1, by omega⟩
      exact congrArg (!(val rAsol.1 x rAsol.2.inc) && ·) ho)
  refine ⟨hout.1, (((hz.2.1.trans hfold.2.1).trans hoh.2.1).trans hninc.2.1).trans hout.2.1, ?_, hout.2.2.2.1, fun x hx => ?_⟩
  · have a1 := hz.2.2.1; have a2 := hfold.2.2.1; have a3 := hoh.2.2.1; have a4 := hninc.2.2.1; have a5 := hout.2.2.1
    simp only [List.length_finRange, mul_one] at a2 a5
    have hB : (m * (5 * m + 9) + 2 * m) + t * (30 * m * m + 49 * m + 16) +
        ((m + 1) + m * ((m + 1) * 5)) + 1 + (m + 1) ≤ cellNodeBound m t := by
      unfold cellNodeBound
      set S := m + t + 2
      have hS1 : 1 ≤ S := by omega
      have hSm : m ≤ S := by omega
      have hSt : t ≤ S := by omega
      nlinarith [sq_nonneg S,
        mul_le_mul hSm hSm (Nat.zero_le m) (Nat.zero_le S),
        mul_le_mul hSt hSm (Nat.zero_le m) (Nat.zero_le S),
        mul_le_mul hSt (mul_le_mul hSm hSm (Nat.zero_le m) (Nat.zero_le S)) (Nat.zero_le _) (Nat.zero_le S)]
    omega
  · funext idx
    rw [evalVec, hout.2.2.2.2 x hx idx, hfold.2.2.2.2 x hx, evalAug_of_extends hx hz.2.1 hAc]
    rfl

private def cSumCells (n m t : ℕ) (Tfound : PivotW m) (a b L : Fin t → VecW m) (baseP wanted : Fin t → ℕ) :
    (rem : ℕ) → (Fin rem → VecW m) → List Gate → AugW m → List Gate × VecW (m + 1)
  | 0, _, g, A_cell => cFinishCell n m t g Tfound a b L baseP wanted A_cell
  | r + 1, found, g, A_cell =>
    let rf := cFalse n g
    let rA0 := cAugInsert n m rf.1 A_cell (found 0) rf.2
    let rb0 := cSumCells n m t Tfound a b L baseP wanted r (fun i => found i.succ) rA0.1 rA0.2
    let rt := cTrue n rb0.1
    let rA1 := cAugInsert n m rt.1 A_cell (found 0) rt.2
    let rb1 := cSumCells n m t Tfound a b L baseP wanted r (fun i => found i.succ) rA1.1 rA1.2
    cAddBits n (m + 1) rb1.1 rb0.2 rb1.2

private lemma cSumCells_spec {n m t : ℕ} (hn : 0 < n) (Tfound : PivotW m) (a b L : Fin t → VecW m)
    (baseP wanted : Fin t → ℕ) :
    ∀ (rem : ℕ) (found : Fin rem → VecW m) (g : List Gate), GoodCircuit n g → ∀ (A_cell : AugW m),
      ValidPivot (n + g.length) Tfound →
      (∀ p, ValidVec (n + g.length) (a p)) → (∀ p, ValidVec (n + g.length) (b p)) →
      (∀ p, ValidVec (n + g.length) (L p)) →
      (∀ p, baseP p < n + g.length) → (∀ p, wanted p < n + g.length) →
      (∀ i, ValidVec (n + g.length) (found i)) →
      ValidAug (n + g.length) A_cell →
      let res := cSumCells n m t Tfound a b L baseP wanted rem found g A_cell
      GoodCircuit n res.1 ∧ Extends g res.1 ∧
      res.1.length + cellNodeBound m t ≤ g.length + 2 * 2 ^ rem * cellNodeBound m t ∧
      ValidVec (n + res.1.length) res.2 ∧
      ∀ x, x.length = n → evalVec res.1 x res.2 =
        sumCells (evalPivot g x Tfound) (fun p => evalVec g x (a p)) (fun p => evalVec g x (b p))
          (fun p => evalVec g x (L p)) (fun p => val g x (baseP p)) (fun p => val g x (wanted p))
          rem (fun i => evalVec g x (found i)) (evalAug g x A_cell) := by
  intro rem
  induction rem with
  | zero =>
    intro found g hg A_cell hTf ha hb hL hbp hw _ hAc
    dsimp only [cSumCells]
    have h := cFinishCell_spec hn g hg Tfound a b L baseP wanted A_cell hTf ha hb hL hbp hw hAc
    refine ⟨h.1, h.2.1, ?_, h.2.2.2.1, h.2.2.2.2⟩
    have a1 := h.2.2.1; simp only [pow_zero, mul_one]; omega
  | succ r ih =>
    intro found g hg A_cell hTf ha hb hL hbp hw hfd hAc
    dsimp only [cSumCells]
    have hf := cFalse_spec hn g hg
    set rf := cFalse n g
    have hA0 := cAugInsert_spec hn rf.1 hf.1 A_cell (found 0) rf.2
      (hAc.mono (by have := hf.2.1.len_le; omega)) ((hfd 0).mono (by have := hf.2.1.len_le; omega)) hf.2.2.2.1
    set rA0 := cAugInsert n m rf.1 A_cell (found 0) rf.2
    have e0_A0 := hf.2.1.trans hA0.2.1
    have hb0 := ih (fun i => found i.succ) rA0.1 hA0.1 rA0.2
      (hTf.mono (by have := e0_A0.len_le; omega))
      (fun p => (ha p).mono (by have := e0_A0.len_le; omega))
      (fun p => (hb p).mono (by have := e0_A0.len_le; omega))
      (fun p => (hL p).mono (by have := e0_A0.len_le; omega))
      (fun p => by have ae := e0_A0.len_le; have ab := hbp p; omega)
      (fun p => by have ae := e0_A0.len_le; have aw := hw p; omega)
      (fun i => (hfd i.succ).mono (by have := e0_A0.len_le; omega)) hA0.2.2.2.1
    set rb0 := cSumCells n m t Tfound a b L baseP wanted r (fun i => found i.succ) rA0.1 rA0.2
    have e0_b0 := e0_A0.trans hb0.2.1
    have ht := cTrue_spec hn rb0.1 hb0.1
    set rt := cTrue n rb0.1
    have e0_t := e0_b0.trans ht.2.1
    have hA1 := cAugInsert_spec hn rt.1 ht.1 A_cell (found 0) rt.2
      (hAc.mono (by have := e0_t.len_le; omega)) ((hfd 0).mono (by have := e0_t.len_le; omega)) ht.2.2.2.1
    set rA1 := cAugInsert n m rt.1 A_cell (found 0) rt.2
    have e0_A1 := e0_t.trans hA1.2.1
    have hb1 := ih (fun i => found i.succ) rA1.1 hA1.1 rA1.2
      (hTf.mono (by have := e0_A1.len_le; omega))
      (fun p => (ha p).mono (by have := e0_A1.len_le; omega))
      (fun p => (hb p).mono (by have := e0_A1.len_le; omega))
      (fun p => (hL p).mono (by have := e0_A1.len_le; omega))
      (fun p => by have ae := e0_A1.len_le; have ab := hbp p; omega)
      (fun p => by have ae := e0_A1.len_le; have aw := hw p; omega)
      (fun i => (hfd i.succ).mono (by have := e0_A1.len_le; omega)) hA1.2.2.2.1
    set rb1 := cSumCells n m t Tfound a b L baseP wanted r (fun i => found i.succ) rA1.1 rA1.2
    have eb0_b1 := (ht.2.1.trans hA1.2.1).trans hb1.2.1
    have hadd := cAddBits_spec hn rb1.1 hb1.1 rb0.2 rb1.2
      (hb0.2.2.2.1.mono (by have := eb0_b1.len_le; omega)) hb1.2.2.2.1
    refine ⟨hadd.1, (e0_A1.trans hb1.2.1).trans hadd.2.1, ?_, hadd.2.2.2.1, fun x hx => ?_⟩
    · have a1 := hf.2.2.1; have a2 := hA0.2.2.1; have a3 := hb0.2.2.1
      have a4 := ht.2.2.1; have a5 := hA1.2.2.1; have a6 := hb1.2.2.1; have a7 := hadd.2.2.1
      have hov : 1 + (14 * m * m + 18 * m + 3) + 1 + (14 * m * m + 18 * m + 3) + (11 * (m + 1) + 1) ≤
          cellNodeBound m t := by
        unfold cellNodeBound
        set S := m + t + 2
        have hS1 : 1 ≤ S := by omega
        have hSm : m ≤ S := by omega
        nlinarith [sq_nonneg S, mul_le_mul hSm hSm (Nat.zero_le m) (Nat.zero_le S)]
      have hpow : 2 * 2 ^ (r + 1) * cellNodeBound m t =
          2 * 2 ^ r * cellNodeBound m t + 2 * 2 ^ r * cellNodeBound m t := by ring
      rw [hpow]
      omega
    · rw [hadd.2.2.2.2 x hx, evalVec_of_extends hx eb0_b1 hb0.2.2.2.1, hb0.2.2.2.2 x hx, hb1.2.2.2.2 x hx,
        hA0.2.2.2.2 x hx, evalAug_of_extends hx hf.2.1 hAc, evalVec_of_extends hx hf.2.1 (hfd 0), hf.2.2.2.2 x hx,
        hA1.2.2.2.2 x hx, evalAug_of_extends hx e0_t hAc, evalVec_of_extends hx e0_t (hfd 0), ht.2.2.2.2 x hx,
        evalPivot_of_extends hx e0_A0 hTf, evalPivot_of_extends hx e0_A1 hTf]
      have ha0 : (fun p => evalVec rA0.1 x (a p)) = fun p => evalVec g x (a p) := funext fun p => evalVec_of_extends hx e0_A0 (ha p)
      have hb0' : (fun p => evalVec rA0.1 x (b p)) = fun p => evalVec g x (b p) := funext fun p => evalVec_of_extends hx e0_A0 (hb p)
      have hL0 : (fun p => evalVec rA0.1 x (L p)) = fun p => evalVec g x (L p) := funext fun p => evalVec_of_extends hx e0_A0 (hL p)
      have hbp0 : (fun p => val rA0.1 x (baseP p)) = fun p => val g x (baseP p) := funext fun p => val_of_extends hx e0_A0 (hbp p)
      have hw0 : (fun p => val rA0.1 x (wanted p)) = fun p => val g x (wanted p) := funext fun p => val_of_extends hx e0_A0 (hw p)
      have hfd0 : (fun i : Fin r => evalVec rA0.1 x (found i.succ)) = fun i : Fin r => evalVec g x (found i.succ) := funext fun i => evalVec_of_extends hx e0_A0 (hfd i.succ)
      have ha1 : (fun p => evalVec rA1.1 x (a p)) = fun p => evalVec g x (a p) := funext fun p => evalVec_of_extends hx e0_A1 (ha p)
      have hb1' : (fun p => evalVec rA1.1 x (b p)) = fun p => evalVec g x (b p) := funext fun p => evalVec_of_extends hx e0_A1 (hb p)
      have hL1 : (fun p => evalVec rA1.1 x (L p)) = fun p => evalVec g x (L p) := funext fun p => evalVec_of_extends hx e0_A1 (hL p)
      have hbp1 : (fun p => val rA1.1 x (baseP p)) = fun p => val g x (baseP p) := funext fun p => val_of_extends hx e0_A1 (hbp p)
      have hw1 : (fun p => val rA1.1 x (wanted p)) = fun p => val g x (wanted p) := funext fun p => val_of_extends hx e0_A1 (hw p)
      have hfd1 : (fun i : Fin r => evalVec rA1.1 x (found i.succ)) = fun i : Fin r => evalVec g x (found i.succ) := funext fun i => evalVec_of_extends hx e0_A1 (hfd i.succ)
      rw [ha0, hb0', hL0, hbp0, hw0, hfd0, ha1, hb1', hL1, hbp1, hw1, hfd1]
      rfl

-- Generator rank table & right shift circuits
private def cGenRankTable (n k m : ℕ) (g : List Gate) (genV : Fin m → VecW k) : List Gate × PivotW k :=
  let r0 := cPivotEmpty n k g
  cFoldl (fun g' T j => cInsertVec n k g' T (genV j)) (List.finRange m) r0.1 r0.2

private lemma cGenRankTable_spec {n k m : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (genV : Fin m → VecW k) (hgen : ∀ j, ValidVec (n + g.length) (genV j)) :
    let res := cGenRankTable n k m g genV
    GoodCircuit n res.1 ∧ Extends g res.1 ∧
    res.1.length ≤ g.length + ((k * k + k) + m * (14 * k * k + 4 * k)) ∧
    ValidPivot (n + res.1.length) res.2 ∧
    ∀ x, x.length = n → evalPivot res.1 x res.2 = genRankTable (fun j => evalVec g x (genV j)) := by
  dsimp only [cGenRankTable]
  have h0 := cPivotEmpty_spec hn (m := k) g hg
  set r0 := cPivotEmpty n k g
  have hf := cFoldl_spec (n := n) ValidPivot evalPivot
    (fun g' T j => cInsertVec n k g' T (genV j))
    (fun x T j => insertVec T (evalVec g x (genV j)))
    (14 * k * k + 4 * k) (List.finRange m) r0.1 r0.2 h0.1 h0.2.2.2.1 (fun g' T j _ hg' hext hT => by
      have hi := cInsertVec_spec hn g' hg' T (genV j) hT ((hgen j).mono (by have := (h0.2.1.trans hext).len_le; omega))
      refine ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, fun x hx => ?_⟩
      rw [hi.2.2.2.2 x hx, evalVec_of_extends hx (h0.2.1.trans hext) (hgen j)])
  refine ⟨hf.1, h0.2.1.trans hf.2.1, ?_, hf.2.2.2.1, fun x hx => ?_⟩
  · have a0 := h0.2.2.1; have af := hf.2.2.1; simp only [List.length_finRange] at af; omega
  · rw [hf.2.2.2.2 x hx, h0.2.2.2.2 x hx]; rfl

private def cShiftRightBits (n k m : ℕ) (g : List Gate) (totalX : VecW (m + 1)) (ohGen : VecW (k + 1)) :
    List Gate × VecW (k + 1) :=
  cBuildFin (k + 1) (fun g' o =>
    let r0 := cFalse n g'
    cFoldl (fun g'' acc r =>
      if h : o.1 + (m - r.1) < m + 1 then
        let r1 := cAnd n g'' (ohGen r) (totalX ⟨o.1 + (m - r.1), h⟩)
        cOr n r1.1 acc r1.2
      else (g'', acc)) (List.finRange (k + 1)) r0.1 r0.2) g

private lemma cShiftRightBits_spec {n k m : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (totalX : VecW (m + 1)) (ohGen : VecW (k + 1))
    (htx : ValidVec (n + g.length) totalX) (hoh : ValidVec (n + g.length) ohGen) :
    let res := cShiftRightBits n k m g totalX ohGen
    GoodCircuit n res.1 ∧ Extends g res.1 ∧ res.1.length ≤ g.length + (k + 1) * (1 + (k + 1) * 2) ∧
    ValidVec (n + res.1.length) res.2 ∧
    ∀ x, x.length = n → evalVec res.1 x res.2 = shiftRightBits (evalVec g x totalX) (evalVec g x ohGen) := by
  dsimp only [cShiftRightBits]
  have hb := cBuildFin_spec (n := n) (fun L w => w < L) (fun hL hw => lt_of_lt_of_le hw hL)
    val (fun hx hext hw => val_of_extends hx hext hw) (k + 1) (1 + (k + 1) * 2)
    (fun g' o =>
      let r0 := cFalse n g'
      cFoldl (fun g'' acc r =>
        if h : o.1 + (m - r.1) < m + 1 then
          let r1 := cAnd n g'' (ohGen r) (totalX ⟨o.1 + (m - r.1), h⟩)
          cOr n r1.1 acc r1.2
        else (g'', acc)) (List.finRange (k + 1)) r0.1 r0.2)
    (fun x o => shiftRightBits (evalVec g x totalX) (evalVec g x ohGen) o) g hg (fun g' o hg' hext => by
      have h0 := cFalse_spec hn g' hg'
      set r0 := cFalse n g'
      have hf := cFoldl_spec (n := n) (fun L w => w < L) val
        (fun g'' acc r =>
          if h : o.1 + (m - r.1) < m + 1 then
            let r1 := cAnd n g'' (ohGen r) (totalX ⟨o.1 + (m - r.1), h⟩)
            cOr n r1.1 acc r1.2
          else (g'', acc))
        (fun x acc r => acc || (val g x (ohGen r) &&
          if h : o.1 + (m - r.1) < m + 1 then val g x (totalX ⟨o.1 + (m - r.1), h⟩) else false))
        2 (List.finRange (k + 1)) r0.1 r0.2 h0.1 h0.2.2.2.1 (fun g'' acc r _ hg'' hext' hacc => by
          by_cases hlt : o.1 + (m - r.1) < m + 1
          · simp only [hlt, ↓reduceDIte]
            have e0'' := hext.trans (h0.2.1.trans hext')
            have h1 := cAnd_spec hn g'' hg'' (ohGen r) (totalX ⟨o.1 + (m - r.1), hlt⟩)
              (by have ae := e0''.len_le; have ao := hoh r; omega)
              (by have ae := e0''.len_le; have atx := htx ⟨o.1 + (m - r.1), hlt⟩; omega)
            set r1 := cAnd n g'' (ohGen r) (totalX ⟨o.1 + (m - r.1), hlt⟩)
            have h2 := cOr_spec hn r1.1 h1.1 acc r1.2 (by have ae := h1.2.1.len_le; omega) h1.2.2.2.1
            refine ⟨h2.1, h1.2.1.trans h2.2.1, by have a1 := h1.2.2.1; have a2 := h2.2.2.1; omega, h2.2.2.2.1, fun x hx => ?_⟩
            rw [h2.2.2.2.2 x hx, val_of_extends hx h1.2.1 hacc, h1.2.2.2.2 x hx,
              val_of_extends hx e0'' (hoh r), val_of_extends hx e0'' (htx ⟨o.1 + (m - r.1), hlt⟩)]
          · simp only [hlt, ↓reduceDIte]
            exact ⟨hg'', Extends.refl g'', by omega, hacc, fun _ _ => by simp⟩)
      refine ⟨hf.1, h0.2.1.trans hf.2.1, ?_, hf.2.2.2.1, fun x hx => ?_⟩
      · dsimp only; have a0 := h0.2.2.1; have af := hf.2.2.1; simp only [List.length_finRange] at af; omega
      · rw [hf.2.2.2.2 x hx, h0.2.2.2.2 x hx]; rfl)
  exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, fun x hx => funext fun o => hb.2.2.2.2 x hx o⟩

-- ============================================================================
-- Section 4: Input Bit Unpacking, Precomputation & Final Assembly
-- ============================================================================

private lemma decide_ne_zero_eq_z2b (x : K) : decide (x ≠ 0) = z2b x := by
  fin_cases x <;> rfl

private lemma list_getD_append_right {α : Type} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

private lemma list_ofFn_getD {α : Type} {k : ℕ} (f : Fin k → α) (j : Fin k) (d : α) :
    (List.ofFn f).getD j.1 d = f j := by
  simp [List.getD_eq_getElem?_getD, j.2]

private lemma flatten_ofFn_length {α : Type} {m k : ℕ} :
    ∀ (f : Fin m → List α), (∀ h, (f h).length = k) →
      (List.ofFn f).flatten.length = m * k := by
  induction m with
  | zero => intro _ _; simp
  | succ m ih =>
    intro f hlen
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hlen 0, ih (fun h => f h.succ) (fun h => hlen h.succ)]
    ring

private lemma list_getD_append_mid {α : Type} (l1 l2 l3 : List α) (i : ℕ) (d : α)
    (h1 : l1.length ≤ i) (h2 : i - l1.length < l2.length) :
    (l1 ++ l2 ++ l3).getD i d = l2.getD (i - l1.length) d := by
  rw [list_getD_append_left _ _ _ _ (by rw [List.length_append]; omega), list_getD_append_right _ _ _ _ h1]

private lemma flatten_ofFn_getD {α : Type} {m k : ℕ} (f : Fin m → List α)
    (hlen : ∀ h, (f h).length = k) (h : Fin m) (j : Fin k) (d : α) :
    (List.ofFn f).flatten.getD (h.1 * k + j.1) d = (f h).getD j.1 d := by
  induction m with
  | zero => exact h.elim0
  | succ m ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ (fun h' => ?_) h
    · simp only [Fin.val_zero, zero_mul, zero_add]
      rw [list_getD_append_left _ _ _ _ (by rw [hlen 0]; exact j.2)]
    · have hge : (f 0).length ≤ (h'.succ).1 * k + j.1 := by
        rw [hlen 0]; simp only [Fin.val_succ]
        have : (h'.1 + 1) * k = h'.1 * k + k := by ring
        omega
      rw [list_getD_append_right _ _ _ _ hge, hlen 0]
      have hsub : (h'.succ).1 * k + j.1 - k = h'.1 * k + j.1 := by
        simp only [Fin.val_succ]
        have : (h'.1 + 1) * k = h'.1 * k + k := by ring
        omega
      rw [hsub]
      exact ih (fun i => f i.succ) (fun i => hlen i.succ) h'

private def baseW {k : ℕ} (j : Fin k) : ℕ := j.1
private def genW {k m : ℕ} (h : Fin m) (j : Fin k) : ℕ := k + h.1 * k + j.1
private def uW {k : ℕ} (m : ℕ) (j : Fin k) : ℕ := (m + 1) * k + j.1
private def vW {k : ℕ} (m : ℕ) (j : Fin k) : ℕ := (m + 2) * k + j.1
private def crW {k : ℕ} (m : ℕ) (j : Fin k) : ℕ := (m + 3) * k + j.1
private def ccW {k : ℕ} (m : ℕ) (j : Fin k) : ℕ := (m + 4) * k + j.1
private def wantedW {t : ℕ} (k m : ℕ) (p : Fin t) : ℕ := (m + 5) * k + p.1

-- Input precomputation helpers
private def cXor3 (n : ℕ) (g : List Gate) (w1 w2 w3 : ℕ) : List Gate × ℕ :=
  let r1 := cXor n g w1 w2
  cXor n r1.1 r1.2 w3

private lemma cXor3_spec {n : ℕ} (hn : 0 < n) (g : List Gate) (hg : GoodCircuit n g)
    (w1 w2 w3 : ℕ) (h1 : w1 < n + g.length) (h2 : w2 < n + g.length) (h3 : w3 < n + g.length) :
    let res := cXor3 n g w1 w2 w3
    GoodCircuit n res.1 ∧ Extends g res.1 ∧ res.1.length ≤ g.length + 8 ∧ res.2 < n + res.1.length ∧
    ∀ x, x.length = n → val res.1 x res.2 = xor (xor (val g x w1) (val g x w2)) (val g x w3) := by
  dsimp only [cXor3]
  have ha := cXor_spec hn g hg w1 w2 h1 h2
  set r1 := cXor n g w1 w2
  have hb := cXor_spec hn r1.1 ha.1 r1.2 w3 ha.2.2.2.1 (by have ae := ha.2.1.len_le; omega)
  refine ⟨hb.1, ha.2.1.trans hb.2.1, by have a1 := ha.2.2.1; have a2 := hb.2.2.1; omega, hb.2.2.2.1, fun x hx => ?_⟩
  rw [hb.2.2.2.2 x hx, ha.2.2.2.2 x hx, val_of_extends hx ha.2.1 h3]

private def cMixed0At {k : ℕ} (n : ℕ) (hk : 0 < k) (d s : ℕ) (wW : VecW k) (mid : Fin k) (g : List Gate) :
    List Gate × ℕ :=
  let m1 := ixAux k hk (mid.val + d)
  let m2 := ixAux k hk (mid.val + k - d % k)
  let j0 := ixAux k hk (mid.val + k - s % k)
  let j1 := ixAux k hk (m1.val + k - s % k)
  let j2 := ixAux k hk (m2.val + k - s % k)
  cXor3 n g (wW j0) (wW j1) (wW j2)

private lemma cMixed0At_spec {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (d s : ℕ) (wW : VecW k) (mid : Fin k)
    (g : List Gate) (hg : GoodCircuit n g) (hw : ValidVec (n + g.length) wW) :
    let res := cMixed0At n hk d s wW mid g
    GoodCircuit n res.1 ∧ Extends g res.1 ∧ res.1.length ≤ g.length + 8 ∧ res.2 < n + res.1.length ∧
    ∀ x, x.length = n → b2z (val res.1 x res.2) = mixedAux hk d s (vecToK (evalVec g x wW)) 0 mid := by
  dsimp only [cMixed0At]
  let j0 := ixAux k hk (mid.val + k - s % k)
  let j1 := ixAux k hk ((ixAux k hk (mid.val + d)).val + k - s % k)
  let j2 := ixAux k hk ((ixAux k hk (mid.val + k - d % k)).val + k - s % k)
  have h := cXor3_spec hn g hg (wW j0) (wW j1) (wW j2) (hw j0) (hw j1) (hw j2)
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun x hx => ?_⟩
  rw [h.2.2.2.2 x hx, b2z_xor, b2z_xor]
  simp only [mixedAux, rotAux, Pi.add_apply, Pi.zero_apply, add_zero, vecToK, evalVec, j0, j1, j2]

private def cMixedAt {k : ℕ} (n : ℕ) (hk : 0 < k) (d s : ℕ) (wW nameW : VecW k) (mid : Fin k) (g : List Gate) :
    List Gate × ℕ :=
  let m1 := ixAux k hk (mid.val + d)
  let m2 := ixAux k hk (mid.val + k - d % k)
  let r0 := cXor n g (wW (ixAux k hk (mid.val + k - s % k))) (nameW mid)
  let r1 := cXor n r0.1 (wW (ixAux k hk (m1.val + k - s % k))) (nameW m1)
  let r2 := cXor n r1.1 (wW (ixAux k hk (m2.val + k - s % k))) (nameW m2)
  cXor3 n r2.1 r0.2 r1.2 r2.2

private lemma cMixedAt_spec {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (d s : ℕ) (wW nameW : VecW k) (mid : Fin k)
    (g : List Gate) (hg : GoodCircuit n g)
    (hw : ValidVec (n + g.length) wW) (hnm : ValidVec (n + g.length) nameW) :
    let res := cMixedAt n hk d s wW nameW mid g
    GoodCircuit n res.1 ∧ Extends g res.1 ∧ res.1.length ≤ g.length + 20 ∧ res.2 < n + res.1.length ∧
    ∀ x, x.length = n → b2z (val res.1 x res.2) = mixedAux hk d s (vecToK (evalVec g x wW)) (vecToK (evalVec g x nameW)) mid := by
  dsimp only [cMixedAt]
  set m1 := ixAux k hk (mid.val + d)
  set m2 := ixAux k hk (mid.val + k - d % k)
  set j0 := ixAux k hk (mid.val + k - s % k)
  set j1 := ixAux k hk (m1.val + k - s % k)
  set j2 := ixAux k hk (m2.val + k - s % k)
  have h0 := cXor_spec hn g hg (wW j0) (nameW mid) (hw j0) (hnm mid)
  set r0 := cXor n g (wW j0) (nameW mid)
  have h1 := cXor_spec hn r0.1 h0.1 (wW j1) (nameW m1)
    (by have ae := h0.2.1.len_le; have aw := hw j1; omega)
    (by have ae := h0.2.1.len_le; have an := hnm m1; omega)
  set r1 := cXor n r0.1 (wW j1) (nameW m1)
  have h2 := cXor_spec hn r1.1 h1.1 (wW j2) (nameW m2)
    (by have ae := (h0.2.1.trans h1.2.1).len_le; have aw := hw j2; omega)
    (by have ae := (h0.2.1.trans h1.2.1).len_le; have an := hnm m2; omega)
  set r2 := cXor n r1.1 (wW j2) (nameW m2)
  have h3 := cXor3_spec hn r2.1 h2.1 r0.2 r1.2 r2.2
    (by have ae := (h1.2.1.trans h2.2.1).len_le; have a0 := h0.2.2.2.1; omega)
    (by have ae := h2.2.1.len_le; have a1 := h1.2.2.2.1; omega) h2.2.2.2.1
  refine ⟨h3.1, ((h0.2.1.trans h1.2.1).trans h2.2.1).trans h3.2.1,
    by have a0 := h0.2.2.1; have a1 := h1.2.2.1; have a2 := h2.2.2.1; have a3 := h3.2.2.1; omega,
    h3.2.2.2.1, fun x hx => ?_⟩
  rw [h3.2.2.2.2 x hx, b2z_xor, b2z_xor,
    val_of_extends hx (h1.2.1.trans h2.2.1) h0.2.2.2.1, h0.2.2.2.2 x hx,
    val_of_extends hx h2.2.1 h1.2.2.2.1, h1.2.2.2.2 x hx,
    val_of_extends hx h0.2.1 (hw j1), val_of_extends hx h0.2.1 (hnm m1),
    h2.2.2.2.2 x hx, val_of_extends hx (h0.2.1.trans h1.2.1) (hw j2), val_of_extends hx (h0.2.1.trans h1.2.1) (hnm m2),
    b2z_xor, b2z_xor, b2z_xor]
  simp only [mixedAux, rotAux, Pi.add_apply, vecToK, evalVec, m1, m2, j0, j1, j2]

private def cBaseProbe {k t : ℕ} (n : ℕ) (hk : 0 < k) (site : Fin t → Fin k) (col : Fin t → Bool)
    (baseW uW vW crW ccW : VecW k) (p : Fin t) (g : List Gate) : List Gate × ℕ :=
  let sp := if col p then 2 else 1
  let st := if col p then 3 else 1
  let inj := if col p then 4 else 0
  let nmW := if col p then vW else uW
  let cW := if col p then ccW else crW
  let j := site p
  let j1 := ixAux k hk (j.val + 1)
  let j2 := ixAux k hk (j.val + 2)
  let ry0 := cMixedAt n hk sp st baseW nmW j g
  let ry1 := cMixedAt n hk sp st baseW nmW j1 ry0.1
  let ry2 := cMixedAt n hk sp st baseW nmW j2 ry1.1
  let rny1 := cNot n ry2.1 ry1.2
  let rprod := cAnd n rny1.1 rny1.2 ry2.2
  let rs1 := cXor n rprod.1 ry0.2 rprod.2
  let rs2 := cXor n rs1.1 rs1.2 (baseW (ixAux k hk (j.val + k - inj % k)))
  cXor n rs2.1 rs2.2 (cW j)

private lemma cBaseProbe_spec {n k t : ℕ} (hn : 0 < n) (hk : 0 < k) (site : Fin t → Fin k) (col : Fin t → Bool)
    (baseW uW vW crW ccW : VecW k) (p : Fin t) (g : List Gate) (hg : GoodCircuit n g)
    (hbase : ValidVec (n + g.length) baseW) (hu : ValidVec (n + g.length) uW) (hv : ValidVec (n + g.length) vW)
    (hcr : ValidVec (n + g.length) crW) (hcc : ValidVec (n + g.length) ccW) :
    let res := cBaseProbe n hk site col baseW uW vW crW ccW p g
    GoodCircuit n res.1 ∧ Extends g res.1 ∧ res.1.length ≤ g.length + 74 ∧ res.2 < n + res.1.length ∧
    ∀ x, x.length = n → b2z (val res.1 x res.2) =
      probeAux hk site col (vecToK (evalVec g x uW)) (vecToK (evalVec g x vW))
        (vecToK (evalVec g x crW)) (vecToK (evalVec g x ccW)) (vecToK (evalVec g x baseW)) p := by
  dsimp only [cBaseProbe]
  set sp := if col p then 2 else 1
  set st := if col p then 3 else 1
  set inj := if col p then 4 else 0
  set nmW := if col p then vW else uW
  set cW := if col p then ccW else crW
  have hnm : ValidVec (n + g.length) nmW := by dsimp only [nmW]; split_ifs <;> assumption
  have hcW : ValidVec (n + g.length) cW := by dsimp only [cW]; split_ifs <;> assumption
  have hy0 := cMixedAt_spec hn hk sp st baseW nmW (site p) g hg hbase hnm
  set ry0 := cMixedAt n hk sp st baseW nmW (site p) g
  have hy1 := cMixedAt_spec hn hk sp st baseW nmW (ixAux k hk ((site p).val + 1)) ry0.1 hy0.1
    (hbase.mono (by have := hy0.2.1.len_le; omega)) (hnm.mono (by have := hy0.2.1.len_le; omega))
  set ry1 := cMixedAt n hk sp st baseW nmW (ixAux k hk ((site p).val + 1)) ry0.1
  have hy2 := cMixedAt_spec hn hk sp st baseW nmW (ixAux k hk ((site p).val + 2)) ry1.1 hy1.1
    (hbase.mono (by have := (hy0.2.1.trans hy1.2.1).len_le; omega))
    (hnm.mono (by have := (hy0.2.1.trans hy1.2.1).len_le; omega))
  set ry2 := cMixedAt n hk sp st baseW nmW (ixAux k hk ((site p).val + 2)) ry1.1
  have hny1 := cNot_spec hn ry2.1 hy2.1 ry1.2 (by have ae := hy2.2.1.len_le; have a1 := hy1.2.2.2.1; omega)
  set rny1 := cNot n ry2.1 ry1.2
  have hprod := cAnd_spec hn rny1.1 hny1.1 rny1.2 ry2.2 hny1.2.2.2.1
    (by have ae := hny1.2.1.len_le; have a2 := hy2.2.2.2.1; omega)
  set rprod := cAnd n rny1.1 rny1.2 ry2.2
  have ey0_p := ((hy1.2.1.trans hy2.2.1).trans hny1.2.1).trans hprod.2.1
  have hs1 := cXor_spec hn rprod.1 hprod.1 ry0.2 rprod.2 (by have ae := ey0_p.len_le; have a0 := hy0.2.2.2.1; omega) hprod.2.2.2.1
  set rs1 := cXor n rprod.1 ry0.2 rprod.2
  have e0_s1 := (hy0.2.1.trans ey0_p).trans hs1.2.1
  set jInj := ixAux k hk ((site p).val + k - inj % k)
  have hs2 := cXor_spec hn rs1.1 hs1.1 rs1.2 (baseW jInj) hs1.2.2.2.1
    (by have ae := e0_s1.len_le; have ab := hbase jInj; omega)
  set rs2 := cXor n rs1.1 rs1.2 (baseW jInj)
  have hs3 := cXor_spec hn rs2.1 hs2.1 rs2.2 (cW (site p)) hs2.2.2.2.1
    (by have ae := (e0_s1.trans hs2.2.1).len_le; have ac := hcW (site p); omega)
  refine ⟨hs3.1, (e0_s1.trans hs2.2.1).trans hs3.2.1,
    by have a1 := hy0.2.2.1; have a2 := hy1.2.2.1; have a3 := hy2.2.2.1; have a4 := hny1.2.2.1
       have a5 := hprod.2.2.1; have a6 := hs1.2.2.1; have a7 := hs2.2.2.1; have a8 := hs3.2.2.1; omega,
    hs3.2.2.2.1, fun x hx => ?_⟩
  rw [hs3.2.2.2.2 x hx, b2z_xor, hs2.2.2.2.2 x hx, b2z_xor, hs1.2.2.2.2 x hx, b2z_xor,
    val_of_extends hx ey0_p hy0.2.2.2.1, hy0.2.2.2.2 x hx,
    hprod.2.2.2.2 x hx, b2z_and, hny1.2.2.2.2 x hx, b2z_not,
    val_of_extends hx hy2.2.1 hy1.2.2.2.1, hy1.2.2.2.2 x hx,
    val_of_extends hx hny1.2.1 hy2.2.2.2.1, hy2.2.2.2.2 x hx,
    evalVec_of_extends hx hy0.2.1 hbase, evalVec_of_extends hx hy0.2.1 hnm,
    evalVec_of_extends hx (hy0.2.1.trans hy1.2.1) hbase, evalVec_of_extends hx (hy0.2.1.trans hy1.2.1) hnm,
    val_of_extends hx e0_s1 (hbase jInj), val_of_extends hx (e0_s1.trans hs2.2.1) (hcW (site p))]
  have hnm_e : vecToK (evalVec g x nmW) = if col p then vecToK (evalVec g x vW) else vecToK (evalVec g x uW) := by
    dsimp only [nmW]; split_ifs <;> rfl
  have hc_e : b2z (val g x (cW (site p))) = if col p then vecToK (evalVec g x ccW) (site p) else vecToK (evalVec g x crW) (site p) := by
    dsimp only [cW]; split_ifs <;> rfl
  rw [hnm_e, hc_e]
  unfold probeAux rotAux
  dsimp only [sp, st, inj, jInj, vecToK, evalVec]

private def cProbeLinEntry {k : ℕ} (n : ℕ) (hk : 0 < k) (sp st inj : ℕ) (j : Fin k)
    (rny1 ry2 : ℕ) (genH : VecW k) (g' : List Gate) : List Gate × ℕ :=
  let rop0 := cMixed0At n hk sp st genH j g'
  let rop1 := cMixed0At n hk sp st genH (ixAux k hk (j.val + 1)) rop0.1
  let rop2 := cMixed0At n hk sp st genH (ixAux k hk (j.val + 2)) rop1.1
  let rt1 := cXor n rop2.1 rop0.2 (genH (ixAux k hk (j.val + k - inj % k)))
  let rp1 := cAnd n rt1.1 rny1 rop2.2
  let rp2 := cAnd n rp1.1 ry2 rop1.2
  let rt2 := cXor n rp2.1 rp1.2 rp2.2
  cXor n rt2.1 rt1.2 rt2.2

private def cProbeLin {k m t : ℕ} (n : ℕ) (hk : 0 < k) (site : Fin t → Fin k) (col : Fin t → Bool)
    (baseW : VecW k) (genW : Fin m → VecW k) (uW vW : VecW k) (p : Fin t) (g : List Gate) :
    List Gate × VecW m :=
  let sp := if col p then 2 else 1
  let st := if col p then 3 else 1
  let inj := if col p then 4 else 0
  let nmW := if col p then vW else uW
  let j := site p
  let j1 := ixAux k hk (j.val + 1)
  let j2 := ixAux k hk (j.val + 2)
  let ry1 := cMixedAt n hk sp st baseW nmW j1 g
  let ry2 := cMixedAt n hk sp st baseW nmW j2 ry1.1
  let rny1 := cNot n ry2.1 ry1.2
  cBuildFin m (fun g' h => cProbeLinEntry n hk sp st inj j rny1.2 ry2.2 (genW h) g') rny1.1

private lemma cProbeLin_spec {n k m t : ℕ} (hn : 0 < n) (hk : 0 < k) (site : Fin t → Fin k) (col : Fin t → Bool)
    (baseW : VecW k) (genW : Fin m → VecW k) (uW vW : VecW k) (p : Fin t) (g : List Gate) (hg : GoodCircuit n g)
    (hbase : ValidVec (n + g.length) baseW) (hgen : ∀ h, ValidVec (n + g.length) (genW h))
    (hu : ValidVec (n + g.length) uW) (hv : ValidVec (n + g.length) vW) :
    let res := cProbeLin n hk site col baseW genW uW vW p g
    GoodCircuit n res.1 ∧ Extends g res.1 ∧ res.1.length ≤ g.length + (41 + m * 38) ∧
    ValidVec (n + res.1.length) res.2 ∧
    ∀ x, x.length = n → vecToK (evalVec res.1 x res.2) =
      probeLinAux hk site col (vecToK (evalVec g x baseW)) (fun h => vecToK (evalVec g x (genW h)))
        (vecToK (evalVec g x uW)) (vecToK (evalVec g x vW)) p := by
  dsimp only [cProbeLin]
  set sp := if col p then 2 else 1
  set st := if col p then 3 else 1
  set inj := if col p then 4 else 0
  set nmW := if col p then vW else uW
  have hnm : ValidVec (n + g.length) nmW := by dsimp only [nmW]; split_ifs <;> assumption
  have hy1 := cMixedAt_spec hn hk sp st baseW nmW (ixAux k hk ((site p).val + 1)) g hg hbase hnm
  set ry1 := cMixedAt n hk sp st baseW nmW (ixAux k hk ((site p).val + 1)) g
  have hy2 := cMixedAt_spec hn hk sp st baseW nmW (ixAux k hk ((site p).val + 2)) ry1.1 hy1.1
    (hbase.mono (by have := hy1.2.1.len_le; omega)) (hnm.mono (by have := hy1.2.1.len_le; omega))
  set ry2 := cMixedAt n hk sp st baseW nmW (ixAux k hk ((site p).val + 2)) ry1.1
  have hny1 := cNot_spec hn ry2.1 hy2.1 ry1.2 (by have ae := hy2.2.1.len_le; have a1 := hy1.2.2.2.1; omega)
  set rny1 := cNot n ry2.1 ry1.2
  have e0_ny1 := (hy1.2.1.trans hy2.2.1).trans hny1.2.1
  have hb := cBuildFin_spec (n := n) (fun L w => w < L) (fun hL hw => lt_of_lt_of_le hw hL)
    val (fun hx hext hw => val_of_extends hx hext hw) m 38
    (fun g' h => cProbeLinEntry n hk sp st inj (site p) rny1.2 ry2.2 (genW h) g')
    (fun x h => z2b (probeLinAux hk site col (vecToK (evalVec g x baseW)) (fun i => vecToK (evalVec g x (genW i)))
      (vecToK (evalVec g x uW)) (vecToK (evalVec g x vW)) p h))
    rny1.1 hny1.1 (fun g' h hg' hext => by
      dsimp only [cProbeLinEntry]
      set jInj := ixAux k hk ((site p).val + k - inj % k)
      have e0g := e0_ny1.trans hext
      have hop0 := cMixed0At_spec hn hk sp st (genW h) (site p) g' hg' ((hgen h).mono (by have := e0g.len_le; omega))
      set rop0 := cMixed0At n hk sp st (genW h) (site p) g'
      have hop1 := cMixed0At_spec hn hk sp st (genW h) (ixAux k hk ((site p).val + 1)) rop0.1 hop0.1
        ((hgen h).mono (by have := (e0g.trans hop0.2.1).len_le; omega))
      set rop1 := cMixed0At n hk sp st (genW h) (ixAux k hk ((site p).val + 1)) rop0.1
      have hop2 := cMixed0At_spec hn hk sp st (genW h) (ixAux k hk ((site p).val + 2)) rop1.1 hop1.1
        ((hgen h).mono (by have := ((e0g.trans hop0.2.1).trans hop1.2.1).len_le; omega))
      set rop2 := cMixed0At n hk sp st (genW h) (ixAux k hk ((site p).val + 2)) rop1.1
      have eg_op2 := (hop0.2.1.trans hop1.2.1).trans hop2.2.1
      have ht1 := cXor_spec hn rop2.1 hop2.1 rop0.2 (genW h jInj)
        (by have ae := (hop1.2.1.trans hop2.2.1).len_le; have a0 := hop0.2.2.2.1; omega)
        (by have ae := (e0g.trans eg_op2).len_le; have ah := hgen h jInj; omega)
      set rt1 := cXor n rop2.1 rop0.2 (genW h jInj)
      have hp1 := cAnd_spec hn rt1.1 ht1.1 rny1.2 rop2.2
        (by have ae := ((hext.trans eg_op2).trans ht1.2.1).len_le; have an := hny1.2.2.2.1; omega)
        (by have ae := ht1.2.1.len_le; have a2 := hop2.2.2.2.1; omega)
      set rp1 := cAnd n rt1.1 rny1.2 rop2.2
      have hp2 := cAnd_spec hn rp1.1 hp1.1 ry2.2 rop1.2
        (by have ae := (((hny1.2.1.trans hext).trans eg_op2).trans (ht1.2.1.trans hp1.2.1)).len_le; have a2 := hy2.2.2.2.1; omega)
        (by have ae := ((hop2.2.1.trans ht1.2.1).trans hp1.2.1).len_le; have a1 := hop1.2.2.2.1; omega)
      set rp2 := cAnd n rp1.1 ry2.2 rop1.2
      have ht2 := cXor_spec hn rp2.1 hp2.1 rp1.2 rp2.2 (by have ae := hp2.2.1.len_le; have a1 := hp1.2.2.2.1; omega) hp2.2.2.2.1
      set rt2 := cXor n rp2.1 rp1.2 rp2.2
      have ht3 := cXor_spec hn rt2.1 ht2.1 rt1.2 rt2.2
        (by have ae := ((hp1.2.1.trans hp2.2.1).trans ht2.2.1).len_le; have a1 := ht1.2.2.2.1; omega) ht2.2.2.2.1
      refine ⟨ht3.1, (eg_op2.trans (ht1.2.1.trans hp1.2.1)).trans ((hp2.2.1.trans ht2.2.1).trans ht3.2.1),
        by have b1 := hop0.2.2.1; have b2 := hop1.2.2.1; have b3 := hop2.2.2.1; have b4 := ht1.2.2.1
           have b5 := hp1.2.2.1; have b6 := hp2.2.2.1; have b7 := ht2.2.2.1; have b8 := ht3.2.2.1; omega,
        ht3.2.2.2.1, fun x hx => ?_⟩
      apply b2z_injective
      rw [b2z_z2b, ht3.2.2.2.2 x hx, b2z_xor,
        val_of_extends hx ((hp1.2.1.trans hp2.2.1).trans ht2.2.1) ht1.2.2.2.1,
        ht1.2.2.2.2 x hx, b2z_xor, val_of_extends hx (hop1.2.1.trans hop2.2.1) hop0.2.2.2.1,
        hop0.2.2.2.2 x hx, evalVec_of_extends hx e0g (hgen h),
        val_of_extends hx (e0g.trans eg_op2) (hgen h jInj),
        ht2.2.2.2.2 x hx, b2z_xor, val_of_extends hx hp2.2.1 hp1.2.2.2.1,
        hp1.2.2.2.2 x hx, b2z_and, val_of_extends hx ((hext.trans eg_op2).trans ht1.2.1) hny1.2.2.2.1,
        hny1.2.2.2.2 x hx, b2z_not, val_of_extends hx hy2.2.1 hy1.2.2.2.1, hy1.2.2.2.2 x hx,
        val_of_extends hx ht1.2.1 hop2.2.2.2.1, hop2.2.2.2.2 x hx,
        evalVec_of_extends hx ((e0g.trans hop0.2.1).trans hop1.2.1) (hgen h),
        hp2.2.2.2.2 x hx, b2z_and,
        val_of_extends hx (((hny1.2.1.trans hext).trans eg_op2).trans (ht1.2.1.trans hp1.2.1)) hy2.2.2.2.1,
        hy2.2.2.2.2 x hx, evalVec_of_extends hx hy1.2.1 hbase, evalVec_of_extends hx hy1.2.1 hnm,
        val_of_extends hx ((hop2.2.1.trans ht1.2.1).trans hp1.2.1) hop1.2.2.2.1, hop1.2.2.2.2 x hx,
        evalVec_of_extends hx (e0g.trans hop0.2.1) (hgen h)]
      have hnm_e : vecToK (evalVec g x nmW) = if col p then vecToK (evalVec g x vW) else vecToK (evalVec g x uW) := by
        dsimp only [nmW]; split_ifs <;> rfl
      have hix0 : ixAux k hk ((site p).val + 0) = site p :=
        Fin.ext (by simp [ixAux, Nat.mod_eq_of_lt (site p).2])
      rw [hnm_e]
      unfold probeLinAux operandAux rotAux
      rw [hix0]
      dsimp only [sp, st, inj, jInj, vecToK, evalVec]
      ring)
  refine ⟨hb.1, e0_ny1.trans hb.2.1,
    by have a1 := hy1.2.2.1; have a2 := hy2.2.2.1; have a3 := hny1.2.2.1; have a4 := hb.2.2.1; omega,
    hb.2.2.2.1, fun x hx => funext fun h => ?_⟩
  simp only [vecToK, evalVec, hb.2.2.2.2 x hx h, b2z_z2b]

end PEqualNP.Outside.L_meta_25682_aux

open PEqualNP.Outside.L_meta_25682_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_25682 :
    ∀ (k m t q : ℕ) (hk : 0 < k),
      let K := ZMod 2
      let W := Fin k → K
      let X := Fin m → K
      let ix := fun pos : ℕ => (⟨pos % k, Nat.mod_lt _ hk⟩ : Fin k)
      let rot := fun (s : ℕ) (w : W) (j : Fin k) => w (ix (j.val+k-s % k))
      let mixed := fun (d s : ℕ) (w name : W) =>
        let z := rot s w + name
        fun mid : Fin k => z mid + z (ix (mid.val+d)) + z (ix (mid.val+k-d % k))
      ∀ (site : Fin t → Fin k) (col : Fin t → Bool),
        let spacing := fun spacingId => if col spacingId then 2 else 1
        let start := fun startId => if col startId then 3 else 1
        let injectAt := fun injectId => if col injectId then 4 else 0
        let inputs := (m+5)*k+t
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (flag : Fin (inputs+C.size))
          (out : Fin (k+1) → Fin (inputs+C.size)),
          PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
          C.size ≤ 2^20*(k+m+t+2)^8*3^(min q (min m t)) ∧
          ∀ (base : W) (gen : Fin m → W) (u v cr cc : W) (wanted : Fin t → K),
            let key := fun x : X => base + ∑ g : Fin m, x g • gen g
            let probe := fun (raw : W) (idx : Fin t) =>
              let y := mixed (spacing idx) (start idx) raw (if col idx then v else u)
              let j := site idx
              y j + (1+y (ix (j.val+1))) * y (ix (j.val+2)) +
                rot (injectAt idx) raw j + (if col idx then cc j else cr j)
            let operand := fun (p : Fin t) (offset : ℕ) (g : Fin m) =>
              mixed (spacing p) (start p) (gen g) 0 (ix ((site p).val+offset))
            let hits := ∃ basis : Fin q → X,
              let D := Submodule.span K (Set.range basis)
              ∀ j, operand j 1 ∈ D ∨ operand j 2 ∈ D ∨ operand j 1 + operand j 2 ∈ D
            let flat := ∃ U : Submodule K X, m ≤ Module.finrank K U + q ∧
              ∀ (z : X) (p : Fin t), ∃ (ell : X →ₗ[K] K) (c : K),
                ∀ x ∈ U, probe (key (z+x)) p = ell x + c
            let pack := fun word : W => List.ofFn (fun bit : Fin k => decide (word bit ≠ 0))
            let bits := pack base ++ (List.ofFn (fun h => pack (gen h))).flatten ++
              pack u ++ pack v ++ pack cr ++ pack cc ++ List.ofFn (fun targetId => decide (wanted targetId ≠ 0))
            (hits ↔ flat) ∧ ((C.wires bits).getD flag.val false = true ↔ hits) ∧
            (hits →
              let count := Nat.card { raw : W // raw ∈ Set.range key ∧ ∀ p, probe raw p = wanted p }
              ∀ o : Fin (k+1), (C.wires bits).getD (out o).val false = count.testBit o.val) := by
  intro k m t q hk K W X ix rot mixed site col spacing start injectAt inputs
  have hn : 0 < inputs := by dsimp only [inputs]; nlinarith
  let d := min q (min m t)
  have hbase_v : ValidVec (inputs + ([] : List Gate).length) (baseW (k := k)) := fun j => by
    dsimp only [baseW, inputs, List.length_nil]; have := j.2; nlinarith
  have hgen_v : ∀ h : Fin m, ValidVec (inputs + ([] : List Gate).length) (genW (k := k) (m := m) h) := fun h j => by
    dsimp only [genW, inputs, List.length_nil]
    have hj := j.2; have hh := h.2
    have : (h.1 + 1) * k ≤ m * k := Nat.mul_le_mul_right k hh
    nlinarith
  have hu_v : ValidVec (inputs + ([] : List Gate).length) (uW (k := k) m) := fun j => by
    dsimp only [uW, inputs, List.length_nil]; have := j.2; nlinarith
  have hv_v : ValidVec (inputs + ([] : List Gate).length) (vW (k := k) m) := fun j => by
    dsimp only [vW, inputs, List.length_nil]; have := j.2; nlinarith
  have hcr_v : ValidVec (inputs + ([] : List Gate).length) (crW (k := k) m) := fun j => by
    dsimp only [crW, inputs, List.length_nil]; have := j.2; nlinarith
  have hcc_v : ValidVec (inputs + ([] : List Gate).length) (ccW (k := k) m) := fun j => by
    dsimp only [ccW, inputs, List.length_nil]; have := j.2; nlinarith
  have hw_v : ∀ p : Fin t, wantedW k m p < inputs + ([] : List Gate).length := fun p => by
    dsimp only [wantedW, inputs, List.length_nil]; have := p.2; omega
  -- Step 1: Build aW, bW, basePW, LW
  have haW := cBuildFin_spec (n := inputs) ValidVec (fun hL hv => hv.mono hL) evalVec
    (fun hx hext hv => evalVec_of_extends hx hext hv) t (m * 8)
    (fun g' p => cBuildFin m (fun g'' h => cMixed0At inputs hk (spacing p) (start p) (genW h) (ix ((site p).val + 1)) g'') g')
    (fun x p => fun h => z2b (operandAux hk site col (fun i => vecToK (evalVec [] x (genW i))) p 1 h))
    [] (GoodCircuit.nil inputs) (fun g' p hg' hext => by
      have hb := cBuildFin_spec (n := inputs) (fun L w => w < L) (fun hL hw => lt_of_lt_of_le hw hL)
        val (fun hx hext' hw => val_of_extends hx hext' hw) m 8
        (fun g'' h => cMixed0At inputs hk (spacing p) (start p) (genW h) (ix ((site p).val + 1)) g'')
        (fun x h => z2b (operandAux hk site col (fun i => vecToK (evalVec [] x (genW i))) p 1 h))
        g' hg' (fun g'' h hg'' hext'' => by
          have hm := cMixed0At_spec hn hk (spacing p) (start p) (genW h) (ix ((site p).val + 1)) g'' hg''
            ((hgen_v h).mono (by have := (hext.trans hext'').len_le; omega))
          refine ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, fun x hx => ?_⟩
          apply b2z_injective
          rw [b2z_z2b, hm.2.2.2.2 x hx, evalVec_of_extends hx (hext.trans hext'') (hgen_v h)]
          rfl)
      exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, fun x hx => funext fun h => hb.2.2.2.2 x hx h⟩)
  set raW := cBuildFin t (fun g' p => cBuildFin m (fun g'' h => cMixed0At inputs hk (spacing p) (start p) (genW h) (ix ((site p).val + 1)) g'') g') []
  have hbW := cBuildFin_spec (n := inputs) ValidVec (fun hL hv => hv.mono hL) evalVec
    (fun hx hext hv => evalVec_of_extends hx hext hv) t (m * 8)
    (fun g' p => cBuildFin m (fun g'' h => cMixed0At inputs hk (spacing p) (start p) (genW h) (ix ((site p).val + 2)) g'') g')
    (fun x p => fun h => z2b (operandAux hk site col (fun i => vecToK (evalVec [] x (genW i))) p 2 h))
    raW.1 haW.1 (fun g' p hg' hext => by
      have hb := cBuildFin_spec (n := inputs) (fun L w => w < L) (fun hL hw => lt_of_lt_of_le hw hL)
        val (fun hx hext' hw => val_of_extends hx hext' hw) m 8
        (fun g'' h => cMixed0At inputs hk (spacing p) (start p) (genW h) (ix ((site p).val + 2)) g'')
        (fun x h => z2b (operandAux hk site col (fun i => vecToK (evalVec [] x (genW i))) p 2 h))
        g' hg' (fun g'' h hg'' hext'' => by
          have hm := cMixed0At_spec hn hk (spacing p) (start p) (genW h) (ix ((site p).val + 2)) g'' hg''
            ((hgen_v h).mono (by have := ((haW.2.1.trans hext).trans hext'').len_le; omega))
          refine ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, fun x hx => ?_⟩
          apply b2z_injective
          rw [b2z_z2b, hm.2.2.2.2 x hx, evalVec_of_extends hx ((haW.2.1.trans hext).trans hext'') (hgen_v h)]
          rfl)
      exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, fun x hx => funext fun h => hb.2.2.2.2 x hx h⟩)
  set rbW := cBuildFin t (fun g' p => cBuildFin m (fun g'' h => cMixed0At inputs hk (spacing p) (start p) (genW h) (ix ((site p).val + 2)) g'') g') raW.1
  have e0_bW := haW.2.1.trans hbW.2.1
  have hbpW := cBuildFin_spec (n := inputs) (fun L w => w < L) (fun hL hw => lt_of_lt_of_le hw hL)
    val (fun hx hext hw => val_of_extends hx hext hw) t 74
    (fun g' p => cBaseProbe inputs hk site col baseW (uW m) (vW m) (crW m) (ccW m) p g')
    (fun x p => z2b (probeAux hk site col (vecToK (evalVec [] x (uW m))) (vecToK (evalVec [] x (vW m)))
      (vecToK (evalVec [] x (crW m))) (vecToK (evalVec [] x (ccW m))) (vecToK (evalVec [] x baseW)) p))
    rbW.1 hbW.1 (fun g' p hg' hext => by
      have e0g := e0_bW.trans hext
      have hbp := cBaseProbe_spec hn hk site col baseW (uW m) (vW m) (crW m) (ccW m) p g' hg'
        (hbase_v.mono (by have := e0g.len_le; omega)) (hu_v.mono (by have := e0g.len_le; omega))
        (hv_v.mono (by have := e0g.len_le; omega)) (hcr_v.mono (by have := e0g.len_le; omega))
        (hcc_v.mono (by have := e0g.len_le; omega))
      refine ⟨hbp.1, hbp.2.1, hbp.2.2.1, hbp.2.2.2.1, fun x hx => ?_⟩
      apply b2z_injective
      rw [b2z_z2b, hbp.2.2.2.2 x hx, evalVec_of_extends hx e0g hbase_v,
        evalVec_of_extends hx e0g hu_v, evalVec_of_extends hx e0g hv_v,
        evalVec_of_extends hx e0g hcr_v, evalVec_of_extends hx e0g hcc_v])
  set rbpW := cBuildFin t (fun g' p => cBaseProbe inputs hk site col baseW (uW m) (vW m) (crW m) (ccW m) p g') rbW.1
  have e0_bpW := e0_bW.trans hbpW.2.1
  have hLW := cBuildFin_spec (n := inputs) ValidVec (fun hL hv => hv.mono hL) evalVec
    (fun hx hext hv => evalVec_of_extends hx hext hv) t (41 + m * 38)
    (fun g' p => cProbeLin inputs hk site col baseW genW (uW m) (vW m) p g')
    (fun x p => kToVec (probeLinAux hk site col (vecToK (evalVec [] x baseW)) (fun h => vecToK (evalVec [] x (genW h)))
      (vecToK (evalVec [] x (uW m))) (vecToK (evalVec [] x (vW m))) p))
    rbpW.1 hbpW.1 (fun g' p hg' hext => by
      have e0g := e0_bpW.trans hext
      have hL := cProbeLin_spec hn hk site col baseW genW (uW m) (vW m) p g' hg'
        (hbase_v.mono (by have := e0g.len_le; omega)) (fun h => (hgen_v h).mono (by have := e0g.len_le; omega))
        (hu_v.mono (by have := e0g.len_le; omega)) (hv_v.mono (by have := e0g.len_le; omega))
      refine ⟨hL.1, hL.2.1, hL.2.2.1, hL.2.2.2.1, fun x hx => ?_⟩
      have he := hL.2.2.2.2 x hx
      rw [evalVec_of_extends hx e0g hbase_v, evalVec_of_extends hx e0g hu_v, evalVec_of_extends hx e0g hv_v] at he
      have hge : (fun h => vecToK (evalVec g' x (genW h))) = fun h => vecToK (evalVec [] x (genW h)) :=
        funext fun h => congrArg vecToK (evalVec_of_extends hx e0g (hgen_v h))
      rw [hge] at he
      funext h; apply b2z_injective
      simpa [kToVec, vecToK, b2z_z2b] using congrFun he h)
  set rLW := cBuildFin t (fun g' p => cProbeLin inputs hk site col baseW genW (uW m) (vW m) p g') rbpW.1
  have e0_LW := e0_bpW.trans hLW.2.1
  -- Step 2: Stage 1 (cFptSearch)
  have hT0 := cPivotEmpty_spec hn (m := m) rLW.1 hLW.1
  set rT0 := cPivotEmpty inputs m rLW.1
  have ea_T0 := ((hbW.2.1.trans hbpW.2.1).trans hLW.2.1).trans hT0.2.1
  have eb_T0 := (hbpW.2.1.trans hLW.2.1).trans hT0.2.1
  have hS := cFptSearch_spec hn (d := d) raW.2 rbW.2 d (le_refl d) rT0.1 hT0.1 rT0.2 hT0.2.2.2.1
    (fun p => (haW.2.2.2.1 p).mono (by have := ea_T0.len_le; omega))
    (fun p => (hbW.2.2.2.1 p).mono (by have := eb_T0.len_le; omega))
  set rS := cFptSearch inputs m t raW.2 rbW.2 d rT0.1 rT0.2
  -- Step 3: Stage 2 (cSumCells)
  have hA0 := cAugEmpty_spec hn (m := m) rS.1 hS.1
  set rA0 := cAugEmpty inputs m rS.1
  have e0_A0 := ((e0_LW.trans hT0.2.1).trans hS.2.1).trans hA0.2.1
  have ea_A0 := (ea_T0.trans hS.2.1).trans hA0.2.1
  have eb_A0 := (eb_T0.trans hS.2.1).trans hA0.2.1
  have ebp_A0 := ((hLW.2.1.trans hT0.2.1).trans hS.2.1).trans hA0.2.1
  have eL_A0 := (hT0.2.1.trans hS.2.1).trans hA0.2.1
  have hSum := cSumCells_spec hn rS.2.2.1 raW.2 rbW.2 rLW.2 rbpW.2 (wantedW k m) d rS.2.2.2 rA0.1 hA0.1 rA0.2
    (hS.2.2.2.1.2.1.mono (by have := hA0.2.1.len_le; omega))
    (fun p => (haW.2.2.2.1 p).mono (by have := ea_A0.len_le; omega))
    (fun p => (hbW.2.2.2.1 p).mono (by have := eb_A0.len_le; omega))
    (fun p => (hLW.2.2.2.1 p).mono (by have := eL_A0.len_le; omega))
    (fun p => by have ae := ebp_A0.len_le; have ab := hbpW.2.2.2.1 p; omega)
    (fun p => by have ae := e0_A0.len_le; have aw := hw_v p; simp only [List.length_nil] at aw; omega)
    (fun i => (hS.2.2.2.1.2.2 i).mono (by have := hA0.2.1.len_le; omega))
    hA0.2.2.2.1
  set rSum := cSumCells inputs m t rS.2.2.1 raW.2 rbW.2 rLW.2 rbpW.2 (wantedW k m) d rS.2.2.2 rA0.1 rA0.2
  -- Step 4: Generator rank & right shift
  have e0_Sum := e0_A0.trans hSum.2.1
  have hGen := cGenRankTable_spec hn rSum.1 hSum.1 (genW (k := k) (m := m))
    (fun h => (hgen_v h).mono (by have := e0_Sum.len_le; omega))
  set rGen := cGenRankTable inputs k m rSum.1 (genW (k := k) (m := m))
  have hOhGen := cOneHotCount_spec hn rGen.1 hGen.1 rGen.2.hasPiv hGen.2.2.2.1.1
  set rOhGen := cOneHotCount inputs k rGen.1 rGen.2.hasPiv
  have hOut := cShiftRightBits_spec hn rOhGen.1 hOhGen.1 rSum.2 rOhGen.2
    (hSum.2.2.2.1.mono (by have := (hGen.2.1.trans hOhGen.2.1).len_le; omega))
    hOhGen.2.2.2.1
  set rOut := cShiftRightBits inputs k m rOhGen.1 rSum.2 rOhGen.2
  have eS_Out := (((hA0.2.1.trans hSum.2.1).trans hGen.2.1).trans hOhGen.2.1).trans hOut.2.1
  let C : Circuit := ⟨rOut.1, 0⟩
  let flagFin : Fin (inputs + C.size) := ⟨rS.2.1, by
    change rS.2.1 < inputs + rOut.1.length
    have ae := eS_Out.len_le; have af := hS.2.2.2.1.1; omega⟩
  let outFin : Fin (k + 1) → Fin (inputs + C.size) := fun o => ⟨rOut.2 o, hOut.2.2.2.1 o⟩
  refine ⟨C, flagFin, outFin, hOut.1.1, hOut.1.2, ?_, ?_⟩
  · -- Size bound: C.size ≤ 2^20 * (k + m + t + 2)^8 * 3^d
    change rOut.1.length ≤ 2 ^ 20 * (k + m + t + 2) ^ 8 * 3 ^ d
    have a1 := haW.2.2.1; have a2 := hbW.2.2.1; have a3 := hbpW.2.2.1; have a4 := hLW.2.2.1
    have a5 := hT0.2.2.1; have a6 := hS.2.2.1; have a7 := hA0.2.2.1; have a8 := hSum.2.2.1
    have a9 := hGen.2.2.1; have a10 := hOhGen.2.2.1; have a11 := hOut.2.2.1
    simp only [List.length_nil, zero_add] at a1
    set N := k + m + t + 2
    have hN1 : 1 ≤ N := by omega
    have hNk : k ≤ N := by omega
    have hNm : m ≤ N := by omega
    have hNt : t ≤ N := by omega
    have hNd : d ≤ N := by have : d ≤ m := le_trans (min_le_right _ _) (min_le_left _ _); omega
    have hpow23 : 2 ^ d ≤ 3 ^ d := Nat.pow_le_pow_left (by decide) d
    have h3pos : 1 ≤ 3 ^ d := Nat.one_le_pow d 3 (by decide)
    have hN2 : N ^ 2 = N * N := by ring
    have hN3 : N ^ 3 = N * N * N := by ring
    have hN3_le_8 : N ^ 3 ≤ N ^ 8 := Nat.pow_le_pow_right hN1 (by decide)
    have hPre : t * (m * 8) + t * (m * 8) + t * 74 + t * (41 + m * 38) + (m * m + m) +
        (m * m + 2 * m + 1) + ((k * k + k) + m * (14 * k * k + 4 * k)) +
        ((k + 1) + k * ((k + 1) * 5)) + (k + 1) * (1 + (k + 1) * 2) ≤ 256 * N ^ 3 := by
      nlinarith [sq_nonneg N,
        mul_le_mul hNk hNk (Nat.zero_le k) (Nat.zero_le N),
        mul_le_mul hNm hNm (Nat.zero_le m) (Nat.zero_le N),
        mul_le_mul hNt hNm (Nat.zero_le m) (Nat.zero_le N),
        mul_le_mul hNm hNk (Nat.zero_le k) (Nat.zero_le N),
        mul_le_mul hNm (mul_le_mul hNk hNk (Nat.zero_le k) (Nat.zero_le N)) (Nat.zero_le _) (Nat.zero_le N)]
    have hFptB : fptNodeBound m t d ≤ 2048 * N ^ 3 := by
      unfold fptNodeBound
      have h1 : m + t + d + 2 ≤ 2 * N := by omega
      have h2 : (m + t + d + 2) ^ 3 ≤ (2 * N) ^ 3 := Nat.pow_le_pow_left h1 3
      have h3 : (2 * N) ^ 3 = 8 * N ^ 3 := by ring
      omega
    have hCellB : cellNodeBound m t ≤ 128 * N ^ 3 := by
      unfold cellNodeBound
      have h1 : m + t + 2 ≤ N := by omega
      have h2 : (m + t + 2) ^ 3 ≤ N ^ 3 := Nat.pow_le_pow_left h1 3
      omega
    have htot1 : rOut.1.length ≤ 256 * N ^ 3 + 2 * 3 ^ d * (2048 * N ^ 3) + 2 * 3 ^ d * (128 * N ^ 3) := by
      have h6' : rS.1.length ≤ rT0.1.length + 2 * 3 ^ d * (2048 * N ^ 3) := by
        have := Nat.mul_le_mul_left (2 * 3 ^ d) hFptB; omega
      have h8' : rSum.1.length ≤ rA0.1.length + 2 * 3 ^ d * (128 * N ^ 3) := by
        have h1 := Nat.mul_le_mul_left 2 hpow23
        have h2 := Nat.mul_le_mul h1 hCellB
        omega
      omega
    have htot2 : 256 * N ^ 3 ≤ 256 * N ^ 3 * 3 ^ d := by
      simpa using Nat.mul_le_mul_left (256 * N ^ 3) h3pos
    have htot3 : 256 * N ^ 3 + 2 * 3 ^ d * (2048 * N ^ 3) + 2 * 3 ^ d * (128 * N ^ 3) ≤ 4608 * N ^ 3 * 3 ^ d := by
      have heq : 2 * 3 ^ d * (2048 * N ^ 3) + 2 * 3 ^ d * (128 * N ^ 3) = 4352 * N ^ 3 * 3 ^ d := by ring
      have heq2 : 256 * N ^ 3 * 3 ^ d + 4352 * N ^ 3 * 3 ^ d = 4608 * N ^ 3 * 3 ^ d := by ring
      rw [add_assoc, heq]; omega
    have htot4 : 4608 * N ^ 3 * 3 ^ d ≤ 2 ^ 20 * N ^ 8 * 3 ^ d := by
      refine Nat.mul_le_mul_right (3 ^ d) ?_
      have h4608 : 4608 ≤ 2 ^ 20 := by decide
      exact Nat.mul_le_mul h4608 hN3_le_8
    omega
  · -- Correctness for all inputs (base, gen, u, v, cr, cc, wanted)
    intro base gen u v cr cc wanted key probe operand hits flat pack bits
    have hpack_len : ∀ w : W, (pack w).length = k := fun w => by simp [pack]
    have hgen_len : (List.ofFn (fun h : Fin m => pack (gen h))).flatten.length = m * k :=
      flatten_ofFn_length (fun h => pack (gen h)) (fun h => hpack_len (gen h))
    have hbits_len : bits.length = inputs := by
      simp only [bits, List.length_append, hpack_len, hgen_len, List.length_ofFn, inputs]
      ring
    -- Verify input wire evaluations on `bits`
    have hpack_getD : ∀ (w : W) (j : Fin k), (pack w).getD j.1 false = kToVec w j := fun w j => by
      simp only [pack, list_ofFn_getD, kToVec]
      exact decide_ne_zero_eq_z2b (w j)
    have hbase_eval : evalVec [] bits (baseW (k := k)) = kToVec base := by
      funext j
      rw [evalVec, val_input [] hbits_len (by simpa using hbase_v j)]
      simp only [bits, baseW]
      have h1 := list_getD_append_left (pack base)
        ((List.ofFn (fun h => pack (gen h))).flatten ++ pack u ++ pack v ++ pack cr ++ pack cc ++
          List.ofFn (fun targetId => decide (wanted targetId ≠ 0))) j.1 false (by rw [hpack_len]; exact j.2)
      simp only [List.append_assoc] at h1 ⊢
      rw [h1, hpack_getD]
    have hgen_eval : ∀ h : Fin m, evalVec [] bits (genW (k := k) (m := m) h) = kToVec (gen h) := fun h => by
      funext j
      rw [evalVec, val_input [] hbits_len (by simpa using hgen_v h j)]
      simp only [bits, genW]
      have hsub : k + h.1 * k + j.1 - k = h.1 * k + j.1 := by omega
      have h1 := list_getD_append_mid (pack base) (List.ofFn (fun h => pack (gen h))).flatten
        (pack u ++ pack v ++ pack cr ++ pack cc ++ List.ofFn (fun targetId => decide (wanted targetId ≠ 0)))
        (k + h.1 * k + j.1) false (by rw [hpack_len]; omega) (by
          rw [hpack_len, hgen_len, hsub]; have hh := h.2; have hj := j.2
          have : (h.1 + 1) * k ≤ m * k := Nat.mul_le_mul_right k hh
          nlinarith)
      simp only [List.append_assoc] at h1 ⊢
      rw [h1, hpack_len, hsub, flatten_ofFn_getD (fun i => pack (gen i)) (fun i => hpack_len (gen i)) h j, hpack_getD]
    have hu_eval : evalVec [] bits (uW (k := k) m) = kToVec u := by
      funext j
      rw [evalVec, val_input [] hbits_len (by simpa using hu_v j)]
      simp only [bits, uW]
      have hlen1 : (pack base ++ (List.ofFn (fun h => pack (gen h))).flatten).length = (m + 1) * k := by
        rw [List.length_append, hpack_len, hgen_len]; ring
      have h1 := list_getD_append_mid (pack base ++ (List.ofFn (fun h => pack (gen h))).flatten) (pack u)
        (pack v ++ pack cr ++ pack cc ++ List.ofFn (fun targetId => decide (wanted targetId ≠ 0)))
        ((m + 1) * k + j.1) false (by rw [hlen1]; omega) (by rw [hlen1, Nat.add_sub_cancel_left, hpack_len]; exact j.2)
      simp only [List.append_assoc] at h1 ⊢
      rw [h1, hlen1, Nat.add_sub_cancel_left, hpack_getD]
    have hv_eval : evalVec [] bits (vW (k := k) m) = kToVec v := by
      funext j
      rw [evalVec, val_input [] hbits_len (by simpa using hv_v j)]
      simp only [bits, vW]
      have hlen1 : (pack base ++ (List.ofFn (fun h => pack (gen h))).flatten ++ pack u).length = (m + 2) * k := by
        simp only [List.length_append, hpack_len, hgen_len]; ring
      have h1 := list_getD_append_mid (pack base ++ (List.ofFn (fun h => pack (gen h))).flatten ++ pack u) (pack v)
        (pack cr ++ pack cc ++ List.ofFn (fun targetId => decide (wanted targetId ≠ 0)))
        ((m + 2) * k + j.1) false (by rw [hlen1]; omega) (by rw [hlen1, Nat.add_sub_cancel_left, hpack_len]; exact j.2)
      rw [hlen1, Nat.add_sub_cancel_left] at h1
      simp only [List.append_assoc] at h1 ⊢
      rw [h1, hpack_getD]
    have hcr_eval : evalVec [] bits (crW (k := k) m) = kToVec cr := by
      funext j
      rw [evalVec, val_input [] hbits_len (by simpa using hcr_v j)]
      simp only [bits, crW]
      have hlen1 : (pack base ++ (List.ofFn (fun h => pack (gen h))).flatten ++ pack u ++ pack v).length = (m + 3) * k := by
        simp only [List.length_append, hpack_len, hgen_len]; ring
      have h1 := list_getD_append_mid (pack base ++ (List.ofFn (fun h => pack (gen h))).flatten ++ pack u ++ pack v) (pack cr)
        (pack cc ++ List.ofFn (fun targetId => decide (wanted targetId ≠ 0)))
        ((m + 3) * k + j.1) false (by rw [hlen1]; omega) (by rw [hlen1, Nat.add_sub_cancel_left, hpack_len]; exact j.2)
      rw [hlen1, Nat.add_sub_cancel_left] at h1
      simp only [List.append_assoc] at h1 ⊢
      rw [h1, hpack_getD]
    have hcc_eval : evalVec [] bits (ccW (k := k) m) = kToVec cc := by
      funext j
      rw [evalVec, val_input [] hbits_len (by simpa using hcc_v j)]
      simp only [bits, ccW]
      have hlen1 : (pack base ++ (List.ofFn (fun h => pack (gen h))).flatten ++ pack u ++ pack v ++ pack cr).length = (m + 4) * k := by
        simp only [List.length_append, hpack_len, hgen_len]; ring
      have h1 := list_getD_append_mid (pack base ++ (List.ofFn (fun h => pack (gen h))).flatten ++ pack u ++ pack v ++ pack cr) (pack cc)
        (List.ofFn (fun targetId => decide (wanted targetId ≠ 0)))
        ((m + 4) * k + j.1) false (by rw [hlen1]; omega) (by rw [hlen1, Nat.add_sub_cancel_left, hpack_len]; exact j.2)
      rw [hlen1, Nat.add_sub_cancel_left] at h1
      simp only [List.append_assoc] at h1 ⊢
      rw [h1, hpack_getD]
    have hwanted_eval : ∀ p : Fin t, val [] bits (wantedW k m p) = z2b (wanted p) := fun p => by
      rw [val_input [] hbits_len (by simpa using hw_v p)]
      simp only [bits, wantedW]
      have h1 : (pack base ++ (List.ofFn (fun h => pack (gen h))).flatten ++ pack u ++ pack v ++ pack cr ++ pack cc).length = (m + 5) * k := by
        simp only [List.length_append, hpack_len, hgen_len]; ring
      rw [list_getD_append_right _ _ _ _ (by rw [h1]; omega), h1, Nat.add_sub_cancel_left, list_ofFn_getD, decide_ne_zero_eq_z2b]
    -- Pure Boolean arrays for this input
    let aP : Fin t → Vec m := fun p => kToVec (operandAux hk site col gen p 1)
    let bP : Fin t → Vec m := fun p => kToVec (operandAux hk site col gen p 2)
    let LP : Fin t → Vec m := fun p => kToVec (probeLinAux hk site col base gen u v p)
    let basePP : Fin t → Bool := fun p => z2b (probeAux hk site col u v cr cc base p)
    let wantedP : Fin t → Bool := fun p => z2b (wanted p)
    have hgen_k : (fun h => vecToK (evalVec [] bits (genW (k := k) (m := m) h))) = gen :=
      funext fun h => by rw [hgen_eval h, vecToK_kToVec]
    have ha_ev : ∀ p, evalVec raW.1 bits (raW.2 p) = aP p := fun p => by
      rw [haW.2.2.2.2 bits hbits_len p, hgen_k]; rfl
    have hb_ev : ∀ p, evalVec rbW.1 bits (rbW.2 p) = bP p := fun p => by
      rw [hbW.2.2.2.2 bits hbits_len p, hgen_k]; rfl
    have hbp_ev : ∀ p, val rbpW.1 bits (rbpW.2 p) = basePP p := fun p => by
      rw [hbpW.2.2.2.2 bits hbits_len p, hbase_eval, hu_eval, hv_eval, hcr_eval, hcc_eval,
        vecToK_kToVec, vecToK_kToVec, vecToK_kToVec, vecToK_kToVec, vecToK_kToVec]
    have hL_ev : ∀ p, evalVec rLW.1 bits (rLW.2 p) = LP p := fun p => by
      rw [hLW.2.2.2.2 bits hbits_len p, hbase_eval, hu_eval, hv_eval, hgen_k,
        vecToK_kToVec, vecToK_kToVec, vecToK_kToVec]
    -- Stage 1 evaluation
    have hS_ev : (val rS.1 bits rS.2.1, evalPivot rS.1 bits rS.2.2.1, fun i => evalVec rS.1 bits (rS.2.2.2 i)) =
        fptSearch aP bP d (PivotTable.empty m) := by
      rw [hS.2.2.2.2 bits hbits_len, hT0.2.2.2.2 bits hbits_len]
      have ha1 : (fun p => evalVec rT0.1 bits (raW.2 p)) = aP :=
        funext fun p => by rw [evalVec_of_extends hbits_len ea_T0 (haW.2.2.2.1 p), ha_ev p]
      have hb1 : (fun p => evalVec rT0.1 bits (rbW.2 p)) = bP :=
        funext fun p => by rw [evalVec_of_extends hbits_len eb_T0 (hbW.2.2.2.1 p), hb_ev p]
      rw [ha1, hb1]
    have hflag_eq : (C.wires bits).getD flagFin.val false = (fptSearch aP bP d (PivotTable.empty m)).1 := by
      change val rOut.1 bits rS.2.1 = _
      rw [val_of_extends hbits_len eS_Out hS.2.2.2.1.1]
      exact congrArg Prod.fst hS_ev
    have hfpt_iff : (fptSearch aP bP d (PivotTable.empty m)).1 = true ↔ hits := by
      have h1 := fptSearch_iff_hits (q := q) aP bP
      change (fptSearch aP bP d (PivotTable.empty m)).1 = true ↔
        ∃ basis : Fin q → X,
          let D := Submodule.span K (Set.range basis)
          ∀ p : Fin t, vecToK (aP p) ∈ D ∨ vecToK (bP p) ∈ D ∨ vecToK (aP p) + vecToK (bP p) ∈ D at h1
      have ha_eq : ∀ p, vecToK (aP p) = operand p 1 := fun p => by
        dsimp only [aP]; rw [vecToK_kToVec]; rfl
      have hb_eq : ∀ p, vecToK (bP p) = operand p 2 := fun p => by
        dsimp only [bP]; rw [vecToK_kToVec]; rfl
      simpa only [ha_eq, hb_eq] using h1
    refine ⟨?_, ?_, ?_⟩
    · exact hits_iff_flat_aux hk site col base gen u v cr cc
    · rw [hflag_eq]; exact hfpt_iff
    · intro hhits count o
      have hok : (fptSearch aP bP d (PivotTable.empty m)).1 = true := hfpt_iff.mpr hhits
      obtain ⟨hTf_wf, hTf_sp, hTf_cov⟩ := fptSearch_sound aP bP d (PivotTable.empty m) (PivotTable.empty_wf m) hok
      rw [PivotTable.empty_span, bot_sup_eq] at hTf_sp
      -- Stage 2 evaluation
      have hSum_ev : evalVec rSum.1 bits rSum.2 =
          sumCells (fptSearch aP bP d (PivotTable.empty m)).2.1 aP bP LP basePP wantedP d
            (fptSearch aP bP d (PivotTable.empty m)).2.2 (AugTable.empty m) := by
        rw [hSum.2.2.2.2 bits hbits_len, hA0.2.2.2.2 bits hbits_len,
          evalPivot_of_extends hbits_len hA0.2.1 hS.2.2.2.1.2.1]
        have hT' : evalPivot rS.1 bits rS.2.2.1 = (fptSearch aP bP d (PivotTable.empty m)).2.1 :=
          congrArg (fun p => p.2.1) hS_ev
        have hF' : (fun i => evalVec rA0.1 bits (rS.2.2.2 i)) = (fptSearch aP bP d (PivotTable.empty m)).2.2 :=
          (funext fun i => evalVec_of_extends hbits_len hA0.2.1 (hS.2.2.2.1.2.2 i)).trans (congrArg (fun p => p.2.2) hS_ev)
        have ha2 : (fun p => evalVec rA0.1 bits (raW.2 p)) = aP :=
          funext fun p => by rw [evalVec_of_extends hbits_len ea_A0 (haW.2.2.2.1 p), ha_ev p]
        have hb2 : (fun p => evalVec rA0.1 bits (rbW.2 p)) = bP :=
          funext fun p => by rw [evalVec_of_extends hbits_len eb_A0 (hbW.2.2.2.1 p), hb_ev p]
        have hL2 : (fun p => evalVec rA0.1 bits (rLW.2 p)) = LP :=
          funext fun p => by rw [evalVec_of_extends hbits_len eL_A0 (hLW.2.2.2.1 p), hL_ev p]
        have hbp2 : (fun p => val rA0.1 bits (rbpW.2 p)) = basePP :=
          funext fun p => by rw [val_of_extends hbits_len ebp_A0 (hbpW.2.2.2.1 p), hbp_ev p]
        have hw2 : (fun p => val rA0.1 bits (wantedW k m p)) = wantedP :=
          funext fun p => by rw [val_of_extends hbits_len e0_A0 (by simpa using hw_v p), hwanted_eval p]
        rw [hT', hF', ha2, hb2, hL2, hbp2, hw2]
      -- Generator rank & shift evaluation
      have hGen_ev : evalPivot rGen.1 bits rGen.2 = genRankTable (fun h => kToVec (gen h)) := by
        rw [hGen.2.2.2.2 bits hbits_len]
        have hg2 : (fun h => evalVec rSum.1 bits (genW (k := k) (m := m) h)) = fun h => kToVec (gen h) :=
          funext fun h => by rw [evalVec_of_extends hbits_len e0_Sum (hgen_v h), hgen_eval h]
        rw [hg2]
      have hOhGen_ev : evalVec rOhGen.1 bits rOhGen.2 = oneHotCount (genRankTable (fun h => kToVec (gen h))).hasPiv := by
        rw [hOhGen.2.2.2.2 bits hbits_len]
        exact congrArg oneHotCount (congrArg PivotTable.hasPiv hGen_ev)
      have hOut_ev : (C.wires bits).getD (outFin o).val false =
          shiftRightBits (sumCells (fptSearch aP bP d (PivotTable.empty m)).2.1 aP bP LP basePP wantedP d
            (fptSearch aP bP d (PivotTable.empty m)).2.2 (AugTable.empty m))
            (oneHotCount (genRankTable (fun h => kToVec (gen h))).hasPiv) o := by
        change val rOut.1 bits (rOut.2 o) = _
        have h1 := congrFun (hOut.2.2.2.2 bits hbits_len) o
        rw [evalVec_of_extends hbits_len (hGen.2.1.trans hOhGen.2.1) hSum.2.2.2.1, hSum_ev, hOhGen_ev] at h1
        exact h1
      rw [hOut_ev]
      -- Connect sumCells to count * 2 ^ (m - rank(gen))
      let Lgen : (Fin m → K) →ₗ[K] (Fin k → K) :=
        { toFun := fun x => ∑ g : Fin m, x g • gen g
          map_add' := fun x y => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
          map_smul' := fun c x => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, Finset.smul_sum] }
      let rk := Module.finrank K (LinearMap.range Lgen)
      have hrk_k : rk ≤ k := by
        have := Submodule.finrank_le (LinearMap.range Lgen)
        simpa [Module.finrank_fin_fun] using this
      have hrk_m : rk ≤ m := by
        have := LinearMap.finrank_range_le Lgen
        simpa [Module.finrank_fin_fun] using this
      have hgen_rk := genRankTable_spec gen
      have hoh_spec : ∀ r : Fin (k + 1), oneHotCount (genRankTable (fun h => kToVec (gen h))).hasPiv r = decide (r.1 = rk) := by
        intro r; rw [oneHotCount_spec, hgen_rk.2]
      have hsum_val : bitsToNat (sumCells (fptSearch aP bP d (PivotTable.empty m)).2.1 aP bP LP basePP wantedP d
          (fptSearch aP bP d (PivotTable.empty m)).2.2 (AugTable.empty m)) = count * 2 ^ (m - rk) := by
        have hsc := sumCells_spec (fptSearch aP bP d (PivotTable.empty m)).2.1 hTf_wf aP bP LP basePP wantedP hTf_cov
          d (fptSearch aP bP d (PivotTable.empty m)).2.2 (AugTable.empty m) (PivotTable.empty_wf m)
          (by rw [hTf_sp]; exact le_sup_right)
        rw [hsc]
        have hfib := fiber_card_eq_count_mul_ker base gen (fun raw => ∀ p : Fin t, probe raw p = wanted p)
        dsimp only at hfib
        rw [← hfib]
        refine congrArg Finset.card ?_
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hxA : x ∈ (AugTable.empty m).Sols := ⟨rfl, fun j hp => by simp [AugTable.empty, PivotTable.empty] at hp⟩
        simp only [hxA, true_and]
        refine forall_congr' fun p => ?_
        have hexp := probeAux_key_expand hk site col base gen u v cr cc x p
        have hp_eq : probe (base + ∑ g : Fin m, x g • gen g) p = probeAux hk site col u v cr cc (base + ∑ g : Fin m, x g • gen g) p := rfl
        rw [hp_eq, hexp]
        simp only [aP, bP, LP, basePP, wantedP, vecToK_kToVec, b2z_z2b]
      exact shiftRightBits_spec _ _ rk count hrk_k hrk_m hoh_spec hsum_val o

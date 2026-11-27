import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25604_aux

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> rfl

lemma zmod2_sub_eq_add (a b : ZMod 2) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> rfl

lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_two_mul (a : ZMod 2) : 2 * a = 0 := by
  fin_cases a <;> rfl

lemma zmod2_three_mul (a : ZMod 2) : a + a + a = a := by
  fin_cases a <;> rfl

def W (k : ℕ) := ZMod k → ZMod 2

def evec {k : ℕ} (i : ZMod k) : ZMod k → ZMod 2 :=
  fun x => if x = i then 1 else 0

def rotZ {k : ℕ} (t : ZMod k) : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2) where
  toFun v j := v (j - t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rotEquiv {k : ℕ} (t : ZMod k) : (ZMod k → ZMod 2) ≃ₗ[ZMod 2] (ZMod k → ZMod 2) :=
  LinearEquiv.ofLinearMap (rotZ t) (rotZ (-t))
    (by ext v j; simp [rotZ])
    (by ext v j; simp [rotZ])

def mixZ {k : ℕ} (d : ℕ) : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2) where
  toFun v j := v j + v (j + (d : ZMod k)) + v (j - (d : ZMod k))
  map_add' u v := by
    ext j
    simp only [Pi.add_apply]
    ring
  map_smul' c v := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

lemma coprime_three_mul_d {k d : ℕ} (hodd : Odd k) (h3 : k % 3 ≠ 0) (hd : d = 1 ∨ d = 2) :
    Nat.Coprime (3 * d) k := by
  have h2 : Nat.Coprime 2 k := by
    rcases hodd with ⟨m, rfl⟩
    rw [Nat.coprime_comm]
    simp [Nat.Coprime]
  have h3c : Nat.Coprime 3 k := by
    rw [Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)]
    intro hdv
    exact h3 (Nat.mod_eq_zero_of_dvd hdv)
  rcases hd with rfl | rfl
  · simpa using h3c
  · exact h3c.mul_left h2

lemma coprime_two_mul_d {k d : ℕ} (hodd : Odd k) (hd : d = 1 ∨ d = 2) :
    Nat.Coprime (2 * d) k := by
  have h2 : Nat.Coprime 2 k := by
    rcases hodd with ⟨m, rfl⟩
    rw [Nat.coprime_comm]
    simp [Nat.Coprime]
  rcases hd with rfl | rfl
  · simpa using h2
  · simpa using h2.mul_left h2

lemma mixZ_injective {k d : ℕ} [NeZero k] (hodd : Odd k) (h3 : k % 3 ≠ 0) (hd : d = 1 ∨ d = 2) :
    Function.Injective (mixZ (k := k) d) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hrel : ∀ j : ZMod k, v (j + (d : ZMod k)) = v j + v (j - (d : ZMod k)) := by
    intro j
    have hj := congrFun hv j
    simp only [mixZ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hj
    have h1 := congrArg (· + v (j + (d : ZMod k))) hj
    rw [zero_add] at h1
    have h2 : v j + v (j + (d : ZMod k)) + v (j - (d : ZMod k)) + v (j + (d : ZMod k)) =
        v j + v (j - (d : ZMod k)) := by
      have : v (j + (d : ZMod k)) + v (j + (d : ZMod k)) = 0 := zmod2_add_self _
      linear_combination this
    rw [h2] at h1
    exact h1.symm
  have hper3 : ∀ j : ZMod k, v (j + (3 * d : ℕ)) = v j := by
    intro j
    have h1 := hrel (j + (2 * d : ℕ))
    have h2 := hrel (j + (d : ZMod k))
    have e1 : j + (2 * d : ℕ) + (d : ZMod k) = j + (3 * d : ℕ) := by push_cast; ring
    have e2 : j + (2 * d : ℕ) - (d : ZMod k) = j + (d : ZMod k) := by push_cast; ring
    have e3 : j + (d : ZMod k) + (d : ZMod k) = j + (2 * d : ℕ) := by push_cast; ring
    have e4 : j + (d : ZMod k) - (d : ZMod k) = j := by ring
    rw [e1, e2] at h1
    rw [e3, e4] at h2
    rw [h1, h2]
    have hs : v (j + (d : ZMod k)) + v (j + (d : ZMod k)) = 0 := zmod2_add_self _
    linear_combination hs
  have hper3m : ∀ (m : ℕ) (j : ZMod k), v (j + (m : ZMod k) * (3 * d : ℕ)) = v j := by
    intro m
    induction m with
    | zero => intro j; simp
    | succ m ih =>
      intro j
      have e : j + ((m + 1 : ℕ) : ZMod k) * (3 * d : ℕ) =
          (j + (m : ZMod k) * (3 * d : ℕ)) + (3 * d : ℕ) := by push_cast; ring
      rw [e, hper3, ih]
  have hcop := coprime_three_mul_d hodd h3 hd
  have hunit : IsUnit ((3 * d : ℕ) : ZMod k) := (ZMod.isUnit_iff_coprime (3 * d) k).mpr hcop
  rcases hunit with ⟨u, hu⟩
  have hconst : ∀ j : ZMod k, v (j + 1) = v j := by
    intro j
    have hm : ((u⁻¹ : (ZMod k)ˣ).val.val : ZMod k) * (3 * d : ℕ) = 1 := by
      rw [ZMod.natCast_zmod_val, ← hu]
      exact Units.inv_mul u
    have := hper3m (u⁻¹ : (ZMod k)ˣ).val.val j
    rw [hm] at this
    exact this
  have hall : ∀ j : ZMod k, v j = v 0 := by
    intro j
    have hnat : ∀ m : ℕ, v (m : ZMod k) = v 0 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        push_cast
        rw [hconst, ih]
    rw [← ZMod.natCast_zmod_val j]
    exact hnat j.val
  ext j
  have h0 := congrFun hv 0
  simp only [mixZ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
  rw [hall (0 + (d : ZMod k)), hall (0 - (d : ZMod k)), zmod2_three_mul] at h0
  rw [hall j, h0]
  rfl

noncomputable def mixEquiv {k d : ℕ} [NeZero k] (hodd : Odd k) (h3 : k % 3 ≠ 0) (hd : d = 1 ∨ d = 2) :
    (ZMod k → ZMod 2) ≃ₗ[ZMod 2] (ZMod k → ZMod 2) :=
  LinearEquiv.ofBijective (mixZ (k := k) d)
    ⟨mixZ_injective hodd h3 hd, (Finite.injective_iff_surjective).mp (mixZ_injective hodd h3 hd)⟩

def stepZ {k : ℕ} (v : ZMod k → ZMod 2) (j : ZMod k) : ZMod 2 :=
  v j + (1 + v (j + 1)) * v (j + 2)

def D1 {α : Type*} [AddCommGroup α] (w : α) (F : α → ZMod 2) (x : α) : ZMod 2 :=
  F (x + w) + F x

def D2 {α : Type*} [AddCommGroup α] (w₁ w₂ : α) (F : α → ZMod 2) (x : α) : ZMod 2 :=
  D1 w₂ (D1 w₁ F) x

def D3 {α : Type*} [AddCommGroup α] (w₁ w₂ w₃ : α) (F : α → ZMod 2) (x : α) : ZMod 2 :=
  D1 w₃ (D2 w₁ w₂ F) x

def D4 {α : Type*} [AddCommGroup α] (w₁ w₂ w₃ w₄ : α) (F : α → ZMod 2) (x : α) : ZMod 2 :=
  D1 w₄ (D3 w₁ w₂ w₃ F) x

lemma D1_add {α : Type*} [AddCommGroup α] (w : α) (F G : α → ZMod 2) (x : α) :
    D1 w (fun y => F y + G y) x = D1 w F x + D1 w G x := by
  simp only [D1]; ring

lemma D1_smul {α : Type*} [AddCommGroup α] (w : α) (c : ZMod 2) (F : α → ZMod 2) (x : α) :
    D1 w (fun y => c * F y) x = c * D1 w F x := by
  simp only [D1]; ring

lemma D1_const {α : Type*} [AddCommGroup α] (w : α) (c : ZMod 2) (x : α) :
    D1 w (fun _ => c) x = 0 := by
  simp only [D1]; exact zmod2_add_self c

lemma D1_comm {α : Type*} [AddCommGroup α] (u v : α) (F : α → ZMod 2) (x : α) :
    D1 u (D1 v F) x = D1 v (D1 u F) x := by
  simp only [D1]
  rw [add_right_comm x v u]
  ring

lemma D1_self {α : Type*} [AddCommGroup α] (u : α) (F : α → ZMod 2)
    (h2 : ∀ y : α, y + y = 0) (x : α) :
    D1 u (D1 u F) x = 0 := by
  simp only [D1]
  rw [add_assoc x u u, h2 u, add_zero]
  have s1 := zmod2_add_self (F x)
  have s2 := zmod2_add_self (F (x + u))
  linear_combination s1 + s2

lemma D1_add_eq_of_two {α : Type*} [AddCommGroup α] (h2 : ∀ y : α, y + y = 0)
    (u v : α) (F : α → ZMod 2) (y : α) :
    D1 (v + u) (D1 u F) y = D1 v (D1 u F) y := by
  simp only [D1]
  have e1 : y + (v + u) + u = y + v := by rw [add_assoc, add_assoc v u u, h2 u, add_zero]
  have e2 : y + (v + u) = y + v + u := by abel
  rw [e1, e2]
  ring

lemma D1_sum {α ι : Type*} [AddCommGroup α] (s : Finset ι) (w : α) (F : ι → α → ZMod 2) (x : α) :
    D1 w (fun y => ∑ i ∈ s, F i y) x = ∑ i ∈ s, D1 w (F i) x := by
  simp only [D1, Finset.sum_add_distrib]

lemma D2_add {α : Type*} [AddCommGroup α] (u v : α) (F G : α → ZMod 2) (x : α) :
    D2 u v (fun y => F y + G y) x = D2 u v F x + D2 u v G x := by
  simp only [D2, D1]; ring

lemma D2_const {α : Type*} [AddCommGroup α] (u v : α) (c : ZMod 2) (x : α) :
    D2 u v (fun _ => c) x = 0 := by
  simp only [D2, D1, zmod2_add_self]

lemma D2_of_deg1 {α : Type*} [AddCommGroup α] {F : α → ZMod 2} {L : α → ZMod 2}
    (h1 : ∀ u x, D1 u F x = L u) (u v x : α) :
    D2 u v F x = 0 := by
  unfold D2
  rw [show D1 u F = fun _ => L u from funext (h1 u), D1_const]

lemma D3_add {α : Type*} [AddCommGroup α] (u v w : α) (F G : α → ZMod 2) (x : α) :
    D3 u v w (fun y => F y + G y) x = D3 u v w F x + D3 u v w G x := by
  simp only [D3, D2, D1]; ring

lemma D3_const {α : Type*} [AddCommGroup α] (u v w : α) (c : ZMod 2) (x : α) :
    D3 u v w (fun _ => c) x = 0 := by
  simp only [D3, D2, D1, zmod2_add_self]

lemma D3_of_deg2 {α : Type*} [AddCommGroup α] {F : α → ZMod 2} {B : α → α → ZMod 2}
    (h2 : ∀ u v x, D2 u v F x = B u v) (u v w x : α) :
    D3 u v w F x = 0 := by
  unfold D3
  rw [show D2 u v F = fun _ => B u v from funext (h2 u v), D1_const]

lemma D4_add {α : Type*} [AddCommGroup α] (w₁ w₂ w₃ w₄ : α) (F G : α → ZMod 2) (x : α) :
    D4 w₁ w₂ w₃ w₄ (fun y => F y + G y) x = D4 w₁ w₂ w₃ w₄ F x + D4 w₁ w₂ w₃ w₄ G x := by
  simp only [D4, D3, D2, D1]; ring

lemma D4_smul {α : Type*} [AddCommGroup α] (w₁ w₂ w₃ w₄ : α) (c : ZMod 2) (F : α → ZMod 2) (x : α) :
    D4 w₁ w₂ w₃ w₄ (fun y => c * F y) x = c * D4 w₁ w₂ w₃ w₄ F x := by
  simp only [D4, D3, D2, D1]; ring

lemma D4_sum {α ι : Type*} [AddCommGroup α] (s : Finset ι) (w₁ w₂ w₃ w₄ : α)
    (F : ι → α → ZMod 2) (x : α) :
    D4 w₁ w₂ w₃ w₄ (fun y => ∑ i ∈ s, F i y) x = ∑ i ∈ s, D4 w₁ w₂ w₃ w₄ (F i) x := by
  simp only [D4, D3, D2, D1, Finset.sum_add_distrib]

lemma D4_of_deg2 {α : Type*} [AddCommGroup α] {F : α → ZMod 2} {B : α → α → ZMod 2}
    (h2 : ∀ u v x, D2 u v F x = B u v) (w₁ w₂ w₃ w₄ x : α) :
    D4 w₁ w₂ w₃ w₄ F x = 0 := by
  unfold D4
  rw [show D3 w₁ w₂ w₃ F = fun _ => 0 from funext (D3_of_deg2 h2 w₁ w₂ w₃), D1_const]

lemma D1_mul {α : Type*} [AddCommGroup α] (w : α) (f g : α → ZMod 2) (x : α) :
    D1 w (fun y => f y * g y) x = D1 w f x * g x + f x * D1 w g x + D1 w f x * D1 w g x := by
  simp only [D1]
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination -(f (x + w) * g x + f x * g (x + w) + f x * g x) * h2

lemma D2_mul_deg1_deg1 {α : Type*} [AddCommGroup α] {f g : α → ZMod 2} {Lf Lg : α → ZMod 2}
    (hf : ∀ u x, D1 u f x = Lf u) (hg : ∀ u x, D1 u g x = Lg u) (u v x : α) :
    D2 u v (fun y => f y * g y) x = Lf u * Lg v + Lf v * Lg u := by
  have hfun : D1 u (fun y => f y * g y) = fun y => Lf u * g y + f y * Lg u + Lf u * Lg u := by
    funext y
    rw [D1_mul, hf, hg]
  unfold D2
  rw [hfun, D1_add, D1_add, D1_smul, D1_const, add_zero]
  have hmul : D1 v (fun y => f y * Lg u) x = Lf v * Lg u := by
    have : (fun y => f y * Lg u) = fun y => Lg u * f y := by funext y; ring
    rw [this, D1_smul, hf]
    ring
  rw [hmul, hg]

lemma D3_mul_deg1_deg1 {α : Type*} [AddCommGroup α] {f g : α → ZMod 2} {Lf Lg : α → ZMod 2}
    (hf : ∀ u x, D1 u f x = Lf u) (hg : ∀ u x, D1 u g x = Lg u) (u v w x : α) :
    D3 u v w (fun y => f y * g y) x = 0 := by
  unfold D3
  have hfun : D2 u v (fun y => f y * g y) = fun _ => Lf u * Lg v + Lf v * Lg u := by
    funext y
    exact D2_mul_deg1_deg1 hf hg u v y
  rw [hfun, D1_const]

lemma D3_mul_deg1_deg2 {α : Type*} [AddCommGroup α] {h g : α → ZMod 2}
    {L : α → ZMod 2} {B : α → α → ZMod 2}
    (hh : ∀ u x, D1 u h x = L u) (hg : ∀ u v x, D2 u v g x = B u v) (w₂ w₃ w₄ x : α) :
    D3 w₂ w₃ w₄ (fun y => h y * g y) x = L w₂ * B w₃ w₄ + L w₃ * B w₂ w₄ + L w₄ * B w₂ w₃ := by
  have h1 : D1 w₂ (fun y => h y * g y) =
      fun y => L w₂ * g y + h y * D1 w₂ g y + L w₂ * D1 w₂ g y := by
    funext y
    rw [D1_mul, hh]
  change D2 w₃ w₄ (D1 w₂ (fun y => h y * g y)) x = _
  rw [h1, D2_add, D2_add]
  have t1 : D2 w₃ w₄ (fun y => L w₂ * g y) x = L w₂ * B w₃ w₄ := by
    rw [← hg w₃ w₄ x]
    simp only [D2, D1]
    ring
  have hg1 : ∀ u y, D1 u (D1 w₂ g) y = B w₂ u := fun u y => hg w₂ u y
  have t2 : D2 w₃ w₄ (fun y => h y * D1 w₂ g y) x = L w₃ * B w₂ w₄ + L w₄ * B w₂ w₃ :=
    D2_mul_deg1_deg1 hh hg1 w₃ w₄ x
  have t3 : D2 w₃ w₄ (fun y => L w₂ * D1 w₂ g y) x = 0 := by
    have : D1 w₃ (fun y => L w₂ * D1 w₂ g y) = fun _ => L w₂ * B w₂ w₃ := by
      funext y; rw [D1_smul, hg1]
    unfold D2
    rw [this, D1_const]
  rw [t1, t2, t3, add_zero]
  ring

lemma D4_mul_deg2_deg2 {α : Type*} [AddCommGroup α] {f g : α → ZMod 2}
    {Bf Bg : α → α → ZMod 2}
    (hf : ∀ u v x, D2 u v f x = Bf u v) (hg : ∀ u v x, D2 u v g x = Bg u v)
    (w₁ w₂ w₃ w₄ x : α) :
    D4 w₁ w₂ w₃ w₄ (fun y => f y * g y) x =
      Bf w₁ w₂ * Bg w₃ w₄ + Bf w₃ w₄ * Bg w₁ w₂ +
      Bf w₁ w₃ * Bg w₂ w₄ + Bf w₂ w₄ * Bg w₁ w₃ +
      Bf w₁ w₄ * Bg w₂ w₃ + Bf w₂ w₃ * Bg w₁ w₄ := by
  have h1 : D1 w₁ (fun y => f y * g y) =
      fun y => D1 w₁ f y * g y + f y * D1 w₁ g y + D1 w₁ f y * D1 w₁ g y := by
    funext y
    exact D1_mul w₁ f g y
  change D3 w₂ w₃ w₄ (D1 w₁ (fun y => f y * g y)) x = _
  rw [h1, D3_add, D3_add]
  have hf1 : ∀ u y, D1 u (D1 w₁ f) y = Bf w₁ u := fun u y => hf w₁ u y
  have hg1 : ∀ u y, D1 u (D1 w₁ g) y = Bg w₁ u := fun u y => hg w₁ u y
  have t1 := D3_mul_deg1_deg2 hf1 hg w₂ w₃ w₄ x
  have t2 : D3 w₂ w₃ w₄ (fun y => f y * D1 w₁ g y) x =
      Bg w₁ w₂ * Bf w₃ w₄ + Bg w₁ w₃ * Bf w₂ w₄ + Bg w₁ w₄ * Bf w₂ w₃ := by
    have : (fun y => f y * D1 w₁ g y) = fun y => D1 w₁ g y * f y := by funext y; ring
    rw [this]
    exact D3_mul_deg1_deg2 hg1 hf w₂ w₃ w₄ x
  have t3 := D3_mul_deg1_deg1 hf1 hg1 w₂ w₃ w₄ x
  rw [t1, t2, t3, add_zero]
  ring

lemma D4_comm12 {α : Type*} [AddCommGroup α] (w₁ w₂ w₃ w₄ : α) (F : α → ZMod 2) (x : α) :
    D4 w₁ w₂ w₃ w₄ F x = D4 w₂ w₁ w₃ w₄ F x := by
  unfold D4 D3 D2
  have h : D1 w₂ (D1 w₁ F) = D1 w₁ (D1 w₂ F) := funext fun y => D1_comm w₂ w₁ F y
  rw [h]

lemma D4_comm23 {α : Type*} [AddCommGroup α] (w₁ w₂ w₃ w₄ : α) (F : α → ZMod 2) (x : α) :
    D4 w₁ w₂ w₃ w₄ F x = D4 w₁ w₃ w₂ w₄ F x := by
  unfold D4 D3 D2
  have h : D1 w₃ (D1 w₂ (D1 w₁ F)) = D1 w₂ (D1 w₃ (D1 w₁ F)) :=
    funext fun y => D1_comm w₃ w₂ (D1 w₁ F) y
  rw [h]

lemma D4_comm34 {α : Type*} [AddCommGroup α] (w₁ w₂ w₃ w₄ : α) (F : α → ZMod 2) (x : α) :
    D4 w₁ w₂ w₃ w₄ F x = D4 w₁ w₂ w₄ w₃ F x := by
  unfold D4 D3
  exact D1_comm w₄ w₃ (D2 w₁ w₂ F) x

def pDet {k : ℕ} (u v : ZMod k → ZMod 2) (i : ZMod k) : ZMod 2 :=
  u (i + 1) * v (i + 2) + v (i + 1) * u (i + 2)

def betaD {k : ℕ} (d : ℕ) (u v : ZMod k → ZMod 2) (r : ZMod k) : ZMod 2 :=
  pDet u v r + pDet u v (r + (d : ZMod k)) + pDet u v (r - (d : ZMod k))

lemma D2_stepZ_shift {k : ℕ} (c₀ : ZMod k → ZMod 2) (i : ZMod k) (u v x : ZMod k → ZMod 2) :
    D2 u v (fun w => stepZ (w + c₀) i) x = pDet u v i := by
  have heq : (fun w => stepZ (w + c₀) i) =
      fun w => (w i + c₀ i) + (w (i + 2) + c₀ (i + 2)) +
        (w (i + 1) + c₀ (i + 1)) * (w (i + 2) + c₀ (i + 2)) := by
    funext w
    simp only [stepZ, Pi.add_apply]
    ring
  rw [heq, D2_add, D2_add]
  have hlin : ∀ (r : ZMod k) (a b y : ZMod k → ZMod 2), D1 a (fun w => w r + c₀ r) y = a r := by
    intro r a _ y
    simp only [D1, Pi.add_apply]
    have h1 := zmod2_add_self (y r)
    have h2 := zmod2_add_self (c₀ r)
    linear_combination h1 + h2
  have h01 : D2 u v (fun w => w i + c₀ i) x = 0 :=
    D2_of_deg1 (fun a y => hlin i a v y) u v x
  have h02 : D2 u v (fun w => w (i + 2) + c₀ (i + 2)) x = 0 :=
    D2_of_deg1 (fun a y => hlin (i + 2) a v y) u v x
  have hprod : D2 u v (fun w => (w (i + 1) + c₀ (i + 1)) * (w (i + 2) + c₀ (i + 2))) x = pDet u v i :=
    D2_mul_deg1_deg1 (fun a y => hlin (i + 1) a v y) (fun a y => hlin (i + 2) a v y) u v x
  rw [h01, h02, hprod, zero_add, zero_add]

lemma D2_linear_add_const {k : ℕ} (L : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2))
    (c₁ : ZMod k → ZMod 2) (i : ZMod k) (u v x : ZMod k → ZMod 2) :
    D2 u v (fun w => L w i + c₁ i) x = 0 := by
  apply D2_of_deg1 (L := fun a => L a i)
  intro a y
  simp only [D1, map_add, Pi.add_apply]
  have h1 := zmod2_add_self (L y i)
  have h2 := zmod2_add_self (c₁ i)
  linear_combination h1 + h2

lemma D2_Y {k : ℕ} (d : ℕ) (c₀ c₁ : ZMod k → ZMod 2)
    (L : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2))
    (r : ZMod k) (u v x : ZMod k → ZMod 2) :
    D2 u v (fun w => mixZ d (fun i => stepZ (w + c₀) i + L w i + c₁ i) r) x = betaD d u v r := by
  have h1 : ∀ (i : ZMod k), D2 u v (fun w => stepZ (w + c₀) i + L w i + c₁ i) x = pDet u v i := by
    intro i
    have : (fun w => stepZ (w + c₀) i + L w i + c₁ i) =
        fun w => stepZ (w + c₀) i + (L w i + c₁ i) := by funext w; ring
    rw [this, D2_add, D2_stepZ_shift, D2_linear_add_const, add_zero]
  simp only [mixZ, LinearMap.coe_mk, AddHom.coe_mk]
  rw [D2_add, D2_add, h1 r, h1 (r + (d : ZMod k)), h1 (r - (d : ZMod k))]
  rfl

lemma D4_Z_formula {k : ℕ} (d : ℕ) (c₀ c₁ : ZMod k → ZMod 2)
    (L : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2))
    (j : ZMod k) (w₁ w₂ w₃ w₄ : ZMod k → ZMod 2) :
    let Y := fun w => mixZ d (fun i => stepZ (w + c₀) i + L w i + c₁ i)
    D4 w₁ w₂ w₃ w₄ (fun w => stepZ (Y w) j) 0 =
      betaD d w₁ w₂ (j + 1) * betaD d w₃ w₄ (j + 2) +
      betaD d w₃ w₄ (j + 1) * betaD d w₁ w₂ (j + 2) +
      betaD d w₁ w₃ (j + 1) * betaD d w₂ w₄ (j + 2) +
      betaD d w₂ w₄ (j + 1) * betaD d w₁ w₃ (j + 2) +
      betaD d w₁ w₄ (j + 1) * betaD d w₂ w₃ (j + 2) +
      betaD d w₂ w₃ (j + 1) * betaD d w₁ w₄ (j + 2) := by
  intro Y
  have hstep : (fun w => stepZ (Y w) j) =
      fun w => Y w j + Y w (j + 2) + Y w (j + 1) * Y w (j + 2) := by
    funext w; simp only [stepZ]; ring
  rw [hstep, D4_add, D4_add]
  have h01 : D4 w₁ w₂ w₃ w₄ (fun w => Y w j) 0 = 0 :=
    D4_of_deg2 (fun u v x => D2_Y d c₀ c₁ L j u v x) w₁ w₂ w₃ w₄ 0
  have h02 : D4 w₁ w₂ w₃ w₄ (fun w => Y w (j + 2)) 0 = 0 :=
    D4_of_deg2 (fun u v x => D2_Y d c₀ c₁ L (j + 2) u v x) w₁ w₂ w₃ w₄ 0
  have hprod := D4_mul_deg2_deg2
    (fun u v x => D2_Y d c₀ c₁ L (j + 1) u v x)
    (fun u v x => D2_Y d c₀ c₁ L (j + 2) u v x)
    w₁ w₂ w₃ w₄ 0
  rw [h01, h02, hprod, zero_add, zero_add]

lemma zmod_nat_ne_zero {k m : ℕ} [NeZero k] (hpos : 0 < m) (hlt : m < k) :
    (m : ZMod k) ≠ 0 := by
  intro h
  have := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at this
  omega

lemma pDet_evec_evec_zero {k : ℕ} [NeZero k] {r s : ZMod k}
    (h1 : s - r ≠ 1) (h2 : r - s ≠ 1) (i : ZMod k) :
    pDet (evec r) (evec s) i = 0 := by
  unfold pDet evec
  have t1 : (if i + 1 = r then (1 : ZMod 2) else 0) * (if i + 2 = s then 1 else 0) = 0 := by
    by_cases c1 : i + 1 = r
    · by_cases c2 : i + 2 = s
      · exfalso; apply h1; rw [← c2, ← c1]; ring
      · simp [c1, c2]
    · simp [c1]
  have t2 : (if i + 1 = s then (1 : ZMod 2) else 0) * (if i + 2 = r then 1 else 0) = 0 := by
    by_cases c1 : i + 1 = s
    · by_cases c2 : i + 2 = r
      · exfalso; apply h2; rw [← c2, ← c1]; ring
      · simp [c1, c2]
    · simp [c1]
  rw [t1, t2, add_zero]

lemma pDet_u_evec {k : ℕ} [NeZero k] (_hk : 2 < k) (u : ZMod k → ZMod 2) (s i : ZMod k) :
    pDet u (evec s) i =
      (if i = s - 2 then u (s - 1) else 0) + (if i = s - 1 then u (s + 1) else 0) := by
  unfold pDet evec
  have h1 : i + 2 = s ↔ i = s - 2 := by
    constructor <;> intro h <;> linear_combination h
  have h2 : i + 1 = s ↔ i = s - 1 := by
    constructor <;> intro h <;> linear_combination h
  have t1 : u (i + 1) * (if i + 2 = s then (1 : ZMod 2) else 0) = if i = s - 2 then u (s - 1) else 0 := by
    by_cases ha : i = s - 2
    · have ha' : i + 2 = s := h1.mpr ha
      have hi1 : i + 1 = s - 1 := by rw [ha]; ring
      rw [if_pos ha', if_pos ha, mul_one, hi1]
    · have ha' : ¬ i + 2 = s := fun h => ha (h1.mp h)
      rw [if_neg ha', if_neg ha, mul_zero]
  have t2 : (if i + 1 = s then (1 : ZMod 2) else 0) * u (i + 2) = if i = s - 1 then u (s + 1) else 0 := by
    by_cases hb : i = s - 1
    · have hb' : i + 1 = s := h2.mpr hb
      have hi2 : i + 2 = s + 1 := by rw [hb]; ring
      rw [if_pos hb', if_pos hb, one_mul, hi2]
    · have hb' : ¬ i + 1 = s := fun h => hb (h2.mp h)
      rw [if_neg hb', if_neg hb, zero_mul]
  rw [t1, t2]

lemma betaD_u_evec_eq_zero_of_out {k d : ℕ} [NeZero k] (hk : 4 * d + 4 < k)
    (u : ZMod k → ZMod 2) (s r : ZMod k)
    (hout : 2 * d + 1 < (r - s + (2 + d : ℕ)).val) :
    betaD d u (evec s) r = 0 := by
  unfold betaD
  have hk2 : 2 < k := by omega
  have hp : ∀ (t : ZMod k), t ≠ s - 2 → t ≠ s - 1 → pDet u (evec s) t = 0 := by
    intro t ht1 ht2
    rw [pDet_u_evec hk2]
    simp [ht1, ht2]
  have hneq : ∀ (m : ℕ), m ≤ 2 * d + 1 → r - s + (2 + d : ℕ) ≠ (m : ZMod k) := by
    intro m hm heq
    rw [heq, ZMod.val_natCast_of_lt (by omega)] at hout
    omega
  have hr1 : r ≠ s - 2 := fun h => hneq d (by omega) (by rw [h]; push_cast; ring)
  have hr2 : r ≠ s - 1 := fun h => hneq (d + 1) (by omega) (by rw [h]; push_cast; ring)
  have hrd1 : r + (d : ZMod k) ≠ s - 2 := fun h => hneq 0 (by omega) (by push_cast; linear_combination h)
  have hrd2 : r + (d : ZMod k) ≠ s - 1 := fun h => hneq 1 (by omega) (by push_cast; linear_combination h)
  have hrm1 : r - (d : ZMod k) ≠ s - 2 := fun h => hneq (2 * d) (by omega) (by
    have : r = s - 2 + (d : ZMod k) := by linear_combination h
    rw [this]; push_cast; ring)
  have hrm2 : r - (d : ZMod k) ≠ s - 1 := fun h => hneq (2 * d + 1) (by omega) (by
    have : r = s - 1 + (d : ZMod k) := by linear_combination h
    rw [this]; push_cast; ring)
  rw [hp r hr1 hr2, hp (r + d) hrd1 hrd2, hp (r - d) hrm1 hrm2]
  simp

lemma betaD_u_evec_at_upper {k d : ℕ} [NeZero k] (hd : d = 1 ∨ d = 2) (hk : 4 * d + 4 < k)
    (u : ZMod k → ZMod 2) (a : ZMod k) :
    betaD d u (evec (a - 1)) (a + (d : ZMod k) - 2) = u a := by
  unfold betaD
  have hk2 : 2 < k := by omega
  rw [pDet_u_evec hk2, pDet_u_evec hk2, pDet_u_evec hk2]
  have hne : ∀ m : ℕ, 0 < m → m < k → (m : ZMod k) ≠ 0 := fun m h1 h2 => zmod_nat_ne_zero h1 h2
  have c1 : a + (d : ZMod k) - 2 ≠ a - 1 - 2 := by
    intro h; exact hne (d + 1) (by omega) (by omega) (by push_cast; linear_combination h)
  have c2 : a + (d : ZMod k) - 2 ≠ a - 1 - 1 := by
    intro h; exact hne d (by omega) (by omega) (by linear_combination h)
  have c3 : a + (d : ZMod k) - 2 + (d : ZMod k) ≠ a - 1 - 2 := by
    intro h; exact hne (2 * d + 1) (by omega) (by omega) (by push_cast; linear_combination h)
  have c4 : a + (d : ZMod k) - 2 + (d : ZMod k) ≠ a - 1 - 1 := by
    intro h; exact hne (2 * d) (by omega) (by omega) (by push_cast; linear_combination h)
  have c5 : a + (d : ZMod k) - 2 - (d : ZMod k) ≠ a - 1 - 2 := by
    intro h; exact hne 1 (by omega) (by omega) (by push_cast; linear_combination h)
  have c6 : a + (d : ZMod k) - 2 - (d : ZMod k) = a - 1 - 1 := by ring
  have c7 : a - 1 + 1 = a := by ring
  rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_neg c5, if_pos c6, c7]
  ring

lemma betaD_u_evec_at_lower {k d : ℕ} [NeZero k] (hd : d = 1 ∨ d = 2) (hk : 4 * d + 4 < k)
    (u : ZMod k → ZMod 2) (b : ZMod k) :
    betaD d u (evec (b + 1)) (b - (d : ZMod k) - 1) = u b := by
  unfold betaD
  have hk2 : 2 < k := by omega
  rw [pDet_u_evec hk2, pDet_u_evec hk2, pDet_u_evec hk2]
  have hne : ∀ m : ℕ, 0 < m → m < k → (m : ZMod k) ≠ 0 := fun m h1 h2 => zmod_nat_ne_zero h1 h2
  have c1 : b - (d : ZMod k) - 1 ≠ b + 1 - 2 := by
    intro h; exact hne d (by omega) (by omega) (by linear_combination -h)
  have c2 : b - (d : ZMod k) - 1 ≠ b + 1 - 1 := by
    intro h; exact hne (d + 1) (by omega) (by omega) (by push_cast; linear_combination -h)
  have c3 : b - (d : ZMod k) - 1 + (d : ZMod k) = b + 1 - 2 := by ring
  have c4 : b - (d : ZMod k) - 1 + (d : ZMod k) ≠ b + 1 - 1 := by
    intro h; exact hne 1 (by omega) (by omega) (by push_cast; linear_combination -h)
  have c5 : b - (d : ZMod k) - 1 - (d : ZMod k) ≠ b + 1 - 2 := by
    intro h; exact hne (2 * d) (by omega) (by omega) (by push_cast; linear_combination -h)
  have c6 : b - (d : ZMod k) - 1 - (d : ZMod k) ≠ b + 1 - 1 := by
    intro h; exact hne (2 * d + 1) (by omega) (by omega) (by push_cast; linear_combination -h)
  have c7 : b + 1 - 1 = b := by ring
  rw [if_neg c1, if_neg c2, if_pos c3, if_neg c4, if_neg c5, if_neg c6, c7]
  ring

lemma D4_Z_endpoint {k d : ℕ} [NeZero k] (hd : d = 1 ∨ d = 2) (hk : 4 * d + 4 < k)
    (c₀ c₁ : ZMod k → ZMod 2) (L : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2))
    (a j : ZMod k) (u v : ZMod k → ZMod 2) :
    let b := a + (2 * d : ℕ)
    let Y := fun w => mixZ d (fun i => stepZ (w + c₀) i + L w i + c₁ i)
    D4 u v (evec (a - 1)) (evec (b + 1)) (fun w => stepZ (Y w) j) 0 =
      if j = a + (d : ZMod k) - 3 then u a * v b + v a * u b else 0 := by
  intro b Y
  rw [D4_Z_formula]
  have hpp : ∀ r : ZMod k, betaD d (evec (a - 1)) (evec (b + 1)) r = 0 := by
    intro r
    unfold betaD
    have h1 : (b + 1) - (a - 1) ≠ 1 := by
      intro h
      have : ((2 * d + 1 : ℕ) : ZMod k) = 0 := by
        dsimp only [b] at h; push_cast at h ⊢; linear_combination h
      exact zmod_nat_ne_zero (by omega) (by omega) this
    have h2 : (a - 1) - (b + 1) ≠ 1 := by
      intro h
      have : ((2 * d + 3 : ℕ) : ZMod k) = 0 := by
        dsimp only [b] at h; push_cast at h ⊢; linear_combination -h
      exact zmod_nat_ne_zero (by omega) (by omega) this
    rw [pDet_evec_evec_zero h1 h2, pDet_evec_evec_zero h1 h2, pDet_evec_evec_zero h1 h2]
    simp
  rw [hpp (j + 1), hpp (j + 2)]
  simp only [mul_zero, zero_mul, zero_add]
  have hcross_zero : ∀ (x y : ZMod k → ZMod 2),
      betaD d x (evec (b + 1)) (j + 1) * betaD d y (evec (a - 1)) (j + 2) = 0 := by
    intro x y
    by_cases h1 : 2 * d + 1 < ((j + 1) - (b + 1) + (2 + d : ℕ)).val
    · rw [betaD_u_evec_eq_zero_of_out hk x (b + 1) (j + 1) h1, zero_mul]
    · push Not at h1
      have h2 : 2 * d + 1 < ((j + 2) - (a - 1) + (2 + d : ℕ)).val := by
        set z := (j + 1) - (b + 1) + (2 + d : ℕ)
        have hrel : (j + 2) - (a - 1) + (2 + d : ℕ) = z + ((2 * d + 3 : ℕ) : ZMod k) := by
          dsimp only [z, b]; push_cast; ring
        rw [hrel]
        have hz : z = (z.val : ZMod k) := (ZMod.natCast_zmod_val z).symm
        rw [hz, ← Nat.cast_add, ZMod.val_natCast_of_lt (by omega)]
        omega
      rw [betaD_u_evec_eq_zero_of_out hk y (a - 1) (j + 2) h2, mul_zero]
  rw [hcross_zero v u, hcross_zero u v, add_zero]
  have h1' : betaD d u (evec (a - 1)) (j + 1) * betaD d v (evec (b + 1)) (j + 2) + 0 +
      betaD d v (evec (a - 1)) (j + 1) * betaD d u (evec (b + 1)) (j + 2) =
      betaD d u (evec (a - 1)) (j + 1) * betaD d v (evec (b + 1)) (j + 2) +
      betaD d v (evec (a - 1)) (j + 1) * betaD d u (evec (b + 1)) (j + 2) := by ring
  rw [h1']
  by_cases hj : j = a + (d : ZMod k) - 3
  · subst hj
    simp only [ite_true]
    have e1 : a + (d : ZMod k) - 3 + 1 = a + (d : ZMod k) - 2 := by ring
    have e2 : a + (d : ZMod k) - 3 + 2 = b - (d : ZMod k) - 1 := by dsimp only [b]; push_cast; ring
    rw [e1, e2, betaD_u_evec_at_upper hd hk u a, betaD_u_evec_at_lower hd hk v b,
        betaD_u_evec_at_upper hd hk v a, betaD_u_evec_at_lower hd hk u b]
  · simp only [hj, ite_false]
    have hprod_zero : ∀ (x y : ZMod k → ZMod 2),
        betaD d x (evec (a - 1)) (j + 1) * betaD d y (evec (b + 1)) (j + 2) = 0 := by
      intro x y
      by_cases h1 : 2 * d + 1 < ((j + 1) - (a - 1) + (2 + d : ℕ)).val
      · rw [betaD_u_evec_eq_zero_of_out hk x (a - 1) (j + 1) h1, zero_mul]
      · push Not at h1
        have hlt : ((j + 1) - (a - 1) + (2 + d : ℕ)).val < 2 * d + 1 := by
          by_contra hge
          have heq : ((j + 1) - (a - 1) + (2 + d : ℕ)).val = 2 * d + 1 := by omega
          have hz : (j + 1) - (a - 1) + ((2 + d : ℕ) : ZMod k) = ((2 * d + 1 : ℕ) : ZMod k) := by
            rw [← ZMod.natCast_zmod_val ((j + 1) - (a - 1) + ((2 + d : ℕ) : ZMod k)), heq]
          apply hj
          push_cast at hz
          linear_combination hz
        have h2 : 2 * d + 1 < ((j + 2) - (b + 1) + (2 + d : ℕ)).val := by
          set z := (j + 1) - (a - 1) + (2 + d : ℕ)
          have hrel : (j + 2) - (b + 1) + (2 + d : ℕ) = z + ((k - (2 * d + 1) : ℕ) : ZMod k) := by
            have hk_eq : ((k - (2 * d + 1) : ℕ) : ZMod k) = -((2 * d + 1 : ℕ) : ZMod k) := by
              rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
            rw [hk_eq]
            dsimp only [z, b]
            push_cast
            ring
          rw [hrel]
          have hz : z = (z.val : ZMod k) := (ZMod.natCast_zmod_val z).symm
          rw [hz, ← Nat.cast_add, ZMod.val_natCast_of_lt (by omega)]
          omega
        rw [betaD_u_evec_eq_zero_of_out hk y (b + 1) (j + 2) h2, mul_zero]
    rw [hprod_zero u v, hprod_zero v u, add_zero]

lemma D4_Z_quad {k d : ℕ} [NeZero k] (hd : d = 1 ∨ d = 2) (hk : 4 * d + 4 < k)
    (c₀ c₁ : ZMod k → ZMod 2) (L : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2))
    (a j : ZMod k) :
    let b := a + (2 * d : ℕ)
    let Y := fun w => mixZ d (fun i => stepZ (w + c₀) i + L w i + c₁ i)
    D4 (evec a) (evec b) (evec (a - 1)) (evec (b + 1)) (fun w => stepZ (Y w) j) 0 =
      if j = a + (d : ZMod k) - 3 then 1 else 0 := by
  intro b Y
  rw [D4_Z_endpoint hd hk c₀ c₁ L a j (evec a) (evec b)]
  have hne : a ≠ b := by
    intro h
    have : ((2 * d : ℕ) : ZMod k) = 0 := by dsimp only [b] at h; linear_combination -h
    exact zmod_nat_ne_zero (by omega) (by omega) this
  have hb_eq : a + 2 * (d : ZMod k) = b := by dsimp only [b]; push_cast; ring
  simp [evec, hne, hb_eq]

lemma D2_sep_zero {k : ℕ} (Q : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2))
    (_hQ : ∀ w, Q (Q w) = Q w)
    (F : (ZMod k → ZMod 2) → ZMod 2)
    (left right : (ZMod k → ZMod 2) → ZMod 2)
    (hsep : ∀ x y, F (Q x + (y - Q y)) = left x + right y)
    {u v : ZMod k → ZMod 2} (hu : Q u = u) (hv : Q v = 0) (x : ZMod k → ZMod 2) :
    D2 u v F x = 0 := by
  have h1 : x = Q x + (x - Q x) := by abel
  have h2 : x + u = Q (x + u) + (x - Q x) := by
    rw [map_add, hu]; abel
  have h3 : x + v = Q x + ((x + v) - Q (x + v)) := by
    rw [map_add, hv, add_zero]; abel
  have h4 : x + u + v = Q (x + u) + ((x + v) - Q (x + v)) := by
    rw [map_add, map_add, hu, hv, add_zero]; abel
  have f1 : F x = left x + right x := by conv_lhs => rw [h1]; exact hsep x x
  have f2 : F (x + u) = left (x + u) + right x := by conv_lhs => rw [h2]; exact hsep (x + u) x
  have f3 : F (x + v) = left x + right (x + v) := by conv_lhs => rw [h3]; exact hsep x (x + v)
  have f4 : F (x + u + v) = left (x + u) + right (x + v) := by
    conv_lhs => rw [h4]; exact hsep (x + u) (x + v)
  simp only [D2, D1]
  have e : x + v + u = x + u + v := by abel
  rw [e, f4, f3, f2, f1]
  have s1 := zmod2_add_self (left (x + u))
  have s2 := zmod2_add_self (left x)
  have s3 := zmod2_add_self (right (x + v))
  have s4 := zmod2_add_self (right x)
  linear_combination s1 + s2 + s3 + s4

lemma D4_sep_zero {k : ℕ} (Q : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2))
    (hQ : ∀ w, Q (Q w) = Q w)
    (F : (ZMod k → ZMod 2) → ZMod 2)
    (left right : (ZMod k → ZMod 2) → ZMod 2)
    (hsep : ∀ x y, F (Q x + (y - Q y)) = left x + right y)
    {u v : ZMod k → ZMod 2} (hu : Q u = u) (hv : Q v = 0) (w₃ w₄ x : ZMod k → ZMod 2) :
    D4 u v w₃ w₄ F x = 0 := by
  unfold D4 D3
  have h : D2 u v F = fun _ => 0 := funext fun y => D2_sep_zero Q hQ F left right hsep hu hv y
  rw [h]
  simp only [D1, zmod2_add_self]

lemma det_zero_implies_block {k : ℕ} (Q : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2))
    (hQ : ∀ w, Q (Q w) = Q w) {a b : ZMod k} (hab : a ≠ b)
    (hdet : ∀ u v : ZMod k → ZMod 2, Q u = u → Q v = 0 → u a * v b + v a * u b = 0) :
    (∀ u, Q u = u → u a = 0 ∧ u b = 0) ∨ (∀ v, Q v = 0 → v a = 0 ∧ v b = 0) := by
  by_contra h
  push Not at h
  rcases h with ⟨⟨u, hu, hu_ne⟩, ⟨v, hv, hv_ne⟩⟩
  have hpair : ∀ x y : ZMod k → ZMod 2, Q x = x → Q y = 0 →
      (x a ≠ 0 ∨ x b ≠ 0) → (y a ≠ 0 ∨ y b ≠ 0) → x a = y a ∧ x b = y b := by
    intro x y hx hy hxne hyne
    have hd := hdet x y hx hy
    rcases zmod2_eq_zero_or_one (x a) with hxa | hxa <;>
    rcases zmod2_eq_zero_or_one (x b) with hxb | hxb <;>
    rcases zmod2_eq_zero_or_one (y a) with hya | hya <;>
    rcases zmod2_eq_zero_or_one (y b) with hyb | hyb <;>
    simp [hxa, hxb, hya, hyb] at hd hxne hyne ⊢
  have huv := hpair u v hu hv
    (if ha : u a = 0 then Or.inr (hu_ne ha) else Or.inl ha)
    (if ha : v a = 0 then Or.inr (hv_ne ha) else Or.inl ha)
  have hA_col : ∀ x, Q x = x → x a * v b + v a * x b = 0 := fun x hx => hdet x v hx hv
  have hB_col : ∀ y, Q y = 0 → u a * y b + y a * u b = 0 := fun y hy => hdet u y hu hy
  have hAll_col : ∀ w : ZMod k → ZMod 2, w a * v b + v a * w b = 0 := by
    intro w
    have hw : w = Q w + (w - Q w) := by abel
    have h1 := hA_col (Q w) (hQ w)
    have h2 := hB_col (w - Q w) (by rw [map_sub, hQ, sub_self])
    rw [huv.1, huv.2] at h2
    have hwa : w a = Q w a + (w - Q w) a := by rw [← Pi.add_apply, ← hw]
    have hwb : w b = Q w b + (w - Q w) b := by rw [← Pi.add_apply, ← hw]
    rw [hwa, hwb]
    linear_combination h1 + h2
  have ha0 := hAll_col (evec a)
  have hb0 := hAll_col (evec b)
  simp [evec, hab, hab.symm] at ha0 hb0
  exact hv_ne hb0 ha0

lemma singleton_contradiction {k d : ℕ} [NeZero k] (hd : d = 1 ∨ d = 2) (hk : 4 * d + 4 < k)
    (c₀ c₁ : ZMod k → ZMod 2) (L : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2))
    (Q : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2)) (hQ : ∀ w, Q (Q w) = Q w)
    (hQpos : 0 < Module.finrank (ZMod 2) (LinearMap.range Q))
    (K : Finset (ZMod k)) (hKcard : K.card ≤ 2)
    (hM_unit : ∀ j : ZMod k, j ∉ K →
      ∀ u v w₃ w₄ : ZMod k → ZMod 2, Q u = u → Q v = 0 →
        D4 u v w₃ w₄ (fun w => stepZ (mixZ d (fun i => stepZ (w + c₀) i + L w i + c₁ i)) j) 0 = 0)
    (s : ZMod k) (hvan : ∀ u, Q u = u → ∀ i ≠ s, u i = 0) : False := by
  have he_in_A : Q (evec s) = evec s := by
    have hne : ∃ u ∈ LinearMap.range Q, u ≠ 0 := by
      by_contra h
      push Not at h
      have hbot : LinearMap.range Q = ⊥ := by
        ext u; simp only [Submodule.mem_bot]
        exact ⟨h u, fun hu => hu ▸ Submodule.zero_mem _⟩
      rw [hbot, finrank_bot] at hQpos
      omega
    rcases hne with ⟨u, ⟨w, rfl⟩, hu0⟩
    have hQu : Q (Q w) = Q w := hQ w
    have hus : Q w s = 1 := by
      rcases zmod2_eq_zero_or_one (Q w s) with h0 | h1
      · exfalso; apply hu0; ext i
        by_cases his : i = s
        · subst his; exact h0
        · exact hvan (Q w) hQu i his
      · exact h1
    have heq : Q w = evec s := by
      ext i
      by_cases his : i = s
      · subst his; simp [evec, hus]
      · simp [evec, his, hvan (Q w) hQu i his]
    rw [← heq]
    exact hQu
  have hpartner : ∀ t : ZMod k, t ≠ s → ∃ v : ZMod k → ZMod 2, Q v = 0 ∧
      ∃ lam : ZMod 2, v = evec t + lam • evec s := by
    intro t _
    have hQt : Q (Q (evec t)) = Q (evec t) := hQ (evec t)
    have hQeq : Q (evec t) = (Q (evec t) s) • evec s := by
      ext i
      by_cases his : i = s
      · subst his; simp [evec]
      · simp [evec, his, hvan (Q (evec t)) hQt i his]
    refine ⟨evec t - Q (evec t), by rw [map_sub, hQ, sub_self], Q (evec t) s, ?_⟩
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show Q (evec t) i = Q (evec t) s * evec s i from congrFun hQeq i]
    exact zmod2_sub_eq_add _ _
  have hfour_in_K : ∀ a : ZMod k,
      (s = a - 1 ∨ s = a ∨ s = a + (2 * d : ℕ) ∨ s = a + (2 * d : ℕ) + 1) →
      a + (d : ZMod k) - 3 ∈ K := by
    intro a hmem
    by_contra hnotK
    set b := a + (2 * d : ℕ)
    set j := a + (d : ZMod k) - 3
    have hne : ∀ m : ℕ, 0 < m → m < k → (m : ZMod k) ≠ 0 := fun m h1 h2 => zmod_nat_ne_zero h1 h2
    have hD4_1 : D4 (evec a) (evec b) (evec (a - 1)) (evec (b + 1))
        (fun w => stepZ (mixZ d (fun i => stepZ (w + c₀) i + L w i + c₁ i)) j) 0 = 1 := by
      simpa [b, j] using D4_Z_quad hd hk c₀ c₁ L a j
    have hkill_gen : ∀ (F : (ZMod k → ZMod 2) → ZMod 2),
        (∀ u v w₃ w₄, Q u = u → Q v = 0 → D4 u v w₃ w₄ F 0 = 0) →
        ∀ (i : ZMod k) (w₃ w₄ : ZMod k → ZMod 2), i ≠ s → D4 (evec s) (evec i) w₃ w₄ F 0 = 0 := by
      intro F hF i w₃ w₄ his
      rcases hpartner i his with ⟨v, hv, lam, hv_eq⟩
      have hz := hF (evec s) v w₃ w₄ he_in_A hv
      rw [hv_eq] at hz
      rcases zmod2_eq_zero_or_one lam with rfl | rfl
      · simpa using hz
      · rw [one_smul] at hz
        have hfun : D1 (evec i + evec s) (D1 (evec s) F) = D1 (evec i) (D1 (evec s) F) :=
          funext fun y => D1_add_eq_of_two (fun z => by ext r; exact zmod2_add_self _) (evec s) (evec i) F y
        unfold D4 D3 D2 at hz ⊢
        rw [hfun] at hz
        exact hz
    have hkill := hkill_gen _ (hM_unit j hnotK)
    generalize (fun w => stepZ (mixZ d (fun i => stepZ (w + c₀) i + L w i + c₁ i)) j) = F at hD4_1 hkill
    have h01 : (0 : ZMod 2) ≠ 1 := by decide
    rcases hmem with hs | hs | hs | hs
    · have hne1 : a ≠ s := by
        intro h; rw [hs] at h; exact hne 1 (by omega) (by omega) (by push_cast; linear_combination h)
      have h0 := hkill a (evec b) (evec (b + 1)) hne1
      rw [hs] at h0
      rw [D4_comm23, D4_comm12] at hD4_1
      exact h01 (h0.symm.trans hD4_1)
    · have hne1 : b ≠ s := by
        intro h; rw [hs] at h
        exact hne (2 * d) (by omega) (by omega) (by dsimp only [b] at h; linear_combination h)
      have h0 := hkill b (evec (a - 1)) (evec (b + 1)) hne1
      rw [hs] at h0
      exact h01 (h0.symm.trans hD4_1)
    · have hne1 : a ≠ s := by
        intro h; rw [hs] at h
        exact hne (2 * d) (by omega) (by omega) (by linear_combination -h)
      have h0 := hkill a (evec (a - 1)) (evec (b + 1)) hne1
      rw [hs] at h0
      rw [D4_comm12] at hD4_1
      exact h01 (h0.symm.trans hD4_1)
    · have hne1 : a ≠ s := by
        intro h; rw [hs] at h
        exact hne (2 * d + 1) (by omega) (by omega) (by dsimp only [b] at h; push_cast at h ⊢; linear_combination -h)
      have h0 := hkill a (evec b) (evec (a - 1)) hne1
      rw [hs] at h0
      rw [D4_comm34, D4_comm23, D4_comm12] at hD4_1
      exact h01 (h0.symm.trans hD4_1)
  have j1 : s + (d : ZMod k) - 2 ∈ K := by
    have := hfour_in_K (s + 1) (Or.inl (by ring))
    have e : s + 1 + (d : ZMod k) - 3 = s + (d : ZMod k) - 2 := by ring
    rwa [e] at this
  have j2 : s + (d : ZMod k) - 3 ∈ K := hfour_in_K s (Or.inr (Or.inl rfl))
  have j3 : s - (d : ZMod k) - 3 ∈ K := by
    have := hfour_in_K (s - (2 * d : ℕ)) (Or.inr (Or.inr (Or.inl (by ring))))
    have e : s - (2 * d : ℕ) + (d : ZMod k) - 3 = s - (d : ZMod k) - 3 := by push_cast; ring
    rwa [e] at this
  have hne : ∀ m : ℕ, 0 < m → m < k → (m : ZMod k) ≠ 0 := fun m h1 h2 => zmod_nat_ne_zero h1 h2
  have h12 : s + (d : ZMod k) - 2 ≠ s + (d : ZMod k) - 3 := fun h =>
    hne 1 (by omega) (by omega) (by push_cast; linear_combination h)
  have h13 : s + (d : ZMod k) - 2 ≠ s - (d : ZMod k) - 3 := fun h =>
    hne (2 * d + 1) (by omega) (by omega) (by push_cast; linear_combination h)
  have h23 : s + (d : ZMod k) - 3 ≠ s - (d : ZMod k) - 3 := fun h =>
    hne (2 * d) (by omega) (by omega) (by push_cast; linear_combination h)
  have hsub : ({s + (d : ZMod k) - 2, s + (d : ZMod k) - 3, s - (d : ZMod k) - 3} : Finset (ZMod k)) ⊆ K := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact j1
    · exact j2
    · exact j3
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton] at hcard
  · omega
  · simp [h23]
  · simp [h12, h13]

lemma main_zmod {k d : ℕ} [NeZero k] (hodd : Odd k) (_h3 : k % 3 ≠ 0)
    (hd : d = 1 ∨ d = 2) (hk : 4 * d + 4 < k)
    (c₀ c₁ : ZMod k → ZMod 2) (L : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2))
    (Q : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2)) (hQ : ∀ w, Q (Q w) = Q w)
    (hQpos : 0 < Module.finrank (ZMod 2) (LinearMap.range Q))
    (hQlt : Module.finrank (ZMod 2) (LinearMap.range Q) < k) :
    let Y := fun w => mixZ d (fun i => stepZ (w + c₀) i + L w i + c₁ i)
    let M : Submodule (ZMod 2) (ZMod k → ZMod 2) :=
      { carrier := { mask | ∃ left right : (ZMod k → ZMod 2) → ZMod 2, ∀ x y,
          (∑ j : ZMod k, mask j * stepZ (Y (Q x + (y - Q y))) j) = left x + right y }, add_mem' := by
          rintro m₁ m₂ ⟨l₁, r₁, h₁⟩ ⟨l₂, r₂, h₂⟩
          refine ⟨fun x => l₁ x + l₂ x, fun y => r₁ y + r₂ y, fun x y => ?_⟩
          simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, h₁ x y, h₂ x y]
          ring,
        zero_mem' := ⟨fun _ => 0, fun _ => 0, fun _ _ => by simp⟩,
        smul_mem' := by
          rintro c m ⟨l, r, h⟩
          refine ⟨fun x => c * l x, fun y => c * r y, fun x y => ?_⟩
          simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, h x y]
          ring }
    Module.finrank (ZMod 2) M ≤ k - 3 := by
  intro Y M
  classical
  by_contra hgt
  push Not at hgt
  have hge : k - 2 ≤ Module.finrank (ZMod 2) M := by omega
  let K : Finset (ZMod k) := Finset.univ.filter (fun j => ∀ m ∈ M, m j = 0)
  let S : Submodule (ZMod 2) (ZMod k → ZMod 2) :=
    { carrier := { m | ∀ j ∈ K, m j = 0 }, add_mem' := fun ha hb j hj => by simp [ha j hj, hb j hj],
      zero_mem' := fun _ _ => rfl,
      smul_mem' := fun c _ ha j hj => by simp [ha j hj] }
  have hMS : M ≤ S := by
    intro m hm j hj
    exact (Finset.mem_filter.mp hj).2 m hm
  have hS_finrank : Module.finrank (ZMod 2) S = k - K.card := by
    let eS : S ≃ₗ[ZMod 2] ({ j : ZMod k // j ∉ K } → ZMod 2) :=
      { toFun := fun m j => m.1 j.1,
        map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl,
        invFun := fun f => ⟨fun j => if h : j ∈ K then 0 else f ⟨j, h⟩, fun j hj => by simp [hj]⟩,
        left_inv := fun m => by
          ext j
          by_cases hj : j ∈ K
          · simp [hj, m.2 j hj]
          · simp [hj],
        right_inv := fun f => by
          ext ⟨j, hj⟩
          simp [hj] }
    rw [eS.finrank_eq, Module.finrank_pi, Fintype.card_subtype_compl, ZMod.card, Fintype.card_coe]
  have hKcard : K.card ≤ 2 := by
    have hle := Submodule.finrank_mono hMS
    rw [hS_finrank] at hle
    omega
  have hQ_ker_pos : 0 < Module.finrank (ZMod 2) (LinearMap.ker Q) := by
    have hr := LinearMap.finrank_range_add_finrank_ker Q
    rw [Module.finrank_pi, ZMod.card] at hr
    omega
  have hA_ne : ∃ u, Q u = u ∧ u ≠ 0 := by
    by_contra h
    push Not at h
    have hbot : LinearMap.range Q = ⊥ := by
      ext u; simp only [Submodule.mem_bot]
      exact ⟨fun ⟨w, hw⟩ => hw ▸ h (Q w) (hQ w), fun hu => hu ▸ Submodule.zero_mem _⟩
    rw [hbot, finrank_bot] at hQpos
    omega
  have hB_ne : ∃ v, Q v = 0 ∧ v ≠ 0 := by
    by_contra h
    push Not at h
    have hbot : LinearMap.ker Q = ⊥ := by
      ext v; simp only [Submodule.mem_bot, LinearMap.mem_ker]
      exact ⟨h v, fun hv => hv ▸ map_zero Q⟩
    rw [hbot, finrank_bot] at hQ_ker_pos
    omega
  have hZ_disj : ∀ i : ZMod k, ¬ ((∀ u, Q u = u → u i = 0) ∧ (∀ v, Q v = 0 → v i = 0)) := by
    rintro i ⟨hA, hB⟩
    have hw : evec i = Q (evec i) + (evec i - Q (evec i)) := by abel
    have h1 := hA (Q (evec i)) (hQ (evec i))
    have h2 := hB (evec i - Q (evec i)) (by rw [map_sub, hQ, sub_self])
    have hi := congrFun hw i
    simp only [evec, ite_true, Pi.add_apply, h1, h2, add_zero] at hi
    exact (by decide : (1 : ZMod 2) ≠ 0) hi
  have hedge : ∀ a : ZMod k, a + (d : ZMod k) - 3 ∉ K →
      (∀ u, Q u = u → u a = 0 ∧ u (a + (2 * d : ℕ)) = 0) ∨
      (∀ v, Q v = 0 → v a = 0 ∧ v (a + (2 * d : ℕ)) = 0) := by
    intro a hnotK
    have hm_ex : ∃ m ∈ M, m (a + (d : ZMod k) - 3) ≠ 0 := by
      have h1 := Finset.mem_filter.not.mp hnotK
      simp only [Finset.mem_univ, true_and] at h1
      push Not at h1
      exact h1
    rcases hm_ex with ⟨m, hm, hmj⟩
    have hmj1 : m (a + (d : ZMod k) - 3) = 1 := by
      rcases zmod2_eq_zero_or_one (m (a + (d : ZMod k) - 3)) with h0 | h1
      · exact absurd h0 hmj
      · exact h1
    rcases hm with ⟨left, right, hsep⟩
    have hne : a ≠ a + (2 * d : ℕ) := by
      intro h
      have : ((2 * d : ℕ) : ZMod k) = 0 := by linear_combination -h
      exact zmod_nat_ne_zero (by omega) (by omega) this
    apply det_zero_implies_block Q hQ hne
    intro u v hu hv
    have h0 := D4_sep_zero Q hQ
      (fun w => ∑ j : ZMod k, m j * stepZ (Y w) j) left right hsep hu hv
      (evec (a - 1)) (evec (a + (2 * d : ℕ) + 1)) 0
    rw [D4_sum] at h0
    have hsum : (∑ j : ZMod k, D4 u v (evec (a - 1)) (evec (a + (2 * d : ℕ) + 1))
        (fun w => m j * stepZ (Y w) j) 0) =
        m (a + (d : ZMod k) - 3) * (u a * v (a + (2 * d : ℕ)) + v a * u (a + (2 * d : ℕ))) := by
      have hterm : ∀ j : ZMod k,
          D4 u v (evec (a - 1)) (evec (a + (2 * d : ℕ) + 1))
            (fun w => m j * stepZ (Y w) j) 0 =
          if j = a + (d : ZMod k) - 3 then
            m j * (u a * v (a + (2 * d : ℕ)) + v a * u (a + (2 * d : ℕ)))
          else 0 := by
        intro j
        rw [D4_smul, D4_Z_endpoint hd hk c₀ c₁ L a j u v]
        split_ifs <;> simp
      simp_rw [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hsum, hmj1, one_mul] at h0
    exact h0
  let s : ZMod k := (2 * d : ℕ)
  have hs_unit : IsUnit s := (ZMod.isUnit_iff_coprime (2 * d) k).mpr (coprime_two_mul_d hodd hd)
  rcases hs_unit with ⟨us, hus⟩
  let p : ZMod k → ZMod k := fun m => m * s
  have hp_bij : Function.Bijective p := by
    refine ⟨fun x y h => ?_, fun y => ⟨y * (us⁻¹ : (ZMod k)ˣ).val, ?_⟩⟩
    · have h1 := congrArg (· * (us⁻¹ : (ZMod k)ˣ).val) h
      dsimp only [p] at h1
      rwa [mul_assoc, mul_assoc, ← hus, Units.mul_inv, mul_one, mul_one] at h1
    · dsimp only [p]
      rw [mul_assoc, ← hus, Units.inv_mul, mul_one]
  let ZA : ZMod k → Prop := fun i => ∀ u, Q u = u → u i = 0
  let ZB : ZMod k → Prop := fun i => ∀ v, Q v = 0 → v i = 0
  have hpath_same : ∀ (m0 : ZMod k) (len : ℕ), 2 ≤ len →
      (∀ t : ℕ, t + 1 < len → p (m0 + (t : ZMod k)) + (d : ZMod k) - 3 ∉ K) →
      (∀ t : ℕ, t < len → ZA (p (m0 + (t : ZMod k)))) ∨
      (∀ t : ℕ, t < len → ZB (p (m0 + (t : ZMod k)))) := by
    intro m0 len hlen hno
    have h0 := hedge (p m0) (by simpa using hno 0 (by omega))
    have hp_step : ∀ m : ZMod k, p m + (2 * d : ℕ) = p (m + 1) := by
      intro m; dsimp only [p, s]; ring
    rcases h0 with hA0 | hB0
    · left
      intro t ht
      induction t with
      | zero => simpa using fun u hu => (hA0 u hu).1
      | succ t ih =>
        have hprev := ih (by omega)
        have he := hedge (p (m0 + (t : ZMod k))) (hno t (by omega))
        have hstep : p (m0 + (t : ZMod k)) + (2 * d : ℕ) = p (m0 + ((t + 1 : ℕ) : ZMod k)) := by
          rw [hp_step]; congr 1; push_cast; ring
        rw [hstep] at he
        rcases he with hA | hB
        · exact fun u hu => (hA u hu).2
        · exfalso
          exact hZ_disj (p (m0 + (t : ZMod k))) ⟨hprev, fun v hv => (hB v hv).1⟩
    · right
      intro t ht
      induction t with
      | zero => simpa using fun v hv => (hB0 v hv).1
      | succ t ih =>
        have hprev := ih (by omega)
        have he := hedge (p (m0 + (t : ZMod k))) (hno t (by omega))
        have hstep : p (m0 + (t : ZMod k)) + (2 * d : ℕ) = p (m0 + ((t + 1 : ℕ) : ZMod k)) := by
          rw [hp_step]; congr 1; push_cast; ring
        rw [hstep] at he
        rcases he with hA | hB
        · exfalso
          exact hZ_disj (p (m0 + (t : ZMod k))) ⟨fun u hu => (hA u hu).1, hprev⟩
        · exact fun v hv => (hB v hv).2
  have hnot_all_ZA : ¬ ∀ i, ZA i := by
    intro hall
    rcases hA_ne with ⟨u, hu, hu0⟩
    exact hu0 (funext fun i => hall i u hu)
  have hnot_all_ZB : ¬ ∀ i, ZB i := by
    intro hall
    rcases hB_ne with ⟨v, hv, hv0⟩
    exact hv0 (funext fun i => hall i v hv)
  have hKcard2 : K.card = 2 := by
    by_contra hne2
    have hle1 : K.card ≤ 1 := by omega
    have hex : ∃ m0 : ZMod k, ∀ j ∈ K, j = p m0 + (d : ZMod k) - 3 := by
      rcases K.eq_empty_or_nonempty with hEmp | ⟨j0, hj0⟩
      · exact ⟨0, fun j hj => by rw [hEmp] at hj; simp at hj⟩
      · rcases hp_bij.2 (j0 - (d : ZMod k) + 3) with ⟨m0, hm0⟩
        refine ⟨m0, fun j hj => ?_⟩
        have hjj0 : j = j0 := Finset.card_le_one.mp hle1 j hj j0 hj0
        rw [hjj0, hm0]; ring
    rcases hex with ⟨m0, hm0⟩
    have hno : ∀ t : ℕ, t + 1 < k → p (m0 + 1 + (t : ZMod k)) + (d : ZMod k) - 3 ∉ K := by
      intro t ht hmem
      have heq := hm0 _ hmem
      have hp_eq : p (m0 + 1 + (t : ZMod k)) = p m0 := by linear_combination heq
      have hm_eq := hp_bij.1 hp_eq
      have ht1 : ((t + 1 : ℕ) : ZMod k) = 0 := by push_cast; linear_combination hm_eq
      exact zmod_nat_ne_zero (by omega) (by omega) ht1
    have hsame := hpath_same (m0 + 1) k (by omega) hno
    have hcover : ∀ i : ZMod k, ∃ t < k, p (m0 + 1 + (t : ZMod k)) = i := by
      intro i
      rcases hp_bij.2 i with ⟨m, rfl⟩
      refine ⟨(m - (m0 + 1)).val, ZMod.val_lt _, ?_⟩
      congr 1
      rw [ZMod.natCast_zmod_val]
      ring
    rcases hsame with hA | hB
    · exact hnot_all_ZA fun i => by rcases hcover i with ⟨t, ht, rfl⟩; exact hA t ht
    · exact hnot_all_ZB fun i => by rcases hcover i with ⟨t, ht, rfl⟩; exact hB t ht
  have hMS_eq : M = S := by
    apply Submodule.eq_of_le_of_finrank_eq hMS
    have hle := Submodule.finrank_mono hMS
    rw [hS_finrank, hKcard2] at hle ⊢
    omega
  have hM_unit : ∀ j : ZMod k, j ∉ K →
      ∀ u v w₃ w₄ : ZMod k → ZMod 2, Q u = u → Q v = 0 →
        D4 u v w₃ w₄ (fun w => stepZ (Y w) j) 0 = 0 := by
    intro j hj u v w₃ w₄ hu hv
    have hej : evec j ∈ M := by
      rw [hMS_eq]
      intro i hi
      have hne : i ≠ j := fun h => hj (h ▸ hi)
      simp [evec, hne]
    rcases hej with ⟨left, right, hsep⟩
    have h0 := D4_sep_zero Q hQ
      (fun w => ∑ i : ZMod k, evec j i * stepZ (Y w) i) left right hsep hu hv w₃ w₄ 0
    have hfun : (fun w => ∑ i : ZMod k, evec j i * stepZ (Y w) i) = fun w => stepZ (Y w) j := by
      funext w
      simp [evec]
    rw [hfun] at h0
    exact h0
  rcases Finset.card_eq_two.mp hKcard2 with ⟨j₁, j₂, hj12, hKeq⟩
  rcases hp_bij.2 (j₁ - (d : ZMod k) + 3) with ⟨m₁, hm₁⟩
  rcases hp_bij.2 (j₂ - (d : ZMod k) + 3) with ⟨m₂, hm₂⟩
  have hm₁' : p m₁ + (d : ZMod k) - 3 = j₁ := by rw [hm₁]; ring
  have hm₂' : p m₂ + (d : ZMod k) - 3 = j₂ := by rw [hm₂]; ring
  have hm12 : m₁ ≠ m₂ := fun h => hj12 (by rw [← hm₁', ← hm₂', h])
  set L1 := (m₂ - m₁).val
  have hL1_pos : 0 < L1 := by
    by_contra h0
    have hz : (m₂ - m₁).val = 0 := by omega
    have hsub0 : m₂ - m₁ = 0 := by rw [← ZMod.natCast_zmod_val (m₂ - m₁), hz]; simp
    exact hm12 (by linear_combination -hsub0)
  have hL1_lt : L1 < k := ZMod.val_lt _
  have hnotK_iff : ∀ m : ZMod k, p m + (d : ZMod k) - 3 ∉ K ↔ m ≠ m₁ ∧ m ≠ m₂ := by
    intro m
    rw [hKeq, Finset.mem_insert, Finset.mem_singleton]
    push Not
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (by rw [h, hm₁']), fun h => h2 (by rw [h, hm₂'])⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (hp_bij.1 (by linear_combination h.trans hm₁'.symm)),
             fun h => h2 (hp_bij.1 (by linear_combination h.trans hm₂'.symm))⟩
  have hno1 : ∀ t : ℕ, t + 1 < L1 → p (m₁ + 1 + (t : ZMod k)) + (d : ZMod k) - 3 ∉ K := by
    intro t ht
    rw [hnotK_iff]
    constructor
    · intro h
      have : ((t + 1 : ℕ) : ZMod k) = 0 := by push_cast; linear_combination h
      exact zmod_nat_ne_zero (by omega) (by omega) this
    · intro h
      have hsub : m₂ - m₁ = ((t + 1 : ℕ) : ZMod k) := by push_cast; linear_combination -h
      have := congrArg ZMod.val hsub
      rw [ZMod.val_natCast_of_lt (by omega)] at this
      omega
  have hno2 : ∀ t : ℕ, t + 1 < k - L1 → p (m₂ + 1 + (t : ZMod k)) + (d : ZMod k) - 3 ∉ K := by
    intro t ht
    rw [hnotK_iff]
    constructor
    · intro h
      have hsub : m₁ - m₂ = ((t + 1 : ℕ) : ZMod k) := by push_cast; linear_combination -h
      have hsum : (m₂ - m₁) + (m₁ - m₂) = 0 := by ring
      have hcast : ((L1 + (t + 1) : ℕ) : ZMod k) = 0 := by
        rw [Nat.cast_add, ZMod.natCast_zmod_val, ← hsub, hsum]
      exact zmod_nat_ne_zero (by omega) (by omega) hcast
    · intro h
      have : ((t + 1 : ℕ) : ZMod k) = 0 := by push_cast; linear_combination h
      exact zmod_nat_ne_zero (by omega) (by omega) this
  have hsing : ∀ (Q' : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2)),
      (∀ w, Q' (Q' w) = Q' w) → 0 < Module.finrank (ZMod 2) (LinearMap.range Q') →
      (∀ j ∉ K, ∀ u v w₃ w₄, Q' u = u → Q' v = 0 → D4 u v w₃ w₄ (fun w => stepZ (Y w) j) 0 = 0) →
      ∀ s0 : ZMod k, (∀ u, Q' u = u → ∀ i ≠ s0, u i = 0) → False :=
    fun Q' hQ' hQp' hMu' s0 hv => singleton_contradiction hd hk c₀ c₁ L Q' hQ' hQp' K hKcard hMu' s0 hv
  let Qd : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2) := LinearMap.id - Q
  have hM_unit_dual : ∀ j : ZMod k, j ∉ K →
      ∀ u v w₃ w₄ : ZMod k → ZMod 2, Qd u = u → Qd v = 0 →
        D4 u v w₃ w₄ (fun w => stepZ (Y w) j) 0 = 0 := by
    intro j hj u v w₃ w₄ hu hv
    have hu0 : Q u = 0 := by
      simp only [Qd, LinearMap.sub_apply, LinearMap.id_apply] at hu
      have := congrArg (· - u) hu
      simpa using this
    have hv1 : Q v = v := by
      simp only [Qd, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hv
      exact hv.symm
    rw [D4_comm12]
    exact hM_unit j hj v u w₃ w₄ hv1 hu0
  have hQdual_idem : ∀ w, Qd (Qd w) = Qd w := by
    intro w
    simp only [Qd, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hQ]
    abel
  have hQdual_pos : 0 < Module.finrank (ZMod 2) (LinearMap.range Qd) := by
    have hker_le : LinearMap.ker Q ≤ LinearMap.range Qd := by
      intro v hv
      refine ⟨v, ?_⟩
      simp [Qd, LinearMap.mem_ker.mp hv]
    exact lt_of_lt_of_le hQ_ker_pos (Submodule.finrank_mono hker_le)
  have hvan_dual : ∀ s0 : ZMod k, (∀ i ≠ s0, ZB i) → False := by
    intro s0 hZB
    apply hsing Qd hQdual_idem hQdual_pos hM_unit_dual s0
    intro u hu i hi
    have hu0 : Q u = 0 := by
      simp only [Qd, LinearMap.sub_apply, LinearMap.id_apply] at hu
      have := congrArg (· - u) hu
      simpa using this
    exact hZB i hi u hu0
  have hL1_ge2 : 2 ≤ L1 := by
    by_contra h1
    have hL1_eq : L1 = 1 := by omega
    have hsame2 := hpath_same (m₂ + 1) (k - L1) (by omega) hno2
    have hcov2 : ∀ i : ZMod k, i ≠ p m₂ → ∃ t < k - L1, p (m₂ + 1 + (t : ZMod k)) = i := by
      intro i hi
      rcases hp_bij.2 i with ⟨m, rfl⟩
      have hmm2 : m ≠ m₂ := fun h => hi (by rw [h])
      have hne0 : m - (m₂ + 1) ≠ ((k - 1 : ℕ) : ZMod k) := by
        intro h
        apply hmm2
        have hk1 : ((k - 1 : ℕ) : ZMod k) = -1 := by
          rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub, Nat.cast_one]
        rw [hk1] at h
        linear_combination h
      have hlt : (m - (m₂ + 1)).val < k - 1 := by
        have hlt0 := ZMod.val_lt (m - (m₂ + 1))
        by_contra hge1
        have heq : (m - (m₂ + 1)).val = k - 1 := by omega
        apply hne0
        rw [← ZMod.natCast_zmod_val (m - (m₂ + 1)), heq]
      refine ⟨(m - (m₂ + 1)).val, by omega, ?_⟩
      congr 1; rw [ZMod.natCast_zmod_val]; ring
    rcases hsame2 with hA | hB
    · exact hsing Q hQ hQpos hM_unit (p m₂) (fun u hu i hi => by
        rcases hcov2 i hi with ⟨t, ht, rfl⟩; exact hA t ht u hu)
    · exact hvan_dual (p m₂) (fun i hi => by
        rcases hcov2 i hi with ⟨t, ht, rfl⟩; exact hB t ht)
  have hL2_ge2 : 2 ≤ k - L1 := by
    by_contra h1
    have hL1_eq : L1 = k - 1 := by omega
    have hsame1 := hpath_same (m₁ + 1) L1 (by omega) hno1
    have hcov1 : ∀ i : ZMod k, i ≠ p m₁ → ∃ t < L1, p (m₁ + 1 + (t : ZMod k)) = i := by
      intro i hi
      rcases hp_bij.2 i with ⟨m, rfl⟩
      have hmm1 : m ≠ m₁ := fun h => hi (by rw [h])
      have hne0 : m - (m₁ + 1) ≠ ((k - 1 : ℕ) : ZMod k) := by
        intro h
        apply hmm1
        have hk1 : ((k - 1 : ℕ) : ZMod k) = -1 := by
          rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub, Nat.cast_one]
        rw [hk1] at h
        linear_combination h
      have hlt : (m - (m₁ + 1)).val < k - 1 := by
        have hlt0 := ZMod.val_lt (m - (m₁ + 1))
        by_contra hge1
        have heq : (m - (m₁ + 1)).val = k - 1 := by omega
        apply hne0
        rw [← ZMod.natCast_zmod_val (m - (m₁ + 1)), heq]
      refine ⟨(m - (m₁ + 1)).val, by omega, ?_⟩
      congr 1; rw [ZMod.natCast_zmod_val]; ring
    rcases hsame1 with hA | hB
    · exact hsing Q hQ hQpos hM_unit (p m₁) (fun u hu i hi => by
        rcases hcov1 i hi with ⟨t, ht, rfl⟩; exact hA t ht u hu)
    · exact hvan_dual (p m₁) (fun i hi => by
        rcases hcov1 i hi with ⟨t, ht, rfl⟩; exact hB t ht)
  have hP1 := hpath_same (m₁ + 1) L1 hL1_ge2 hno1
  have hP2 := hpath_same (m₂ + 1) (k - L1) hL2_ge2 hno2
  let inP1 : ZMod k → Prop := fun i => ∃ t < L1, p (m₁ + 1 + (t : ZMod k)) = i
  let inP2 : ZMod k → Prop := fun i => ∃ t < k - L1, p (m₂ + 1 + (t : ZMod k)) = i
  have hpart : ∀ i : ZMod k, inP1 i ∨ inP2 i := by
    intro i
    rcases hp_bij.2 i with ⟨m, rfl⟩
    set r := (m - m₁).val
    by_cases hr0 : r = 0
    · right
      have hm_eq : m = m₁ := by
        have h0 : m - m₁ = 0 := by
          rw [← ZMod.natCast_zmod_val (m - m₁)]
          change (r : ZMod k) = 0
          rw [hr0]; simp
        linear_combination h0
      refine ⟨k - L1 - 1, by omega, ?_⟩
      rw [hm_eq]; congr 1
      have hL1c : (L1 : ZMod k) = m₂ - m₁ := ZMod.natCast_zmod_val _
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), ZMod.natCast_self, hL1c, Nat.cast_one]
      ring
    · by_cases hrL : r ≤ L1
      · left
        refine ⟨r - 1, by omega, ?_⟩
        congr 1
        have hrc : (r : ZMod k) = m - m₁ := ZMod.natCast_zmod_val _
        rw [Nat.cast_sub (by omega), hrc, Nat.cast_one]
        ring
      · right
        have hr_lt : r < k := ZMod.val_lt _
        refine ⟨r - L1 - 1, by omega, ?_⟩
        congr 1
        have hrc : (r : ZMod k) = m - m₁ := ZMod.natCast_zmod_val _
        have hL1c : (L1 : ZMod k) = m₂ - m₁ := ZMod.natCast_zmod_val _
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hrc, hL1c, Nat.cast_one]
        ring
  have hdisjP : ∀ i, ¬ (inP1 i ∧ inP2 i) := by
    rintro i ⟨⟨t₁, ht₁, h1⟩, ⟨t₂, ht₂, h2⟩⟩
    have hm_eq := hp_bij.1 (h1.trans h2.symm)
    have hL1c : (L1 : ZMod k) = m₂ - m₁ := ZMod.natCast_zmod_val _
    have hdiff : ((L1 + t₂ + 1 : ℕ) : ZMod k) = ((t₁ + 1 : ℕ) : ZMod k) := by
      push_cast; rw [hL1c]; linear_combination -hm_eq
    have h0 : ((L1 + t₂ - t₁ : ℕ) : ZMod k) = 0 := by
      rw [Nat.cast_sub (by omega)]
      push_cast at hdiff ⊢
      linear_combination hdiff
    exact zmod_nat_ne_zero (by omega) (by omega) h0
  have hblocks : (∀ i, inP1 i ↔ ZB i) ∧ (∀ i, inP2 i ↔ ZA i) ∨
      (∀ i, inP1 i ↔ ZA i) ∧ (∀ i, inP2 i ↔ ZB i) := by
    rcases hP1 with h1A | h1B <;> rcases hP2 with h2A | h2B
    · exfalso; apply hnot_all_ZA; intro i
      rcases hpart i with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
      · exact h1A t ht
      · exact h2A t ht
    · right
      refine ⟨fun i => ⟨fun ⟨t, ht, heq⟩ => heq ▸ h1A t ht, fun hi => ?_⟩,
              fun i => ⟨fun ⟨t, ht, heq⟩ => heq ▸ h2B t ht, fun hi => ?_⟩⟩
      · rcases hpart i with h1 | ⟨t, ht, rfl⟩
        · exact h1
        · exact absurd ⟨hi, h2B t ht⟩ (hZ_disj _)
      · rcases hpart i with ⟨t, ht, rfl⟩ | h2
        · exact absurd ⟨h1A t ht, hi⟩ (hZ_disj _)
        · exact h2
    · left
      refine ⟨fun i => ⟨fun ⟨t, ht, heq⟩ => heq ▸ h1B t ht, fun hi => ?_⟩,
              fun i => ⟨fun ⟨t, ht, heq⟩ => heq ▸ h2A t ht, fun hi => ?_⟩⟩
      · rcases hpart i with h1 | ⟨t, ht, rfl⟩
        · exact h1
        · exact absurd ⟨h2A t ht, hi⟩ (hZ_disj _)
      · rcases hpart i with ⟨t, ht, rfl⟩ | h2
        · exact absurd ⟨hi, h1B t ht⟩ (hZ_disj _)
        · exact h2
    · exfalso; apply hnot_all_ZB; intro i
      rcases hpart i with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
      · exact h1B t ht
      · exact h2B t ht
  have hevec_block : ∀ i : ZMod k, (ZB i → Q (evec i) = evec i) ∧ (ZA i → Q (evec i) = 0) := by
    have hcovZ : ∀ j, ZA j ∨ ZB j := by
      intro j
      rcases hpart j with h1 | h2
      · rcases hblocks with ⟨hB, _⟩ | ⟨hA, _⟩
        · exact Or.inr ((hB j).mp h1)
        · exact Or.inl ((hA j).mp h1)
      · rcases hblocks with ⟨_, hA⟩ | ⟨_, hB⟩
        · exact Or.inl ((hA j).mp h2)
        · exact Or.inr ((hB j).mp h2)
    intro i
    constructor
    · intro hBi
      ext j
      by_cases hij : j = i
      · subst hij
        have hv0 := hBi (evec j - Q (evec j)) (by rw [map_sub, hQ, sub_self])
        simp only [Pi.sub_apply, sub_eq_zero] at hv0
        exact hv0.symm
      · rcases hcovZ j with hAj | hBj
        · rw [hAj (Q (evec i)) (hQ _)]; simp [evec, hij]
        · have hv0 := hBj (evec i - Q (evec i)) (by rw [map_sub, hQ, sub_self])
          simp only [Pi.sub_apply, sub_eq_zero] at hv0
          exact hv0.symm
    · intro hAi
      ext j
      by_cases hij : j = i
      · subst hij; exact hAi (Q (evec j)) (hQ _)
      · rcases hcovZ j with hAj | hBj
        · exact hAj (Q (evec i)) (hQ _)
        · have hv0 := hBj (evec i - Q (evec i)) (by rw [map_sub, hQ, sub_self])
          simp only [Pi.sub_apply, sub_eq_zero, evec, hij, ite_false] at hv0
          exact hv0.symm
  have hinternal : ∀ a : ZMod k, a + (d : ZMod k) - 3 ∉ K →
      ((ZB a → ZB (a - 1) ∧ ZB (a + (2 * d : ℕ) + 1)) ∧
       (ZA a → ZA (a - 1) ∧ ZA (a + (2 * d : ℕ) + 1))) := by
    intro a hnotK
    set b := a + (2 * d : ℕ)
    set j := a + (d : ZMod k) - 3
    have hD1 : D4 (evec a) (evec b) (evec (a - 1)) (evec (b + 1)) (fun w => stepZ (Y w) j) 0 = 1 :=
      by simpa [b, j] using D4_Z_quad hd hk c₀ c₁ L a j
    have hcovZ : ∀ r, ZA r ∨ ZB r := by
      intro r
      rcases hpart r with h1 | h2
      · rcases hblocks with ⟨hB, _⟩ | ⟨hA, _⟩
        · exact Or.inr ((hB r).mp h1)
        · exact Or.inl ((hA r).mp h1)
      · rcases hblocks with ⟨_, hA⟩ | ⟨_, hB⟩
        · exact Or.inl ((hA r).mp h2)
        · exact Or.inr ((hB r).mp h2)
    have h01 : (0 : ZMod 2) ≠ 1 := by decide
    constructor
    · intro hBa
      have hQa := (hevec_block a).1 hBa
      constructor
      · rcases hcovZ (a - 1) with hA1 | hB1
        · exfalso
          have h0 : D4 (evec a) (evec b) (evec (a - 1)) (evec (b + 1)) (fun w => stepZ (Y w) j) 0 = 0 := by
            rw [D4_comm23]
            exact hM_unit j hnotK (evec a) (evec (a - 1)) (evec b) (evec (b + 1)) hQa ((hevec_block (a - 1)).2 hA1)
          exact h01 (h0.symm.trans hD1)
        · exact hB1
      · rcases hcovZ (b + 1) with hA1 | hB1
        · exfalso
          have h0 : D4 (evec a) (evec b) (evec (a - 1)) (evec (b + 1)) (fun w => stepZ (Y w) j) 0 = 0 := by
            rw [D4_comm34, D4_comm23]
            exact hM_unit j hnotK (evec a) (evec (b + 1)) (evec b) (evec (a - 1)) hQa ((hevec_block (b + 1)).2 hA1)
          exact h01 (h0.symm.trans hD1)
        · exact hB1
    · intro hAa
      have hQa := (hevec_block a).2 hAa
      constructor
      · rcases hcovZ (a - 1) with hA1 | hB1
        · exact hA1
        · exfalso
          have h0 : D4 (evec a) (evec b) (evec (a - 1)) (evec (b + 1)) (fun w => stepZ (Y w) j) 0 = 0 := by
            rw [D4_comm23, D4_comm12]
            exact hM_unit j hnotK (evec (a - 1)) (evec a) (evec b) (evec (b + 1)) ((hevec_block (a - 1)).1 hB1) hQa
          exact h01 (h0.symm.trans hD1)
      · rcases hcovZ (b + 1) with hA1 | hB1
        · exact hA1
        · exfalso
          have h0 : D4 (evec a) (evec b) (evec (a - 1)) (evec (b + 1)) (fun w => stepZ (Y w) j) 0 = 0 := by
            rw [D4_comm34, D4_comm23, D4_comm12]
            exact hM_unit j hnotK (evec (b + 1)) (evec a) (evec b) (evec (a - 1)) ((hevec_block (b + 1)).1 hB1) hQa
          exact h01 (h0.symm.trans hD1)
  have hP1_internal : ∀ a, inP1 a → a + (d : ZMod k) - 3 ∉ K → inP1 (a - 1) ∧ inP1 (a + (2 * d : ℕ) + 1) := by
    intro a ha hnotK
    rcases hblocks with ⟨hB, _⟩ | ⟨hA, _⟩
    · have := (hinternal a hnotK).1 ((hB a).mp ha)
      exact ⟨(hB _).mpr this.1, (hB _).mpr this.2⟩
    · have := (hinternal a hnotK).2 ((hA a).mp ha)
      exact ⟨(hA _).mpr this.1, (hA _).mpr this.2⟩
  have hP2_internal : ∀ a, inP2 a → a + (d : ZMod k) - 3 ∉ K → inP2 (a - 1) ∧ inP2 (a + (2 * d : ℕ) + 1) := by
    intro a ha hnotK
    rcases hblocks with ⟨_, hA⟩ | ⟨_, hB⟩
    · have := (hinternal a hnotK).2 ((hA a).mp ha)
      exact ⟨(hA _).mpr this.1, (hA _).mpr this.2⟩
    · have := (hinternal a hnotK).1 ((hB a).mp ha)
      exact ⟨(hB _).mpr this.1, (hB _).mpr this.2⟩
  have hexit : ∃ x : ZMod k, inP1 x ∧ inP2 (x + 1) := by
    by_contra hno
    push Not at hno
    have hstep : ∀ x, inP1 x → inP1 (x + 1) := by
      intro x hx
      rcases hpart (x + 1) with h1 | h2
      · exact h1
      · exact absurd h2 (hno x hx)
    have h0 : inP1 (p (m₁ + 1)) := ⟨0, by omega, by simp⟩
    have hall : ∀ n : ℕ, inP1 (p (m₁ + 1) + (n : ZMod k)) := by
      intro n
      induction n with
      | zero => simpa using h0
      | succ n ih =>
        push_cast
        rw [← add_assoc]
        exact hstep _ ih
    have hin1 : inP1 (p (m₂ + 1)) := by
      have := hall (p (m₂ + 1) - p (m₁ + 1)).val
      rw [ZMod.natCast_zmod_val, add_sub_cancel] at this
      exact this
    have hin2 : inP2 (p (m₂ + 1)) := ⟨0, by omega, by simp⟩
    exact hdisjP _ ⟨hin1, hin2⟩
  rcases hexit with ⟨x, hx1, hx2⟩
  have hx_start : x = p (m₁ + 1) := by
    rcases hx1 with ⟨t, ht, rfl⟩
    by_cases ht0 : t = 0
    · subst ht0; simp
    · exfalso
      have ha_in : inP1 (p (m₁ + 1 + ((t - 1 : ℕ) : ZMod k))) := ⟨t - 1, by omega, rfl⟩
      have ha_no : p (m₁ + 1 + ((t - 1 : ℕ) : ZMod k)) + (d : ZMod k) - 3 ∉ K := hno1 (t - 1) (by omega)
      have hnext := (hP1_internal _ ha_in ha_no).2
      have heq : p (m₁ + 1 + ((t - 1 : ℕ) : ZMod k)) + (2 * d : ℕ) + 1 = p (m₁ + 1 + (t : ZMod k)) + 1 := by
        dsimp only [p, s]
        rw [Nat.cast_sub (by omega), Nat.cast_one]
        ring
      rw [heq] at hnext
      exact hdisjP _ ⟨hnext, hx2⟩
  have hy_end : x + 1 = p m₁ := by
    rcases hx2 with ⟨t, ht, ht_eq⟩
    by_cases hlast : t + 1 = k - L1
    · rw [← ht_eq]
      congr 1
      have hL1c : (L1 : ZMod k) = m₂ - m₁ := ZMod.natCast_zmod_val _
      have ht_c : ((t + 1 : ℕ) : ZMod k) = ((k - L1 : ℕ) : ZMod k) := by rw [hlast]
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, hL1c, zero_sub] at ht_c
      push_cast at ht_c
      linear_combination ht_c
    · exfalso
      have ha_in : inP2 (p (m₂ + 1 + (t : ZMod k))) := ⟨t, ht, rfl⟩
      have ha_no : p (m₂ + 1 + (t : ZMod k)) + (d : ZMod k) - 3 ∉ K := hno2 t (by omega)
      have hprev := (hP2_internal _ ha_in ha_no).1
      rw [ht_eq, add_sub_cancel_right] at hprev
      exact hdisjP _ ⟨hx1, hprev⟩
  have h2d1 : ((2 * d + 1 : ℕ) : ZMod k) = 0 := by
    have h1 : p (m₁ + 1) + 1 = p m₁ := by rw [← hx_start, hy_end]
    dsimp only [p, s] at h1
    push_cast at h1 ⊢
    linear_combination h1
  exact zmod_nat_ne_zero (by omega) (by omega) h2d1

end PEqualNP.Outside.L_meta_25604_aux

theorem PEqualNP.Outside.L_meta_25604 :
∀ (k d : Nat) (hk : 0 < k), Odd k → k % 3 ≠ 0 →
  (d = 1 ∨ d = 2) → 4 * d + 4 < k →
  let ix := fun (a : Nat) => (⟨a % k, Nat.mod_lt _ hk⟩ : Fin k)
  let W := Fin k → ZMod 2
  let rot := fun (t : Nat) (v : W) (j : Fin k) => v (ix (j.val + k - t % k))
  let mix := fun (v : W) (j : Fin k) =>
    v j + v (ix (j.val + d)) + v (ix (j.val + k - d % k))
  let step := fun (v : W) (j : Fin k) =>
    v j + (1 + v (ix (j.val + 1))) * v (ix (j.val + 2))
  ∀ (initial middle finalShift : Nat) (name c₁ c₂ : W),
    let run := fun (key : W) =>
      let firstState := step (mix (rot initial key + name)) + rot middle key + c₁
      step (mix firstState) + rot finalShift key + c₂
    ∀ P : W →ₗ[ZMod 2] W, (∀ w, P (P w) = P w) →
      0 < Module.finrank (ZMod 2) (LinearMap.range P) →
      Module.finrank (ZMod 2) (LinearMap.range P) < k →
      Nat.card { mask : W //
        ∃ left right : W → ZMod 2, ∀ a b : W,
          (∑ j : Fin k, mask j * run (P a + (b - P b)) j) = left a + right b } ≤
        2 ^ (k - 3) := by
  intro k d hk hodd h3 hd hkd ix W rot mix step initial middle finalShift name c₁ c₂ run P hP hPpos hPlt
  classical
  have : NeZero k := ⟨Nat.ne_of_gt hk⟩
  let toZ : Fin k → ZMod k := fun j => (j.val : ZMod k)
  let ofZ : ZMod k → Fin k := fun z => ⟨z.val, ZMod.val_lt z⟩
  have htoZ_ofZ : ∀ z : ZMod k, toZ (ofZ z) = z := fun z => ZMod.natCast_zmod_val z
  have hofZ_toZ : ∀ j : Fin k, ofZ (toZ j) = j := fun j => Fin.ext (ZMod.val_natCast_of_lt j.isLt)
  have hix_toZ : ∀ a : ℕ, toZ (ix a) = (a : ZMod k) := fun a => by
    dsimp only [toZ, ix]
    exact ZMod.natCast_mod a k
  have hix_add : ∀ (z : ZMod k) (r : ℕ), toZ (ix ((ofZ z).val + r)) = z + (r : ZMod k) := by
    intro z r
    rw [hix_toZ, Nat.cast_add]
    congr 1
    exact ZMod.natCast_zmod_val z
  have hix_sub : ∀ (z : ZMod k) (r : ℕ), toZ (ix ((ofZ z).val + k - r % k)) = z - (r : ZMod k) := by
    intro z r
    rw [hix_toZ]
    have hlt : r % k < k := Nat.mod_lt r hk
    rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero, ZMod.natCast_mod]
  let eW : W ≃ₗ[ZMod 2] (ZMod k → ZMod 2) :=
    { toFun := fun v z => v (ofZ z),
      map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl,
      invFun := fun v j => v (toZ j),
      left_inv := fun v => funext fun j => by dsimp only; rw [hofZ_toZ],
      right_inv := fun v => funext fun z => by dsimp only; rw [htoZ_ofZ] }
  have heW_rot : ∀ (t : ℕ) (v : W), eW (rot t v) = PEqualNP.Outside.L_meta_25604_aux.rotZ (t : ZMod k) (eW v) := by
    intro t v
    ext z
    simp only [eW, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, rot, PEqualNP.Outside.L_meta_25604_aux.rotZ]
    have : ix ((ofZ z).val + k - t % k) = ofZ (z - (t : ZMod k)) := by
      rw [← hofZ_toZ (ix _), hix_sub]
    rw [this]
  have heW_mix : ∀ v : W, eW (mix v) = PEqualNP.Outside.L_meta_25604_aux.mixZ d (eW v) := by
    intro v
    ext z
    simp only [eW, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, mix, PEqualNP.Outside.L_meta_25604_aux.mixZ]
    have h1 : ix ((ofZ z).val + d) = ofZ (z + (d : ZMod k)) := by
      rw [← hofZ_toZ (ix _), hix_add]
    have h2 : ix ((ofZ z).val + k - d % k) = ofZ (z - (d : ZMod k)) := by
      rw [← hofZ_toZ (ix _), hix_sub]
    rw [h1, h2]
  have heW_step : ∀ v : W, eW (step v) = PEqualNP.Outside.L_meta_25604_aux.stepZ (eW v) := by
    intro v
    ext z
    simp only [eW, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, step, PEqualNP.Outside.L_meta_25604_aux.stepZ]
    have h1 : ix ((ofZ z).val + 1) = ofZ (z + 1) := by
      rw [← hofZ_toZ (ix _), hix_add]; simp
    have h2 : ix ((ofZ z).val + 2) = ofZ (z + 2) := by
      rw [← hofZ_toZ (ix _), hix_add]; simp
    rw [h1, h2]
  let T : (ZMod k → ZMod 2) ≃ₗ[ZMod 2] (ZMod k → ZMod 2) :=
    (PEqualNP.Outside.L_meta_25604_aux.rotEquiv (initial : ZMod k)).trans
      (PEqualNP.Outside.L_meta_25604_aux.mixEquiv hodd h3 hd)
  let P' : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2) :=
    eW.toLinearMap.comp (P.comp eW.symm.toLinearMap)
  let Q : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2) :=
    T.toLinearMap.comp (P'.comp T.symm.toLinearMap)
  have hQ : ∀ w, Q (Q w) = Q w := by
    intro w
    simp only [Q, P', LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply, hP]
  have hQ_range_eq : Module.finrank (ZMod 2) (LinearMap.range Q) =
      Module.finrank (ZMod 2) (LinearMap.range P) := by
    let eTE : W ≃ₗ[ZMod 2] (ZMod k → ZMod 2) := eW.trans T
    have hQeq : Q = eTE.toLinearMap.comp (P.comp eTE.symm.toLinearMap) := by
      ext w z; rfl
    rw [hQeq]
    have hr : LinearMap.range (eTE.toLinearMap.comp (P.comp eTE.symm.toLinearMap)) =
        Submodule.map eTE.toLinearMap (LinearMap.range P) := by
      ext y
      simp only [LinearMap.mem_range, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Submodule.mem_map]
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨P (eTE.symm x), ⟨eTE.symm x, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨eTE x, by simp⟩
    rw [hr]
    exact LinearEquiv.finrank_map_eq eTE (LinearMap.range P)
  let c₀ : ZMod k → ZMod 2 := PEqualNP.Outside.L_meta_25604_aux.mixZ d (eW name)
  let c₁' : ZMod k → ZMod 2 := eW c₁
  let c₂' : ZMod k → ZMod 2 := eW c₂
  let L : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2) :=
    (PEqualNP.Outside.L_meta_25604_aux.rotZ (middle : ZMod k)).comp T.symm.toLinearMap
  let L2 : (ZMod k → ZMod 2) →ₗ[ZMod 2] (ZMod k → ZMod 2) :=
    (PEqualNP.Outside.L_meta_25604_aux.rotZ (finalShift : ZMod k)).comp T.symm.toLinearMap
  let Y := fun w => PEqualNP.Outside.L_meta_25604_aux.mixZ d
    (fun i => PEqualNP.Outside.L_meta_25604_aux.stepZ (w + c₀) i + L w i + c₁' i)
  have hmain := PEqualNP.Outside.L_meta_25604_aux.main_zmod hodd h3 hd hkd c₀ c₁' L Q hQ
    (by rw [hQ_range_eq]; exact hPpos) (by rw [hQ_range_eq]; exact hPlt)
  dsimp only at hmain
  set M : Submodule (ZMod 2) (ZMod k → ZMod 2) :=
    { carrier := { mask | ∃ left right : (ZMod k → ZMod 2) → ZMod 2, ∀ x y,
        (∑ j : ZMod k, mask j * PEqualNP.Outside.L_meta_25604_aux.stepZ (Y (Q x + (y - Q y))) j) =
          left x + right y }, add_mem' := by
        rintro m₁ m₂ ⟨l₁, r₁, h₁⟩ ⟨l₂, r₂, h₂⟩
        refine ⟨fun x => l₁ x + l₂ x, fun y => r₁ y + r₂ y, fun x y => ?_⟩
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, h₁ x y, h₂ x y]
        ring,
      zero_mem' := ⟨fun _ => 0, fun _ => 0, fun _ _ => by simp⟩,
      smul_mem' := by
        rintro c m ⟨l, r, h⟩
        refine ⟨fun x => c * l x, fun y => c * r y, fun x y => ?_⟩
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, h x y]
        ring }
  have hrun_eq : ∀ w : ZMod k → ZMod 2,
      eW (run (eW.symm (T.symm w))) =
        PEqualNP.Outside.L_meta_25604_aux.stepZ (Y w) + L2 w + c₂' := by
    intro w
    dsimp only [run]
    rw [map_add, map_add, heW_step, heW_mix, heW_rot, LinearEquiv.apply_symm_apply]
    have hfirst : eW (step (mix (rot initial (eW.symm (T.symm w)) + name)) +
        rot middle (eW.symm (T.symm w)) + c₁) =
        fun i => PEqualNP.Outside.L_meta_25604_aux.stepZ (w + c₀) i + L w i + c₁' i := by
      rw [map_add, map_add, heW_step, heW_mix, map_add, heW_rot, heW_rot,
          LinearEquiv.apply_symm_apply, map_add]
      have hT : PEqualNP.Outside.L_meta_25604_aux.mixZ d
          (PEqualNP.Outside.L_meta_25604_aux.rotZ (initial : ZMod k) (T.symm w)) = w := by
        exact T.apply_symm_apply w
      rw [hT]
      rfl
    rw [hfirst]
    rfl
  have hmap : ∀ mask : W,
      (∃ left right : W → ZMod 2, ∀ a b : W,
        (∑ j : Fin k, mask j * run (P a + (b - P b)) j) = left a + right b) →
      eW mask ∈ M := by
    rintro mask ⟨left, right, hsep⟩
    refine ⟨fun x => left (eW.symm (T.symm x)) + ∑ j : ZMod k, eW mask j * L2 (Q x) j,
            fun y => right (eW.symm (T.symm y)) + ∑ j : ZMod k, eW mask j * (L2 (y - Q y) j + c₂' j),
            fun x y => ?_⟩
    have hsum_eq : (∑ j : Fin k, mask j * run (P (eW.symm (T.symm x)) +
        (eW.symm (T.symm y) - P (eW.symm (T.symm y)))) j) =
        ∑ j : ZMod k, eW mask j * eW (run (eW.symm (T.symm (Q x + (y - Q y))))) j := by
      have harg : P (eW.symm (T.symm x)) + (eW.symm (T.symm y) - P (eW.symm (T.symm y))) =
          eW.symm (T.symm (Q x + (y - Q y))) := by
        apply eW.injective
        apply T.injective
        simp only [Q, P', map_add, map_sub, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
          LinearEquiv.apply_symm_apply]
      rw [harg]
      refine Finset.sum_bij (fun j _ => toZ j) (fun _ _ => Finset.mem_univ _)
        (fun j₁ _ j₂ _ h => by rw [← hofZ_toZ j₁, ← hofZ_toZ j₂, h])
        (fun z _ => ⟨ofZ z, Finset.mem_univ _, htoZ_ofZ z⟩)
        (fun j _ => by simp only [eW, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, hofZ_toZ])
    have hsepxy := hsep (eW.symm (T.symm x)) (eW.symm (T.symm y))
    rw [hsum_eq, hrun_eq] at hsepxy
    have hsplit : (∑ j : ZMod k, eW mask j *
        (PEqualNP.Outside.L_meta_25604_aux.stepZ (Y (Q x + (y - Q y))) + L2 (Q x + (y - Q y)) + c₂') j) =
        (∑ j : ZMod k, eW mask j * PEqualNP.Outside.L_meta_25604_aux.stepZ (Y (Q x + (y - Q y))) j) +
        (∑ j : ZMod k, eW mask j * L2 (Q x) j) +
        (∑ j : ZMod k, eW mask j * (L2 (y - Q y) j + c₂' j)) := by
      simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      ring
    rw [hsplit] at hsepxy
    have s1 := PEqualNP.Outside.L_meta_25604_aux.zmod2_add_self (∑ j : ZMod k, eW mask j * L2 (Q x) j)
    have s2 := PEqualNP.Outside.L_meta_25604_aux.zmod2_add_self (∑ j : ZMod k, eW mask j * (L2 (y - Q y) j + c₂' j))
    linear_combination hsepxy - s1 - s2
  let f : { mask : W // ∃ left right : W → ZMod 2, ∀ a b : W,
      (∑ j : Fin k, mask j * run (P a + (b - P b)) j) = left a + right b } → M :=
    fun m => ⟨eW m.1, hmap m.1 m.2⟩
  have hf_inj : Function.Injective f := by
    intro m₁ m₂ h
    ext j
    have h1 : eW m₁.1 = eW m₂.1 := congrArg Subtype.val h
    exact congrFun (eW.injective h1) j
  have hle_card : Nat.card { mask : W // ∃ left right : W → ZMod 2, ∀ a b : W,
      (∑ j : Fin k, mask j * run (P a + (b - P b)) j) = left a + right b } ≤ Nat.card M :=
    Nat.card_le_card_of_injective f hf_inj
  have hM_card : Nat.card M = 2 ^ Module.finrank (ZMod 2) M := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := M), ZMod.card]
  rw [hM_card] at hle_card
  exact le_trans hle_card (Nat.pow_le_pow_right (by omega) hmain)

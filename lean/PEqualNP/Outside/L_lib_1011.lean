import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1011_aux

lemma testBit_eq_of_lt_two_pow {q : ℕ} {x y : Fin (2 ^ q)}
    (h : ∀ i : Fin q, x.val.testBit i.val = y.val.testBit i.val) : x = y := by
  ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < q
  · exact h ⟨j, hj⟩
  · have hpow : 2 ^ q ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt hpow),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le y.isLt hpow)]

def toVec {q : ℕ} (x : Fin (2 ^ q)) : Fin q → ZMod 2 :=
  fun i => if x.val.testBit i.val then 1 else 0

lemma toVec_inj (q : ℕ) : Function.Injective (@toVec q) := by
  intro x y h
  apply testBit_eq_of_lt_two_pow
  intro i
  have hi := congrFun h i
  simp only [toVec] at hi
  cases hx : x.val.testBit i.val <;> cases hy : y.val.testBit i.val <;> simp [hx, hy] at hi ⊢

noncomputable def toVecEquiv (q : ℕ) : Fin (2 ^ q) ≃ (Fin q → ZMod 2) :=
  Equiv.ofBijective (@toVec q) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨toVec_inj q, by simp [ZMod.card]⟩)

lemma zmod2_add_iff (a b : Bool) :
    ((if a then (1 : ZMod 2) else 0) + (if b then 1 else 0)) = if xor a b then 1 else 0 := by
  cases a <;> cases b <;> decide

lemma zmod2_eq_ite_iff (a b : Bool) :
    ((if a then (1 : ZMod 2) else 0) = (if b then 1 else 0)) ↔ a = b := by
  cases a <;> cases b <;> decide

lemma par_eq_sum {q : ℕ} (P : Nat → Bool) (y : Fin (2 ^ q)) :
    (if (List.range q).foldl (fun b j => xor b (P j && y.val.testBit j)) false then (1 : ZMod 2) else 0) =
      ∑ i : Fin q, if P i.val then toVec y i else 0 := by
  have hgen : ∀ n : ℕ, n ≤ q → ∀ init : Bool,
      (if (List.range n).foldl (fun b j => xor b (P j && y.val.testBit j)) init then (1 : ZMod 2) else 0) =
      (if init then (1 : ZMod 2) else 0) +
        ∑ j ∈ Finset.range n, if P j && y.val.testBit j then (1 : ZMod 2) else 0 := by
    intro n
    induction n with
    | zero =>
      intro _ init
      simp only [List.range_zero, List.foldl_nil, Finset.range_zero, Finset.sum_empty, add_zero]
      rfl
    | succ n ih =>
      intro hn init
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Finset.sum_range_succ, ← zmod2_add_iff, ih (by omega) init, add_assoc]
  rw [hgen q (le_refl q) false]
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  rw [← Fin.sum_univ_eq_sum_range (fun j => if P j && y.val.testBit j then (1 : ZMod 2) else 0) q]
  apply Finset.sum_congr rfl
  intro i _
  simp only [toVec]
  cases P i.val <;> cases y.val.testBit i.val <;> decide

def nextOpt {q : ℕ} (hq : 0 < q) (h : Fin q → Fin 3) (i : Fin q) : Option (Fin q) :=
  if (h i).val = 0 then none else some ⟨(i.val + (h i).val) % q, Nat.mod_lt _ hq⟩

def walk {q : ℕ} (hq : 0 < q) (h : Fin q → Fin 3) (i : Fin q) : ℕ → Option (Fin q)
  | 0 => some i
  | k + 1 => (walk hq h i k).bind (nextOpt hq h)

lemma walk_add {q : ℕ} (hq : 0 < q) (h : Fin q → Fin 3) (i j : Fin q) (a b : ℕ)
    (ha : walk hq h i a = some j) : walk hq h i (a + b) = walk hq h j b := by
  induction b with
  | zero => exact ha
  | succ b ih =>
    rw [Nat.add_succ, walk, ih, walk]

lemma walk_none_add {q : ℕ} (hq : 0 < q) (h : Fin q → Fin 3) (i : Fin q) (a b : ℕ)
    (ha : walk hq h i a = none) : walk hq h i (a + b) = none := by
  induction b with
  | zero => exact ha
  | succ b ih =>
    rw [Nat.add_succ, walk, ih]
    rfl

def isCyc {q : ℕ} (hq : 0 < q) (h : Fin q → Fin 3) (i : Fin q) : Prop :=
  ∃ t : ℕ, 0 < t ∧ walk hq h i t = some i

lemma isCyc_step {q : ℕ} (hq : 0 < q) (h : Fin q → Fin 3) {i j : Fin q}
    (hi : isCyc hq h i) (hij : nextOpt hq h i = some j) : isCyc hq h j := by
  obtain ⟨t, ht, hwt⟩ := hi
  refine ⟨t, ht, ?_⟩
  cases t with
  | zero => omega
  | succ t' =>
    have h1 : walk hq h i (1 + t') = some i := by rwa [add_comm]
    have h2 : walk hq h i 1 = some j := by simp [walk, hij]
    rw [walk_add hq h i j 1 t' h2] at h1
    rw [walk, h1]
    exact hij

lemma isCyc_walk {q : ℕ} (hq : 0 < q) (h : Fin q → Fin 3) {i j : Fin q} {t : ℕ}
    (hi : isCyc hq h i) (hwt : walk hq h i t = some j) : isCyc hq h j := by
  induction t generalizing j with
  | zero =>
    simp only [walk, Option.some.injEq] at hwt
    exact hwt ▸ hi
  | succ t ih =>
    rw [walk] at hwt
    cases hw : walk hq h i t with
    | none => rw [hw] at hwt; cases hwt
    | some u =>
      rw [hw] at hwt
      exact isCyc_step hq h (ih hw) hwt

lemma reaches_none_or_cyc {q : ℕ} (hq : 0 < q) (h : Fin q → Fin 3) (i : Fin q) :
    (∃ t : ℕ, walk hq h i t = none) ∨ (∃ t : ℕ, ∃ j : Fin q, walk hq h i t = some j ∧ isCyc hq h j) := by
  by_cases hn : ∃ t : ℕ, walk hq h i t = none
  · exact Or.inl hn
  · right
    push Not at hn
    have hsome : ∀ t : ℕ, ∃ j : Fin q, walk hq h i t = some j := by
      intro t
      cases hw : walk hq h i t with
      | none => exact absurd hw (hn t)
      | some j => exact ⟨j, rfl⟩
    let f : Fin (q + 1) → Fin q := fun k => (hsome k.val).choose
    have hnotinj : ¬ Function.Injective f := by
      intro hinj
      have := Fintype.card_le_of_injective f hinj
      simp at this
    rw [Function.Injective] at hnotinj
    push Not at hnotinj
    obtain ⟨a, b, hab, hne⟩ := hnotinj
    have ha : walk hq h i a.val = some (f a) := (hsome a.val).choose_spec
    have hb : walk hq h i b.val = some (f b) := (hsome b.val).choose_spec
    wlog hlt : a.val < b.val generalizing a b
    · have hgt : b.val < a.val := by
        have : a.val ≠ b.val := fun h => hne (Fin.ext h)
        omega
      exact this b a hab.symm hne.symm hb ha hgt
    refine ⟨a.val, f a, ha, b.val - a.val, by omega, ?_⟩
    have hadd : a.val + (b.val - a.val) = b.val := by omega
    rw [← walk_add hq h i (f a) a.val (b.val - a.val) ha, hadd, hb, hab]

noncomputable def cycOf {q : ℕ} (hq : 0 < q) (h : Fin q → Fin 3) (i : Fin q) : Finset (Fin q) := by
  classical
  exact Finset.univ.filter (fun u => ∃ t : ℕ, walk hq h i t = some u)

lemma mem_cycOf {q : ℕ} (hq : 0 < q) (h : Fin q → Fin 3) {i u : Fin q} :
    u ∈ cycOf hq h i ↔ ∃ t : ℕ, walk hq h i t = some u := by
  classical
  simp [cycOf]

lemma self_mem_cycOf {q : ℕ} (hq : 0 < q) (h : Fin q → Fin 3) (i : Fin q) :
    i ∈ cycOf hq h i := (mem_cycOf hq h).2 ⟨0, rfl⟩

lemma cycOf_eq_of_mem {q : ℕ} (hq : 0 < q) (h : Fin q → Fin 3) {i j : Fin q}
    (hi : isCyc hq h i) (hij : j ∈ cycOf hq h i) : cycOf hq h j = cycOf hq h i := by
  obtain ⟨k, hk⟩ := (mem_cycOf hq h).1 hij
  obtain ⟨p, hp, hwp⟩ := hi
  have hpow : ∀ m : ℕ, walk hq h i (p * m) = some i := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Nat.mul_succ, walk_add hq h i i (p * m) p ih, hwp]
  have hback : ∃ r : ℕ, walk hq h j r = some i := by
    refine ⟨p * (k + 1) - k, ?_⟩
    have hsum : k + (p * (k + 1) - k) = p * (k + 1) := by
      have : k ≤ p * (k + 1) := by
        calc k ≤ k + 1 := Nat.le_succ k
          _ = 1 * (k + 1) := (Nat.one_mul _).symm
          _ ≤ p * (k + 1) := Nat.mul_le_mul_right _ hp
      omega
    rw [← walk_add hq h i j k (p * (k + 1) - k) hk, hsum, hpow]
  obtain ⟨r, hr⟩ := hback
  ext u
  rw [mem_cycOf, mem_cycOf]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨k + t, by rw [walk_add hq h i j k t hk, ht]⟩
  · rintro ⟨t, ht⟩
    exact ⟨r + t, by rw [walk_add hq h j i r t hr, ht]⟩

lemma cyc_has_pred {q : ℕ} (hq : 0 < q) (h : Fin q → Fin 3) {i u : Fin q}
    (hi : isCyc hq h i) (hu : u ∈ cycOf hq h i) :
    ∃ v ∈ cycOf hq h i, nextOpt hq h v = some u := by
  have hu_cyc : isCyc hq h u := by
    obtain ⟨t, ht⟩ := (mem_cycOf hq h).1 hu
    exact isCyc_walk hq h hi ht
  obtain ⟨p, hp, hwp⟩ := hu_cyc
  cases p with
  | zero => omega
  | succ p' =>
    rw [walk] at hwp
    cases hw : walk hq h u p' with
    | none => rw [hw] at hwp; cases hwp
    | some v =>
      rw [hw] at hwp
      refine ⟨v, ?_, hwp⟩
      rw [← cycOf_eq_of_mem hq h hi hu, mem_cycOf]
      exact ⟨p', hw⟩

lemma mod_cancel_right {q a b c : ℕ} (ha : a < q) (hb : b < q) (hc : c < q)
    (hab : (a + c) % q = (b + c) % q) : a = b := by
  by_cases h1 : a + c < q <;> by_cases h2 : b + c < q
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hab; omega
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hab; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h2] at hab; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hab; omega

lemma cyc_hits_consec {q : ℕ} (hq : 0 < q) (h : Fin q → Fin 3) {i : Fin q}
    (hi : isCyc hq h i) :
    ∀ x : Fin q, x ∈ cycOf hq h i ∨ ⟨(x.val + 1) % q, Nat.mod_lt _ hq⟩ ∈ cycOf hq h i := by
  intro x
  by_contra hboth
  push Not at hboth
  obtain ⟨hx0, hx1⟩ := hboth
  have hex : ∃ k : ℕ, k < q ∧ ⟨(x.val + k) % q, Nat.mod_lt _ hq⟩ ∈ cycOf hq h i := by
    refine ⟨(i.val + q - x.val) % q, Nat.mod_lt _ hq, ?_⟩
    have heq : (⟨(x.val + (i.val + q - x.val) % q) % q, Nat.mod_lt _ hq⟩ : Fin q) = i := by
      ext
      simp only [Nat.add_mod_mod]
      have h1 : x.val + (i.val + q - x.val) = i.val + q := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
    rw [heq]
    exact self_mem_cycOf hq h i
  classical
  let k := Nat.find hex
  have hk_spec : k < q ∧ ⟨(x.val + k) % q, Nat.mod_lt _ hq⟩ ∈ cycOf hq h i := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0] at hk_spec
    have heq : (⟨(x.val + 0) % q, Nat.mod_lt _ hq⟩ : Fin q) = x := by
      ext; simp [Nat.mod_eq_of_lt x.isLt]
    rw [heq] at hk_spec
    exact hx0 hk_spec.2
  have hk1 : k ≠ 1 := by
    intro h1
    rw [h1] at hk_spec
    exact hx1 hk_spec.2
  have hk_ge2 : 2 ≤ k := by omega
  obtain ⟨v, hv_mem, hv_step⟩ := cyc_has_pred hq h hi hk_spec.2
  simp only [nextOpt] at hv_step
  by_cases h0 : (h v).val = 0
  · simp [h0] at hv_step
  · simp only [h0, ↓reduceIte, Option.some.injEq] at hv_step
    have hstep_val : (v.val + (h v).val) % q = (x.val + k) % q := congrArg Fin.val hv_step
    have hhv : (h v).val = 1 ∨ (h v).val = 2 := by
      have := (h v).isLt
      omega
    have hv_eq : v = ⟨(x.val + (k - (h v).val)) % q, Nat.mod_lt _ hq⟩ := by
      ext
      have h1 : (v.val + (h v).val) % q = ((x.val + (k - (h v).val)) + (h v).val) % q := by
        rw [hstep_val, Nat.add_assoc, Nat.sub_add_cancel (by omega)]
      have hmod1 : (v.val + (h v).val) % q = (v.val % q + (h v).val % q) % q := Nat.add_mod _ _ _
      have hmod2 : ((x.val + (k - (h v).val)) + (h v).val) % q =
          ((x.val + (k - (h v).val)) % q + (h v).val % q) % q := Nat.add_mod _ _ _
      rw [Nat.mod_eq_of_lt v.isLt] at hmod1
      rw [hmod1, hmod2] at h1
      exact mod_cancel_right v.isLt (Nat.mod_lt _ hq) (Nat.mod_lt _ hq) h1
    rw [hv_eq] at hv_mem
    have hlt_k : k - (h v).val < k := by omega
    exact Nat.find_min hex hlt_k ⟨by omega, hv_mem⟩

lemma cyc_next_bij {q : ℕ} (hq : 0 < q) (h : Fin q → Fin 3) {i : Fin q} (hi : isCyc hq h i) :
    ∀ u ∈ cycOf hq h i, (h u).val ≠ 0 ∧
      ⟨(u.val + (h u).val) % q, Nat.mod_lt _ hq⟩ ∈ cycOf hq h i := by
  intro u hu
  have hu_cyc : isCyc hq h u := by
    obtain ⟨t, ht⟩ := (mem_cycOf hq h).1 hu
    exact isCyc_walk hq h hi ht
  obtain ⟨t, ht, hwt⟩ := hu_cyc
  have h1 : nextOpt hq h u ≠ none := by
    intro hnone
    cases t with
    | zero => omega
    | succ t' =>
      have h2 : walk hq h u 1 = none := by simp [walk, hnone]
      have h3 : walk hq h u (1 + t') = none := walk_none_add hq h u 1 t' h2
      rw [add_comm, hwt] at h3
      cases h3
  simp only [nextOpt] at h1
  have hnz : (h u).val ≠ 0 := by
    intro h0; simp [h0] at h1
  refine ⟨hnz, ?_⟩
  rw [← cycOf_eq_of_mem hq h hi hu, mem_cycOf]
  exact ⟨1, by simp [walk, nextOpt, hnz]⟩

def linT {q : ℕ} (hq : 0 < q) (h : Fin q → Fin 3) : (Fin q → ZMod 2) →ₗ[ZMod 2] (Fin q → ZMod 2) where
  toFun v i := v i + if (h i).val ≠ 0 then v ⟨(i.val + (h i).val) % q, Nat.mod_lt _ hq⟩ else 0
  map_add' u v := by
    ext i
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' a v := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

def sumOn {q : ℕ} (S : Finset (Fin q)) : (Fin q → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun w := ∑ i ∈ S, w i
  map_add' u v := by simp [Finset.sum_add_distrib]
  map_smul' a v := by simp [Finset.mul_sum]

lemma sumOn_linT_eq_zero {q : ℕ} (hq : 0 < q) (h : Fin q → Fin 3) {i : Fin q} (hi : isCyc hq h i)
    (v : Fin q → ZMod 2) : sumOn (cycOf hq h i) (linT hq h v) = 0 := by
  simp only [sumOn, LinearMap.coe_mk, AddHom.coe_mk, linT, Finset.sum_add_distrib]
  have h1 : ∑ u ∈ cycOf hq h i,
      (if (h u).val ≠ 0 then v ⟨(u.val + (h u).val) % q, Nat.mod_lt _ hq⟩ else 0) =
      ∑ u ∈ cycOf hq h i, v u := by
    have hcongr : ∑ u ∈ cycOf hq h i,
        (if (h u).val ≠ 0 then v ⟨(u.val + (h u).val) % q, Nat.mod_lt _ hq⟩ else 0) =
        ∑ u ∈ cycOf hq h i, v ⟨(u.val + (h u).val) % q, Nat.mod_lt _ hq⟩ := by
      apply Finset.sum_congr rfl
      intro u hu
      simp [(cyc_next_bij hq h hi u hu).1]
    rw [hcongr]
    have hsurj : (cycOf hq h i).image (fun x => ⟨(x.val + (h x).val) % q, Nat.mod_lt _ hq⟩) = cycOf hq h i := by
      ext w
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (cyc_next_bij hq h hi x hx).2
      · intro hw
        obtain ⟨x, hx, hstep⟩ := cyc_has_pred hq h hi hw
        have hnz := (cyc_next_bij hq h hi x hx).1
        simp only [nextOpt, hnz, ↓reduceIte, Option.some.injEq] at hstep
        exact ⟨x, hx, hstep⟩
    have hinj := Finset.injOn_of_card_image_eq (s := cycOf hq h i)
      (f := fun x : Fin q => (⟨(x.val + (h x).val) % q, Nat.mod_lt _ hq⟩ : Fin q)) (by rw [hsurj])
    rw [← Finset.sum_image hinj, hsurj]
  rw [h1]
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  exact h2 _

lemma ker_walk_eq {q : ℕ} (hq : 0 < q) (h : Fin q → Fin 3) {v : Fin q → ZMod 2}
    (hv : v ∈ LinearMap.ker (linT hq h)) :
    (∀ i t, walk hq h i t = none → v i = 0) ∧
    (∀ i j t, walk hq h i t = some j → v i = v j) := by
  have hstep : ∀ i : Fin q,
      ((h i).val = 0 → v i = 0) ∧
      ((h i).val ≠ 0 → v i = v ⟨(i.val + (h i).val) % q, Nat.mod_lt _ hq⟩) := by
    intro i
    have hi : (linT hq h v) i = 0 := congrFun hv i
    simp only [linT, LinearMap.coe_mk, AddHom.coe_mk] at hi
    constructor
    · intro h0; simpa [h0] using hi
    · intro hnz
      simp only [hnz, ne_eq, not_false_eq_true, ↓reduceIte] at hi
      have h2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
      exact h2 _ _ hi
  have h2 : ∀ i j t, walk hq h i t = some j → v i = v j := by
    intro i j t
    induction t generalizing j with
    | zero =>
      intro hw
      simp only [walk, Option.some.injEq] at hw
      rw [hw]
    | succ t ih =>
      intro hw
      rw [walk] at hw
      cases hwt : walk hq h i t with
      | none => rw [hwt] at hw; cases hw
      | some u =>
        rw [hwt] at hw
        simp only [Option.bind_some, nextOpt] at hw
        by_cases h0 : (h u).val = 0
        · simp [h0] at hw
        · simp only [h0, ↓reduceIte, Option.some.injEq] at hw
          rw [ih u hwt, (hstep u).2 h0, hw]
  refine ⟨?_, h2⟩
  intro i t
  induction t with
  | zero => intro hw; simp [walk] at hw
  | succ t ih =>
    intro hw
    rw [walk] at hw
    cases hwt : walk hq h i t with
    | none => exact ih hwt
    | some u =>
      rw [hwt] at hw
      simp only [Option.bind_some, nextOpt] at hw
      by_cases h0 : (h u).val = 0
      · rw [h2 i u t hwt, (hstep u).1 h0]
      · simp [h0] at hw

lemma nat_card_fiber_linT {q : ℕ} (hq : 0 < q) (h : Fin q → Fin 3) (w : Fin q → ZMod 2)
    [Decidable (w ∈ LinearMap.range (linT hq h))] :
    Nat.card {v : Fin q → ZMod 2 // linT hq h v = w} =
      if w ∈ LinearMap.range (linT hq h) then 2 ^ Module.finrank (ZMod 2) (LinearMap.ker (linT hq h)) else 0 := by
  classical
  by_cases hw : w ∈ LinearMap.range (linT hq h)
  · simp only [hw, ↓reduceIte]
    obtain ⟨v0, rfl⟩ := hw
    have heq : {v : Fin q → ZMod 2 // linT hq h v = linT hq h v0} ≃ LinearMap.ker (linT hq h) :=
      { toFun := fun v => ⟨v.1 - v0, by simp [LinearMap.mem_ker, v.2]⟩
        invFun := fun u => ⟨u.1 + v0, by simp [LinearMap.mem_ker.1 u.2]⟩
        left_inv := fun v => by ext; simp
        right_inv := fun u => by ext; simp }
    rw [Nat.card_congr heq, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  · simp only [hw, ↓reduceIte]
    haveI : IsEmpty {v : Fin q → ZMod 2 // linT hq h v = w} :=
      ⟨fun v => hw ⟨v.1, v.2⟩⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero]

lemma zmod2_eq_decide (a : ZMod 2) : a = if decide (a = 1) then 1 else 0 := by
  fin_cases a <;> rfl

lemma linT_coord_iff (a b c d : Bool) :
    ((if a then (1 : ZMod 2) else 0) + (if b then 1 else 0) =
      (if d then 1 else 0) - (if c then 1 else 0)) ↔ xor c (xor a b) = d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

lemma forward_dir {q : ℕ} (hq : 0 < q) (aff : Bool) (h : Fin q → Fin 3) (c : Fin q → Bool)
    (hc : aff = true ∨ ∀ i, c i = false) :
    let W := Fin (2 ^ q)
    let value := fun (h : Fin q → Fin 3) (c : Fin q → Bool) (x : W) (i : Fin q) =>
      xor (c i) (xor (x.val.testBit i.val)
        (decide ((h i).val ≠ 0) && x.val.testBit ((i.val + (h i).val) % q)))
    let side := fun (b : Bool) => aff = true ∨ b = false
    let par := fun (P : Nat → Bool) (y : W) =>
      (List.range q).foldl (fun b j => xor b (P j && y.val.testBit j)) false
    let H := fun y : W => Nat.card {x : W // ∀ i, value h c x i = y.val.testBit i.val}
    (∀ y, H y = 1) ∨
    (∃ (S : W) (b : Bool), S.val ≠ 0 ∧ side b ∧
      (∀ i : Fin q, S.val.testBit i.val = true ∨ S.val.testBit ((i.val + 1) % q) = true) ∧
      ∀ y, H y = if par (fun j => S.val.testBit j) y = b then 2 else 0) ∨
    (q % 2 = 0 ∧ ∃ a b : Bool, side a ∧ side b ∧ ∀ y,
      H y = if par (fun j => decide (j % 2 = 0)) y = a ∧
        par (fun j => decide (j % 2 = 1)) y = b then 4 else 0) := by
  intro W value side par H
  classical
  let cV : Fin q → ZMod 2 := fun i => if c i then 1 else 0
  have hH_eq : ∀ y : W, H y =
      if toVec y - cV ∈ LinearMap.range (linT hq h) then
        2 ^ Module.finrank (ZMod 2) (LinearMap.ker (linT hq h))
      else 0 := by
    intro y
    rw [← nat_card_fiber_linT hq h (toVec y - cV)]
    apply Nat.card_congr
    refine Equiv.subtypeEquiv (toVecEquiv q) ?_
    intro x
    simp only [toVecEquiv, Equiv.ofBijective_apply]
    have hcoord : ∀ i : Fin q,
        ((linT hq h (toVec x)) i = (toVec y - cV) i) ↔ value h c x i = y.val.testBit i.val := by
      intro i
      simp only [linT, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, toVec, cV, value]
      have h1 : (if (h i).val ≠ 0 then (if x.val.testBit ((i.val + (h i).val) % q) then (1 : ZMod 2) else 0) else 0) =
          if (decide ((h i).val ≠ 0) && x.val.testBit ((i.val + (h i).val) % q)) then 1 else 0 := by
        by_cases hnz : (h i).val ≠ 0 <;> cases x.val.testBit ((i.val + (h i).val) % q) <;> simp [hnz]
      rw [h1]
      exact linT_coord_iff _ _ _ _
    constructor
    · intro hx; ext i; exact (hcoord i).2 (hx i)
    · intro hx i; exact (hcoord i).1 (congrFun hx i)
  let Cycs : Finset (Finset (Fin q)) :=
    (Finset.univ.filter (fun i : Fin q => isCyc hq h i)).image (cycOf hq h)
  have hCycs_disj : ∀ C1 ∈ Cycs, ∀ C2 ∈ Cycs, C1 ≠ C2 → Disjoint C1 C2 := by
    intro C1 h1 C2 h2 hne
    rw [Finset.mem_image] at h1 h2
    obtain ⟨i1, hi1, rfl⟩ := h1
    obtain ⟨i2, hi2, rfl⟩ := h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    exact hne (by rw [← cycOf_eq_of_mem hq h hi1 hu1, cycOf_eq_of_mem hq h hi2 hu2])
  have hCycs_hits : ∀ C ∈ Cycs, ∀ x : Fin q,
      x ∈ C ∨ ⟨(x.val + 1) % q, Nat.mod_lt _ hq⟩ ∈ C := by
    intro C hC x
    rw [Finset.mem_image] at hC
    obtain ⟨i, hi, rfl⟩ := hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact cyc_hits_consec hq h hi x
  have hCycs_le2 : Cycs.card ≤ 2 := by
    let p0 : Finset (Fin q) := {⟨0, hq⟩, ⟨1 % q, Nat.mod_lt _ hq⟩}
    have hcard_p0 : p0.card ≤ 2 := Finset.card_le_two
    have hinj : ∀ C ∈ Cycs, ∃ x ∈ p0, x ∈ C := by
      intro C hC
      rcases hCycs_hits C hC ⟨0, hq⟩ with h0 | h1
      · exact ⟨⟨0, hq⟩, by simp [p0], h0⟩
      · exact ⟨⟨1 % q, Nat.mod_lt _ hq⟩, by simp [p0], by simpa using h1⟩
    let pick : Finset (Fin q) → Fin q := fun C =>
      if h : C ∈ Cycs then (hinj C h).choose else ⟨0, hq⟩
    have hpick_mem : ∀ C ∈ Cycs, pick C ∈ p0 ∧ pick C ∈ C := by
      intro C hC
      simp only [pick, hC, ↓reduceDIte]
      exact (hinj C hC).choose_spec
    have hpick_inj : Set.InjOn pick Cycs := by
      intro C1 h1 C2 h2 heq
      by_contra hne
      have hdisj := hCycs_disj C1 h1 C2 h2 hne
      have hp1 := (hpick_mem C1 h1).2
      have hp2 := (hpick_mem C2 h2).2
      rw [heq] at hp1
      exact Finset.disjoint_left.1 hdisj hp1 hp2
    have hsub : Cycs.image pick ⊆ p0 := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨C, hC, rfl⟩ := hx
      exact (hpick_mem C hC).1
    calc Cycs.card = (Cycs.image pick).card := (Finset.card_image_of_injOn hpick_inj).symm
      _ ≤ p0.card := Finset.card_le_card hsub
      _ ≤ 2 := hcard_p0
  have hker_card : Fintype.card (LinearMap.ker (linT hq h)) = 2 ^ Cycs.card := by
    have hbij : LinearMap.ker (linT hq h) ≃ ({C // C ∈ Cycs} → ZMod 2) := by
      have hrep : ∀ C : {C // C ∈ Cycs}, ∃ i : Fin q, isCyc hq h i ∧ cycOf hq h i = C.1 := by
        rintro ⟨C, hC⟩
        rw [Finset.mem_image] at hC
        obtain ⟨i, hi, rfl⟩ := hC
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact ⟨i, hi, rfl⟩
      let rep : {C // C ∈ Cycs} → Fin q := fun C => (hrep C).choose
      have hrep_spec : ∀ C : {C // C ∈ Cycs}, isCyc hq h (rep C) ∧ cycOf hq h (rep C) = C.1 :=
        fun C => (hrep C).choose_spec
      let toF : LinearMap.ker (linT hq h) → ({C // C ∈ Cycs} → ZMod 2) :=
        fun v C => v.1 (rep C)
      let ofF_fun : ({C // C ∈ Cycs} → ZMod 2) → (Fin q → ZMod 2) := fun α i =>
        if hex : ∃ t : ℕ, ∃ j : Fin q, walk hq h i t = some j ∧ isCyc hq h j then
          let j := (hex.choose_spec).choose
          have hj : isCyc hq h j := (hex.choose_spec).choose_spec.2
          α ⟨cycOf hq h j, Finset.mem_image.2 ⟨j, by simp [hj], rfl⟩⟩
        else 0
      have hofF_ker : ∀ α, ofF_fun α ∈ LinearMap.ker (linT hq h) := by
        intro α
        rw [LinearMap.mem_ker]
        ext i
        simp only [linT, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
        by_cases h0 : (h i).val = 0
        · simp only [h0, ne_eq, not_true_eq_false, ↓reduceIte, add_zero]
          have hno : ¬ ∃ t : ℕ, ∃ j : Fin q, walk hq h i t = some j ∧ isCyc hq h j := by
            rintro ⟨t, j, hwt, hj⟩
            have hn1 : walk hq h i 1 = none := by simp [walk, nextOpt, h0]
            cases t with
            | zero =>
              simp only [walk, Option.some.injEq] at hwt
              subst hwt
              obtain ⟨p, hp, hwp⟩ := hj
              cases p with
              | zero => omega
              | succ p' =>
                have h2 := walk_none_add hq h i 1 p' hn1
                rw [add_comm, hwp] at h2
                cases h2
            | succ t' =>
              have h2 := walk_none_add hq h i 1 t' hn1
              rw [add_comm, hwt] at h2
              cases h2
          simp [ofF_fun, hno]
        · simp only [h0, ne_eq, not_false_eq_true, ↓reduceIte]
          let i' : Fin q := ⟨(i.val + (h i).val) % q, Nat.mod_lt _ hq⟩
          have hstep1 : walk hq h i 1 = some i' := by simp [walk, nextOpt, h0, i']
          have hsame : ofF_fun α i = ofF_fun α i' := by
            by_cases hex1 : ∃ t : ℕ, ∃ j : Fin q, walk hq h i t = some j ∧ isCyc hq h j
            · have hex2 : ∃ t : ℕ, ∃ j : Fin q, walk hq h i' t = some j ∧ isCyc hq h j := by
                obtain ⟨t, j, hwt, hj⟩ := hex1
                cases t with
                | zero =>
                  simp only [walk, Option.some.injEq] at hwt
                  subst hwt
                  exact ⟨0, i', rfl, isCyc_walk hq h hj hstep1⟩
                | succ t' =>
                  refine ⟨t', j, ?_, hj⟩
                  have := walk_add hq h i i' 1 t' hstep1
                  rw [add_comm] at this
                  rw [← this, hwt]
              simp only [ofF_fun, hex1, hex2, ↓reduceDIte]
              congr 1
              apply Subtype.ext
              let t1 := hex1.choose
              let j1 := hex1.choose_spec.choose
              have hj1 := hex1.choose_spec.choose_spec
              let t2 := hex2.choose
              let j2 := hex2.choose_spec.choose_spec
              let j2' := hex2.choose_spec.choose
              have hw1 : walk hq h i (1 + t2) = some j2' := by
                rw [walk_add hq h i i' 1 t2 hstep1]
                exact j2.1
              have hsame_c : cycOf hq h j1 = cycOf hq h j2' := by
                by_cases hle : t1 ≤ 1 + t2
                · have hw := walk_add hq h i j1 t1 (1 + t2 - t1) hj1.1
                  rw [Nat.add_sub_of_le hle, hw1] at hw
                  exact (cycOf_eq_of_mem hq h hj1.2 ((mem_cycOf hq h).2 ⟨1 + t2 - t1, hw.symm⟩)).symm
                · have hw := walk_add hq h i j2' (1 + t2) (t1 - (1 + t2)) hw1
                  rw [Nat.add_sub_of_le (by omega), hj1.1] at hw
                  exact cycOf_eq_of_mem hq h j2.2 ((mem_cycOf hq h).2 ⟨t1 - (1 + t2), hw.symm⟩)
              exact hsame_c
            · have hno2 : ¬ ∃ t : ℕ, ∃ j : Fin q, walk hq h i' t = some j ∧ isCyc hq h j := by
                rintro ⟨t, j, hwt, hj⟩
                apply hex1
                exact ⟨1 + t, j, by rw [walk_add hq h i i' 1 t hstep1, hwt], hj⟩
              simp [ofF_fun, hex1, hno2]
          rw [hsame]
          have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
          exact h2 _
      refine ⟨toF, fun α => ⟨ofF_fun α, hofF_ker α⟩, ?_, ?_⟩
      · intro v
        ext i
        simp only [toF]
        rcases reaches_none_or_cyc hq h i with ⟨t, ht⟩ | hex
        · have hno : ¬ ∃ t : ℕ, ∃ j : Fin q, walk hq h i t = some j ∧ isCyc hq h j := by
            rintro ⟨t2, j, hwt, hj⟩
            by_cases hle : t ≤ t2
            · have := walk_none_add hq h i t (t2 - t) ht
              rw [Nat.add_sub_of_le hle, hwt] at this; cases this
            · have := walk_add hq h i j t2 (t - t2) hwt
              rw [Nat.add_sub_of_le (by omega), ht] at this
              obtain ⟨p, hp, hwp⟩ := hj
              have hpow : ∀ m : ℕ, walk hq h j (p * m) = some j := by
                intro m
                induction m with
                | zero => rfl
                | succ m ih => rw [Nat.mul_succ, walk_add hq h j j (p * m) p ih, hwp]
              have hm : t - t2 ≤ p * (t - t2 + 1) := by
                calc t - t2 ≤ t - t2 + 1 := Nat.le_succ _
                  _ = 1 * (t - t2 + 1) := (Nat.one_mul _).symm
                  _ ≤ p * (t - t2 + 1) := Nat.mul_le_mul_right _ hp
              have hnone := walk_none_add hq h j (t - t2) (p * (t - t2 + 1) - (t - t2)) this.symm
              rw [Nat.add_sub_of_le hm, hpow] at hnone
              cases hnone
          simp only [ofF_fun, hno, ↓reduceDIte]
          exact ((ker_walk_eq hq h v.2).1 i t ht).symm
        · simp only [ofF_fun, hex, ↓reduceDIte]
          let j := hex.choose_spec.choose
          have hj := hex.choose_spec.choose_spec
          have hmem : j ∈ cycOf hq h (rep ⟨cycOf hq h j, Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj.2⟩, rfl⟩⟩) := by
            rw [(hrep_spec _).2]
            exact self_mem_cycOf hq h j
          obtain ⟨t', ht'⟩ := (mem_cycOf hq h).1 hmem
          exact ((ker_walk_eq hq h v.2).2 _ _ _ ht').trans ((ker_walk_eq hq h v.2).2 _ _ _ hj.1).symm
      · intro α
        ext C
        simp only [toF]
        have hex : ∃ t : ℕ, ∃ j : Fin q, walk hq h (rep C) t = some j ∧ isCyc hq h j :=
          ⟨0, rep C, rfl, (hrep_spec C).1⟩
        simp only [ofF_fun, hex, ↓reduceDIte]
        congr 1
        apply Subtype.ext
        dsimp only
        let j := hex.choose_spec.choose
        have hj := hex.choose_spec.choose_spec
        have hmem : j ∈ cycOf hq h (rep C) := (mem_cycOf hq h).2 ⟨hex.choose, hj.1⟩
        rw [cycOf_eq_of_mem hq h (hrep_spec C).1 hmem, (hrep_spec C).2]
    rw [Fintype.card_congr hbij, Fintype.card_fun, ZMod.card, Fintype.card_coe]
  have hfinrank_ker : Module.finrank (ZMod 2) (LinearMap.ker (linT hq h)) = Cycs.card := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker (linT hq h))
    rw [ZMod.card, hker_card] at h1
    exact Nat.pow_right_injective (by omega : 1 < 2) h1.symm
  have hfinrank_range : Module.finrank (ZMod 2) (LinearMap.range (linT hq h)) + Cycs.card = q := by
    have hr := LinearMap.finrank_range_add_finrank_ker (linT hq h)
    rw [hfinrank_ker, Module.finrank_fin_fun] at hr
    exact hr
  have hc_case : Cycs.card = 0 ∨ Cycs.card = 1 ∨ Cycs.card = 2 := by omega
  rcases hc_case with h0 | h1 | h2
  · left
    intro y
    rw [hH_eq y, hfinrank_ker, h0, pow_zero]
    have htop : LinearMap.range (linT hq h) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]
      omega
    simp [htop]
  · right; left
    obtain ⟨C, hC_eq⟩ := Finset.card_eq_one.1 h1
    have hC_mem : C ∈ Cycs := by rw [hC_eq]; simp
    have hC_mem_img := hC_mem
    rw [Finset.mem_image] at hC_mem_img
    obtain ⟨i0, hi0, rfl⟩ := hC_mem_img
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi0
    let S_vec : Fin q → ZMod 2 := fun j => if j ∈ cycOf hq h i0 then 1 else 0
    let S : W := (toVecEquiv q).symm S_vec
    have hS_bit : ∀ j : Fin q, S.val.testBit j.val = decide (j ∈ cycOf hq h i0) := by
      intro j
      have h1 : toVec S j = S_vec j := by
        have := (toVecEquiv q).apply_symm_apply S_vec
        exact congrFun this j
      simp only [toVec, S_vec] at h1
      cases hx : S.val.testBit j.val <;> by_cases hm : j ∈ cycOf hq h i0 <;> simp [hx, hm] at h1 ⊢
    have hS_ne : S.val ≠ 0 := by
      intro h0
      have hb := hS_bit i0
      rw [h0, Nat.zero_testBit] at hb
      have := self_mem_cycOf hq h i0
      simp [this] at hb
    let b : Bool := decide (sumOn (cycOf hq h i0) cV = 1)
    have hb_side : side b := by
      rcases hc with rfl | hc0
      · exact Or.inl rfl
      · right
        have hcV0 : cV = 0 := by ext j; simp [cV, hc0 j]
        simp [b, hcV0, sumOn]
    have hrange_eq : LinearMap.range (linT hq h) = LinearMap.ker (sumOn (cycOf hq h i0)) := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rintro _ ⟨v, rfl⟩
        exact sumOn_linT_eq_zero hq h hi0 v
      · have hsurj : Function.Surjective (sumOn (cycOf hq h i0)) := by
          intro a
          refine ⟨Pi.single i0 a, ?_⟩
          simp [sumOn, Finset.sum_pi_single, self_mem_cycOf hq h i0]
        have hr := LinearMap.finrank_range_add_finrank_ker (sumOn (cycOf hq h i0))
        rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at hr
        omega
    refine ⟨S, b, hS_ne, hb_side, ?_, ?_⟩
    · intro j
      rcases cyc_hits_consec hq h hi0 j with h1' | h2'
      · left; rw [hS_bit j]; simp [h1']
      · right; rw [hS_bit ⟨(j.val + 1) % q, Nat.mod_lt _ hq⟩]; simp [h2']
    · intro y
      rw [hH_eq y, hfinrank_ker, h1, pow_one, hrange_eq, LinearMap.mem_ker, map_sub, sub_eq_zero]
      have hpar : (if par (fun j => S.val.testBit j) y then (1 : ZMod 2) else 0) =
          sumOn (cycOf hq h i0) (toVec y) := by
        rw [par_eq_sum]
        simp only [sumOn, LinearMap.coe_mk, AddHom.coe_mk]
        have hr : ∑ j ∈ cycOf hq h i0, toVec y j = ∑ j : Fin q, if j ∈ cycOf hq h i0 then toVec y j else 0 := by
          rw [← Finset.sum_filter]
          congr 1
          ext j; simp
        rw [hr]
        apply Finset.sum_congr rfl
        intro j _
        rw [hS_bit j]
        by_cases hm : j ∈ cycOf hq h i0 <;> simp [hm]
      have hiff : sumOn (cycOf hq h i0) (toVec y) = sumOn (cycOf hq h i0) cV ↔
          par (fun j => S.val.testBit j) y = b := by
        rw [← hpar, zmod2_eq_decide (sumOn (cycOf hq h i0) cV), zmod2_eq_ite_iff]
      simp [hiff]
  · right; right
    obtain ⟨C0, C1, hne, hC_eq⟩ := Finset.card_eq_two.1 h2
    have hC0_mem : C0 ∈ Cycs := by rw [hC_eq]; simp
    have hC1_mem : C1 ∈ Cycs := by rw [hC_eq]; simp
    have hdisj : Disjoint C0 C1 := hCycs_disj C0 hC0_mem C1 hC1_mem hne
    have hhits0 := hCycs_hits C0 hC0_mem
    have hhits1 := hCycs_hits C1 hC1_mem
    have halt : ∀ x : Fin q,
        (x ∈ C0 ↔ ⟨(x.val + 1) % q, Nat.mod_lt _ hq⟩ ∉ C0) ∧
        (x ∈ C0 ↔ x ∉ C1) := by
      have hcov : ∀ x : Fin q, x ∈ C0 ∨ x ∈ C1 := by
        intro x
        by_contra hnone
        push Not at hnone
        have h10 : ⟨(x.val + 1) % q, Nat.mod_lt _ hq⟩ ∈ C0 := (hhits0 x).resolve_left hnone.1
        have h11 : ⟨(x.val + 1) % q, Nat.mod_lt _ hq⟩ ∈ C1 := (hhits1 x).resolve_left hnone.2
        exact Finset.disjoint_left.1 hdisj h10 h11
      intro x
      have hcomp : x ∈ C0 ↔ x ∉ C1 :=
        ⟨fun h0 h1 => Finset.disjoint_left.1 hdisj h0 h1, fun hn1 => (hcov x).resolve_right hn1⟩
      refine ⟨?_, hcomp⟩
      constructor
      · intro hx0 hx1
        have h1 : x ∉ C1 := fun h => Finset.disjoint_left.1 hdisj hx0 h
        have h2 : ⟨(x.val + 1) % q, Nat.mod_lt _ hq⟩ ∉ C1 := fun h => Finset.disjoint_left.1 hdisj hx1 h
        rcases hhits1 x with h | h
        · exact h1 h
        · exact h2 h
      · intro hnx
        exact (hhits0 x).resolve_right hnx
    have hC0_par : ∀ t : ℕ, ∀ ht : t < q, (⟨t, ht⟩ ∈ C0 ↔ (⟨0, hq⟩ ∈ C0 ↔ t % 2 = 0)) := by
      intro t
      induction t with
      | zero => intro _; simp
      | succ t ih =>
        intro ht
        have hstep := (halt ⟨t, by omega⟩).1
        have heq : (⟨(t + 1) % q, Nat.mod_lt _ hq⟩ : Fin q) = ⟨t + 1, ht⟩ := by
          ext; simp [Nat.mod_eq_of_lt ht]
        rw [heq] at hstep
        have iht := ih (by omega)
        have hmod : (t + 1) % 2 = 0 ↔ t % 2 ≠ 0 := by omega
        have hb : (⟨t + 1, ht⟩ : Fin q) ∈ C0 ↔ (⟨t, by omega⟩ : Fin q) ∉ C0 := by
          rw [hstep, not_not]
        rw [hb, iht, hmod]
        by_cases h0 : (⟨0, hq⟩ : Fin q) ∈ C0 <;> by_cases hm : t % 2 = 0 <;> simp [h0, hm]
    have hq_even : q % 2 = 0 := by
      have hstep := (halt ⟨q - 1, by omega⟩).1
      have heq : (⟨(q - 1 + 1) % q, Nat.mod_lt _ hq⟩ : Fin q) = ⟨0, hq⟩ := by
        ext; simp [show q - 1 + 1 = q by omega]
      rw [heq] at hstep
      have hlast := hC0_par (q - 1) (by omega)
      rw [hlast] at hstep
      have hmod : (q - 1) % 2 ≠ 0 := by
        by_cases h0 : (⟨0, hq⟩ : Fin q) ∈ C0 <;> simp [h0] at hstep <;> omega
      omega
    let Ev : Finset (Fin q) := Finset.univ.filter (fun j : Fin q => j.val % 2 = 0)
    let Od : Finset (Fin q) := Finset.univ.filter (fun j : Fin q => j.val % 2 = 1)
    have hEvOd : (C0 = Ev ∧ C1 = Od) ∨ (C0 = Od ∧ C1 = Ev) := by
      by_cases h0in : ⟨0, hq⟩ ∈ C0
      · left
        have hC0 : C0 = Ev := by
          ext j
          simp only [Ev, Finset.mem_filter, Finset.mem_univ, true_and]
          have := hC0_par j.val j.isLt
          simpa [h0in] using this
        have hC1 : C1 = Od := by
          ext j
          simp only [Od, Finset.mem_filter, Finset.mem_univ, true_and]
          have h1 := (halt j).2
          rw [hC0] at h1
          simp only [Ev, Finset.mem_filter, Finset.mem_univ, true_and] at h1
          constructor
          · intro hj; by_contra hne; exact h1.1 (by omega) hj
          · intro hj; by_contra hne; exact (by omega : j.val % 2 ≠ 0) (h1.2 hne)
        exact ⟨hC0, hC1⟩
      · right
        have hC0 : C0 = Od := by
          ext j
          simp only [Od, Finset.mem_filter, Finset.mem_univ, true_and]
          have := hC0_par j.val j.isLt
          have hiff : j ∈ C0 ↔ j.val % 2 ≠ 0 := by simpa [h0in] using this
          rw [hiff]
          exact ⟨fun h => by omega, fun h => by omega⟩
        have hC1 : C1 = Ev := by
          ext j
          simp only [Ev, Finset.mem_filter, Finset.mem_univ, true_and]
          have h1 := (halt j).2
          rw [hC0] at h1
          simp only [Od, Finset.mem_filter, Finset.mem_univ, true_and] at h1
          constructor
          · intro hj; by_contra hne; exact h1.1 (by omega) hj
          · intro hj; by_contra hne; exact (by omega : j.val % 2 ≠ 1) (h1.2 hne)
        exact ⟨hC0, hC1⟩
    have hEv_in : Ev ∈ Cycs := by rcases hEvOd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hOd_in : Od ∈ Cycs := by rcases hEvOd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hEv_zero : ∀ v, sumOn Ev (linT hq h v) = 0 := by
      rw [Finset.mem_image] at hEv_in
      obtain ⟨i, hi, hi_eq⟩ := hEv_in
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [← hi_eq]
      exact sumOn_linT_eq_zero hq h hi
    have hOd_zero : ∀ v, sumOn Od (linT hq h v) = 0 := by
      rw [Finset.mem_image] at hOd_in
      obtain ⟨i, hi, hi_eq⟩ := hOd_in
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [← hi_eq]
      exact sumOn_linT_eq_zero hq h hi
    let pairMap : (Fin q → ZMod 2) →ₗ[ZMod 2] (ZMod 2 × ZMod 2) := (sumOn Ev).prod (sumOn Od)
    have hrange_eq : LinearMap.range (linT hq h) = LinearMap.ker pairMap := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rintro _ ⟨v, rfl⟩
        simp [LinearMap.mem_ker, pairMap, hEv_zero v, hOd_zero v]
      · have hq2 : 2 ≤ q := by omega
        have hsurj : Function.Surjective pairMap := by
          rintro ⟨a, b⟩
          refine ⟨Pi.single ⟨0, by omega⟩ a + Pi.single ⟨1, by omega⟩ b, ?_⟩
          apply Prod.ext
          · simp [pairMap, sumOn, Ev, Finset.sum_add_distrib, Finset.sum_pi_single]
          · simp [pairMap, sumOn, Od, Finset.sum_add_distrib, Finset.sum_pi_single]
        have hr := LinearMap.finrank_range_add_finrank_ker pairMap
        rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_prod,
          Module.finrank_self, Module.finrank_fin_fun] at hr
        omega
    let a : Bool := decide (sumOn Ev cV = 1)
    let b : Bool := decide (sumOn Od cV = 1)
    have ha_side : side a := by
      rcases hc with rfl | hc0
      · exact Or.inl rfl
      · right
        have hcV0 : cV = 0 := by ext j; simp [cV, hc0 j]
        simp [a, hcV0, sumOn]
    have hb_side : side b := by
      rcases hc with rfl | hc0
      · exact Or.inl rfl
      · right
        have hcV0 : cV = 0 := by ext j; simp [cV, hc0 j]
        simp [b, hcV0, sumOn]
    refine ⟨hq_even, a, b, ha_side, hb_side, ?_⟩
    intro y
    rw [hH_eq y, hfinrank_ker, h2, show 2 ^ 2 = 4 by decide, hrange_eq, LinearMap.mem_ker,
      map_sub, sub_eq_zero]
    have hparE : (if par (fun j => decide (j % 2 = 0)) y then (1 : ZMod 2) else 0) =
        sumOn Ev (toVec y) := by
      rw [par_eq_sum]
      simp only [sumOn, LinearMap.coe_mk, AddHom.coe_mk, Ev, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hm : j.val % 2 = 0 <;> simp [hm]
    have hparO : (if par (fun j => decide (j % 2 = 1)) y then (1 : ZMod 2) else 0) =
        sumOn Od (toVec y) := by
      rw [par_eq_sum]
      simp only [sumOn, LinearMap.coe_mk, AddHom.coe_mk, Od, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hm : j.val % 2 = 1 <;> simp [hm]
    have hiff : pairMap (toVec y) = pairMap cV ↔
        par (fun j => decide (j % 2 = 0)) y = a ∧ par (fun j => decide (j % 2 = 1)) y = b := by
      rw [Prod.ext_iff]
      change sumOn Ev (toVec y) = sumOn Ev cV ∧ sumOn Od (toVec y) = sumOn Od cV ↔ _
      rw [← hparE, ← hparO, zmod2_eq_decide (sumOn Ev cV), zmod2_eq_decide (sumOn Od cV),
        zmod2_eq_ite_iff, zmod2_eq_ite_iff]
    simp [hiff]

lemma backward_dir {q : ℕ} (hq : 0 < q) (aff : Bool) (H : Fin (2 ^ q) → Nat)
    (hrhs :
      (∀ y, H y = 1) ∨
      (∃ (S : Fin (2 ^ q)) (b : Bool), S.val ≠ 0 ∧ (aff = true ∨ b = false) ∧
        (∀ i : Fin q, S.val.testBit i.val = true ∨ S.val.testBit ((i.val + 1) % q) = true) ∧
        ∀ y, H y = if (List.range q).foldl (fun acc j => xor acc (S.val.testBit j && y.val.testBit j)) false = b then 2 else 0) ∨
      (q % 2 = 0 ∧ ∃ a b : Bool, (aff = true ∨ a = false) ∧ (aff = true ∨ b = false) ∧ ∀ y,
        H y = if (List.range q).foldl (fun acc j => xor acc (decide (j % 2 = 0) && y.val.testBit j)) false = a ∧
          (List.range q).foldl (fun acc j => xor acc (decide (j % 2 = 1) && y.val.testBit j)) false = b then 4 else 0)) :
    ∃ (h : Fin q → Fin 3) (c : Fin q → Bool), (aff = true ∨ ∀ i, c i = false) ∧ ∀ y : Fin (2 ^ q),
      H y = Nat.card {x : Fin (2 ^ q) // ∀ i,
        xor (c i) (xor (x.val.testBit i.val)
          (decide ((h i).val ≠ 0) && x.val.testBit ((i.val + (h i).val) % q))) = y.val.testBit i.val} := by
  classical
  have hcard_eq : ∀ (h : Fin q → Fin 3) (c : Fin q → Bool) (y : Fin (2 ^ q)),
      Nat.card {x : Fin (2 ^ q) // ∀ i,
        xor (c i) (xor (x.val.testBit i.val)
          (decide ((h i).val ≠ 0) && x.val.testBit ((i.val + (h i).val) % q))) = y.val.testBit i.val} =
      if toVec y - (fun i => if c i then (1 : ZMod 2) else 0) ∈ LinearMap.range (linT hq h) then
        2 ^ Module.finrank (ZMod 2) (LinearMap.ker (linT hq h))
      else 0 := by
    intro h c y
    rw [← nat_card_fiber_linT hq h (toVec y - (fun i => if c i then (1 : ZMod 2) else 0))]
    apply Nat.card_congr
    refine Equiv.subtypeEquiv (toVecEquiv q) ?_
    intro x
    simp only [toVecEquiv, Equiv.ofBijective_apply]
    have hcoord : ∀ i : Fin q,
        ((linT hq h (toVec x)) i = (toVec y - (fun i => if c i then (1 : ZMod 2) else 0)) i) ↔
        xor (c i) (xor (x.val.testBit i.val)
          (decide ((h i).val ≠ 0) && x.val.testBit ((i.val + (h i).val) % q))) = y.val.testBit i.val := by
      intro i
      simp only [linT, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, toVec]
      have h1 : (if (h i).val ≠ 0 then (if x.val.testBit ((i.val + (h i).val) % q) then (1 : ZMod 2) else 0) else 0) =
          if (decide ((h i).val ≠ 0) && x.val.testBit ((i.val + (h i).val) % q)) then 1 else 0 := by
        by_cases hnz : (h i).val ≠ 0 <;> cases x.val.testBit ((i.val + (h i).val) % q) <;> simp [hnz]
      rw [h1]
      exact linT_coord_iff _ _ _ _
    constructor
    · intro hx; ext i; exact (hcoord i).2 (hx i)
    · intro hx i; exact (hcoord i).1 (congrFun hx i)
  rcases hrhs with h1 | ⟨S, b, hS_ne, hb_side, hS_cov, hH⟩ | ⟨hq_even, a, b, ha_side, hb_side, hH⟩
  · refine ⟨fun _ => 0, fun _ => false, Or.inr (fun _ => rfl), ?_⟩
    intro y
    rw [h1 y, hcard_eq]
    have hT : linT hq (fun _ => 0) = LinearMap.id := by
      ext v i; simp [linT]
    rw [hT, LinearMap.range_id, LinearMap.ker_id]
    simp
  · let M : Finset (Fin q) := Finset.univ.filter (fun i : Fin q => S.val.testBit i.val = true)
    have hM_ne : M.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hzero : S = ⟨0, Nat.two_pow_pos q⟩ := by
        apply testBit_eq_of_lt_two_pow
        intro i
        have hi : i ∉ M := by rw [hempty]; simp
        simp only [M, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hi
        simp [hi]
      exact hS_ne (congrArg Fin.val hzero)
    obtain ⟨i0, hi0⟩ := hM_ne
    let h : Fin q → Fin 3 := fun i =>
      if S.val.testBit i.val = false then 0
      else if S.val.testBit ((i.val + 1) % q) = true then 1 else 2
    let c : Fin q → Bool := fun i => if i = i0 then b else false
    have hc_ok : aff = true ∨ ∀ i, c i = false := by
      rcases hb_side with rfl | rfl
      · exact Or.inl rfl
      · right; intro i; simp [c]
    have hnext_in : ∀ i ∈ M, (h i).val ≠ 0 ∧ ⟨(i.val + (h i).val) % q, Nat.mod_lt _ hq⟩ ∈ M := by
      intro i hi
      simp only [M, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      by_cases h1 : S.val.testBit ((i.val + 1) % q) = true
      · have hhi : h i = 1 := by simp [h, hi, h1]
        rw [hhi]
        exact ⟨by decide, h1⟩
      · have hhi : h i = 2 := by simp [h, hi, h1]
        rw [hhi]
        have h2 := hS_cov ⟨(i.val + 1) % q, Nat.mod_lt _ hq⟩
        simp only [h1, Bool.false_eq_true, false_or] at h2
        have hmod : ((i.val + 1) % q + 1) % q = (i.val + 2) % q := by
          rw [Nat.mod_add_mod, Nat.add_assoc]
        rw [hmod] at h2
        exact ⟨by decide, h2⟩
    have hker_eq : LinearMap.ker (linT hq h) = Submodule.span (ZMod 2) {fun i : Fin q => if i ∈ M then (1 : ZMod 2) else 0} := by
      let u0 : Fin q → ZMod 2 := fun i => if i ∈ M then 1 else 0
      have hu0 : u0 ∈ LinearMap.ker (linT hq h) := by
        rw [LinearMap.mem_ker]
        ext i
        simp only [linT, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, u0]
        by_cases hm : i ∈ M
        · obtain ⟨hnz, hnxt⟩ := hnext_in i hm
          simp only [hm, hnz, hnxt, ne_eq, not_false_eq_true, ↓reduceIte]
          have h11 : (1 : ZMod 2) + 1 = 0 := by decide
          exact h11
        · have h0 : h i = 0 := by
            simp only [M, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hm
            simp [h, hm]
          simp [hm, h0]
      apply le_antisymm
      · intro v hv
        rw [Submodule.mem_span_singleton]
        refine ⟨v i0, ?_⟩
        have hv_zero : ∀ i, i ∉ M → v i = 0 := by
          intro i hi
          have h0 : h i = 0 := by
            simp only [M, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hi
            simp [h, hi]
          have hvi := congrFun (LinearMap.mem_ker.1 hv) i
          simp [linT, h0] at hvi
          exact hvi
        have hv_step : ∀ i ∈ M, v i = v ⟨(i.val + (h i).val) % q, Nat.mod_lt _ hq⟩ := by
          intro i hi
          have hnz := (hnext_in i hi).1
          have hvi := congrFun (LinearMap.mem_ker.1 hv) i
          simp only [linT, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, hnz, ne_eq, not_false_eq_true, ↓reduceIte] at hvi
          have h2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
          exact h2 _ _ hvi
        have hv_const : ∀ t : ℕ, t < q → ∀ i : Fin q,
            i = ⟨(i0.val + t) % q, Nat.mod_lt _ hq⟩ → i ∈ M → v i = v i0 := by
          intro t
          induction t using Nat.strong_induction_on with
          | ind t ih =>
            intro ht i hi_eq hiM
            by_cases ht0 : t = 0
            · subst ht0
              have heq : i = i0 := by rw [hi_eq]; ext; simp [Nat.mod_eq_of_lt i0.isLt]
              rw [heq]
            · by_cases h1 : ⟨(i0.val + (t - 1)) % q, Nat.mod_lt _ hq⟩ ∈ M
              · have hprev := ih (t - 1) (by omega) (by omega) _ rfl h1
                have hhi : h ⟨(i0.val + (t - 1)) % q, Nat.mod_lt _ hq⟩ = 1 := by
                  simp only [M, Finset.mem_filter, Finset.mem_univ, true_and] at h1 hiM
                  have hmod : ((i0.val + (t - 1)) % q + 1) % q = i.val := by
                    rw [Nat.mod_add_mod, Nat.add_assoc, show t - 1 + 1 = t by omega, hi_eq]
                  simp [h, h1, hmod, hiM]
                have hst := hv_step _ h1
                rw [hhi] at hst
                have h1val : (1 : Fin 3).val = 1 := rfl
                have heq : (⟨((⟨(i0.val + (t - 1)) % q, Nat.mod_lt _ hq⟩ : Fin q).val + (1 : Fin 3).val) % q, Nat.mod_lt _ hq⟩ : Fin q) = i := by
                  ext; dsimp only; rw [h1val, Nat.mod_add_mod, Nat.add_assoc, show t - 1 + 1 = t by omega, hi_eq]
                rw [heq] at hst
                rw [← hst, hprev]
              · have ht2 : 2 ≤ t := by
                  by_contra hlt
                  have ht1 : t = 1 := by omega
                  subst ht1
                  have heq : (⟨(i0.val + 0) % q, Nat.mod_lt _ hq⟩ : Fin q) = i0 := by
                    ext; simp [Nat.mod_eq_of_lt i0.isLt]
                  rw [show 1 - 1 = 0 by omega, heq] at h1
                  exact h1 hi0
                have h2 : ⟨(i0.val + (t - 2)) % q, Nat.mod_lt _ hq⟩ ∈ M := by
                  have hcov := hS_cov ⟨(i0.val + (t - 2)) % q, Nat.mod_lt _ hq⟩
                  have hmod : ((i0.val + (t - 2)) % q + 1) % q = (i0.val + (t - 1)) % q := by
                    rw [Nat.mod_add_mod, Nat.add_assoc, show t - 2 + 1 = t - 1 by omega]
                  simp only [M, Finset.mem_filter, Finset.mem_univ, true_and] at h1 ⊢
                  rw [hmod] at hcov
                  exact hcov.resolve_right h1
                have hprev := ih (t - 2) (by omega) (by omega) _ rfl h2
                have hhi : h ⟨(i0.val + (t - 2)) % q, Nat.mod_lt _ hq⟩ = 2 := by
                  have hmod : ((i0.val + (t - 2)) % q + 1) % q = (i0.val + (t - 1)) % q := by
                    rw [Nat.mod_add_mod, Nat.add_assoc, show t - 2 + 1 = t - 1 by omega]
                  simp only [M, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
                  simp [h, h2, hmod, h1]
                have hst := hv_step _ h2
                rw [hhi] at hst
                have h2val : (2 : Fin 3).val = 2 := rfl
                have heq : (⟨((⟨(i0.val + (t - 2)) % q, Nat.mod_lt _ hq⟩ : Fin q).val + (2 : Fin 3).val) % q, Nat.mod_lt _ hq⟩ : Fin q) = i := by
                  ext; dsimp only; rw [h2val, Nat.mod_add_mod, Nat.add_assoc, show t - 2 + 2 = t by omega, hi_eq]
                rw [heq] at hst
                rw [← hst, hprev]
        ext i
        simp only [Pi.smul_apply, smul_eq_mul, u0]
        by_cases hiM : i ∈ M
        · simp only [hiM, ↓reduceIte, mul_one]
          let t := (i.val + q - i0.val) % q
          have heq : i = ⟨(i0.val + t) % q, Nat.mod_lt _ hq⟩ := by
            ext
            simp only [t, Nat.add_mod_mod]
            have h1 : i0.val + (i.val + q - i0.val) = i.val + q := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
          exact (hv_const t (Nat.mod_lt _ hq) i heq hiM).symm
        · simp only [hiM, ↓reduceIte, mul_zero]
          exact (hv_zero i hiM).symm
      · rw [Submodule.span_singleton_le_iff_mem]
        exact hu0
    have hfin_ker : Module.finrank (ZMod 2) (LinearMap.ker (linT hq h)) = 1 := by
      rw [hker_eq, finrank_span_singleton]
      intro h0
      have := congrFun h0 i0
      simp [hi0] at this
    have hsum_zero : ∀ v, sumOn M (linT hq h v) = 0 := by
      intro v
      simp only [sumOn, LinearMap.coe_mk, AddHom.coe_mk, linT, Finset.sum_add_distrib]
      have h1 : ∑ i ∈ M, (if (h i).val ≠ 0 then v ⟨(i.val + (h i).val) % q, Nat.mod_lt _ hq⟩ else 0) =
          ∑ i ∈ M, v i := by
        have hcongr : ∑ i ∈ M, (if (h i).val ≠ 0 then v ⟨(i.val + (h i).val) % q, Nat.mod_lt _ hq⟩ else 0) =
            ∑ i ∈ M, v ⟨(i.val + (h i).val) % q, Nat.mod_lt _ hq⟩ := by
          apply Finset.sum_congr rfl
          intro i hi; simp [(hnext_in i hi).1]
        rw [hcongr]
        have hinj : Set.InjOn (fun i : Fin q => (⟨(i.val + (h i).val) % q, Nat.mod_lt _ hq⟩ : Fin q)) M := by
          intro a ha b hb hab
          have hval : (a.val + (h a).val) % q = (b.val + (h b).val) % q := congrArg Fin.val hab
          have hna := (hnext_in a ha).1
          have hnb := (hnext_in b hb).1
          have ha_lt := (h a).isLt
          have hb_lt := (h b).isLt
          have ha' : S.val.testBit a.val = true := (Finset.mem_filter.1 ha).2
          have hb' : S.val.testBit b.val = true := (Finset.mem_filter.1 hb).2
          by_cases heq : (h a).val = (h b).val
          · rw [heq] at hval
            ext
            exact mod_cancel_right (c := (h b).val % q) a.isLt b.isLt (Nat.mod_lt _ hq) (by
              rw [Nat.add_mod_mod, Nat.add_mod_mod]; exact hval)
          · exfalso
            have hcases : ((h a).val = 1 ∧ (h b).val = 2) ∨ ((h a).val = 2 ∧ (h b).val = 1) := by omega
            rcases hcases with ⟨ha1, hb2⟩ | ⟨ha2, hb1⟩
            · have hb_not : S.val.testBit ((b.val + 1) % q) = false := by
                by_contra htr
                have htr' : S.val.testBit ((b.val + 1) % q) = true := Bool.eq_true_of_not_eq_false htr
                have : h b = 1 := by simp [h, hb', htr']
                rw [this] at hb2; omega
              have ha_eq : a.val = (b.val + 1) % q := by
                rw [ha1, hb2] at hval
                have hval' : (a.val + 1) % q = ((b.val + 1) % q + 1) % q := by
                  rw [Nat.mod_add_mod, Nat.add_assoc]; exact hval
                exact mod_cancel_right (c := 1 % q) a.isLt (Nat.mod_lt _ hq) (Nat.mod_lt _ hq) (by
                  rw [Nat.add_mod_mod, Nat.add_mod_mod]; exact hval')
              rw [← ha_eq, ha'] at hb_not
              cases hb_not
            · have ha_not : S.val.testBit ((a.val + 1) % q) = false := by
                by_contra htr
                have htr' : S.val.testBit ((a.val + 1) % q) = true := Bool.eq_true_of_not_eq_false htr
                have : h a = 1 := by simp [h, ha', htr']
                rw [this] at ha2; omega
              have hb_eq : b.val = (a.val + 1) % q := by
                rw [ha2, hb1] at hval
                have hval' : (b.val + 1) % q = ((a.val + 1) % q + 1) % q := by
                  rw [Nat.mod_add_mod, Nat.add_assoc]; exact hval.symm
                exact mod_cancel_right (c := 1 % q) b.isLt (Nat.mod_lt _ hq) (Nat.mod_lt _ hq) (by
                  rw [Nat.add_mod_mod, Nat.add_mod_mod]; exact hval')
              rw [← hb_eq, hb'] at ha_not
              cases ha_not
        have himg : M.image (fun i : Fin q => (⟨(i.val + (h i).val) % q, Nat.mod_lt _ hq⟩ : Fin q)) = M := by
          apply Finset.eq_of_subset_of_card_le
          · intro x hx
            rw [Finset.mem_image] at hx
            obtain ⟨i, hi, rfl⟩ := hx
            exact (hnext_in i hi).2
          · rw [Finset.card_image_of_injOn hinj]
        rw [← Finset.sum_image hinj, himg]
      rw [h1]
      have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
      exact h2 _
    have hrange_eq : LinearMap.range (linT hq h) = LinearMap.ker (sumOn M) := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rintro _ ⟨v, rfl⟩; exact hsum_zero v
      · have hsurj : Function.Surjective (sumOn M) := by
          intro a; refine ⟨Pi.single i0 a, ?_⟩; simp [sumOn, Finset.sum_pi_single, hi0]
        have hr1 := LinearMap.finrank_range_add_finrank_ker (linT hq h)
        have hr2 := LinearMap.finrank_range_add_finrank_ker (sumOn M)
        rw [hfin_ker, Module.finrank_fin_fun] at hr1
        rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at hr2
        omega
    refine ⟨h, c, hc_ok, ?_⟩
    intro y
    rw [hH y, hcard_eq, hfin_ker, pow_one, hrange_eq, LinearMap.mem_ker, map_sub, sub_eq_zero]
    have hpar : (if (List.range q).foldl (fun acc j => xor acc (S.val.testBit j && y.val.testBit j)) false
        then (1 : ZMod 2) else 0) = sumOn M (toVec y) := by
      rw [par_eq_sum]
      simp only [sumOn, LinearMap.coe_mk, AddHom.coe_mk, M, Finset.sum_filter]
    have hsumC : sumOn M (fun i => if c i then (1 : ZMod 2) else 0) = if b then 1 else 0 := by
      simp only [sumOn, LinearMap.coe_mk, AddHom.coe_mk, c]
      rw [Finset.sum_eq_single i0]
      · simp
      · intro j _ hj; simp [hj]
      · intro hni; exact absurd hi0 hni
    have hiff : sumOn M (toVec y) = sumOn M (fun i => if c i then (1 : ZMod 2) else 0) ↔
        (List.range q).foldl (fun acc j => xor acc (S.val.testBit j && y.val.testBit j)) false = b := by
      rw [← hpar, hsumC, zmod2_eq_ite_iff]
    simp [hiff]
  · have hq2 : 2 ≤ q := by omega
    let h : Fin q → Fin 3 := fun _ => 2
    let c : Fin q → Bool := fun i =>
      if i.val = 0 then a else if i.val = 1 then b else false
    have hc_ok : aff = true ∨ ∀ i, c i = false := by
      rcases ha_side with rfl | rfl
      · exact Or.inl rfl
      · rcases hb_side with rfl | rfl
        · exact Or.inl rfl
        · right; intro i; simp [c]
    let Ev : Finset (Fin q) := Finset.univ.filter (fun j : Fin q => j.val % 2 = 0)
    let Od : Finset (Fin q) := Finset.univ.filter (fun j : Fin q => j.val % 2 = 1)
    let uE : Fin q → ZMod 2 := fun j => if j.val % 2 = 0 then 1 else 0
    let uO : Fin q → ZMod 2 := fun j => if j.val % 2 = 1 then 1 else 0
    have hker_eq : LinearMap.ker (linT hq h) = Submodule.span (ZMod 2) {uE, uO} := by
      have huE : uE ∈ LinearMap.ker (linT hq h) := by
        rw [LinearMap.mem_ker]; ext i
        have hpar : (i.val + 2) % q % 2 = i.val % 2 := by
          have hdiv : 2 ∣ q := Nat.dvd_of_mod_eq_zero hq_even
          rw [Nat.mod_mod_of_dvd _ hdiv]; omega
        have h11 : (1 : ZMod 2) + 1 = 0 := by decide
        have h2val : (2 : Fin 3).val = 2 := rfl
        have hnz : (2 : Fin 3).val ≠ 0 := by decide
        simp only [linT, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, h, uE,
          hnz, ne_eq, not_false_eq_true, ↓reduceIte, h2val, hpar]
        by_cases hm : i.val % 2 = 0 <;> simp [hm, h11]
      have huO : uO ∈ LinearMap.ker (linT hq h) := by
        rw [LinearMap.mem_ker]; ext i
        have hpar : (i.val + 2) % q % 2 = i.val % 2 := by
          have hdiv : 2 ∣ q := Nat.dvd_of_mod_eq_zero hq_even
          rw [Nat.mod_mod_of_dvd _ hdiv]; omega
        have h11 : (1 : ZMod 2) + 1 = 0 := by decide
        have h2val : (2 : Fin 3).val = 2 := rfl
        have hnz : (2 : Fin 3).val ≠ 0 := by decide
        simp only [linT, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, h, uO,
          hnz, ne_eq, not_false_eq_true, ↓reduceIte, h2val, hpar]
        by_cases hm : i.val % 2 = 1 <;> simp [hm, h11]
      apply le_antisymm
      · intro v hv
        have hstep : ∀ i : Fin q, v i = v ⟨(i.val + 2) % q, Nat.mod_lt _ hq⟩ := by
          intro i
          have hvi := congrFun (LinearMap.mem_ker.1 hv) i
          simp only [linT, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, h] at hvi
          have hnz : (2 : Fin 3).val ≠ 0 := by decide
          simp only [hnz, ne_eq, not_false_eq_true, ↓reduceIte] at hvi
          have h2 : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
          exact h2 _ _ hvi
        have hconst : ∀ t : ℕ, ∀ ht : t < q,
            v ⟨t, ht⟩ = if t % 2 = 0 then v ⟨0, by omega⟩ else v ⟨1, by omega⟩ := by
          intro t
          induction t using Nat.strong_induction_on with
          | ind t ih =>
            intro ht
            by_cases h0 : t = 0
            · subst h0; simp
            · by_cases h1 : t = 1
              · subst h1; simp
              · have hst := hstep ⟨t - 2, by omega⟩
                have heq : (⟨(t - 2 + 2) % q, Nat.mod_lt _ hq⟩ : Fin q) = ⟨t, ht⟩ := by
                  ext; dsimp only; rw [show t - 2 + 2 = t by omega, Nat.mod_eq_of_lt ht]
                rw [heq] at hst
                rw [← hst, ih (t - 2) (by omega) (by omega)]
                have hmod : (t - 2) % 2 = t % 2 := by omega
                rw [hmod]
        have hveq : v = v ⟨0, by omega⟩ • uE + v ⟨1, by omega⟩ • uO := by
          ext i
          have hc := hconst i.val i.isLt
          simp only [Fin.eta] at hc
          rw [hc]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, uE, uO]
          by_cases hm : i.val % 2 = 0
          · have hm1 : i.val % 2 ≠ 1 := by omega
            simp [hm, hm1]
          · have hm1 : i.val % 2 = 1 := by omega
            simp [hm, hm1]
        rw [hveq]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      · rw [Submodule.span_le]
        rintro x (rfl | rfl)
        · exact huE
        · exact huO
    have hfin_ker : Module.finrank (ZMod 2) (LinearMap.ker (linT hq h)) = 2 := by
      have hcard_ker : Fintype.card (LinearMap.ker (linT hq h)) = 4 := by
        have hbij : LinearMap.ker (linT hq h) ≃ (ZMod 2 × ZMod 2) :=
          { toFun := fun v => (v.1 ⟨0, by omega⟩, v.1 ⟨1, by omega⟩)
            invFun := fun p => ⟨p.1 • uE + p.2 • uO, by
              rw [hker_eq]
              exact Submodule.add_mem _
                (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
                (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))⟩
            left_inv := fun v => by
              ext i
              have hv : v.1 ∈ Submodule.span (ZMod 2) {uE, uO} := hker_eq ▸ v.2
              rw [Submodule.mem_span_pair] at hv
              obtain ⟨α, β, hab⟩ := hv
              have hv0 : v.1 ⟨0, by omega⟩ = α := by rw [← hab]; simp [uE, uO]
              have hv1 : v.1 ⟨1, by omega⟩ = β := by rw [← hab]; simp [uE, uO]
              rw [← hab]
              simp [uE, uO, hv0, hv1]
            right_inv := fun p => by
              apply Prod.ext <;> simp [uE, uO] }
        rw [Fintype.card_congr hbij, Fintype.card_prod, ZMod.card]
      have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker (linT hq h))
      rw [ZMod.card, hcard_ker] at h1
      exact Nat.pow_right_injective (by omega : 1 < 2) (by simpa using h1.symm)
    let pairMap : (Fin q → ZMod 2) →ₗ[ZMod 2] (ZMod 2 × ZMod 2) := (sumOn Ev).prod (sumOn Od)
    have hsum_set : ∀ (S : Finset (Fin q)),
        (∀ i ∈ S, ⟨(i.val + 2) % q, Nat.mod_lt _ hq⟩ ∈ S) →
        ∀ v, sumOn S (linT hq h v) = 0 := by
      intro S hS v
      simp only [sumOn, LinearMap.coe_mk, AddHom.coe_mk, linT, Finset.sum_add_distrib, h]
      have h2val : (2 : Fin 3).val = 2 := rfl
      have h2nz : (2 : ℕ) ≠ 0 := by decide
      simp only [h2val, h2nz, ne_eq, not_false_eq_true, ↓reduceIte]
      have hinj : Set.InjOn (fun i : Fin q => (⟨(i.val + 2) % q, Nat.mod_lt _ hq⟩ : Fin q)) S := by
        intro x _ y _ hxy
        have hval := congrArg Fin.val hxy
        ext
        exact mod_cancel_right (c := 2 % q) x.isLt y.isLt (Nat.mod_lt _ hq) (by
          rw [Nat.add_mod_mod, Nat.add_mod_mod]; exact hval)
      have himg : S.image (fun i : Fin q => (⟨(i.val + 2) % q, Nat.mod_lt _ hq⟩ : Fin q)) = S := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx; rw [Finset.mem_image] at hx; obtain ⟨i, hi, rfl⟩ := hx; exact hS i hi
        · rw [Finset.card_image_of_injOn hinj]
      rw [← Finset.sum_image hinj, himg]
      have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
      exact h2 _
    have hrange_eq : LinearMap.range (linT hq h) = LinearMap.ker pairMap := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rintro _ ⟨v, rfl⟩
        simp only [LinearMap.mem_ker, pairMap, LinearMap.prod_apply]
        have hdiv : 2 ∣ q := Nat.dvd_of_mod_eq_zero hq_even
        apply Prod.ext
        · exact hsum_set Ev (fun i hi => by
            simp only [Ev, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            rw [Nat.mod_mod_of_dvd _ hdiv]; omega) v
        · exact hsum_set Od (fun i hi => by
            simp only [Od, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            rw [Nat.mod_mod_of_dvd _ hdiv]; omega) v
      · have hsurj : Function.Surjective pairMap := by
          rintro ⟨x, y⟩
          refine ⟨Pi.single ⟨0, by omega⟩ x + Pi.single ⟨1, by omega⟩ y, ?_⟩
          apply Prod.ext
          · simp [pairMap, sumOn, Ev, Finset.sum_add_distrib, Finset.sum_pi_single]
          · simp [pairMap, sumOn, Od, Finset.sum_add_distrib, Finset.sum_pi_single]
        have hr1 := LinearMap.finrank_range_add_finrank_ker (linT hq h)
        have hr2 := LinearMap.finrank_range_add_finrank_ker pairMap
        rw [hfin_ker, Module.finrank_fin_fun] at hr1
        rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_prod,
          Module.finrank_self, Module.finrank_fin_fun] at hr2
        omega
    refine ⟨h, c, hc_ok, ?_⟩
    intro y
    rw [hH y, hcard_eq, hfin_ker, show 2 ^ 2 = 4 by decide, hrange_eq, LinearMap.mem_ker,
      map_sub, sub_eq_zero]
    have hparE : (if (List.range q).foldl (fun acc j => xor acc (decide (j % 2 = 0) && y.val.testBit j)) false
        then (1 : ZMod 2) else 0) = sumOn Ev (toVec y) := by
      rw [par_eq_sum]
      simp only [sumOn, LinearMap.coe_mk, AddHom.coe_mk, Ev, Finset.sum_filter]
      apply Finset.sum_congr rfl; intro j _; by_cases hm : j.val % 2 = 0 <;> simp [hm]
    have hparO : (if (List.range q).foldl (fun acc j => xor acc (decide (j % 2 = 1) && y.val.testBit j)) false
        then (1 : ZMod 2) else 0) = sumOn Od (toVec y) := by
      rw [par_eq_sum]
      simp only [sumOn, LinearMap.coe_mk, AddHom.coe_mk, Od, Finset.sum_filter]
      apply Finset.sum_congr rfl; intro j _; by_cases hm : j.val % 2 = 1 <;> simp [hm]
    have hsumE : sumOn Ev (fun i => if c i then (1 : ZMod 2) else 0) = if a then 1 else 0 := by
      simp only [sumOn, LinearMap.coe_mk, AddHom.coe_mk, c]
      rw [Finset.sum_eq_single ⟨0, by omega⟩]
      · simp
      · intro j hj hne
        simp only [Ev, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have h0 : j.val ≠ 0 := fun h => hne (Fin.ext h)
        have h1 : j.val ≠ 1 := by omega
        simp [h0, h1]
      · intro hni; exfalso; apply hni; simp [Ev]
    have hsumO : sumOn Od (fun i => if c i then (1 : ZMod 2) else 0) = if b then 1 else 0 := by
      simp only [sumOn, LinearMap.coe_mk, AddHom.coe_mk, c]
      rw [Finset.sum_eq_single ⟨1, by omega⟩]
      · simp
      · intro j hj hne
        simp only [Od, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have h1 : j.val ≠ 1 := fun h => hne (Fin.ext h)
        have h0 : j.val ≠ 0 := by omega
        simp [h0, h1]
      · intro hni; exfalso; apply hni; simp [Od]
    have hiff : pairMap (toVec y) = pairMap (fun i => if c i then (1 : ZMod 2) else 0) ↔
        (List.range q).foldl (fun acc j => xor acc (decide (j % 2 = 0) && y.val.testBit j)) false = a ∧
        (List.range q).foldl (fun acc j => xor acc (decide (j % 2 = 1) && y.val.testBit j)) false = b := by
      rw [Prod.ext_iff]
      change sumOn Ev (toVec y) = sumOn Ev (fun i => if c i then (1 : ZMod 2) else 0) ∧
        sumOn Od (toVec y) = sumOn Od (fun i => if c i then (1 : ZMod 2) else 0) ↔ _
      rw [← hparE, ← hparO, hsumE, hsumO, zmod2_eq_ite_iff, zmod2_eq_ite_iff]
    simp [hiff]

end PEqualNP.Outside.L_lib_1011_aux

theorem PEqualNP.Outside.L_lib_1011 : ∀ (q : Nat), 0 < q → ∀ (aff : Bool),
  let W := Fin (2^q)
  let value := fun (h : Fin q → Fin 3) (c : Fin q → Bool) (x : W) (i : Fin q) =>
    xor (c i) (xor (x.val.testBit i.val)
      (decide ((h i).val ≠ 0) && x.val.testBit ((i.val+(h i).val)%q)))
  let allowed := fun (c : Fin q → Bool) => aff = true ∨ ∀ i, c i = false
  let side := fun (b : Bool) => aff = true ∨ b = false
  let par := fun (P : Nat → Bool) (y : W) =>
    (List.range q).foldl (fun b j => xor b (P j && y.val.testBit j)) false
  ∀ H : W → Nat,
    (∃ (h : Fin q → Fin 3) (c : Fin q → Bool), allowed c ∧ ∀ y : W,
      H y = Nat.card {x : W // ∀ i, value h c x i = y.val.testBit i.val}) ↔
    (∀ y, H y = 1) ∨
    (∃ (S : W) (b : Bool), S.val ≠ 0 ∧ side b ∧
      (∀ i : Fin q, S.val.testBit i.val = true ∨ S.val.testBit ((i.val+1)%q) = true) ∧
      ∀ y, H y = if par (fun j => S.val.testBit j) y = b then 2 else 0) ∨
    (q % 2 = 0 ∧ ∃ a b : Bool, side a ∧ side b ∧ ∀ y,
      H y = if par (fun j => decide (j % 2 = 0)) y = a ∧
        par (fun j => decide (j % 2 = 1)) y = b then 4 else 0) := by
  intro q hq aff W value allowed side par H
  constructor
  · rintro ⟨h, c, hc, hH⟩
    have hH' : H = fun y : W => Nat.card {x : W // ∀ i, value h c x i = y.val.testBit i.val} := funext hH
    rw [hH']
    exact PEqualNP.Outside.L_lib_1011_aux.forward_dir hq aff h c hc
  · intro hrhs
    exact PEqualNP.Outside.L_lib_1011_aux.backward_dir hq aff H hrhs

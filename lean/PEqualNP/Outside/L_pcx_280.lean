import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_280_aux

open scoped BigOperators

def bx (b : Bool) : ZMod 2 := if b then 1 else 0

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  revert x; decide

lemma zmod2_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  rcases zmod2_zero_or_one x with h | h
  · exact absurd h hx
  · exact h

lemma bx_xor (a b : Bool) : bx (a ^^ b) = bx a + bx b := by
  cases a <;> cases b <;> decide

lemma bx_not (a : Bool) : bx (!a) = bx a + 1 := by
  cases a <;> decide

lemma bx_decide_eq_one (x : ZMod 2) : bx (decide (x = 1)) = x := by
  revert x; decide

lemma bx_injective {a b : Bool} (h : bx a = bx b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

lemma odd_iff_zmod2_eq_one (k : ℕ) : Odd k ↔ (k : ZMod 2) = 1 := by
  rw [Nat.odd_iff]
  have h2z : ((2 : ℕ) : ZMod 2) = 0 := by decide
  have h1 : (k : ZMod 2) = ((k % 2 : ℕ) : ZMod 2) := by
    have hdiv := Nat.div_add_mod k 2
    have h2 := congrArg (fun n : ℕ => (n : ZMod 2)) hdiv
    rw [Nat.cast_add, Nat.cast_mul, h2z, zero_mul, zero_add] at h2
    exact h2.symm
  rw [h1]
  have hlt : k % 2 < 2 := Nat.mod_lt k (by omega)
  interval_cases (k % 2) <;> decide

lemma even_iff_zmod2_eq_zero (k : ℕ) : Even k ↔ (k : ZMod 2) = 0 := by
  rw [Nat.even_iff]
  have h2z : ((2 : ℕ) : ZMod 2) = 0 := by decide
  have h1 : (k : ZMod 2) = ((k % 2 : ℕ) : ZMod 2) := by
    have hdiv := Nat.div_add_mod k 2
    have h2 := congrArg (fun n : ℕ => (n : ZMod 2)) hdiv
    rw [Nat.cast_add, Nat.cast_mul, h2z, zero_mul, zero_add] at h2
    exact h2.symm
  rw [h1]
  have hlt : k % 2 < 2 := Nat.mod_lt k (by omega)
  interval_cases (k % 2) <;> decide

lemma fredholm_zmod2 {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J (ZMod 2)) (rhs : I → ZMod 2)
    (horth : ∀ c : I → ZMod 2, M.transpose.mulVec c = 0 → dotProduct c rhs = 0) :
    ∃ x : J → ZMod 2, M.mulVec x = rhs := by
  classical
  let orth : Submodule (ZMod 2) (I → ZMod 2) :=
    { carrier := {y : I → ZMod 2 | ∀ c ∈ LinearMap.ker M.transpose.mulVecLin, dotProduct c y = 0}
      zero_mem' := fun c _ => dotProduct_zero c, add_mem' := fun {u v} hu hv c hc => by
        rw [dotProduct_add, hu c hc, hv c hc, add_zero]
      smul_mem' := fun a {u} hu c hc => by
        rw [dotProduct_smul, hu c hc, smul_zero] }
  have hle : LinearMap.range M.mulVecLin ≤ orth := by
    rintro y ⟨x, rfl⟩ c hc
    have hMt : M.transpose.mulVec c = 0 := hc
    have hdot : dotProduct c (M.mulVec x) = dotProduct (M.transpose.mulVec c) x := by
      simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    change dotProduct c (M.mulVec x) = 0
    rw [hdot, hMt, zero_dotProduct]
  have horth_dim : Module.finrank (ZMod 2) orth =
      Fintype.card I - Module.finrank (ZMod 2) (LinearMap.ker M.transpose.mulVecLin) := by
    let b := Module.finBasis (ZMod 2) (LinearMap.ker M.transpose.mulVecLin)
    let evalK : (I → ZMod 2) →ₗ[ZMod 2]
        (Fin (Module.finrank (ZMod 2) (LinearMap.ker M.transpose.mulVecLin)) → ZMod 2) :=
      { toFun := fun v j => dotProduct (b j).1 v
        map_add' := fun u v => by ext j; simp [dotProduct_add]
        map_smul' := fun a v => by ext j; simp [dotProduct_smul] }
    have hker_eq : LinearMap.ker evalK = orth := by
      ext v
      constructor
      · intro hv c hc
        have hc_eq : (⟨c, hc⟩ : LinearMap.ker M.transpose.mulVecLin) =
            ∑ j, b.repr ⟨c, hc⟩ j • b j := (b.sum_repr ⟨c, hc⟩).symm
        have hval : c = ∑ j, b.repr ⟨c, hc⟩ j • (b j).1 := by
          have h1 := congrArg Subtype.val hc_eq
          simp only [Submodule.coe_sum, SetLike.val_smul] at h1
          exact h1
        rw [hval, sum_dotProduct]
        refine Finset.sum_eq_zero fun j _ => ?_
        have hvj : dotProduct (b j).1 v = 0 := congrFun hv j
        rw [smul_dotProduct, smul_eq_mul, hvj, mul_zero]
      · intro hv; ext j; exact hv (b j).1 (b j).2
    have hsurj : Module.finrank (ZMod 2) (LinearMap.range evalK) =
        Module.finrank (ZMod 2) (LinearMap.ker M.transpose.mulVecLin) := by
      let B : Matrix I (Fin (Module.finrank (ZMod 2) (LinearMap.ker M.transpose.mulVecLin))) (ZMod 2) :=
        Matrix.of fun i j => (b j).1 i
      have hB_inj : Function.Injective B.mulVecLin := by
        rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
        intro c hc
        have hc' : (∑ j, c j • (b j).1) = 0 := by
          ext i
          have hi := congrFun hc i
          simp only [B, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
            Pi.zero_apply] at hi
          simpa [Finset.sum_apply, mul_comm] using hi
        have hcK : (∑ j, c j • b j) = 0 := by apply Subtype.ext; simpa using hc'
        exact funext (Fintype.linearIndependent_iff.mp b.linearIndependent c hcK)
      have hB_rank : B.rank = Module.finrank (ZMod 2) (LinearMap.ker M.transpose.mulVecLin) := by
        have hr := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
        rw [LinearMap.ker_eq_bot.mpr hB_inj] at hr
        simp at hr
        exact hr
      have hBt : B.transpose.mulVecLin = evalK := by
        apply LinearMap.ext; intro v; ext j
        simp [B, evalK, Matrix.mulVec, dotProduct]
      rw [← hBt]
      change B.transpose.rank = Module.finrank (ZMod 2) (LinearMap.ker M.transpose.mulVecLin)
      rw [Matrix.rank_transpose, hB_rank]
    have hr := LinearMap.finrank_range_add_finrank_ker evalK
    rw [hsurj, hker_eq] at hr
    have hd : Module.finrank (ZMod 2) (I → ZMod 2) = Fintype.card I := by simp
    rw [hd] at hr
    omega
  have hrMt := LinearMap.finrank_range_add_finrank_ker M.transpose.mulVecLin
  have hd : Module.finrank (ZMod 2) (I → ZMod 2) = Fintype.card I := by simp
  rw [hd] at hrMt
  have hrank_eq : Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) =
      Module.finrank (ZMod 2) (LinearMap.range M.transpose.mulVecLin) := by
    change M.rank = M.transpose.rank
    exact (Matrix.rank_transpose M).symm
  have heq : LinearMap.range M.mulVecLin = orth := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    omega
  have hrhs : rhs ∈ LinearMap.range M.mulVecLin := by
    rw [heq]
    intro c hc
    exact horth c hc
  rcases hrhs with ⟨x, hx⟩
  exact ⟨x, hx⟩

def ind {m : ℕ} (D : Finset (Fin m)) : Fin m → ZMod 2 :=
  fun i => if i ∈ D then 1 else 0

def supp {m : ℕ} (c : Fin m → ZMod 2) : Finset (Fin m) :=
  Finset.univ.filter (fun i => c i = 1)

lemma ind_supp {m : ℕ} (c : Fin m → ZMod 2) : ind (supp c) = c := by
  ext i
  simp only [ind, supp, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases zmod2_zero_or_one (c i) with h | h
  · simp [h]
  · simp [h]

lemma supp_ind {m : ℕ} (D : Finset (Fin m)) : supp (ind D) = D := by
  ext i
  simp only [supp, ind]
  by_cases h : i ∈ D <;> simp [h]

def xorSet {m : ℕ} (D E : Finset (Fin m)) : Finset (Fin m) :=
  supp (ind D + ind E)

lemma ind_xorSet {m : ℕ} (D E : Finset (Fin m)) : ind (xorSet D E) = ind D + ind E :=
  ind_supp (ind D + ind E)

lemma xorSet_cancel_right {m : ℕ} (D E : Finset (Fin m)) : xorSet (xorSet D E) E = D := by
  unfold xorSet
  rw [ind_supp, add_assoc]
  have h0 : ind E + ind E = 0 := by ext i; exact zmod2_add_self (ind E i)
  rw [h0, add_zero, supp_ind]

def incMat {n m : ℕ} (left right : Fin m → Fin n) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  Matrix.of fun i v => (if left i = v then (1 : ZMod 2) else 0) + (if right i = v then 1 else 0)

lemma incMat_mulVec {n m : ℕ} (left right : Fin m → Fin n) (x : Fin n → ZMod 2) (i : Fin m) :
    (incMat left right).mulVec x i = x (left i) + x (right i) := by
  simp only [incMat, Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib]
  have h1 : (∑ v : Fin n, (if left i = v then (1 : ZMod 2) else 0) * x v) = x (left i) := by
    rw [Finset.sum_eq_single (left i)]
    · simp
    · intro v _ hne; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h2 : (∑ v : Fin n, (if right i = v then (1 : ZMod 2) else 0) * x v) = x (right i) := by
    rw [Finset.sum_eq_single (right i)]
    · simp
    · intro v _ hne; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1, h2]

lemma dotProduct_incMat_mulVec {n m : ℕ} (left right : Fin m → Fin n)
    (c : Fin m → ZMod 2) (x : Fin n → ZMod 2)
    (hc : (incMat left right).transpose.mulVec c = 0) :
    dotProduct c ((incMat left right).mulVec x) = 0 := by
  have hdot : dotProduct c ((incMat left right).mulVec x) =
      dotProduct ((incMat left right).transpose.mulVec c) x := by
    simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  rw [hdot, hc, zero_dotProduct]

lemma incMat_transpose_ind_iff {n m : ℕ} (left right : Fin m → Fin n) (D : Finset (Fin m)) :
    (incMat left right).transpose.mulVec (ind D) = 0 ↔
      ∀ v : Fin n, Even ((D.filter (fun tail => left tail = v)).card +
        (D.filter (fun head => right head = v)).card) := by
  constructor
  · intro hker v
    rw [even_iff_zmod2_eq_zero, Nat.cast_add]
    have hv := congrFun hker v
    simp only [incMat, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply,
      Pi.zero_apply, ind, add_mul, Finset.sum_add_distrib] at hv
    have hL : ((D.filter (fun tail => left tail = v)).card : ZMod 2) =
        ∑ i : Fin m, (if left i = v then (1 : ZMod 2) else 0) * (if i ∈ D then 1 else 0) := by
      rw [Finset.card_filter, Nat.cast_sum]
      calc
        (∑ i ∈ D, ((if left i = v then 1 else 0 : ℕ) : ZMod 2))
            = ∑ i : Fin m, if i ∈ D then ((if left i = v then 1 else 0 : ℕ) : ZMod 2) else 0 := by
          rw [← Finset.sum_filter]
          have hf : Finset.univ.filter (fun i : Fin m => i ∈ D) = D := by ext i; simp
          rw [hf]
        _ = ∑ i : Fin m, (if left i = v then (1 : ZMod 2) else 0) * (if i ∈ D then 1 else 0) := by
          refine Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
    have hR : ((D.filter (fun head => right head = v)).card : ZMod 2) =
        ∑ i : Fin m, (if right i = v then (1 : ZMod 2) else 0) * (if i ∈ D then 1 else 0) := by
      rw [Finset.card_filter, Nat.cast_sum]
      calc
        (∑ i ∈ D, ((if right i = v then 1 else 0 : ℕ) : ZMod 2))
            = ∑ i : Fin m, if i ∈ D then ((if right i = v then 1 else 0 : ℕ) : ZMod 2) else 0 := by
          rw [← Finset.sum_filter]
          have hf : Finset.univ.filter (fun i : Fin m => i ∈ D) = D := by ext i; simp
          rw [hf]
        _ = ∑ i : Fin m, (if right i = v then (1 : ZMod 2) else 0) * (if i ∈ D then 1 else 0) := by
          refine Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
    rw [hL, hR]
    exact hv
  · intro heven
    ext v
    have hv := (even_iff_zmod2_eq_zero _).mp (heven v)
    rw [Nat.cast_add] at hv
    simp only [incMat, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply,
      Pi.zero_apply, ind, add_mul, Finset.sum_add_distrib]
    have hL : ((D.filter (fun tail => left tail = v)).card : ZMod 2) =
        ∑ i : Fin m, (if left i = v then (1 : ZMod 2) else 0) * (if i ∈ D then 1 else 0) := by
      rw [Finset.card_filter, Nat.cast_sum]
      calc
        (∑ i ∈ D, ((if left i = v then 1 else 0 : ℕ) : ZMod 2))
            = ∑ i : Fin m, if i ∈ D then ((if left i = v then 1 else 0 : ℕ) : ZMod 2) else 0 := by
          rw [← Finset.sum_filter]
          have hf : Finset.univ.filter (fun i : Fin m => i ∈ D) = D := by ext i; simp
          rw [hf]
        _ = ∑ i : Fin m, (if left i = v then (1 : ZMod 2) else 0) * (if i ∈ D then 1 else 0) := by
          refine Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
    have hR : ((D.filter (fun head => right head = v)).card : ZMod 2) =
        ∑ i : Fin m, (if right i = v then (1 : ZMod 2) else 0) * (if i ∈ D then 1 else 0) := by
      rw [Finset.card_filter, Nat.cast_sum]
      calc
        (∑ i ∈ D, ((if right i = v then 1 else 0 : ℕ) : ZMod 2))
            = ∑ i : Fin m, if i ∈ D then ((if right i = v then 1 else 0 : ℕ) : ZMod 2) else 0 := by
          rw [← Finset.sum_filter]
          have hf : Finset.univ.filter (fun i : Fin m => i ∈ D) = D := by ext i; simp
          rw [hf]
        _ = ∑ i : Fin m, (if right i = v then (1 : ZMod 2) else 0) * (if i ∈ D then 1 else 0) := by
          refine Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
    rw [← hL, ← hR]
    exact hv

lemma dotProduct_ind_sign_iff {m : ℕ} (sign : Fin m → Bool) (D : Finset (Fin m)) :
    dotProduct (ind D) (fun i => bx (sign i)) = 1 ↔
      Odd ((D.filter (fun edge => sign edge = true)).card) := by
  rw [odd_iff_zmod2_eq_one]
  have hEq : dotProduct (ind D) (fun i => bx (sign i)) =
      ((D.filter (fun edge => sign edge = true)).card : ZMod 2) := by
    rw [Finset.card_filter, Nat.cast_sum]
    simp only [dotProduct, ind]
    calc
      (∑ i : Fin m, (if i ∈ D then (1 : ZMod 2) else 0) * bx (sign i))
          = ∑ i : Fin m, if i ∈ D then ((if sign i = true then 1 else 0 : ℕ) : ZMod 2) else 0 := by
        refine Finset.sum_congr rfl fun i _ => by
          by_cases hD : i ∈ D <;> cases sign i <;> simp [hD, bx]
      _ = ∑ i ∈ D, ((if sign i = true then 1 else 0 : ℕ) : ZMod 2) := by
        rw [← Finset.sum_filter]
        have hf : Finset.univ.filter (fun i : Fin m => i ∈ D) = D := by ext i; simp
        rw [hf]
  rw [hEq]

abbrev oddSetPred {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (D : Finset (Fin m)) : Prop :=
  Odd ((D.filter (fun edge => sign edge = true)).card) ∧
  ∀ v : Fin n, Even ((D.filter (fun tail => left tail = v)).card +
    (D.filter (fun head => right head = v)).card)

lemma oddSetPred_iff {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (D : Finset (Fin m)) :
    oddSetPred left right sign D ↔
      (incMat left right).transpose.mulVec (ind D) = 0 ∧
      dotProduct (ind D) (fun i => bx (sign i)) = 1 := by
  unfold oddSetPred
  rw [← incMat_transpose_ind_iff, ← dotProduct_ind_sign_iff, and_comm]

abbrev faultsOf {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (x : Fin n → Bool) : Finset (Fin m) :=
  Finset.univ.filter (fun idx => x (right idx) ≠ (x (left idx) ^^ sign idx))

abbrev missedOf {n m : ℕ} (left right : Fin m → Fin n) (sign start : Fin m → Bool)
    (y : Fin n → Bool) : Finset (Fin m) :=
  (faultsOf left right sign y).filter (fun idx => y (left idx) = start idx)

lemma ind_faultsOf {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (x : Fin n → Bool) :
    ind (faultsOf left right sign x) =
      (incMat left right).mulVec (fun v => bx (x v)) + (fun i => bx (sign i)) := by
  ext i
  rw [Pi.add_apply, incMat_mulVec]
  simp only [ind, faultsOf, Finset.mem_filter, Finset.mem_univ, true_and]
  cases h1 : x (right i) <;> cases h2 : x (left i) <;> cases h3 : sign i <;> decide

lemma faultsOf_not {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (x : Fin n → Bool) :
    faultsOf left right sign (fun v => !(x v)) = faultsOf left right sign x := by
  ext i
  simp only [faultsOf, Finset.mem_filter, Finset.mem_univ, true_and]
  cases x (right i) <;> cases x (left i) <;> cases sign i <;> decide

lemma missedOf_disjoint_not {n m : ℕ} (left right : Fin m → Fin n) (sign start : Fin m → Bool)
    (x : Fin n → Bool) :
    Disjoint (missedOf left right sign start x)
      (missedOf left right sign start (fun v => !(x v))) := by
  rw [Finset.disjoint_left]
  intro i h1 h2
  have hx1 : x (left i) = start i := (Finset.mem_filter.mp h1).2
  have hx2 : (!(x (left i))) = start i := (Finset.mem_filter.mp h2).2
  rw [hx1] at hx2
  cases hs : start i <;> rw [hs] at hx2 <;> exact absurd hx2 (by decide)

lemma missedOf_union_not {n m : ℕ} (left right : Fin m → Fin n) (sign start : Fin m → Bool)
    (x : Fin n → Bool) :
    missedOf left right sign start x ∪ missedOf left right sign start (fun v => !(x v)) =
      faultsOf left right sign x := by
  ext i
  simp only [Finset.mem_union, missedOf, Finset.mem_filter, faultsOf_not]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    by_cases hls : x (left i) = start i
    · exact Or.inl ⟨h, hls⟩
    · refine Or.inr ⟨h, ?_⟩
      revert hls
      cases x (left i) <;> cases start i <;> decide

lemma exists_faults_iff {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (S : Finset (Fin m)) :
    (∃ word : Fin n → Bool, faultsOf left right sign word = S) ↔
      ∀ c : Fin m → ZMod 2, (incMat left right).transpose.mulVec c = 0 →
        dotProduct c (ind S) = dotProduct c (fun i => bx (sign i)) := by
  constructor
  · rintro ⟨word, rfl⟩ c hc
    rw [ind_faultsOf, dotProduct_add, dotProduct_incMat_mulVec left right c _ hc, zero_add]
  · intro horth
    have hfred := fredholm_zmod2 (incMat left right) (ind S + fun i => bx (sign i)) (fun c hc => by
      rw [dotProduct_add, horth c hc, zmod2_add_self])
    rcases hfred with ⟨x, hx⟩
    refine ⟨fun v => decide (x v = 1), ?_⟩
    rw [← supp_ind (faultsOf left right sign _), ← supp_ind S]
    congr 1
    rw [ind_faultsOf]
    have hbx : (fun v => bx (decide (x v = 1))) = x := funext fun v => bx_decide_eq_one (x v)
    rw [hbx, hx, add_assoc]
    have h0 : (fun i => bx (sign i)) + (fun i => bx (sign i)) = 0 := by
      ext i; exact zmod2_add_self _
    rw [h0, add_zero]

lemma two_le_card_faults {n m : ℕ} (left right : Fin m → Fin n) (sign start : Fin m → Bool)
    (hmiss : ∀ x, (missedOf left right sign start x).Nonempty)
    (x : Fin n → Bool) :
    2 ≤ (faultsOf left right sign x).card := by
  have hcard : (faultsOf left right sign x).card =
      (missedOf left right sign start x).card +
      (missedOf left right sign start (fun v => !(x v))).card := by
    rw [← Finset.card_union_of_disjoint (missedOf_disjoint_not left right sign start x),
      missedOf_union_not]
  have h1 : 1 ≤ (missedOf left right sign start x).card := Finset.card_pos.mpr (hmiss x)
  have h2 : 1 ≤ (missedOf left right sign start (fun v => !(x v))).card :=
    Finset.card_pos.mpr (hmiss (fun v => !(x v)))
  omega

lemma W_nonempty {n m : ℕ} (left right : Fin m → Fin n) (sign start : Fin m → Bool)
    (hmiss : ∀ x, (missedOf left right sign start x).Nonempty) :
    (Finset.univ.filter (oddSetPred left right sign)).Nonempty := by
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  have hall0 : ∀ c : Fin m → ZMod 2, (incMat left right).transpose.mulVec c = 0 →
      dotProduct c (ind (∅ : Finset (Fin m))) = dotProduct c (fun i => bx (sign i)) := by
    intro c hc
    have hind0 : ind (∅ : Finset (Fin m)) = 0 := by ext i; simp [ind]
    rw [hind0, dotProduct_zero]
    rcases zmod2_zero_or_one (dotProduct c (fun i => bx (sign i))) with h0 | h1
    · exact h0.symm
    · exfalso
      have hmem : supp c ∈ Finset.univ.filter (oddSetPred left right sign) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, (oddSetPred_iff left right sign (supp c)).mpr ?_⟩
        rw [ind_supp]
        exact ⟨hc, h1⟩
      rw [hemp] at hmem
      exact Finset.notMem_empty _ hmem
  rcases (exists_faults_iff left right sign ∅).mpr hall0 with ⟨w, hw⟩
  have h2 := two_le_card_faults left right sign start hmiss w
  rw [hw, Finset.card_empty] at h2
  omega

lemma exists_not_mem_W {n m : ℕ} (left right : Fin m → Fin n) (sign start : Fin m → Bool)
    (hmiss : ∀ x, (missedOf left right sign start x).Nonempty)
    (i : Fin m) :
    ∃ D ∈ Finset.univ.filter (oddSetPred left right sign), i ∉ D := by
  by_contra hall
  push Not at hall
  rcases W_nonempty left right sign start hmiss with ⟨D0, hD0⟩
  have hD0' := (oddSetPred_iff left right sign D0).mp (Finset.mem_filter.mp hD0).2
  have hiD0 : i ∈ D0 := hall D0 hD0
  have horth : ∀ c : Fin m → ZMod 2, (incMat left right).transpose.mulVec c = 0 →
      dotProduct c (ind ({i} : Finset (Fin m))) = dotProduct c (fun j => bx (sign j)) := by
    intro c hc
    have hdot_i : dotProduct c (ind ({i} : Finset (Fin m))) = c i := by
      simp only [dotProduct, ind, Finset.mem_singleton]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hdot_i]
    rcases zmod2_zero_or_one (dotProduct c (fun j => bx (sign j))) with h0 | h1
    · rw [h0]
      let D1 := supp (ind D0 + c)
      have hD1 : D1 ∈ Finset.univ.filter (oddSetPred left right sign) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, (oddSetPred_iff left right sign D1).mpr ?_⟩
        rw [ind_supp]
        refine ⟨?_, ?_⟩
        · rw [Matrix.mulVec_add, hD0'.1, hc, add_zero]
        · rw [add_dotProduct, hD0'.2, h0, add_zero]
      have hiD1 : i ∈ D1 := hall D1 hD1
      have hval : (ind D0 + c) i = 1 := (Finset.mem_filter.mp hiD1).2
      have hD0i : ind D0 i = 1 := by simp [ind, hiD0]
      rw [Pi.add_apply, hD0i] at hval
      rcases zmod2_zero_or_one (c i) with hc0 | hc1
      · exact hc0
      · rw [hc1] at hval; exact absurd hval (by decide)
    · rw [h1]
      have hmem : supp c ∈ Finset.univ.filter (oddSetPred left right sign) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, (oddSetPred_iff left right sign (supp c)).mpr ?_⟩
        rw [ind_supp]
        exact ⟨hc, h1⟩
      have hiC : i ∈ supp c := hall (supp c) hmem
      exact (Finset.mem_filter.mp hiC).2
  rcases (exists_faults_iff left right sign {i}).mpr horth with ⟨w, hw⟩
  have h2 := two_le_card_faults left right sign start hmiss w
  rw [hw, Finset.card_singleton] at h2
  omega

lemma pair_witness_iff {n m : ℕ} (left right : Fin m → Fin n) (sign start : Fin m → Bool)
    (hmiss : ∀ x, (missedOf left right sign start x).Nonempty)
    {i j : Fin m} (hij : i ≠ j) :
    (∃ word : Fin n → Bool, faultsOf left right sign word = {i, j} ∧
      missedOf left right sign start word = {i} ∧
      missedOf left right sign start (fun v => !(word v)) = {j}) ↔
    (∀ D ∈ Finset.univ.filter (oddSetPred left right sign), i ∈ D ↔ j ∉ D) := by
  let W := Finset.univ.filter (oddSetPred left right sign)
  constructor
  · rintro ⟨word, hfw, _, _⟩ D hD
    have hD' := (oddSetPred_iff left right sign D).mp (Finset.mem_filter.mp hD).2
    have horth := (exists_faults_iff left right sign {i, j}).mp ⟨word, hfw⟩ (ind D) hD'.1
    rw [hD'.2] at horth
    have hsum : dotProduct (ind D) (ind ({i, j} : Finset (Fin m))) = ind D i + ind D j := by
      simp only [dotProduct, ind, Finset.mem_insert, Finset.mem_singleton]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin m => k = i ∨ k = j)]
      have h0 : (∑ k ∈ Finset.univ.filter (fun k : Fin m => ¬ (k = i ∨ k = j)),
          (if k ∈ D then (1 : ZMod 2) else 0) * (if k = i ∨ k = j then 1 else 0)) = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hnot := (Finset.mem_filter.mp hk).2
        simp [hnot]
      rw [h0, add_zero]
      have hf : Finset.univ.filter (fun k : Fin m => k = i ∨ k = j) = {i, j} := by
        ext k; simp
      rw [hf, Finset.sum_pair hij]
      simp
    rw [hsum] at horth
    by_cases hi : i ∈ D <;> by_cases hj : j ∈ D
    · simp [ind, hi, hj] at horth
    · simp [hi, hj]
    · simp [hi, hj]
    · simp [ind, hi, hj] at horth
  · intro hcomp
    rcases W_nonempty left right sign start hmiss with ⟨D0, hD0⟩
    have hD0' := (oddSetPred_iff left right sign D0).mp (Finset.mem_filter.mp hD0).2
    have hD0_sum : ind D0 i + ind D0 j = 1 := by
      have hc := hcomp D0 hD0
      by_cases hi : i ∈ D0
      · have hj : j ∉ D0 := hc.mp hi
        simp [ind, hi, hj]
      · have hj : j ∈ D0 := by by_contra h; exact hi (hc.mpr h)
        simp [ind, hi, hj]
    have horth : ∀ c : Fin m → ZMod 2, (incMat left right).transpose.mulVec c = 0 →
        dotProduct c (ind ({i, j} : Finset (Fin m))) = dotProduct c (fun k => bx (sign k)) := by
      intro c hc
      have hsum : dotProduct c (ind ({i, j} : Finset (Fin m))) = c i + c j := by
        simp only [dotProduct, ind, Finset.mem_insert, Finset.mem_singleton]
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin m => k = i ∨ k = j)]
        have h0 : (∑ k ∈ Finset.univ.filter (fun k : Fin m => ¬ (k = i ∨ k = j)),
            c k * (if k = i ∨ k = j then (1 : ZMod 2) else 0)) = 0 := by
          refine Finset.sum_eq_zero fun k hk => ?_
          have hnot := (Finset.mem_filter.mp hk).2
          simp [hnot]
        rw [h0, add_zero]
        have hf : Finset.univ.filter (fun k : Fin m => k = i ∨ k = j) = {i, j} := by
          ext k; simp
        rw [hf, Finset.sum_pair hij]
        simp
      rw [hsum]
      rcases zmod2_zero_or_one (dotProduct c (fun k => bx (sign k))) with h0 | h1
      · rw [h0]
        let D1 := supp (ind D0 + c)
        have hD1 : D1 ∈ W := by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, (oddSetPred_iff left right sign D1).mpr ?_⟩
          rw [ind_supp]
          refine ⟨?_, ?_⟩
          · rw [Matrix.mulVec_add, hD0'.1, hc, add_zero]
          · rw [add_dotProduct, hD0'.2, h0, add_zero]
        have hD1_sum : ind D1 i + ind D1 j = 1 := by
          have hcc := hcomp D1 hD1
          by_cases hi : i ∈ D1
          · have hj : j ∉ D1 := hcc.mp hi
            simp [ind, hi, hj]
          · have hj : j ∈ D1 := by by_contra h; exact hi (hcc.mpr h)
            simp [ind, hi, hj]
        rw [ind_supp, Pi.add_apply, Pi.add_apply] at hD1_sum
        have hcalc : (ind D0 i + ind D0 j) + (c i + c j) = 1 := by
          calc
            (ind D0 i + ind D0 j) + (c i + c j) = (ind D0 i + c i) + (ind D0 j + c j) := by ring
            _ = 1 := hD1_sum
        rw [hD0_sum] at hcalc
        rcases zmod2_zero_or_one (c i + c j) with hz | ho
        · exact hz
        · rw [ho] at hcalc; exact absurd hcalc (by decide)
      · rw [h1]
        have hmem : supp c ∈ W := by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, (oddSetPred_iff left right sign (supp c)).mpr ?_⟩
          rw [ind_supp]
          exact ⟨hc, h1⟩
        have hcc := hcomp (supp c) hmem
        by_cases hi : i ∈ supp c
        · have hj : j ∉ supp c := hcc.mp hi
          have hci : c i = 1 := (Finset.mem_filter.mp hi).2
          have hcj : c j = 0 := by
            rcases zmod2_zero_or_one (c j) with hz | ho
            · exact hz
            · exact absurd (show j ∈ supp c from Finset.mem_filter.mpr ⟨Finset.mem_univ j, ho⟩) hj
          rw [hci, hcj, add_zero]
        · have hj : j ∈ supp c := by by_contra h; exact hi (hcc.mpr h)
          have hcj : c j = 1 := (Finset.mem_filter.mp hj).2
          have hci : c i = 0 := by
            rcases zmod2_zero_or_one (c i) with hz | ho
            · exact hz
            · exact absurd (show i ∈ supp c from Finset.mem_filter.mpr ⟨Finset.mem_univ i, ho⟩) hi
          rw [hci, hcj, zero_add]
    rcases (exists_faults_iff left right sign {i, j}).mpr horth with ⟨w, hw⟩
    have hunion := missedOf_union_not left right sign start w
    have hdisj := missedOf_disjoint_not left right sign start w
    rw [hw] at hunion
    have hne1 := hmiss w
    have hne2 := hmiss (fun v => !(w v))
    have hcard_sum : (missedOf left right sign start w).card +
        (missedOf left right sign start (fun v => !(w v))).card = 2 := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_pair hij]
    have hc1 : (missedOf left right sign start w).card = 1 := by
      have := Finset.card_pos.mpr hne1
      have := Finset.card_pos.mpr hne2
      omega
    have hc2 : (missedOf left right sign start (fun v => !(w v))).card = 1 := by omega
    rcases Finset.card_eq_one.mp hc1 with ⟨a, ha⟩
    rcases Finset.card_eq_one.mp hc2 with ⟨b, hb⟩
    rw [ha, hb] at hunion hdisj
    have hab : a ≠ b := by
      intro heq; subst heq
      exact Finset.disjoint_left.mp hdisj (Finset.mem_singleton_self a) (Finset.mem_singleton_self a)
    have ha_mem : a ∈ ({i, j} : Finset (Fin m)) := by
      rw [← hunion]; exact Finset.mem_union_left _ (Finset.mem_singleton_self a)
    have hb_mem : b ∈ ({i, j} : Finset (Fin m)) := by
      rw [← hunion]; exact Finset.mem_union_right _ (Finset.mem_singleton_self b)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem hb_mem
    rcases ha_mem with rfl | rfl
    · rcases hb_mem with rfl | rfl
      · exact absurd rfl hab
      · exact ⟨w, hw, ha, hb⟩
    · rcases hb_mem with rfl | rfl
      · refine ⟨fun v => !(w v), ?_, hb, ?_⟩
        · rw [faultsOf_not]; exact hw
        · have hnotnot : (fun site => !(!(w site))) = w := funext fun v => Bool.not_not (w v)
          rw [hnotnot]; exact ha
      · exact absurd rfl hab

lemma W_half_linear {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (φ : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (h0 : ∃ D0 ∈ Finset.univ.filter (oddSetPred left right sign), φ (ind D0) = 0)
    (h1 : ∃ D1 ∈ Finset.univ.filter (oddSetPred left right sign), φ (ind D1) = 1) :
    let W := Finset.univ.filter (oddSetPred left right sign)
    2 * (W.filter (fun D => φ (ind D) = 1)).card = W.card := by
  intro W
  rcases h0 with ⟨D0, hD0, hφ0⟩
  rcases h1 with ⟨D1, hD1, hφ1⟩
  have hD0' := (oddSetPred_iff left right sign D0).mp (Finset.mem_filter.mp hD0).2
  have hD1' := (oddSetPred_iff left right sign D1).mp (Finset.mem_filter.mp hD1).2
  let E := xorSet D0 D1
  have hEker : (incMat left right).transpose.mulVec (ind E) = 0 := by
    rw [ind_xorSet, Matrix.mulVec_add, hD0'.1, hD1'.1, add_zero]
  have hEsign : dotProduct (ind E) (fun i => bx (sign i)) = 0 := by
    rw [ind_xorSet, add_dotProduct, hD0'.2, hD1'.2, zmod2_add_self]
  have hEφ : φ (ind E) = 1 := by
    rw [ind_xorSet, map_add, hφ0, hφ1, zero_add]
  have hbij : (W.filter (fun D => φ (ind D) = 1)).card =
      (W.filter (fun D => ¬ φ (ind D) = 1)).card := by
    refine Finset.card_bij (fun D _ => xorSet D E) ?_ ?_ ?_
    · intro D hD
      have hDW : D ∈ W := (Finset.mem_filter.mp hD).1
      have hDφ : φ (ind D) = 1 := (Finset.mem_filter.mp hD).2
      have hD' := (oddSetPred_iff left right sign D).mp (Finset.mem_filter.mp hDW).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (oddSetPred_iff left right sign _).mpr ?_⟩, ?_⟩
      · rw [ind_xorSet, Matrix.mulVec_add, hD'.1, hEker, add_zero, add_dotProduct, hD'.2, hEsign, add_zero]
        exact ⟨rfl, rfl⟩
      · rw [ind_xorSet, map_add, hDφ, hEφ, zmod2_add_self]
        decide
    · intro D _ D' _ heq
      have h := congrArg (fun X => xorSet X E) heq
      rw [xorSet_cancel_right, xorSet_cancel_right] at h
      exact h
    · intro D hD
      have hDW : D ∈ W := (Finset.mem_filter.mp hD).1
      have hDφne : φ (ind D) ≠ 1 := (Finset.mem_filter.mp hD).2
      have hDφ0 : φ (ind D) = 0 := by
        rcases zmod2_zero_or_one (φ (ind D)) with hz | ho
        · exact hz
        · exact absurd ho hDφne
      have hD' := (oddSetPred_iff left right sign D).mp (Finset.mem_filter.mp hDW).2
      refine ⟨xorSet D E, ?_, xorSet_cancel_right D E⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (oddSetPred_iff left right sign _).mpr ?_⟩, ?_⟩
      · rw [ind_xorSet, Matrix.mulVec_add, hD'.1, hEker, add_zero, add_dotProduct, hD'.2, hEsign, add_zero]
        exact ⟨rfl, rfl⟩
      · rw [ind_xorSet, map_add, hDφ0, hEφ, zero_add]
  have htot := Finset.card_filter_add_card_filter_not (s := W) (p := fun D => φ (ind D) = 1)
  omega

lemma W_half_coord {n m : ℕ} (left right : Fin m → Fin n) (sign start : Fin m → Bool)
    (hmiss : ∀ x, (missedOf left right sign start x).Nonempty)
    {i : Fin m} (hiU : i ∈ (Finset.univ.filter (oddSetPred left right sign)).biUnion id) :
    let W := Finset.univ.filter (oddSetPred left right sign)
    2 * (W.filter (fun D => i ∈ D)).card = W.card := by
  intro W
  rcases Finset.mem_biUnion.mp hiU with ⟨D1, hD1, hiD1⟩
  dsimp only [id] at hiD1
  rcases exists_not_mem_W left right sign start hmiss i with ⟨D0, hD0, hiD0⟩
  let φ : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 := LinearMap.proj i
  have h := W_half_linear left right sign φ
    ⟨D0, hD0, by simp [φ, ind, hiD0]⟩
    ⟨D1, hD1, by simp [φ, ind, hiD1]⟩
  dsimp only at h
  have hfilt : W.filter (fun D => φ (ind D) = 1) = W.filter (fun D => i ∈ D) := by
    ext D
    simp only [Finset.mem_filter, φ, LinearMap.proj_apply, ind]
    by_cases hD : i ∈ D <;> simp [hD]
  change 2 * (W.filter (fun D => φ (ind D) = 1)).card = W.card at h
  rw [hfilt] at h
  exact h

abbrev validMate {n m : ℕ} (left right : Fin m → Fin n) (sign start : Fin m → Bool)
    (mate : Fin m → Fin m) : Prop :=
  Function.Involutive mate ∧
  ∀ idx, mate idx ≠ idx → ∃ word, faultsOf left right sign word = {idx, mate idx} ∧
    missedOf left right sign start word = {idx} ∧
    missedOf left right sign start (fun site => !(word site)) = {mate idx}

abbrev fixedOf {m : ℕ} (mate : Fin m → Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun pos => mate pos = pos)

lemma involution_card_eq {m : ℕ} (mate : Fin m → Fin m) (hinv : Function.Involutive mate) :
    2 * (Finset.univ.filter (fun i : Fin m => i < mate i)).card + (fixedOf mate).card = m := by
  let L := Finset.univ.filter (fun i : Fin m => i < mate i)
  let G := Finset.univ.filter (fun i : Fin m => mate i < i)
  have hLG : L.card = G.card := by
    refine Finset.card_bij (fun i _ => mate i) ?_ ?_ ?_
    · intro i hi
      have hlt : i < mate i := (Finset.mem_filter.mp hi).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hinv i]
      exact hlt
    · intro i1 _ i2 _ heq
      have h := congrArg mate heq
      rw [hinv i1, hinv i2] at h
      exact h
    · intro j hj
      have hlt : mate j < j := (Finset.mem_filter.mp hj).2
      refine ⟨mate j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hinv j⟩
      rw [hinv j]
      exact hlt
  have hdisj1 : Disjoint L G := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have h1 := (Finset.mem_filter.mp hi1).2
    have h2 := (Finset.mem_filter.mp hi2).2
    exact lt_asymm h1 h2
  have hdisj2 : Disjoint (L ∪ G) (fixedOf mate) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have h2 : mate i = i := (Finset.mem_filter.mp hi2).2
    rcases Finset.mem_union.mp hi1 with hL | hG
    · have h1 := (Finset.mem_filter.mp hL).2
      rw [h2] at h1; exact lt_irrefl _ h1
    · have h1 := (Finset.mem_filter.mp hG).2
      rw [h2] at h1; exact lt_irrefl _ h1
  have hunion : (L ∪ G) ∪ fixedOf mate = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true, fixedOf, L, G]
    rcases lt_trichotomy i (mate i) with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h.symm
    · exact Or.inl (Or.inr h)
  have htot := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
    Finset.card_univ, Fintype.card_fin, ← hLG] at htot
  dsimp only [L] at htot
  omega

lemma validMate_D_card {n m : ℕ} (left right : Fin m → Fin n) (sign start : Fin m → Bool)
    (hmiss : ∀ x, (missedOf left right sign start x).Nonempty)
    (mate : Fin m → Fin m) (hval : validMate left right sign start mate)
    {D : Finset (Fin m)} (hD : D ∈ Finset.univ.filter (oddSetPred left right sign)) :
    D.card = (Finset.univ.filter (fun i : Fin m => i < mate i)).card + (D ∩ fixedOf mate).card := by
  let L := Finset.univ.filter (fun i : Fin m => i < mate i)
  have hcomp : ∀ i : Fin m, mate i ≠ i → (i ∈ D ↔ mate i ∉ D) := by
    intro i hne
    have h := (pair_witness_iff left right sign start hmiss hne.symm).mp (hval.2 i hne) D hD
    exact h
  have hnonfix : (D \ fixedOf mate).card = L.card := by
    refine Finset.card_bij (fun i _ => if i < mate i then i else mate i) ?_ ?_ ?_
    · intro i hi
      have hne : mate i ≠ i := by
        intro heq
        exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩)
      split_ifs with hlt
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [hval.1 i]
        rcases lt_trichotomy i (mate i) with h | h | h
        · exact absurd h hlt
        · exact absurd h.symm hne
        · exact h
    · intro i1 hi1 i2 hi2 heq
      have h1D : i1 ∈ D := (Finset.mem_sdiff.mp hi1).1
      have h2D : i2 ∈ D := (Finset.mem_sdiff.mp hi2).1
      have hne1 : mate i1 ≠ i1 := by
        intro h; exact (Finset.mem_sdiff.mp hi1).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have hne2 : mate i2 ≠ i2 := by
        intro h; exact (Finset.mem_sdiff.mp hi2).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      split_ifs at heq with h1 h2
      · exact heq
      · rw [heq] at h1D
        exact absurd h1D ((hcomp i2 hne2).mp h2D)
      · rw [← heq] at h2D
        exact absurd h2D ((hcomp i1 hne1).mp h1D)
      · have h := congrArg mate heq
        rw [hval.1 i1, hval.1 i2] at h
        exact h
    · intro i hi
      have hlt : i < mate i := (Finset.mem_filter.mp hi).2
      have hne : mate i ≠ i := ne_of_gt hlt
      by_cases hiD : i ∈ D
      · refine ⟨i, Finset.mem_sdiff.mpr ⟨hiD, ?_⟩, by simp [hlt]⟩
        simp [fixedOf, hne]
      · have hmD : mate i ∈ D := by
          by_contra hnot
          exact hiD ((hcomp i hne).mpr hnot)
        have hne' : mate (mate i) ≠ mate i := by rw [hval.1 i]; exact hne.symm
        refine ⟨mate i, Finset.mem_sdiff.mpr ⟨hmD, ?_⟩, ?_⟩
        · simp [fixedOf, hne']
        · simp only [hval.1 i, not_lt.mpr (le_of_lt hlt), ↓reduceIte]
  have hpart : (D \ fixedOf mate).card + (D ∩ fixedOf mate).card = D.card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_sdiff_inter D (fixedOf mate)), Finset.sdiff_union_inter]
  dsimp only [L] at hnonfix
  omega

lemma validMate_nonfixed_mem_biUnion {n m : ℕ} (left right : Fin m → Fin n)
    (sign start : Fin m → Bool)
    (hmiss : ∀ x, (missedOf left right sign start x).Nonempty)
    (mate : Fin m → Fin m) (hval : validMate left right sign start mate)
    {i : Fin m} (hne : mate i ≠ i) :
    i ∈ (Finset.univ.filter (oddSetPred left right sign)).biUnion id := by
  rcases exists_not_mem_W left right sign start hmiss (mate i) with ⟨D, hD, hnot⟩
  have hcomp := (pair_witness_iff left right sign start hmiss hne.symm).mp (hval.2 i hne) D hD
  exact Finset.mem_biUnion.mpr ⟨D, hD, hcomp.mpr hnot⟩

lemma exists_min_validMate {n m : ℕ} (left right : Fin m → Fin n) (sign start : Fin m → Bool) :
    ∃ mate0 : Fin m → Fin m, validMate left right sign start mate0 ∧
      ∀ mate : Fin m → Fin m, validMate left right sign start mate →
        (fixedOf mate0).card ≤ (fixedOf mate).card := by
  classical
  let S : Finset (Fin m → Fin m) := Finset.univ.filter (validMate left right sign start)
  have hSne : S.Nonempty := by
    refine ⟨id, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨fun _ => rfl, fun idx hne => ?_⟩⟩⟩
    exact absurd rfl hne
  rcases Finset.exists_min_image S (fun f => (fixedOf f).card) hSne with ⟨mate0, hmem, hmin⟩
  exact ⟨mate0, (Finset.mem_filter.mp hmem).2, fun mate hm =>
    hmin mate (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)⟩

lemma min_validMate_no_comp {n m : ℕ} (left right : Fin m → Fin n) (sign start : Fin m → Bool)
    (hmiss : ∀ x, (missedOf left right sign start x).Nonempty)
    (mate0 : Fin m → Fin m)
    (hval0 : validMate left right sign start mate0)
    (hmin0 : ∀ mate : Fin m → Fin m, validMate left right sign start mate →
      (fixedOf mate0).card ≤ (fixedOf mate).card)
    {i j : Fin m} (hi : i ∈ fixedOf mate0) (hj : j ∈ fixedOf mate0) (hij : i ≠ j) :
    ¬ (∀ D ∈ Finset.univ.filter (oddSetPred left right sign), i ∈ D ↔ j ∉ D) := by
  intro hcomp
  have hi_fix : mate0 i = i := (Finset.mem_filter.mp hi).2
  have hj_fix : mate0 j = j := (Finset.mem_filter.mp hj).2
  let mate1 : Fin m → Fin m := fun k =>
    if k = i then j else if k = j then i else mate0 k
  have hinv1 : Function.Involutive mate1 := by
    intro k
    dsimp only [mate1]
    by_cases hki : k = i
    · subst hki; simp [hij.symm]
    · by_cases hkj : k = j
      · subst hkj; simp [hki]
      · have hmi : mate0 k ≠ i := fun heq => by
          have := congrArg mate0 heq; rw [hval0.1 k, hi_fix] at this; exact hki this
        have hmj : mate0 k ≠ j := fun heq => by
          have := congrArg mate0 heq; rw [hval0.1 k, hj_fix] at this; exact hkj this
        simp [hki, hkj, hmi, hmj, hval0.1 k]
  have hval1 : validMate left right sign start mate1 := by
    refine ⟨hinv1, fun k hk => ?_⟩
    by_cases hki : k = i
    · subst hki
      have hm : mate1 k = j := by simp [mate1]
      rw [hm]
      exact (pair_witness_iff left right sign start hmiss hij).mpr hcomp
    · by_cases hkj : k = j
      · subst hkj
        have hm : mate1 k = i := by simp [mate1, hki]
        rw [hm]
        exact (pair_witness_iff left right sign start hmiss hij.symm).mpr
          (fun D hD => ⟨fun h1 h2 => (hcomp D hD).mp h2 h1,
            fun hnot => by by_contra h2; exact hnot ((hcomp D hD).mpr h2)⟩)
      · have hm : mate1 k = mate0 k := by simp [mate1, hki, hkj]
        rw [hm] at hk ⊢
        exact hval0.2 k hk
  have hfix_sub : fixedOf mate1 = ((fixedOf mate0).erase i).erase j := by
    ext k
    simp only [fixedOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, mate1]
    by_cases hki : k = i
    · subst hki; simp [hij.symm]
    · by_cases hkj : k = j
      · subst hkj; simp [hki, hij]
      · simp [hki, hkj]
  have hcard1 : (fixedOf mate1).card + 2 = (fixedOf mate0).card := by
    rw [hfix_sub]
    have hj_mem : j ∈ (fixedOf mate0).erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
    rw [Finset.card_erase_of_mem hj_mem, Finset.card_erase_of_mem hi]
    have hge2 : 2 ≤ (fixedOf mate0).card := by
      have hsub : ({i, j} : Finset (Fin m)) ⊆ fixedOf mate0 := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hij] at this
      exact this
    omega
  have hle := hmin0 mate1 hval1
  omega

lemma variance_miracle {n m : ℕ} (left right : Fin m → Fin n) (sign start : Fin m → Bool)
    (hmiss : ∀ x, (missedOf left right sign start x).Nonempty)
    (R : Finset (Fin m)) (k : ℕ) (hk : 1 ≤ k) (hRcard : R.card = 2 * k + 1)
    (hno_comp : ∀ i ∈ R, ∀ j ∈ R, i ≠ j →
      ¬ (∀ D ∈ Finset.univ.filter (oddSetPred left right sign), i ∈ D ↔ j ∉ D))
    (hge : ∀ D ∈ Finset.univ.filter (oddSetPred left right sign), k ≤ (D ∩ R).card) :
    let W := Finset.univ.filter (oddSetPred left right sign)
    R ⊆ W.biUnion id ∧
    (∀ D ∈ W, (D ∩ R).card = k ∨ R ⊆ D) ∧
    (∃ D_all ∈ W, R ⊆ D_all) ∧
    (∀ i ∈ R, ∀ j ∈ R, i ≠ j → ∃ D ∈ W, ¬ (i ∈ D ↔ j ∈ D)) ∧
    (R.card + 1) * (W.filter (fun D => R ⊆ D)).card = W.card := by
  intro W
  have hWne : W.Nonempty := W_nonempty left right sign start hmiss
  have hWpos : 0 < W.card := Finset.card_pos.mpr hWne
  let U := W.biUnion id
  let Ru := R ∩ U
  have hpair_ge : ∀ i ∈ Ru, ∀ j ∈ Ru,
      (0 : ℤ) ≤ ∑ D ∈ W, (if i ∈ D then (-1 : ℤ) else 1) * (if j ∈ D then (-1 : ℤ) else 1) := by
    intro i hi j hj
    by_cases heq : i = j
    · subst heq
      have h1 : (∑ D ∈ W, (if i ∈ D then (-1 : ℤ) else 1) * (if i ∈ D then (-1 : ℤ) else 1)) =
          (W.card : ℤ) := by
        calc
          (∑ D ∈ W, (if i ∈ D then (-1 : ℤ) else 1) * (if i ∈ D then (-1 : ℤ) else 1))
              = ∑ _D ∈ W, (1 : ℤ) := Finset.sum_congr rfl fun D _ => by split_ifs <;> ring
          _ = (W.card : ℤ) := by simp
      rw [h1]; omega
    · by_cases hall : ∀ D ∈ W, i ∈ D ↔ j ∈ D
      · have h1 : (∑ D ∈ W, (if i ∈ D then (-1 : ℤ) else 1) * (if j ∈ D then (-1 : ℤ) else 1)) =
            (W.card : ℤ) := by
          calc
            (∑ D ∈ W, (if i ∈ D then (-1 : ℤ) else 1) * (if j ∈ D then (-1 : ℤ) else 1))
                = ∑ _D ∈ W, (1 : ℤ) := Finset.sum_congr rfl fun D hD => by
                  by_cases hiD : i ∈ D
                  · have hjD : j ∈ D := (hall D hD).mp hiD
                    simp [hiD, hjD]
                  · have hjD : j ∉ D := fun h => hiD ((hall D hD).mpr h)
                    simp [hiD, hjD]
            _ = (W.card : ℤ) := by simp
        rw [h1]; omega
      · push Not at hall
        rcases hall with ⟨D1, hD1, hne1⟩
        have hnotcomp := hno_comp i (Finset.mem_inter.mp hi).1 j (Finset.mem_inter.mp hj).1 heq
        push Not at hnotcomp
        rcases hnotcomp with ⟨D0, hD0, hsame0⟩
        let φ : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
          { toFun := fun v => v i + v j
            map_add' := fun u v => by simp only [Pi.add_apply]; ring
            map_smul' := fun a v => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
        have hφ0 : φ (ind D0) = 0 := by
          change ind D0 i + ind D0 j = 0
          simp only [ind]
          by_cases hi0 : i ∈ D0 <;> by_cases hj0 : j ∈ D0 <;> simp_all
          exact zmod2_add_self 1
        have hφ1 : φ (ind D1) = 1 := by
          change ind D1 i + ind D1 j = 1
          simp only [ind]
          by_cases hi1 : i ∈ D1 <;> by_cases hj1 : j ∈ D1 <;> simp_all
        have hhalf := W_half_linear left right sign φ ⟨D0, hD0, hφ0⟩ ⟨D1, hD1, hφ1⟩
        dsimp only at hhalf
        change 2 * (W.filter (fun D => φ (ind D) = 1)).card = W.card at hhalf
        have hsum0 : (∑ D ∈ W, (if i ∈ D then (-1 : ℤ) else 1) * (if j ∈ D then (-1 : ℤ) else 1)) = 0 := by
          have hterm : ∀ D ∈ W,
              (if i ∈ D then (-1 : ℤ) else 1) * (if j ∈ D then (-1 : ℤ) else 1) =
              if φ (ind D) = 1 then (-1 : ℤ) else 1 := fun D _ => by
            change (if i ∈ D then (-1 : ℤ) else 1) * (if j ∈ D then (-1 : ℤ) else 1) =
              if ind D i + ind D j = 1 then (-1 : ℤ) else 1
            simp only [ind]
            by_cases hiD : i ∈ D <;> by_cases hjD : j ∈ D <;> simp [hiD, hjD]
          rw [Finset.sum_congr rfl hterm]
          rw [← Finset.sum_filter_add_sum_filter_not W (fun D => φ (ind D) = 1)]
          have hs1 : (∑ D ∈ W.filter (fun D => φ (ind D) = 1),
              if φ (ind D) = 1 then (-1 : ℤ) else 1) =
              -((W.filter (fun D => φ (ind D) = 1)).card : ℤ) := by
            calc
              (∑ D ∈ W.filter (fun D => φ (ind D) = 1), if φ (ind D) = 1 then (-1 : ℤ) else 1)
                  = ∑ _D ∈ W.filter (fun D => φ (ind D) = 1), (-1 : ℤ) :=
                Finset.sum_congr rfl fun D hD => by simp [(Finset.mem_filter.mp hD).2]
              _ = -((W.filter (fun D => φ (ind D) = 1)).card : ℤ) := by simp
          have hs2 : (∑ D ∈ W.filter (fun D => ¬ φ (ind D) = 1),
              if φ (ind D) = 1 then (-1 : ℤ) else 1) =
              ((W.filter (fun D => ¬ φ (ind D) = 1)).card : ℤ) := by
            calc
              (∑ D ∈ W.filter (fun D => ¬ φ (ind D) = 1), if φ (ind D) = 1 then (-1 : ℤ) else 1)
                  = ∑ _D ∈ W.filter (fun D => ¬ φ (ind D) = 1), (1 : ℤ) :=
                Finset.sum_congr rfl fun D hD => by simp [(Finset.mem_filter.mp hD).2]
              _ = ((W.filter (fun D => ¬ φ (ind D) = 1)).card : ℤ) := by simp
          have htot := Finset.card_filter_add_card_filter_not (s := W) (p := fun D => φ (ind D) = 1)
          rw [hs1, hs2]
          omega
        rw [hsum0]
  have hsingle0 : ∀ i ∈ Ru, (∑ D ∈ W, (if i ∈ D then (-1 : ℤ) else 1)) = 0 := by
    intro i hi
    have hhalf := W_half_coord left right sign start hmiss (Finset.mem_inter.mp hi).2
    dsimp only at hhalf
    change 2 * (W.filter (fun D => i ∈ D)).card = W.card at hhalf
    rw [← Finset.sum_filter_add_sum_filter_not W (fun D => i ∈ D)]
    have hs1 : (∑ D ∈ W.filter (fun D => i ∈ D), if i ∈ D then (-1 : ℤ) else 1) =
        -((W.filter (fun D => i ∈ D)).card : ℤ) := by
      calc
        (∑ D ∈ W.filter (fun D => i ∈ D), if i ∈ D then (-1 : ℤ) else 1)
            = ∑ _D ∈ W.filter (fun D => i ∈ D), (-1 : ℤ) :=
          Finset.sum_congr rfl fun D hD => by simp [(Finset.mem_filter.mp hD).2]
        _ = -((W.filter (fun D => i ∈ D)).card : ℤ) := by simp
    have hs2 : (∑ D ∈ W.filter (fun D => ¬ i ∈ D), if i ∈ D then (-1 : ℤ) else 1) =
        ((W.filter (fun D => ¬ i ∈ D)).card : ℤ) := by
      calc
        (∑ D ∈ W.filter (fun D => ¬ i ∈ D), if i ∈ D then (-1 : ℤ) else 1)
            = ∑ _D ∈ W.filter (fun D => ¬ i ∈ D), (1 : ℤ) :=
          Finset.sum_congr rfl fun D hD => by simp [(Finset.mem_filter.mp hD).2]
        _ = ((W.filter (fun D => ¬ i ∈ D)).card : ℤ) := by simp
    have htot := Finset.card_filter_add_card_filter_not (s := W) (p := fun D => i ∈ D)
    rw [hs1, hs2]
    omega
  let Yu : Finset (Fin m) → ℤ := fun D => ∑ i ∈ Ru, (if i ∈ D then (-1 : ℤ) else 1)
  have hYu_eq : ∀ D ∈ W, Yu D = (Ru.card : ℤ) - 2 * ((D ∩ R).card : ℤ) := by
    intro D hD
    have hDR : D ∩ R = Ru.filter (fun i => i ∈ D) := by
      ext i
      simp only [Finset.mem_inter, Finset.mem_filter, Ru, U, Finset.mem_biUnion, id_eq]
      constructor
      · rintro ⟨hiD, hiR⟩
        exact ⟨⟨hiR, ⟨D, hD, hiD⟩⟩, hiD⟩
      · rintro ⟨⟨hiR, _⟩, hiD⟩
        exact ⟨hiD, hiR⟩
    have htot := Finset.card_filter_add_card_filter_not (s := Ru) (p := fun i => i ∈ D)
    dsimp only [Yu]
    rw [← Finset.sum_filter_add_sum_filter_not Ru (fun i => i ∈ D)]
    have hs1 : (∑ i ∈ Ru.filter (fun i => i ∈ D), if i ∈ D then (-1 : ℤ) else 1) =
        -((Ru.filter (fun i => i ∈ D)).card : ℤ) := by
      calc
        (∑ i ∈ Ru.filter (fun i => i ∈ D), if i ∈ D then (-1 : ℤ) else 1)
            = ∑ _i ∈ Ru.filter (fun i => i ∈ D), (-1 : ℤ) :=
          Finset.sum_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
        _ = -((Ru.filter (fun i => i ∈ D)).card : ℤ) := by simp
    have hs2 : (∑ i ∈ Ru.filter (fun i => ¬ i ∈ D), if i ∈ D then (-1 : ℤ) else 1) =
        ((Ru.filter (fun i => ¬ i ∈ D)).card : ℤ) := by
      calc
        (∑ i ∈ Ru.filter (fun i => ¬ i ∈ D), if i ∈ D then (-1 : ℤ) else 1)
            = ∑ _i ∈ Ru.filter (fun i => ¬ i ∈ D), (1 : ℤ) :=
          Finset.sum_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
        _ = ((Ru.filter (fun i => ¬ i ∈ D)).card : ℤ) := by simp
    rw [hs1, hs2, hDR]
    omega
  have hsum_Yu : (∑ D ∈ W, Yu D) = 0 := by
    dsimp only [Yu]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero hsingle0
  have hsum_Yu_sq : (Ru.card : ℤ) * (W.card : ℤ) ≤ ∑ D ∈ W, (Yu D) ^ 2 := by
    have hexp : (∑ D ∈ W, (Yu D) ^ 2) =
        ∑ i ∈ Ru, ∑ j ∈ Ru,
          ∑ D ∈ W, (if i ∈ D then (-1 : ℤ) else 1) * (if j ∈ D then (-1 : ℤ) else 1) := by
      have h1 : ∀ D ∈ W, (Yu D) ^ 2 =
          ∑ i ∈ Ru, ∑ j ∈ Ru,
            (if i ∈ D then (-1 : ℤ) else 1) * (if j ∈ D then (-1 : ℤ) else 1) := fun D _ => by
        dsimp only [Yu]
        rw [sq, Finset.sum_mul_sum]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [hexp]
    have hdiag : ∀ i ∈ Ru, (W.card : ℤ) ≤
        ∑ j ∈ Ru, ∑ D ∈ W, (if i ∈ D then (-1 : ℤ) else 1) * (if j ∈ D then (-1 : ℤ) else 1) := by
      intro i hi
      have h1 : (∑ D ∈ W, (if i ∈ D then (-1 : ℤ) else 1) * (if i ∈ D then (-1 : ℤ) else 1)) =
          (W.card : ℤ) := by
        calc
          (∑ D ∈ W, (if i ∈ D then (-1 : ℤ) else 1) * (if i ∈ D then (-1 : ℤ) else 1))
              = ∑ _D ∈ W, (1 : ℤ) := Finset.sum_congr rfl fun D _ => by split_ifs <;> ring
          _ = (W.card : ℤ) := by simp
      rw [← h1]
      exact Finset.single_le_sum (fun j hj => hpair_ge i hi j hj) hi
    calc
      (Ru.card : ℤ) * (W.card : ℤ) = ∑ _i ∈ Ru, (W.card : ℤ) := by simp
      _ ≤ ∑ i ∈ Ru, ∑ j ∈ Ru,
            ∑ D ∈ W, (if i ∈ D then (-1 : ℤ) else 1) * (if j ∈ D then (-1 : ℤ) else 1) :=
        Finset.sum_le_sum hdiag
  have hRu_le : Ru.card ≤ R.card := Finset.card_le_card Finset.inter_subset_left
  have hRsubU : R ⊆ U := by
    by_contra hnot
    have hRu_lt : Ru.card < R.card := by
      have hsub : Ru ⊆ R := Finset.inter_subset_left
      have hne : Ru ≠ R := fun heq => hnot (heq ▸ Finset.inter_subset_right)
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    have hYu_le0 : ∀ D ∈ W, Yu D ≤ 0 := by
      intro D hD
      rw [hYu_eq D hD]
      have := hge D hD
      omega
    have hYu_zero : ∀ D ∈ W, Yu D = 0 := by
      intro D hD
      by_contra hne0
      have hlt0 : Yu D < 0 := lt_of_le_of_ne (hYu_le0 D hD) hne0
      have hsum_neg : (∑ D' ∈ W, Yu D') < 0 := by
        calc
          (∑ D' ∈ W, Yu D') = Yu D + ∑ D' ∈ W.erase D, Yu D' :=
            (Finset.add_sum_erase W Yu hD).symm
          _ ≤ Yu D + ∑ _D' ∈ W.erase D, (0 : ℤ) := by
            exact add_le_add (le_refl _) (Finset.sum_le_sum fun D' hD' => hYu_le0 D' (Finset.mem_of_mem_erase hD'))
          _ = Yu D := by simp
          _ < 0 := hlt0
      omega
    have hsq0 : (∑ D ∈ W, (Yu D) ^ 2) = 0 := by
      refine Finset.sum_eq_zero fun D hD => ?_
      rw [hYu_zero D hD]; ring
    have hRu_pos : 1 ≤ Ru.card := by
      rcases hWne with ⟨D0, hD0⟩
      have h0 := hYu_zero D0 hD0
      rw [hYu_eq D0 hD0] at h0
      have := hge D0 hD0
      omega
    nlinarith
  have hRu_eq : Ru = R := Finset.inter_eq_left.mpr hRsubU
  have hYu_bounds : ∀ D ∈ W, 0 ≤ (1 - Yu D) * (Yu D + (R.card : ℤ)) := by
    intro D hD
    rw [hYu_eq D hD, hRu_eq]
    have h1 := hge D hD
    have h2 : (D ∩ R).card ≤ R.card := Finset.card_le_card Finset.inter_subset_right
    have ha : (0 : ℤ) ≤ 1 - ((R.card : ℤ) - 2 * ((D ∩ R).card : ℤ)) := by omega
    have hb : (0 : ℤ) ≤ ((R.card : ℤ) - 2 * ((D ∩ R).card : ℤ)) + (R.card : ℤ) := by omega
    exact mul_nonneg ha hb
  have hsum_poly : (∑ D ∈ W, (1 - Yu D) * (Yu D + (R.card : ℤ))) =
      (R.card : ℤ) * (W.card : ℤ) - ∑ D ∈ W, (Yu D) ^ 2 := by
    have hexp : ∀ D ∈ W, (1 - Yu D) * (Yu D + (R.card : ℤ)) =
        (R.card : ℤ) + (1 - (R.card : ℤ)) * Yu D - (Yu D) ^ 2 := fun D _ => by ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hsum_Yu, mul_zero, add_zero]
    simp [mul_comm]
  have hsq_eq : (∑ D ∈ W, (Yu D) ^ 2) = (R.card : ℤ) * (W.card : ℤ) := by
    have hge0 : (0 : ℤ) ≤ ∑ D ∈ W, (1 - Yu D) * (Yu D + (R.card : ℤ)) :=
      Finset.sum_nonneg hYu_bounds
    rw [hsum_poly] at hge0
    rw [hRu_eq] at hsum_Yu_sq
    omega
  have hpoly_zero : ∀ D ∈ W, (1 - Yu D) * (Yu D + (R.card : ℤ)) = 0 := by
    intro D hD
    have hsum0 : (∑ D' ∈ W, (1 - Yu D') * (Yu D' + (R.card : ℤ))) = 0 := by
      rw [hsum_poly, hsq_eq, sub_self]
    by_contra hne0
    have hpos : (0 : ℤ) < (1 - Yu D) * (Yu D + (R.card : ℤ)) :=
      lt_of_le_of_ne (hYu_bounds D hD) (Ne.symm hne0)
    have hsum_pos : (0 : ℤ) < ∑ D' ∈ W, (1 - Yu D') * (Yu D' + (R.card : ℤ)) := by
      calc
        (0 : ℤ) < (1 - Yu D) * (Yu D + (R.card : ℤ)) := hpos
        _ = (1 - Yu D) * (Yu D + (R.card : ℤ)) + ∑ _D' ∈ W.erase D, (0 : ℤ) := by simp
        _ ≤ (1 - Yu D) * (Yu D + (R.card : ℤ)) +
            ∑ D' ∈ W.erase D, (1 - Yu D') * (Yu D' + (R.card : ℤ)) := by
          exact add_le_add (le_refl _) (Finset.sum_le_sum fun D' hD' =>
            hYu_bounds D' (Finset.mem_of_mem_erase hD'))
        _ = ∑ D' ∈ W, (1 - Yu D') * (Yu D' + (R.card : ℤ)) :=
          Finset.add_sum_erase W (fun D' => (1 - Yu D') * (Yu D' + (R.card : ℤ))) hD
    omega
  have hdich : ∀ D ∈ W, (D ∩ R).card = k ∨ R ⊆ D := by
    intro D hD
    rcases mul_eq_zero.mp (hpoly_zero D hD) with h1 | h2
    · left
      rw [hYu_eq D hD, hRu_eq] at h1
      omega
    · right
      rw [hYu_eq D hD, hRu_eq] at h2
      have hcard_eq : (D ∩ R).card = R.card := by omega
      have hEq : D ∩ R = R := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
      intro i hi
      rw [← hEq] at hi
      exact (Finset.mem_inter.mp hi).1
  have hcount : (R.card + 1) * (W.filter (fun D => R ⊆ D)).card = W.card := by
    have hsplit : (∑ D ∈ W, Yu D) =
        (∑ D ∈ W.filter (fun D => R ⊆ D), Yu D) +
        (∑ D ∈ W.filter (fun D => ¬ R ⊆ D), Yu D) :=
      (Finset.sum_filter_add_sum_filter_not W (fun D => R ⊆ D) Yu).symm
    have hs1 : (∑ D ∈ W.filter (fun D => R ⊆ D), Yu D) =
        -((W.filter (fun D => R ⊆ D)).card : ℤ) * (R.card : ℤ) := by
      calc
        (∑ D ∈ W.filter (fun D => R ⊆ D), Yu D)
            = ∑ _D ∈ W.filter (fun D => R ⊆ D), -(R.card : ℤ) := by
          refine Finset.sum_congr rfl fun D hD => ?_
          have hDW : D ∈ W := (Finset.mem_filter.mp hD).1
          have hsub : R ⊆ D := (Finset.mem_filter.mp hD).2
          rw [hYu_eq D hDW, hRu_eq, Finset.inter_eq_right.mpr hsub]
          omega
        _ = -((W.filter (fun D => R ⊆ D)).card : ℤ) * (R.card : ℤ) := by simp
    have hs2 : (∑ D ∈ W.filter (fun D => ¬ R ⊆ D), Yu D) =
        ((W.filter (fun D => ¬ R ⊆ D)).card : ℤ) := by
      calc
        (∑ D ∈ W.filter (fun D => ¬ R ⊆ D), Yu D)
            = ∑ _D ∈ W.filter (fun D => ¬ R ⊆ D), (1 : ℤ) := by
          refine Finset.sum_congr rfl fun D hD => ?_
          have hDW : D ∈ W := (Finset.mem_filter.mp hD).1
          have hnot : ¬ R ⊆ D := (Finset.mem_filter.mp hD).2
          have hk_eq : (D ∩ R).card = k := (hdich D hDW).resolve_right hnot
          rw [hYu_eq D hDW, hRu_eq, hk_eq]
          omega
        _ = ((W.filter (fun D => ¬ R ⊆ D)).card : ℤ) := by simp
    have htot := Finset.card_filter_add_card_filter_not (s := W) (p := fun D => R ⊆ D)
    rw [hsum_Yu, hs1, hs2] at hsplit
    zify
    nlinarith
  have hex_all : ∃ D_all ∈ W, R ⊆ D_all := by
    have hpos : 0 < (W.filter (fun D => R ⊆ D)).card := by
      by_contra h0
      have hz : (W.filter (fun D => R ⊆ D)).card = 0 := by omega
      rw [hz, mul_zero] at hcount
      omega
    rcases Finset.card_pos.mp hpos with ⟨D_all, hmem⟩
    exact ⟨D_all, (Finset.mem_filter.mp hmem).1, (Finset.mem_filter.mp hmem).2⟩
  have hsep : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → ∃ D ∈ W, ¬ (i ∈ D ↔ j ∈ D) := by
    intro i hi j hj hij
    by_contra hall
    push Not at hall
    have hpair_eq : (∑ D ∈ W, (if i ∈ D then (-1 : ℤ) else 1) * (if j ∈ D then (-1 : ℤ) else 1)) =
        (W.card : ℤ) := by
      calc
        (∑ D ∈ W, (if i ∈ D then (-1 : ℤ) else 1) * (if j ∈ D then (-1 : ℤ) else 1))
            = ∑ _D ∈ W, (1 : ℤ) := Finset.sum_congr rfl fun D hD => by
              by_cases hiD : i ∈ D
              · have hjD : j ∈ D := (hall D hD).mp hiD
                simp [hiD, hjD]
              · have hjD : j ∉ D := fun h => hiD ((hall D hD).mpr h)
                simp [hiD, hjD]
        _ = (W.card : ℤ) := by simp
    have hexp : (∑ D ∈ W, (Yu D) ^ 2) =
        ∑ a ∈ R, ∑ b ∈ R,
          ∑ D ∈ W, (if a ∈ D then (-1 : ℤ) else 1) * (if b ∈ D then (-1 : ℤ) else 1) := by
      have h1 : ∀ D ∈ W, (Yu D) ^ 2 =
          ∑ a ∈ R, ∑ b ∈ R,
            (if a ∈ D then (-1 : ℤ) else 1) * (if b ∈ D then (-1 : ℤ) else 1) := fun D _ => by
        dsimp only [Yu]; rw [hRu_eq, sq, Finset.sum_mul_sum]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    have hrow_i : 2 * (W.card : ℤ) ≤
        ∑ b ∈ R, ∑ D ∈ W, (if i ∈ D then (-1 : ℤ) else 1) * (if b ∈ D then (-1 : ℤ) else 1) := by
      have hpair_sub : ({i, j} : Finset (Fin m)) ⊆ R := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hpair_sub
        (fun b hb _ => hpair_ge i (hRu_eq ▸ hi) b (hRu_eq ▸ hb))
      rw [Finset.sum_pair hij, hpair_eq] at hle
      have hdiag_i : (∑ D ∈ W, (if i ∈ D then (-1 : ℤ) else 1) * (if i ∈ D then (-1 : ℤ) else 1)) =
          (W.card : ℤ) := by
        calc
          (∑ D ∈ W, (if i ∈ D then (-1 : ℤ) else 1) * (if i ∈ D then (-1 : ℤ) else 1))
              = ∑ _D ∈ W, (1 : ℤ) := Finset.sum_congr rfl fun D _ => by split_ifs <;> ring
          _ = (W.card : ℤ) := by simp
      rw [hdiag_i] at hle
      omega
    have hrow_other : ∀ a ∈ R.erase i, (W.card : ℤ) ≤
        ∑ b ∈ R, ∑ D ∈ W, (if a ∈ D then (-1 : ℤ) else 1) * (if b ∈ D then (-1 : ℤ) else 1) := by
      intro a ha
      have haR : a ∈ R := Finset.mem_of_mem_erase ha
      have hdiag_a : (∑ D ∈ W, (if a ∈ D then (-1 : ℤ) else 1) * (if a ∈ D then (-1 : ℤ) else 1)) =
          (W.card : ℤ) := by
        calc
          (∑ D ∈ W, (if a ∈ D then (-1 : ℤ) else 1) * (if a ∈ D then (-1 : ℤ) else 1))
              = ∑ _D ∈ W, (1 : ℤ) := Finset.sum_congr rfl fun D _ => by split_ifs <;> ring
          _ = (W.card : ℤ) := by simp
      rw [← hdiag_a]
      exact Finset.single_le_sum (fun b hb => hpair_ge a (hRu_eq ▸ haR) b (hRu_eq ▸ hb)) haR
    have htot_gt : ((R.card : ℤ) + 1) * (W.card : ℤ) ≤ ∑ D ∈ W, (Yu D) ^ 2 := by
      rw [hexp, ← Finset.add_sum_erase R _ hi]
      have hrest : ((R.erase i).card : ℤ) * (W.card : ℤ) ≤
          ∑ a ∈ R.erase i, ∑ b ∈ R,
            ∑ D ∈ W, (if a ∈ D then (-1 : ℤ) else 1) * (if b ∈ D then (-1 : ℤ) else 1) := by
        calc
          ((R.erase i).card : ℤ) * (W.card : ℤ) = ∑ _a ∈ R.erase i, (W.card : ℤ) := by simp
          _ ≤ _ := Finset.sum_le_sum hrow_other
      rw [Finset.card_erase_of_mem hi] at hrest
      have hRpos : 1 ≤ R.card := by omega
      have hcast : ((R.card - 1 : ℕ) : ℤ) = (R.card : ℤ) - 1 := by omega
      rw [hcast] at hrest
      linarith
    rw [hsq_eq] at htot_gt
    nlinarith
  exact ⟨hRsubU, hdich, hex_all, hsep, hcount⟩

lemma zmod2_fin3_sum_dot (a : Fin 3 → ZMod 2) :
    (∑ u : Fin 3 → ZMod 2, dotProduct a u) = 0 := by
  revert a; decide

lemma zmod2_fin3_sum_dot_mul (a b : Fin 3 → ZMod 2) :
    (∑ u : Fin 3 → ZMod 2, dotProduct a u * dotProduct b u) = 0 := by
  revert a b; decide

lemma zmod2_fin3_cut_uniqueness
    (w : {u : Fin 3 → ZMod 2 // u ≠ 0} → ZMod 2)
    (hsum : (∑ u : {u : Fin 3 → ZMod 2 // u ≠ 0}, w u) = 0)
    (hlin : ∀ t : Fin 3, (∑ u : {u : Fin 3 → ZMod 2 // u ≠ 0}, w u * u.1 t) = 0) :
    let e0 : {u : Fin 3 → ZMod 2 // u ≠ 0} := ⟨![1, 0, 0], by decide⟩
    let e1 : {u : Fin 3 → ZMod 2 // u ≠ 0} := ⟨![0, 1, 0], by decide⟩
    let e2 : {u : Fin 3 → ZMod 2 // u ≠ 0} := ⟨![0, 0, 1], by decide⟩
    ∀ u : {u : Fin 3 → ZMod 2 // u ≠ 0},
      w u = w e0 * u.1 0 + w e1 * u.1 1 + w e2 * u.1 2 := by
  intro e0 e1 e2 u
  let w' : {u : Fin 3 → ZMod 2 // u ≠ 0} → ZMod 2 := fun v =>
    w v + (w e0 * v.1 0 + w e1 * v.1 1 + w e2 * v.1 2)
  have hlin_sum : (∑ v : {u : Fin 3 → ZMod 2 // u ≠ 0},
      (w e0 * v.1 0 + w e1 * v.1 1 + w e2 * v.1 2)) = 0 := by
    have h0 : (∑ v : {u : Fin 3 → ZMod 2 // u ≠ 0}, v.1 0) = 0 := by decide
    have h1 : (∑ v : {u : Fin 3 → ZMod 2 // u ≠ 0}, v.1 1) = 0 := by decide
    have h2 : (∑ v : {u : Fin 3 → ZMod 2 // u ≠ 0}, v.1 2) = 0 := by decide
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h0, h1, h2, mul_zero, add_zero]
  have hlin_t : ∀ t : Fin 3, (∑ v : {u : Fin 3 → ZMod 2 // u ≠ 0},
      (w e0 * v.1 0 + w e1 * v.1 1 + w e2 * v.1 2) * v.1 t) = 0 := by
    intro t
    have h0 : (∑ v : {u : Fin 3 → ZMod 2 // u ≠ 0}, v.1 0 * v.1 t) = 0 := by revert t; decide
    have h1 : (∑ v : {u : Fin 3 → ZMod 2 // u ≠ 0}, v.1 1 * v.1 t) = 0 := by revert t; decide
    have h2 : (∑ v : {u : Fin 3 → ZMod 2 // u ≠ 0}, v.1 2 * v.1 t) = 0 := by revert t; decide
    have hexp : ∀ v : {u : Fin 3 → ZMod 2 // u ≠ 0},
        (w e0 * v.1 0 + w e1 * v.1 1 + w e2 * v.1 2) * v.1 t =
        w e0 * (v.1 0 * v.1 t) + w e1 * (v.1 1 * v.1 t) + w e2 * (v.1 2 * v.1 t) := fun _ => by ring
    simp only [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, h0, h1, h2, mul_zero, add_zero]
  have hw'_sum : (∑ v : {u : Fin 3 → ZMod 2 // u ≠ 0}, w' v) = 0 := by
    simp only [w', Finset.sum_add_distrib, hsum, hlin_sum, add_zero]
  have hw'_t : ∀ t : Fin 3, (∑ v : {u : Fin 3 → ZMod 2 // u ≠ 0}, w' v * v.1 t) = 0 := by
    intro t
    have hstep : ∀ v : {u : Fin 3 → ZMod 2 // u ≠ 0},
        w' v * v.1 t = w v * v.1 t + (w e0 * v.1 0 + w e1 * v.1 1 + w e2 * v.1 2) * v.1 t :=
      fun _ => add_mul _ _ _
    rw [Finset.sum_congr rfl fun v _ => hstep v, Finset.sum_add_distrib, hlin t, hlin_t t, add_zero]
  have hw'e0 : w' e0 = 0 := by simp [w', e0, zmod2_add_self]
  have hw'e1 : w' e1 = 0 := by simp [w', e1, zmod2_add_self]
  have hw'e2 : w' e2 = 0 := by simp [w', e2, zmod2_add_self]
  have hzero_all : ∀ a0 a1 a2 a3 : ZMod 2,
      a0 + a1 + a2 + a3 = 0 →
      a0 + a1 + a3 = 0 →
      a0 + a2 + a3 = 0 →
      a1 + a2 + a3 = 0 →
      a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0 := by
    decide
  let e01 : {u : Fin 3 → ZMod 2 // u ≠ 0} := ⟨![1, 1, 0], by decide⟩
  let e02 : {u : Fin 3 → ZMod 2 // u ≠ 0} := ⟨![1, 0, 1], by decide⟩
  let e12 : {u : Fin 3 → ZMod 2 // u ≠ 0} := ⟨![0, 1, 1], by decide⟩
  let e012 : {u : Fin 3 → ZMod 2 // u ≠ 0} := ⟨![1, 1, 1], by decide⟩
  have hlist : (Finset.univ : Finset {u : Fin 3 → ZMod 2 // u ≠ 0}) =
      {e0, e1, e2, e01, e02, e12, e012} := by decide
  have hfin7 : ∀ f : {u : Fin 3 → ZMod 2 // u ≠ 0} → ZMod 2,
      (∑ v : {u : Fin 3 → ZMod 2 // u ≠ 0}, f v) =
      f e0 + f e1 + f e2 + f e01 + f e02 + f e12 + f e012 := by
    intro f
    rw [hlist,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    ring
  have heq_sum : w' e01 + w' e02 + w' e12 + w' e012 = 0 := by
    rw [hfin7, hw'e0, hw'e1, hw'e2] at hw'_sum
    simpa [add_assoc] using hw'_sum
  have heq_0 : w' e01 + w' e02 + w' e012 = 0 := by
    have h := hw'_t 0
    rw [hfin7] at h
    rw [show e0.1 0 = 1 by decide, show e1.1 0 = 0 by decide, show e2.1 0 = 0 by decide,
      show e01.1 0 = 1 by decide, show e02.1 0 = 1 by decide, show e12.1 0 = 0 by decide,
      show e012.1 0 = 1 by decide, hw'e0] at h
    simpa [add_assoc] using h
  have heq_1 : w' e01 + w' e12 + w' e012 = 0 := by
    have h := hw'_t 1
    rw [hfin7] at h
    rw [show e0.1 1 = 0 by decide, show e1.1 1 = 1 by decide, show e2.1 1 = 0 by decide,
      show e01.1 1 = 1 by decide, show e02.1 1 = 0 by decide, show e12.1 1 = 1 by decide,
      show e012.1 1 = 1 by decide, hw'e1] at h
    simpa [add_assoc] using h
  have heq_2 : w' e02 + w' e12 + w' e012 = 0 := by
    have h := hw'_t 2
    rw [hfin7] at h
    rw [show e0.1 2 = 0 by decide, show e1.1 2 = 0 by decide, show e2.1 2 = 1 by decide,
      show e01.1 2 = 0 by decide, show e02.1 2 = 1 by decide, show e12.1 2 = 1 by decide,
      show e012.1 2 = 1 by decide, hw'e2] at h
    simpa [add_assoc] using h
  rcases hzero_all (w' e01) (w' e02) (w' e12) (w' e012) heq_sum heq_0 heq_1 heq_2 with
    ⟨h01, h02, h12, h012⟩
  have hw'_u : w' u = 0 := by
    have hu_mem : u ∈ ({e0, e1, e2, e01, e02, e12, e012} : Finset _) := by
      rw [← hlist]; exact Finset.mem_univ u
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu_mem
    rcases hu_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hw'e0
    · exact hw'e1
    · exact hw'e2
    · exact h01
    · exact h02
    · exact h12
    · exact h012
  have hadd := congrArg (fun z : ZMod 2 => z + (w e0 * u.1 0 + w e1 * u.1 1 + w e2 * u.1 2)) hw'_u
  dsimp only [w'] at hadd
  rw [add_assoc, zmod2_add_self, add_zero, zero_add] at hadd
  exact hadd

lemma partition_pairs_bound {α : Type*} [DecidableEq α]
    (P : Finset (Finset α)) (hP_ne : ∀ S ∈ P, S.Nonempty)
    (hP_sum : (∑ S ∈ P, S.card) = 8) (hP_ge : 5 ≤ P.card)
    (pairs : Finset (α × α)) (hpairs_card : pairs.card = 14)
    (hpairs_in : ∀ p ∈ pairs, p.1 ≠ p.2 ∧ ∃ S ∈ P, p.1 ∈ S ∧ p.2 ∈ S) : False := by
  let Big : Finset (α × α) := P.biUnion (fun S => (S ×ˢ S).filter (fun p => p.1 ≠ p.2))
  have hsub : pairs ⊆ Big := by
    intro p hp
    rcases hpairs_in p hp with ⟨hne, S, hSP, h1, h2⟩
    exact Finset.mem_biUnion.mpr ⟨S, hSP, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, h2⟩, hne⟩⟩
  have h14_le : 14 ≤ ∑ S ∈ P, S.card * (S.card - 1) := by
    have h1 := Finset.card_le_card hsub
    rw [hpairs_card] at h1
    have h2 : Big.card ≤ ∑ S ∈ P, ((S ×ˢ S).filter (fun p => p.1 ≠ p.2)).card := Finset.card_biUnion_le
    have h3 : ∀ S ∈ P, ((S ×ˢ S).filter (fun p => p.1 ≠ p.2)).card = S.card * (S.card - 1) := by
      intro S _
      have htot := Finset.card_filter_add_card_filter_not (s := S ×ˢ S)
        (p := fun p : α × α => p.1 ≠ p.2)
      have hdiag : ((S ×ˢ S).filter (fun p => ¬ p.1 ≠ p.2)).card = S.card := by
        refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
        · intro p hp; exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
        · intro p1 hp1 p2 hp2 heq
          have h1eq : p1.1 = p1.2 := not_not.mp (Finset.mem_filter.mp hp1).2
          have h2eq : p2.1 = p2.2 := not_not.mp (Finset.mem_filter.mp hp2).2
          exact Prod.ext heq (h1eq.symm.trans (heq.trans h2eq))
        · intro x hx
          exact ⟨(x, x), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hx⟩, not_not.mpr rfl⟩, rfl⟩
      rw [hdiag, Finset.card_product] at htot
      have hmul : S.card * (S.card - 1) + S.card = S.card * S.card := by
        cases hSc : S.card with
        | zero => simp
        | succ t => simp [Nat.mul_succ, Nat.add_comm]
      omega
    rw [Finset.sum_congr rfl h3] at h2
    omega
  let dS : Finset α → ℕ := fun S => S.card - 1
  have hsum_dS : (∑ S ∈ P, dS S) ≤ 3 := by
    have h1 : (∑ S ∈ P, (dS S + 1)) = 8 := by
      rw [← hP_sum]
      refine Finset.sum_congr rfl fun S hS => ?_
      have hpos := Finset.card_pos.mpr (hP_ne S hS)
      dsimp only [dS]
      omega
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at h1
    omega
  have hsum_sq : (∑ S ∈ P, S.card * (S.card - 1)) ≤ (∑ S ∈ P, dS S) * (∑ S ∈ P, dS S) + ∑ S ∈ P, dS S := by
    have hterm : ∀ S ∈ P, S.card * (S.card - 1) = dS S * dS S + dS S := by
      intro S hS
      have hpos := Finset.card_pos.mpr (hP_ne S hS)
      dsimp only [dS]
      cases hSc : S.card with
      | zero => omega
      | succ t => simp; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    refine Nat.add_le_add_right ?_ _
    have hle_sum : ∀ S ∈ P, dS S * dS S ≤ dS S * (∑ T ∈ P, dS T) := fun S hS =>
      Nat.mul_le_mul_left (dS S) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hS)
    calc
      (∑ S ∈ P, dS S * dS S) ≤ ∑ S ∈ P, dS S * (∑ T ∈ P, dS T) := Finset.sum_le_sum hle_sum
      _ = (∑ S ∈ P, dS S) * (∑ T ∈ P, dS T) := (Finset.sum_mul _ _ _).symm
  have h12 : (∑ S ∈ P, dS S) * (∑ S ∈ P, dS S) + ∑ S ∈ P, dS S ≤ 12 := by
    have hsq : (∑ S ∈ P, dS S) * (∑ S ∈ P, dS S) ≤ 3 * 3 := Nat.mul_le_mul hsum_dS hsum_dS
    omega
  omega

lemma card_fin3_zmod2 : Fintype.card (Fin 3 → ZMod 2) = 8 := by decide

lemma card_u7_zmod2 : (Finset.univ : Finset {u : Fin 3 → ZMod 2 // u ≠ 0}).card = 7 := by decide

lemma fano_cut_graph_false
    (a bp : {u : Fin 3 → ZMod 2 // u ≠ 0} → (Fin 3 → ZMod 2))
    (hab : ∀ u, a u + bp u = u.1)
    (hgood : ∀ g : (Fin 3 → ZMod 2) → ZMod 2,
      (∑ u : {u : Fin 3 → ZMod 2 // u ≠ 0}, (g (a u) + g (bp u))) = 0 ∧
      ∀ t : Fin 3, (∑ u : {u : Fin 3 → ZMod 2 // u ≠ 0}, (g (a u) + g (bp u)) * u.1 t) = 0) :
    False := by
  classical
  let C : ((Fin 3 → ZMod 2) → ZMod 2) →ₗ[ZMod 2] ({u : Fin 3 → ZMod 2 // u ≠ 0} → ZMod 2) :=
    { toFun := fun g u => g (a u) + g (bp u)
      map_add' := fun g1 g2 => by ext u; simp only [Pi.add_apply]; ring
      map_smul' := fun c g => by ext u; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hrange_le : Fintype.card (LinearMap.range C) ≤ 8 := by
    let e0 : {u : Fin 3 → ZMod 2 // u ≠ 0} := ⟨![1, 0, 0], by decide⟩
    let e1 : {u : Fin 3 → ZMod 2 // u ≠ 0} := ⟨![0, 1, 0], by decide⟩
    let e2 : {u : Fin 3 → ZMod 2 // u ≠ 0} := ⟨![0, 0, 1], by decide⟩
    let proj3 : LinearMap.range C → (Fin 3 → ZMod 2) := fun w => ![w.1 e0, w.1 e1, w.1 e2]
    have hinj : Function.Injective proj3 := by
      intro w1 w2 heq
      rcases w1.2 with ⟨g1, hg1⟩
      rcases w2.2 with ⟨g2, hg2⟩
      have h1 := zmod2_fin3_cut_uniqueness w1.1 (hg1 ▸ (hgood g1).1) (hg1 ▸ (hgood g1).2)
      have h2 := zmod2_fin3_cut_uniqueness w2.1 (hg2 ▸ (hgood g2).1) (hg2 ▸ (hgood g2).2)
      have hc0 : w1.1 e0 = w2.1 e0 := congrFun heq 0
      have hc1 : w1.1 e1 = w2.1 e1 := congrFun heq 1
      have hc2 : w1.1 e2 = w2.1 e2 := congrFun heq 2
      apply Subtype.ext; ext u
      rw [h1 u, h2 u, hc0, hc1, hc2]
    have hle := Fintype.card_le_of_injective proj3 hinj
    have h8 := card_fin3_zmod2
    omega
  have hker_ge : 32 ≤ Fintype.card (LinearMap.ker C) := by
    have hrk := LinearMap.finrank_range_add_finrank_ker C
    have hdom : Module.finrank (ZMod 2) ((Fin 3 → ZMod 2) → ZMod 2) = 8 := by
      simp
    have hcard_r : Fintype.card (LinearMap.range C) =
        2 ^ Module.finrank (ZMod 2) (LinearMap.range C) := by
      have h := Fintype.card_congr (Module.finBasis (ZMod 2) (LinearMap.range C)).equivFun.toEquiv
      rw [Fintype.card_fun, ZMod.card 2, Fintype.card_fin] at h
      exact h
    have hcard_k : Fintype.card (LinearMap.ker C) =
        2 ^ Module.finrank (ZMod 2) (LinearMap.ker C) := by
      have h := Fintype.card_congr (Module.finBasis (ZMod 2) (LinearMap.ker C)).equivFun.toEquiv
      rw [Fintype.card_fun, ZMod.card 2, Fintype.card_fin] at h
      exact h
    have hfr_le : Module.finrank (ZMod 2) (LinearMap.range C) ≤ 3 := by
      by_contra hgt
      have h4 : 4 ≤ Module.finrank (ZMod 2) (LinearMap.range C) := by omega
      have hpow : 2 ^ 4 ≤ 2 ^ Module.finrank (ZMod 2) (LinearMap.range C) :=
        Nat.pow_le_pow_right (by omega) h4
      omega
    have hfk_ge : 5 ≤ Module.finrank (ZMod 2) (LinearMap.ker C) := by omega
    have hpow : 2 ^ 5 ≤ 2 ^ Module.finrank (ZMod 2) (LinearMap.ker C) :=
      Nat.pow_le_pow_right (by omega) hfk_ge
    omega
  let cls : (Fin 3 → ZMod 2) → Finset (Fin 3 → ZMod 2) := fun x =>
    Finset.univ.filter (fun y => ∀ g ∈ LinearMap.ker C, g x = g y)
  let P : Finset (Finset (Fin 3 → ZMod 2)) := Finset.univ.image cls
  have hcls_self : ∀ x, x ∈ cls x := fun x => Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ _ => rfl⟩
  have hcls_eq : ∀ x y, y ∈ cls x → cls y = cls x := by
    intro x y hy
    have hxy : ∀ g ∈ LinearMap.ker C, g x = g y := (Finset.mem_filter.mp hy).2
    ext z
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hyz g hg; exact (hxy g hg).trans (hyz g hg)
    · intro hxz g hg; exact (hxy g hg).symm.trans (hxz g hg)
  have hP_ne : ∀ S ∈ P, S.Nonempty := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨x, _, rfl⟩
    exact ⟨x, hcls_self x⟩
  have hP_card_ge : 5 ≤ P.card := by
    let rep : P → (Fin 3 → ZMod 2) := fun S => Classical.choose (hP_ne S.1 S.2)
    have hrep_mem : ∀ S : P, rep S ∈ S.1 := fun S => Classical.choose_spec (hP_ne S.1 S.2)
    let evalP : LinearMap.ker C → (P → ZMod 2) := fun g S => g.1 (rep S)
    have hinj : Function.Injective evalP := by
      intro g1 g2 heq
      apply Subtype.ext; ext x
      let Sx : P := ⟨cls x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩
      have hrx : rep Sx ∈ cls x := hrep_mem Sx
      have h1 : g1.1 x = g1.1 (rep Sx) := (Finset.mem_filter.mp hrx).2 g1.1 g1.2
      have h2 : g2.1 x = g2.1 (rep Sx) := (Finset.mem_filter.mp hrx).2 g2.1 g2.2
      rw [h1, h2]
      exact congrFun heq Sx
    have hle := Fintype.card_le_of_injective evalP hinj
    rw [Fintype.card_fun, ZMod.card 2, Fintype.card_coe] at hle
    by_contra hlt
    have hle4 : P.card ≤ 4 := by omega
    have hpow : 2 ^ P.card ≤ 16 := by
      interval_cases P.card <;> decide
    omega
  have hP_disj : (P : Set (Finset (Fin 3 → ZMod 2))).PairwiseDisjoint id := by
    intro S1 hS1 S2 hS2 hne
    rw [Function.onFun, id_eq, id_eq, Finset.disjoint_left]
    intro z hz1 hz2
    rcases Finset.mem_image.mp hS1 with ⟨x1, _, rfl⟩
    rcases Finset.mem_image.mp hS2 with ⟨x2, _, rfl⟩
    have h1 := hcls_eq x1 z hz1
    have h2 := hcls_eq x2 z hz2
    exact hne (h1.symm.trans h2)
  have hP_sum_card : (∑ S ∈ P, S.card) = 8 := by
    have hunion : P.biUnion id = Finset.univ := by
      ext x
      simp only [Finset.mem_biUnion, id_eq, Finset.mem_univ, iff_true]
      exact ⟨cls x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩, hcls_self x⟩
    have hcard := congrArg Finset.card hunion
    rw [Finset.card_biUnion hP_disj] at hcard
    have h8 : (Finset.univ : Finset (Fin 3 → ZMod 2)).card = 8 := by
      rw [Finset.card_univ]; exact card_fin3_zmod2
    simpa using hcard.trans h8
  have hab_ne : ∀ u, a u ≠ bp u := by
    intro u heq
    have h := hab u
    rw [heq] at h
    have h0 : bp u + bp u = 0 := by ext j; exact zmod2_add_self _
    rw [h0] at h
    exact u.2 h.symm
  have hab_cls : ∀ u, bp u ∈ cls (a u) := by
    intro u
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun g hg => ?_⟩
    have h0 : g (a u) + g (bp u) = 0 := congrFun hg u
    have hadd := congrArg (fun z : ZMod 2 => z + g (bp u)) h0
    rw [add_assoc, zmod2_add_self, add_zero, zero_add] at hadd
    exact hadd
  let pairs1 : Finset ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) :=
    Finset.univ.image (fun u => (a u, bp u))
  let pairs2 : Finset ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) :=
    Finset.univ.image (fun u => (bp u, a u))
  have hp1_card : pairs1.card = 7 := by
    rw [Finset.card_image_of_injective]
    · exact card_u7_zmod2
    · intro u1 u2 heq
      rcases Prod.mk.inj heq with ⟨h1, h2⟩
      apply Subtype.ext
      rw [← hab u1, ← hab u2, h1, h2]
  have hp2_card : pairs2.card = 7 := by
    rw [Finset.card_image_of_injective]
    · exact card_u7_zmod2
    · intro u1 u2 heq
      rcases Prod.mk.inj heq with ⟨h1, h2⟩
      apply Subtype.ext
      rw [← hab u1, ← hab u2, h1, h2]
  have hp_disj : Disjoint pairs1 pairs2 := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rcases Finset.mem_image.mp hp1 with ⟨u1, _, rfl⟩
    rcases Finset.mem_image.mp hp2 with ⟨u2, _, heq⟩
    rcases Prod.mk.inj heq with ⟨h1, h2⟩
    have hu : u1 = u2 := by
      apply Subtype.ext
      rw [← hab u1, ← hab u2, ← h1, ← h2, add_comm]
    subst hu
    exact hab_ne u1 h1.symm
  have hp_card : (pairs1 ∪ pairs2).card = 14 := by
    rw [Finset.card_union_of_disjoint hp_disj, hp1_card, hp2_card]
  have hp_in : ∀ p ∈ pairs1 ∪ pairs2, p.1 ≠ p.2 ∧ ∃ S ∈ P, p.1 ∈ S ∧ p.2 ∈ S := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp1 | hp2
    · rcases Finset.mem_image.mp hp1 with ⟨u, _, rfl⟩
      exact ⟨hab_ne u, cls (a u), Finset.mem_image_of_mem cls (Finset.mem_univ (a u)),
        hcls_self (a u), hab_cls u⟩
    · rcases Finset.mem_image.mp hp2 with ⟨u, _, rfl⟩
      exact ⟨(hab_ne u).symm, cls (a u), Finset.mem_image_of_mem cls (Finset.mem_univ (a u)),
        hab_cls u, hcls_self (a u)⟩
  exact partition_pairs_bound P hP_ne hP_sum_card hP_card_ge (pairs1 ∪ pairs2) hp_card hp_in

lemma no_fano_in_graphic {n m : ℕ} (left right : Fin m → Fin n) (sign start : Fin m → Bool)
    (hmiss : ∀ x, (missedOf left right sign start x).Nonempty)
    (R : Finset (Fin m)) (k : ℕ) (hk : 2 ≤ k) (hRcard : R.card = 2 * k + 1)
    (hno_comp : ∀ i ∈ R, ∀ j ∈ R, i ≠ j →
      ¬ (∀ D ∈ Finset.univ.filter (oddSetPred left right sign), i ∈ D ↔ j ∉ D))
    (hge : ∀ D ∈ Finset.univ.filter (oddSetPred left right sign), k ≤ (D ∩ R).card) :
    False := by
  classical
  let W := Finset.univ.filter (oddSetPred left right sign)
  rcases variance_miracle left right sign start hmiss R k (by omega) hRcard hno_comp hge with
    ⟨hRsubU, hdich, ⟨D_all, hDall, hRsubDall⟩, hsep, _⟩
  have hDall' := (oddSetPred_iff left right sign D_all).mp (Finset.mem_filter.mp hDall).2
  let Seven : Submodule (ZMod 2) (Fin m → ZMod 2) :=
    { carrier := {d | (incMat left right).transpose.mulVec d = 0 ∧
        dotProduct d (fun i => bx (sign i)) = 0}
      zero_mem' := ⟨Matrix.mulVec_zero _, zero_dotProduct _⟩, add_mem' := fun {u v} hu hv =>
        ⟨by rw [Matrix.mulVec_add, hu.1, hv.1, add_zero],
         by rw [add_dotProduct, hu.2, hv.2, add_zero]⟩
      smul_mem' := fun a {u} hu =>
        ⟨by rw [Matrix.mulVec_smul, hu.1, smul_zero],
         by rw [smul_dotProduct, hu.2, smul_zero]⟩ }
  let resR : (Fin m → ZMod 2) →ₗ[ZMod 2] (R → ZMod 2) :=
    { toFun := fun d i => d i.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let V : Submodule (ZMod 2) (R → ZMod 2) := Submodule.map resR Seven
  have hV_wt : ∀ v : V, v.1 = 0 ∨ (Finset.univ.filter (fun i : R => v.1 i = 1)).card = k + 1 := by
    intro v
    rcases v.2 with ⟨d, hd, hdv⟩
    let D := supp (ind D_all + d)
    have hDW : D ∈ W := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, (oddSetPred_iff left right sign D).mpr ?_⟩
      rw [ind_supp]
      exact ⟨by rw [Matrix.mulVec_add, hDall'.1, hd.1, add_zero],
        by rw [add_dotProduct, hDall'.2, hd.2, add_zero]⟩
    have hcount_eq : (Finset.univ.filter (fun i : R => v.1 i = 1)).card + (D ∩ R).card = R.card := by
      have hDR_eq : (D ∩ R).card = (Finset.univ.filter (fun i : R => v.1 i = 0)).card := by
        refine Finset.card_bij (fun i hi => ⟨i, (Finset.mem_inter.mp hi).2⟩) ?_ ?_ ?_
        · intro i hi
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have hiD : i ∈ D := (Finset.mem_inter.mp hi).1
          have hiR : i ∈ R := (Finset.mem_inter.mp hi).2
          have h1 : (ind D_all + d) i = 1 := (Finset.mem_filter.mp hiD).2
          have hda : ind D_all i = 1 := by simp [ind, hRsubDall hiR]
          rw [Pi.add_apply, hda] at h1
          have hdi : d i = 0 := by
            rcases zmod2_zero_or_one (d i) with hz | ho
            · exact hz
            · rw [ho] at h1; exact absurd h1 (by decide)
          have := congrFun hdv ⟨i, hiR⟩
          simpa [resR, ← this] using hdi
        · intro i1 _ i2 _ heq
          exact congrArg Subtype.val heq
        · intro i hi
          have hvi0 : v.1 i = 0 := (Finset.mem_filter.mp hi).2
          have hdi0 : d i.1 = 0 := by
            have hEq : d i.1 = v.1 i := congrFun hdv i
            rw [hEq]
            exact hvi0
          have hiD : i.1 ∈ D := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            rw [Pi.add_apply, show ind D_all i.1 = 1 by simp [ind, hRsubDall i.2], hdi0, add_zero]
          exact ⟨i.1, Finset.mem_inter.mpr ⟨hiD, i.2⟩, rfl⟩
      rw [hDR_eq]
      have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset R))
        (p := fun i : R => v.1 i = 1)
      have hneg : Finset.univ.filter (fun i : R => ¬ v.1 i = 1) =
          Finset.univ.filter (fun i : R => v.1 i = 0) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases zmod2_zero_or_one (v.1 i) with hz | ho
        · simp [hz]
        · simp [ho]
      rw [hneg] at htot
      simpa using htot
    rcases hdich D hDW with hk_eq | hsub
    · right; omega
    · left
      have hDRcard : (D ∩ R).card = R.card := by rw [Finset.inter_eq_right.mpr hsub]
      have h0 : (Finset.univ.filter (fun i : R => v.1 i = 1)).card = 0 := by omega
      ext i
      rcases zmod2_zero_or_one (v.1 i) with hz | ho
      · exact hz
      · exfalso
        have hmem : i ∈ Finset.univ.filter (fun j : R => v.1 j = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho⟩
        have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
        omega
  have hV_coord_ex : ∀ i : R, ∃ v : V, v.1 i = 1 := by
    intro i
    rcases exists_not_mem_W left right sign start hmiss i.1 with ⟨D0, hD0, hiD0⟩
    have hD0' := (oddSetPred_iff left right sign D0).mp (Finset.mem_filter.mp hD0).2
    let d := ind D_all + ind D0
    have hd : d ∈ Seven := ⟨by rw [Matrix.mulVec_add, hDall'.1, hD0'.1, add_zero],
      by rw [add_dotProduct, hDall'.2, hD0'.2, zmod2_add_self]⟩
    refine ⟨⟨resR d, ⟨d, hd, rfl⟩⟩, ?_⟩
    simp only [resR, LinearMap.coe_mk, AddHom.coe_mk, d, Pi.add_apply, ind,
      hRsubDall i.2, hiD0, ↓reduceIte, add_zero]
  have hV_coord_half : ∀ i : R, 2 * (Finset.univ.filter (fun v : V => v.1 i = 1)).card =
      Fintype.card V := by
    intro i
    rcases hV_coord_ex i with ⟨v0, hv0⟩
    have hbij : (Finset.univ.filter (fun v : V => v.1 i = 1)).card =
        (Finset.univ.filter (fun v : V => ¬ v.1 i = 1)).card := by
      refine Finset.card_bij (fun v _ => v + v0) ?_ ?_ ?_
      · intro v hv
        have hvi : v.1 i = 1 := (Finset.mem_filter.mp hv).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        change ¬ (v.1 i + v0.1 i = 1)
        rw [hvi, hv0, zmod2_add_self]; decide
      · intro v1 _ v2 _ heq
        have h := congrArg (fun z : V => z + v0) heq
        have hvv : ∀ z : V, z + v0 + v0 = z := fun z => by
          apply Subtype.ext; ext j
          change z.1 j + v0.1 j + v0.1 j = z.1 j
          rw [add_assoc, zmod2_add_self, add_zero]
        rw [hvv v1, hvv v2] at h
        exact h
      · intro v hv
        have hne : v.1 i ≠ 1 := (Finset.mem_filter.mp hv).2
        have hvi0 : v.1 i = 0 := by
          rcases zmod2_zero_or_one (v.1 i) with hz | ho
          · exact hz
          · exact absurd ho hne
        refine ⟨v + v0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · change v.1 i + v0.1 i = 1
          rw [hvi0, hv0, zero_add]
        · apply Subtype.ext; ext j
          change v.1 j + v0.1 j + v0.1 j = v.1 j
          rw [add_assoc, zmod2_add_self, add_zero]
    have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
      (p := fun v : V => v.1 i = 1)
    rw [Finset.card_univ] at htot
    omega
  have hV_card : Fintype.card V = 2 * k + 2 := by
    have hsum1 : 2 * (∑ v : V, (Finset.univ.filter (fun i : R => v.1 i = 1)).card) =
        R.card * Fintype.card V := by
      have hswap : (∑ v : V, (Finset.univ.filter (fun i : R => v.1 i = 1)).card) =
          ∑ i : R, (Finset.univ.filter (fun v : V => v.1 i = 1)).card := by
        have h1 : ∀ v : V, (Finset.univ.filter (fun i : R => v.1 i = 1)).card =
            ∑ i : R, if v.1 i = 1 then 1 else 0 := fun _ => by simp
        have h2 : ∀ i : R, (Finset.univ.filter (fun v : V => v.1 i = 1)).card =
            ∑ v : V, if v.1 i = 1 then 1 else 0 := fun _ => by simp
        rw [Finset.sum_congr rfl fun v _ => h1 v, Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => (h2 i).symm
      rw [hswap, Finset.mul_sum]
      calc
        (∑ i : R, 2 * (Finset.univ.filter (fun v : V => v.1 i = 1)).card)
            = ∑ _i : R, Fintype.card V := Finset.sum_congr rfl fun i _ => hV_coord_half i
        _ = R.card * Fintype.card V := by simp
    have hsum2 : (∑ v : V, (Finset.univ.filter (fun i : R => v.1 i = 1)).card) =
        (Fintype.card V - 1) * (k + 1) := by
      have h0 : (0 : V) ∈ (Finset.univ : Finset V) := Finset.mem_univ 0
      rw [← Finset.add_sum_erase Finset.univ _ h0]
      have hz : (Finset.univ.filter (fun i : R => (0 : V).1 i = 1)).card = 0 := by
        have hemp : Finset.univ.filter (fun i : R => (0 : V).1 i = 1) = ∅ := by
          ext i; simp
        rw [hemp, Finset.card_empty]
      rw [hz, zero_add]
      calc
        (∑ v ∈ Finset.univ.erase (0 : V), (Finset.univ.filter (fun i : R => v.1 i = 1)).card)
            = ∑ _v ∈ Finset.univ.erase (0 : V), (k + 1) := by
          refine Finset.sum_congr rfl fun v hv => ?_
          have hne0 : v.1 ≠ 0 := fun h => (Finset.ne_of_mem_erase hv) (Subtype.ext h)
          exact (hV_wt v).resolve_left hne0
        _ = (Fintype.card V - 1) * (k + 1) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem h0, Finset.card_univ, smul_eq_mul]
    have hVpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨0⟩
    rw [hsum2, hRcard] at hsum1
    have hcast : ((Fintype.card V - 1 : ℕ) : ℤ) = (Fintype.card V : ℤ) - 1 := by omega
    zify at hsum1
    rw [hcast] at hsum1
    nlinarith
  let r := Module.finrank (ZMod 2) V
  let b := Module.finBasis (ZMod 2) V
  have h2r : 2 ^ r = Fintype.card V := by
    have hcard := Fintype.card_congr b.equivFun.toEquiv
    rw [Fintype.card_fun, ZMod.card 2, Fintype.card_fin] at hcard
    exact hcard.symm
  have hr3 : 3 ≤ r := by
    by_contra hlt
    have hle2 : r ≤ 2 := by omega
    have hpow : 2 ^ r ≤ 4 := by
      interval_cases r <;> decide
    omega
  have hb_pre : ∀ t : Fin r, ∃ d ∈ Seven, resR d = (b t).1 := fun t => (b t).2
  let bd : Fin r → (Fin m → ZMod 2) := fun t => Classical.choose (hb_pre t)
  have hbd_mem : ∀ t : Fin r, bd t ∈ Seven := fun t => (Classical.choose_spec (hb_pre t)).1
  have hbd_eq : ∀ t : Fin r, resR (bd t) = (b t).1 := fun t => (Classical.choose_spec (hb_pre t)).2
  let slope : R → (Fin r → ZMod 2) := fun i t => (b t).1 i
  have hslope_ne0 : ∀ i : R, slope i ≠ 0 := by
    intro i h0
    rcases hV_coord_ex i with ⟨v, hvi⟩
    have hv_eq : v = ∑ t : Fin r, b.repr v t • b t := (b.sum_repr v).symm
    have hval : v.1 i = ∑ t : Fin r, b.repr v t * (b t).1 i := by
      have h1 := congrArg (fun z : V => z.1 i) hv_eq
      simp only [Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at h1
      exact h1
    have hzero : v.1 i = 0 := by
      rw [hval]
      refine Finset.sum_eq_zero fun t _ => ?_
      have ht : (b t).1 i = 0 := congrFun h0 t
      rw [ht, mul_zero]
    rw [hvi] at hzero
    exact absurd hzero (by decide)
  have hslope_inj : Function.Injective slope := by
    intro i j heq
    by_contra hne
    have hne_val : i.1 ≠ j.1 := fun h => hne (Subtype.ext h)
    rcases hsep i.1 i.2 j.1 j.2 hne_val with ⟨D, hD, hdiff⟩
    have hD' := (oddSetPred_iff left right sign D).mp (Finset.mem_filter.mp hD).2
    let d := ind D_all + ind D
    have hd : d ∈ Seven := ⟨by rw [Matrix.mulVec_add, hDall'.1, hD'.1, add_zero],
      by rw [add_dotProduct, hDall'.2, hD'.2, zmod2_add_self]⟩
    let v : V := ⟨resR d, ⟨d, hd, rfl⟩⟩
    have hv_eq : v = ∑ t : Fin r, b.repr v t • b t := (b.sum_repr v).symm
    have hvi : v.1 i = ∑ t : Fin r, b.repr v t * slope i t := by
      have h1 := congrArg (fun z : V => z.1 i) hv_eq
      simp only [Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at h1
      exact h1
    have hvj : v.1 j = ∑ t : Fin r, b.repr v t * slope j t := by
      have h1 := congrArg (fun z : V => z.1 j) hv_eq
      simp only [Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at h1
      exact h1
    have hsame : v.1 i = v.1 j := by rw [hvi, hvj, heq]
    simp only [v, resR, LinearMap.coe_mk, AddHom.coe_mk, d, Pi.add_apply, ind,
      hRsubDall i.2, hRsubDall j.2, ↓reduceIte] at hsame
    by_cases hiD : i.1 ∈ D <;> by_cases hjD : j.1 ∈ D
    · exact hdiff ⟨fun _ => hjD, fun _ => hiD⟩
    · simp [hiD, hjD] at hsame
    · simp [hiD, hjD] at hsame
    · exact hdiff ⟨fun h => absurd h hiD, fun h => absurd h hjD⟩
  have hslope_surj : ∀ w : Fin r → ZMod 2, w ≠ 0 → ∃ i : R, slope i = w := by
    let T : Finset (Fin r → ZMod 2) := Finset.univ.erase 0
    have hsub : Finset.univ.image slope ⊆ T := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨i, _, rfl⟩
      exact Finset.mem_erase.mpr ⟨hslope_ne0 i, Finset.mem_univ _⟩
    have hcard_img : (Finset.univ.image slope).card = T.card := by
      rw [Finset.card_image_of_injective _ hslope_inj, Finset.card_univ, Fintype.card_coe,
        Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, Fintype.card_fun,
        ZMod.card 2, Fintype.card_fin, h2r, hV_card, hRcard]
      omega
    have heqT : Finset.univ.image slope = T :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    intro w hw
    have hwT : w ∈ Finset.univ.image slope := by
      rw [heqT]; exact Finset.mem_erase.mpr ⟨hw, Finset.mem_univ _⟩
    rcases Finset.mem_image.mp hwT with ⟨i, _, hi⟩
    exact ⟨i, hi⟩
  let pad : (Fin 3 → ZMod 2) → (Fin r → ZMod 2) := fun u t =>
    if h : t.val < 3 then u ⟨t.val, h⟩ else 0
  have hpad_ne0 : ∀ u : {u : Fin 3 → ZMod 2 // u ≠ 0}, pad u.1 ≠ 0 := by
    intro u h0
    apply u.2
    ext s
    have hs : s.val < r := by have := s.2; omega
    have hval := congrFun h0 ⟨s.val, hs⟩
    simpa [pad, s.2] using hval
  let fR : {u : Fin 3 → ZMod 2 // u ≠ 0} → R := fun u =>
    Classical.choose (hslope_surj (pad u.1) (hpad_ne0 u))
  have hfR_slope : ∀ u : {u : Fin 3 → ZMod 2 // u ≠ 0}, slope (fR u) = pad u.1 := fun u =>
    Classical.choose_spec (hslope_surj (pad u.1) (hpad_ne0 u))
  let f : {u : Fin 3 → ZMod 2 // u ≠ 0} → Fin m := fun u => (fR u).1
  have hf_inj : Function.Injective f := by
    intro u1 u2 heq
    have hR_eq : fR u1 = fR u2 := Subtype.ext heq
    have hp : pad u1.1 = pad u2.1 := by rw [← hfR_slope u1, ← hfR_slope u2, hR_eq]
    apply Subtype.ext
    ext s
    have hs : s.val < r := by have := s.2; omega
    have hval := congrFun hp ⟨s.val, hs⟩
    simpa [pad, s.2] using hval
  have hex_x : ∀ j : Fin 3, ∃ x : Fin n → ZMod 2,
      (∀ u : {u : Fin 3 → ZMod 2 // u ≠ 0}, (incMat left right).mulVec x (f u) = u.1 j) ∧
      (∀ e : Fin m, (∀ u : {u : Fin 3 → ZMod 2 // u ≠ 0}, f u ≠ e) →
        (incMat left right).mulVec x e = 0) := by
    intro j
    let rhs : Fin m → ZMod 2 := fun e =>
      if h : ∃ u : {u : Fin 3 → ZMod 2 // u ≠ 0}, f u = e then (Classical.choose h).1 j else 0
    have hrhs_f : ∀ u : {u : Fin 3 → ZMod 2 // u ≠ 0}, rhs (f u) = u.1 j := by
      intro u
      have hex : ∃ v : {u : Fin 3 → ZMod 2 // u ≠ 0}, f v = f u := ⟨u, rfl⟩
      simp only [rhs, hex, ↓reduceDIte]
      have hEq : Classical.choose hex = u := hf_inj (Classical.choose_spec hex)
      rw [hEq]
    have hrhs_out : ∀ e : Fin m, (∀ u : {u : Fin 3 → ZMod 2 // u ≠ 0}, f u ≠ e) → rhs e = 0 := by
      intro e hno
      dsimp only [rhs]
      split_ifs with h
      · rcases h with ⟨u, hu⟩; exact absurd hu (hno u)
      · rfl
    have hdot_eq : ∀ c : Fin m → ZMod 2,
        dotProduct c rhs = ∑ u : {u : Fin 3 → ZMod 2 // u ≠ 0}, c (f u) * u.1 j := by
      intro c
      simp only [dotProduct]
      let F7 : Finset (Fin m) := Finset.univ.image f
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun e : Fin m => e ∈ F7)]
      have h0 : (∑ e ∈ Finset.univ.filter (fun e : Fin m => ¬ e ∈ F7), c e * rhs e) = 0 := by
        refine Finset.sum_eq_zero fun e he => ?_
        have hnot : e ∉ F7 := (Finset.mem_filter.mp he).2
        have hno : ∀ u, f u ≠ e := fun u hu => hnot (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, hu⟩)
        rw [hrhs_out e hno, mul_zero]
      rw [h0, add_zero]
      have hfilt : Finset.univ.filter (fun e : Fin m => e ∈ F7) = F7 := by ext e; simp
      rw [hfilt, Finset.sum_image (fun u1 _ u2 _ h => hf_inj h)]
      refine Finset.sum_congr rfl fun u _ => by rw [hrhs_f u]
    have horth_even : ∀ d ∈ Seven, dotProduct d rhs = 0 := by
      intro d hd
      rw [hdot_eq d]
      let v : V := ⟨resR d, ⟨d, hd, rfl⟩⟩
      let α : Fin r → ZMod 2 := b.repr v
      let α3 : Fin 3 → ZMod 2 := fun s => α ⟨s.val, by have := s.2; omega⟩
      have hdf : ∀ u : {u : Fin 3 → ZMod 2 // u ≠ 0}, d (f u) = dotProduct α3 u.1 := by
        intro u
        have hv_eq : v = ∑ t : Fin r, α t • b t := (b.sum_repr v).symm
        have hval : v.1 (fR u) = ∑ t : Fin r, α t * slope (fR u) t := by
          have h1 := congrArg (fun z : V => z.1 (fR u)) hv_eq
          simp only [Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply,
            smul_eq_mul] at h1
          exact h1
        change v.1 (fR u) = dotProduct α3 u.1
        rw [hval, hfR_slope u]
        simp only [dotProduct]
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t : Fin r => t.val < 3)]
        have h0 : (∑ t ∈ Finset.univ.filter (fun t : Fin r => ¬ t.val < 3), α t * pad u.1 t) = 0 := by
          refine Finset.sum_eq_zero fun t ht => ?_
          have hnt : ¬ t.val < 3 := (Finset.mem_filter.mp ht).2
          simp [pad, hnt]
        rw [h0, add_zero]
        refine Finset.sum_bij (fun t ht => ⟨t.val, (Finset.mem_filter.mp ht).2⟩)
          (fun _ _ => Finset.mem_univ _)
          (fun t1 _ t2 _ heq => Fin.ext (congrArg (fun x : Fin 3 => x.val) heq))
          (fun s _ => ⟨⟨s.val, by have := s.2; omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, s.2⟩, rfl⟩)
          (fun t ht => by
            have hlt : t.val < 3 := (Finset.mem_filter.mp ht).2
            simp [α3, pad, hlt])
      have hterm : ∀ u : {u : Fin 3 → ZMod 2 // u ≠ 0},
          d (f u) * u.1 j = dotProduct α3 u.1 * dotProduct (Pi.single j (1 : ZMod 2)) u.1 := by
        intro u
        rw [hdf u]
        congr 1
        simp [dotProduct, Pi.single_apply]
      rw [Finset.sum_congr rfl fun u _ => hterm u]
      have hfull := zmod2_fin3_sum_dot_mul α3 (Pi.single j (1 : ZMod 2))
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : Fin 3 → ZMod 2))] at hfull
      have hz0 : dotProduct α3 (0 : Fin 3 → ZMod 2) * dotProduct (Pi.single j (1 : ZMod 2)) 0 = 0 := by
        simp
      rw [hz0, zero_add] at hfull
      rw [← hfull]
      refine Finset.sum_bij (fun u _ => u.1)
        (fun u _ => Finset.mem_erase.mpr ⟨u.2, Finset.mem_univ _⟩)
        (fun u1 _ u2 _ heq => Subtype.ext heq)
        (fun w hw => ⟨⟨w, Finset.ne_of_mem_erase hw⟩, Finset.mem_univ _, rfl⟩)
        (fun _ _ => rfl)
    have horth_Dall : dotProduct (ind D_all) rhs = 0 := by
      rw [hdot_eq (ind D_all)]
      have hterm : ∀ u : {u : Fin 3 → ZMod 2 // u ≠ 0},
          ind D_all (f u) * u.1 j = dotProduct (Pi.single j (1 : ZMod 2)) u.1 := by
        intro u
        have hmem : f u ∈ D_all := hRsubDall (fR u).2
        simp [ind, hmem, dotProduct, Pi.single_apply]
      rw [Finset.sum_congr rfl fun u _ => hterm u]
      have hfull := zmod2_fin3_sum_dot (Pi.single j (1 : ZMod 2))
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : Fin 3 → ZMod 2))] at hfull
      have hz0 : dotProduct (Pi.single j (1 : ZMod 2)) (0 : Fin 3 → ZMod 2) = 0 := by simp
      rw [hz0, zero_add] at hfull
      rw [← hfull]
      refine Finset.sum_bij (fun u _ => u.1)
        (fun u _ => Finset.mem_erase.mpr ⟨u.2, Finset.mem_univ _⟩)
        (fun u1 _ u2 _ heq => Subtype.ext heq)
        (fun w hw => ⟨⟨w, Finset.ne_of_mem_erase hw⟩, Finset.mem_univ _, rfl⟩)
        (fun _ _ => rfl)
    have hfred := fredholm_zmod2 (incMat left right) rhs (fun c hc => by
      rcases zmod2_zero_or_one (dotProduct c (fun i => bx (sign i))) with h0 | h1
      · exact horth_even c ⟨hc, h0⟩
      · have hd : c + ind D_all ∈ Seven :=
          ⟨by rw [Matrix.mulVec_add, hc, hDall'.1, add_zero],
           by rw [add_dotProduct, h1, hDall'.2, zmod2_add_self]⟩
        have hsum := horth_even (c + ind D_all) hd
        rw [add_dotProduct, horth_Dall, add_zero] at hsum
        exact hsum)
    rcases hfred with ⟨x, hx⟩
    exact ⟨x, fun u => by rw [hx, hrhs_f u], fun e hno => by rw [hx, hrhs_out e hno]⟩
  let xs : Fin 3 → (Fin n → ZMod 2) := fun j => Classical.choose (hex_x j)
  have hxs_f : ∀ j u, (incMat left right).mulVec (xs j) (f u) = u.1 j := fun j =>
    (Classical.choose_spec (hex_x j)).1
  have hxs_out : ∀ j e, (∀ u, f u ≠ e) → (incMat left right).mulVec (xs j) e = 0 := fun j =>
    (Classical.choose_spec (hex_x j)).2
  let Φ : Fin n → (Fin 3 → ZMod 2) := fun v j => xs j v
  have hΦ_f : ∀ u : {u : Fin 3 → ZMod 2 // u ≠ 0},
      Φ (left (f u)) + Φ (right (f u)) = u.1 := by
    intro u; ext j
    have h := hxs_f j u
    rw [incMat_mulVec] at h
    exact h
  have hΦ_out : ∀ e : Fin m, (∀ u : {u : Fin 3 → ZMod 2 // u ≠ 0}, f u ≠ e) →
      Φ (left e) = Φ (right e) := by
    intro e hno; ext j
    have h := hxs_out j e hno
    rw [incMat_mulVec] at h
    have hadd := congrArg (fun z : ZMod 2 => z + xs j (right e)) h
    rw [add_assoc, zmod2_add_self, add_zero, zero_add] at hadd
    exact hadd
  let C : ((Fin 3 → ZMod 2) → ZMod 2) →ₗ[ZMod 2] ({u : Fin 3 → ZMod 2 // u ≠ 0} → ZMod 2) :=
    { toFun := fun g u => g (Φ (left (f u))) + g (Φ (right (f u)))
      map_add' := fun g1 g2 => by ext u; simp only [Pi.add_apply]; ring
      map_smul' := fun a g => by ext u; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hC_good : ∀ g : (Fin 3 → ZMod 2) → ZMod 2,
      (∑ u : {u : Fin 3 → ZMod 2 // u ≠ 0}, C g u) = 0 ∧
      ∀ t : Fin 3, (∑ u : {u : Fin 3 → ZMod 2 // u ≠ 0}, C g u * u.1 t) = 0 := by
    intro g
    let yg : Fin n → ZMod 2 := fun v => g (Φ v)
    have hyg_out : ∀ e : Fin m, (∀ u, f u ≠ e) → (incMat left right).mulVec yg e = 0 := by
      intro e hno
      rw [incMat_mulVec]
      dsimp only [yg]
      rw [hΦ_out e hno, zmod2_add_self]
    have hdot_yg : ∀ c : Fin m → ZMod 2,
        dotProduct c ((incMat left right).mulVec yg) =
        ∑ u : {u : Fin 3 → ZMod 2 // u ≠ 0}, c (f u) * C g u := by
      intro c
      simp only [dotProduct]
      let F7 : Finset (Fin m) := Finset.univ.image f
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun e : Fin m => e ∈ F7)]
      have h0 : (∑ e ∈ Finset.univ.filter (fun e : Fin m => ¬ e ∈ F7),
          c e * (incMat left right).mulVec yg e) = 0 := by
        refine Finset.sum_eq_zero fun e he => ?_
        have hnot : e ∉ F7 := (Finset.mem_filter.mp he).2
        have hno : ∀ u, f u ≠ e := fun u hu => hnot (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, hu⟩)
        rw [hyg_out e hno, mul_zero]
      rw [h0, add_zero]
      have hfilt : Finset.univ.filter (fun e : Fin m => e ∈ F7) = F7 := by ext e; simp
      rw [hfilt, Finset.sum_image (fun u1 _ u2 _ h => hf_inj h)]
      refine Finset.sum_congr rfl fun u _ => by
        rw [incMat_mulVec]
        rfl
    constructor
    · have h0 := dotProduct_incMat_mulVec left right (ind D_all) yg hDall'.1
      rw [hdot_yg (ind D_all)] at h0
      have hterm : ∀ u : {u : Fin 3 → ZMod 2 // u ≠ 0}, ind D_all (f u) * C g u = C g u := by
        intro u
        have hmem : f u ∈ D_all := hRsubDall (fR u).2
        simp [ind, hmem]
      rw [Finset.sum_congr rfl fun u _ => hterm u] at h0
      exact h0
    · intro t
      let tr : Fin r := ⟨t.val, by have := t.2; omega⟩
      have h0 := dotProduct_incMat_mulVec left right (bd tr) yg (hbd_mem tr).1
      rw [hdot_yg (bd tr)] at h0
      have hterm : ∀ u : {u : Fin 3 → ZMod 2 // u ≠ 0}, bd tr (f u) * C g u = C g u * u.1 t := by
        intro u
        have hbd_u : bd tr (f u) = u.1 t := by
          have h1 := congrFun (hbd_eq tr) (fR u)
          have h2 := congrFun (hfR_slope u) tr
          simpa [resR, slope, pad, tr, t.2] using h1.trans h2
        rw [hbd_u, mul_comm]
      rw [Finset.sum_congr rfl fun u _ => hterm u] at h0
      exact h0
  exact fano_cut_graph_false (fun u => Φ (left (f u))) (fun u => Φ (right (f u))) hΦ_f hC_good

end PEqualNP.Outside.L_pcx_280_aux

open PEqualNP.Outside.L_pcx_280_aux

theorem PEqualNP.Outside.L_pcx_280 :
∀ (n m : ℕ) (left right : Fin m → Fin n) (sign start : Fin m → Bool),
  let oddSet := fun D : Finset (Fin m) =>
    Odd ((D.filter (fun edge => sign edge = true)).card) ∧
    ∀ v : Fin n, Even ((D.filter (fun tail => left tail = v)).card +
      (D.filter (fun head => right head = v)).card)
  let W := Finset.univ.filter oddSet
  let faults := fun x : Fin n → Bool =>
    Finset.univ.filter (fun idx => x (right idx) ≠ (x (left idx) ^^ sign idx))
  let missed := fun y : Fin n → Bool =>
    (faults y).filter (fun idx => y (left idx) = start idx)
  let fixed := fun mate : Fin m → Fin m => Finset.univ.filter (fun pos => mate pos = pos)
  let valid := fun mate : Fin m → Fin m => Function.Involutive mate ∧
    ∀ idx, mate idx ≠ idx → ∃ word, faults word = {idx, mate idx} ∧
      missed word = {idx} ∧ missed (fun site => !(word site)) = {mate idx}
  let best := fun loss : ℕ => IsLeast {k : ℕ | ∃ mate, valid mate ∧ (fixed mate).card = k} loss
  (∀ x, (missed x).Nonempty) → ∀ g : ℕ, m = 2*g+1 → (∀ D ∈ W, g ≤ D.card) →
    W.Nonempty ∧
    (((Finset.univ \ W.biUnion id).card = 1 ∧ (∀ D ∈ W, D.card = g) ∧ best 1) ∨
     (W.biUnion id = Finset.univ ∧ (∀ D ∈ W, D.card = g ∨ D.card = g+1) ∧
      2*(W.filter (fun subset => subset.card = g+1)).card = W.card ∧ best 1) ∨
     (W.biUnion id = Finset.univ ∧ (∀ D ∈ W, D.card = g ∨ D.card = g+2) ∧
      4*(W.filter (fun subset => subset.card = g+2)).card = W.card ∧ best 3 ∧
      ∀ mate, valid mate → (fixed mate).card = 3 →
        (∃ word, faults word = fixed mate) ∧
        ∀ y, faults y ⊆ fixed mate → faults y = fixed mate)) := by
  intro n m left right sign start oddSet W faults missed fixed valid best hmiss g hm hminD
  have hWne : W.Nonempty := W_nonempty left right sign start hmiss
  refine ⟨hWne, ?_⟩
  rcases exists_min_validMate left right sign start with ⟨mate0, hval0, hmin0⟩
  let R := fixedOf mate0
  let P0 := (Finset.univ.filter (fun i : Fin m => i < mate0 i)).card
  have hinv_eq : 2 * P0 + R.card = 2 * g + 1 := by
    rw [← hm]; exact involution_card_eq mate0 hval0.1
  have hR_odd : R.card % 2 = 1 := by omega
  let k := R.card / 2
  have hRcard : R.card = 2 * k + 1 := by omega
  have hg_eq : g = P0 + k := by omega
  have hD_card0 : ∀ D ∈ W, D.card = P0 + (D ∩ R).card := fun D hD =>
    validMate_D_card left right sign start hmiss mate0 hval0 hD
  have hDR_ge : ∀ D ∈ W, k ≤ (D ∩ R).card := by
    intro D hD
    have h1 := hminD D hD
    have h2 := hD_card0 D hD
    omega
  have hnonR_U : ∀ i : Fin m, i ∉ R → i ∈ W.biUnion id := by
    intro i hi
    have hne : mate0 i ≠ i := fun heq => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩)
    exact validMate_nonfixed_mem_biUnion left right sign start hmiss mate0 hval0 hne
  have hbest_ge1 : ∀ a ∈ {t : ℕ | ∃ mate, valid mate ∧ (fixed mate).card = t}, 1 ≤ a := by
    rintro a ⟨mate, hval, rfl⟩
    have h : 2 * (Finset.univ.filter (fun i : Fin m => i < mate i)).card + (fixed mate).card =
        2 * g + 1 := by
      rw [← hm]; exact involution_card_eq mate hval.1
    omega
  by_cases hk0 : k = 0
  · have hR1 : R.card = 1 := by omega
    rcases Finset.card_eq_one.mp hR1 with ⟨r0, hr0⟩
    have hbest1 : best 1 := ⟨⟨mate0, hval0, hR1⟩, hbest_ge1⟩
    by_cases hr0U : r0 ∈ W.biUnion id
    · right; left
      have hUuniv : W.biUnion id = Finset.univ := by
        ext i
        simp only [Finset.mem_univ, iff_true]
        by_cases hi : i = r0
        · subst hi; exact hr0U
        · exact hnonR_U i (by rw [hr0]; simp [hi])
      have hDc : ∀ D ∈ W, D.card = g ∨ D.card = g + 1 := by
        intro D hD
        have h1 := hD_card0 D hD
        rw [hr0] at h1
        by_cases hmem : r0 ∈ D
        · right
          have hinter : (D ∩ {r0}).card = 1 := by
            have : D ∩ {r0} = {r0} := by ext x; simp [hmem]
            rw [this, Finset.card_singleton]
          omega
        · left
          have hinter : (D ∩ {r0}).card = 0 := by
            have : D ∩ {r0} = ∅ := by ext x; simp [hmem]
            rw [this, Finset.card_empty]
          omega
      have hfilt_eq : W.filter (fun subset => subset.card = g + 1) =
          W.filter (fun D => r0 ∈ D) := by
        ext D
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hDW, hcard⟩
          refine ⟨hDW, ?_⟩
          by_contra hnot
          have h1 := hD_card0 D hDW
          rw [hr0] at h1
          have hinter : (D ∩ {r0}).card = 0 := by
            have : D ∩ {r0} = ∅ := by ext x; simp [hnot]
            rw [this, Finset.card_empty]
          omega
        · rintro ⟨hDW, hmem⟩
          refine ⟨hDW, ?_⟩
          have h1 := hD_card0 D hDW
          rw [hr0] at h1
          have hinter : (D ∩ {r0}).card = 1 := by
            have : D ∩ {r0} = {r0} := by ext x; simp [hmem]
            rw [this, Finset.card_singleton]
          omega
      rw [hfilt_eq]
      exact ⟨hUuniv, hDc, W_half_coord left right sign start hmiss hr0U, hbest1⟩
    · left
      have hsdiff : Finset.univ \ W.biUnion id = {r0} := by
        ext i
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hnot
          by_contra hne
          exact hnot (hnonR_U i (by rw [hr0]; simp [hne]))
        · rintro rfl; exact hr0U
      have hDc : ∀ D ∈ W, D.card = g := by
        intro D hD
        have hnot : r0 ∉ D := fun hmem => hr0U (Finset.mem_biUnion.mpr ⟨D, hD, hmem⟩)
        have h1 := hD_card0 D hD
        rw [hr0] at h1
        have hinter : (D ∩ {r0}).card = 0 := by
          have : D ∩ {r0} = ∅ := by ext x; simp [hnot]
          rw [this, Finset.card_empty]
        omega
      exact ⟨by rw [hsdiff, Finset.card_singleton], hDc, hbest1⟩
  · have hk1 : 1 ≤ k := by omega
    by_cases hk_eq1 : k = 1
    · right; right
      have hR3 : R.card = 3 := by omega
      have hno_comp : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → ¬ (∀ D ∈ W, i ∈ D ↔ j ∉ D) := fun i hi j hj hij =>
        min_validMate_no_comp left right sign start hmiss mate0 hval0 hmin0 hi hj hij
      rcases variance_miracle left right sign start hmiss R 1 (le_refl 1) hR3 hno_comp
        (fun D hD => by have := hDR_ge D hD; omega) with
        ⟨hRsubU, hdich, _, _, hcount⟩
      have hUuniv : W.biUnion id = Finset.univ := by
        ext i
        simp only [Finset.mem_univ, iff_true]
        by_cases hi : i ∈ R
        · exact hRsubU hi
        · exact hnonR_U i hi
      have hDc : ∀ D ∈ W, D.card = g ∨ D.card = g + 2 := by
        intro D hD
        have h1 := hD_card0 D hD
        rcases hdich D hD with h1c | hsub
        · left; omega
        · right
          have hinter : (D ∩ R).card = 3 := by rw [Finset.inter_eq_right.mpr hsub, hR3]
          omega
      have hfilt_eq : W.filter (fun subset => subset.card = g + 2) =
          W.filter (fun D => R ⊆ D) := by
        ext D
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hDW, hcard⟩
          refine ⟨hDW, ?_⟩
          rcases hdich D hDW with h1c | hsub
          · have h1 := hD_card0 D hDW; omega
          · exact hsub
        · rintro ⟨hDW, hsub⟩
          refine ⟨hDW, ?_⟩
          have h1 := hD_card0 D hDW
          have hinter : (D ∩ R).card = 3 := by rw [Finset.inter_eq_right.mpr hsub, hR3]
          omega
      have hbest3 : best 3 := by
        refine ⟨⟨mate0, hval0, hR3⟩, ?_⟩
        rintro a ⟨mate, hval, rfl⟩
        have hle := hmin0 mate hval
        change R.card ≤ (fixed mate).card at hle
        omega
      refine ⟨hUuniv, hDc, ?_, hbest3, ?_⟩
      · rw [hfilt_eq]
        simpa [hR3] using hcount
      · intro mate hval hfix3
        let Rm := fixedOf mate
        have hRm3 : Rm.card = 3 := hfix3
        have hmin_m : ∀ mate' : Fin m → Fin m, validMate left right sign start mate' →
            Rm.card ≤ (fixedOf mate').card := by
          intro mate' hval'
          have hle := hmin0 mate' hval'
          change R.card ≤ (fixedOf mate').card at hle
          omega
        have hno_comp_m : ∀ i ∈ Rm, ∀ j ∈ Rm, i ≠ j → ¬ (∀ D ∈ W, i ∈ D ↔ j ∉ D) :=
          fun i hi j hj hij =>
            min_validMate_no_comp left right sign start hmiss mate hval hmin_m hi hj hij
        have hinv_m : 2 * (Finset.univ.filter (fun i : Fin m => i < mate i)).card + Rm.card =
            2 * g + 1 := by
          rw [← hm]; exact involution_card_eq mate hval.1
        have hDm_ge : ∀ D ∈ W, 1 ≤ (D ∩ Rm).card := by
          intro D hD
          have h1 : D.card = (Finset.univ.filter (fun i : Fin m => i < mate i)).card + (D ∩ Rm).card :=
            validMate_D_card left right sign start hmiss mate hval hD
          have h2 := hminD D hD
          omega
        rcases variance_miracle left right sign start hmiss Rm 1 (le_refl 1) hfix3 hno_comp_m hDm_ge with
          ⟨_, hdich_m, ⟨D0, hD0, _⟩, _, _⟩
        have hD0' := (oddSetPred_iff left right sign D0).mp (Finset.mem_filter.mp hD0).2
        have hodd_Rm : ∀ D ∈ W, dotProduct (ind D) (ind Rm) = 1 := by
          intro D hD
          have hsum : dotProduct (ind D) (ind Rm) = ((D ∩ Rm).card : ZMod 2) := by
            rw [Finset.card_eq_sum_ones, Nat.cast_sum]
            simp only [dotProduct, ind]
            calc
              (∑ i : Fin m, (if i ∈ D then (1 : ZMod 2) else 0) * (if i ∈ Rm then 1 else 0))
                  = ∑ i : Fin m, if i ∈ D ∩ Rm then (1 : ZMod 2) else 0 := by
                refine Finset.sum_congr rfl fun i _ => by
                  by_cases h1 : i ∈ D <;> by_cases h2 : i ∈ Rm <;> simp [h1, h2]
              _ = ∑ _i ∈ D ∩ Rm, (1 : ZMod 2) := by
                rw [← Finset.sum_filter]
                have hf : Finset.univ.filter (fun i : Fin m => i ∈ D ∩ Rm) = D ∩ Rm := by ext i; simp
                rw [hf]
              _ = ∑ _i ∈ D ∩ Rm, ((1 : ℕ) : ZMod 2) := by simp
          rw [hsum]
          rcases hdich_m D hD with h1 | hsub
          · rw [h1]; decide
          · rw [Finset.inter_eq_right.mpr hsub, hfix3]; decide
        constructor
        · refine (exists_faults_iff left right sign Rm).mpr fun c hc => ?_
          rcases zmod2_zero_or_one (dotProduct c (fun i => bx (sign i))) with h0 | h1
          · rw [h0]
            let D1 := supp (ind D0 + c)
            have hD1 : D1 ∈ W := by
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ _, (oddSetPred_iff left right sign D1).mpr ?_⟩
              rw [ind_supp]
              exact ⟨by rw [Matrix.mulVec_add, hD0'.1, hc, add_zero],
                by rw [add_dotProduct, hD0'.2, h0, add_zero]⟩
            have he1 := hodd_Rm D1 hD1
            have he0 := hodd_Rm D0 hD0
            rw [ind_supp, add_dotProduct, he0] at he1
            rcases zmod2_zero_or_one (dotProduct c (ind Rm)) with hz | ho
            · exact hz
            · rw [ho] at he1; exact absurd he1 (by decide)
          · rw [h1]
            have hmem : supp c ∈ W := by
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ _, (oddSetPred_iff left right sign (supp c)).mpr ?_⟩
              rw [ind_supp]
              exact ⟨hc, h1⟩
            have he := hodd_Rm (supp c) hmem
            rw [ind_supp] at he
            exact he
        · intro y hsub
          have hge2 : 2 ≤ (faults y).card := two_le_card_faults left right sign start hmiss y
          have hle3 : (faults y).card ≤ 3 := by
            have := Finset.card_le_card hsub
            omega
          by_cases hc2 : (faults y).card = 2
          · exfalso
            rcases Finset.card_eq_two.mp hc2 with ⟨i, j, hij, hfy⟩
            have hi : i ∈ Rm := hsub (by rw [hfy]; simp)
            have hj : j ∈ Rm := hsub (by rw [hfy]; simp)
            have hcomp : ∀ D ∈ W, i ∈ D ↔ j ∉ D := by
              intro D hD
              have hD' := (oddSetPred_iff left right sign D).mp (Finset.mem_filter.mp hD).2
              have horth := (exists_faults_iff left right sign {i, j}).mp ⟨y, hfy⟩ (ind D) hD'.1
              rw [hD'.2] at horth
              have hsum : dotProduct (ind D) (ind ({i, j} : Finset (Fin m))) = ind D i + ind D j := by
                simp only [dotProduct, ind, Finset.mem_insert, Finset.mem_singleton]
                rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t : Fin m => t = i ∨ t = j)]
                have h0 : (∑ t ∈ Finset.univ.filter (fun t : Fin m => ¬ (t = i ∨ t = j)),
                    (if t ∈ D then (1 : ZMod 2) else 0) * (if t = i ∨ t = j then 1 else 0)) = 0 := by
                  refine Finset.sum_eq_zero fun t ht => ?_
                  have hnot := (Finset.mem_filter.mp ht).2
                  simp [hnot]
                rw [h0, add_zero]
                have hf : Finset.univ.filter (fun t : Fin m => t = i ∨ t = j) = {i, j} := by
                  ext t; simp
                rw [hf, Finset.sum_pair hij]
                simp
              rw [hsum] at horth
              by_cases hiD : i ∈ D <;> by_cases hjD : j ∈ D
              · simp [ind, hiD, hjD] at horth
              · simp [hiD, hjD]
              · simp [hiD, hjD]
              · simp [ind, hiD, hjD] at horth
            exact hno_comp_m i hi j hj hij hcomp
          · exact Finset.eq_of_subset_of_card_le hsub (by omega)
    · exfalso
      have hk2 : 2 ≤ k := by omega
      have hno_comp : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → ¬ (∀ D ∈ W, i ∈ D ↔ j ∉ D) := fun i hi j hj hij =>
        min_validMate_no_comp left right sign start hmiss mate0 hval0 hmin0 hi hj hij
      exact no_fano_in_graphic left right sign start hmiss R k hk2 hRcard hno_comp hDR_ge

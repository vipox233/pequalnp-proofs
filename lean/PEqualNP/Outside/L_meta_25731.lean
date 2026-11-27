import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25731

-- `typ`, `emb`, `card_filter_typ`, `card_filter_typ_perm` are copied from
-- PEqualNP/Outside/L_meta_25714.lean (Apache-2.0), with attribution.

def typ (n b : ℕ) (hn : 0 < n) (i : Fin (n * b)) : Fin n :=
  ⟨i.val % n, Nat.mod_lt _ hn⟩

lemma mul_add_lt_mul {n b : ℕ} (u : Fin n) (m : Fin b) : u.val + m.val * n < n * b := by
  have h1 : m.val + 1 ≤ b := m.isLt
  have h2 : (m.val + 1) * n ≤ b * n := Nat.mul_le_mul_right n h1
  have h3 : u.val + m.val * n < n + m.val * n := Nat.add_lt_add_right u.isLt _
  rw [Nat.add_mul, Nat.one_mul, Nat.add_comm (m.val * n) n, Nat.mul_comm b n] at h2
  exact Nat.lt_of_lt_of_le h3 h2

def emb (n b : ℕ) (u : Fin n) (m : Fin b) : Fin (n * b) :=
  ⟨u.val + m.val * n, mul_add_lt_mul u m⟩

lemma typ_emb (n b : ℕ) (hn : 0 < n) (u : Fin n) (m : Fin b) :
    typ n b hn (emb n b u m) = u := by
  apply Fin.ext
  simp only [typ, emb, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt u.isLt]

lemma emb_injective (n b : ℕ) (hn : 0 < n) (u : Fin n) :
    Function.Injective (emb n b u) := by
  intro m₁ m₂ h
  have hv : u.val + m₁.val * n = u.val + m₂.val * n := congrArg Fin.val h
  have hm : m₁.val * n = m₂.val * n := Nat.add_left_cancel hv
  exact Fin.ext (Nat.eq_of_mul_eq_mul_right hn hm)

lemma filter_typ_eq (n b : ℕ) (hn : 0 < n) (u : Fin n) :
    Finset.univ.filter (fun x : Fin (n * b) => typ n b hn x = u) =
      Finset.univ.image (emb n b u) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h
    refine ⟨⟨x.val / n, Nat.div_lt_of_lt_mul x.isLt⟩, ?_⟩
    apply Fin.ext
    have hval : x.val % n = u.val := congrArg Fin.val h
    change u.val + (x.val / n) * n = x.val
    rw [← hval, Nat.mul_comm (x.val / n) n]
    exact Nat.mod_add_div x.val n
  · rintro ⟨m, rfl⟩
    exact typ_emb n b hn u m

lemma card_filter_typ (n b : ℕ) (hn : 0 < n) (u : Fin n) :
    (Finset.univ.filter (fun x : Fin (n * b) => typ n b hn x = u)).card = b := by
  rw [filter_typ_eq, Finset.card_image_of_injective _ (emb_injective n b hn u),
    Finset.card_univ, Fintype.card_fin]

lemma card_filter_typ_perm (n b : ℕ) (hn : 0 < n) (π : Equiv.Perm (Fin (n * b))) (v : Fin n) :
    (Finset.univ.filter (fun x : Fin (n * b) => typ n b hn (π x) = v)).card = b := by
  have himg :
      (Finset.univ.filter (fun x : Fin (n * b) => typ n b hn (π x) = v)).image π =
        Finset.univ.filter (fun y : Fin (n * b) => typ n b hn y = v) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨π.symm y, by simpa using hy, π.apply_symm_apply y⟩
  rw [← Finset.card_image_of_injective _ π.injective, himg, card_filter_typ]

-- Record types: row type, column type, ternary pool word, sign bit.
abbrev TT (n q : ℕ) := Fin n × Fin n × (Fin q → Fin 3) × Bool

-- Normalized pool state of one copy: 0 = absent (or both), 1 = row-only, 2 = column-only.
def enc (a c : Bool) : Fin 3 := if a then (if c then 0 else 1) else (if c then 2 else 0)

lemma enc_agree : ∀ a1 c1 a2 c2 : Bool, enc a1 c1 = enc a2 c2 → (a1 || c2) = (a2 || c1) := by
  decide

lemma fin3_agree : ∀ a c : Fin 3, decide (a = 1 ∨ c = 2) = decide (c = 1 ∨ a = 2) → a = c := by
  decide

lemma bool_fwd : ∀ G1 G2 a b c d v : Bool,
    Bool.xor G1 G2 ≠ Bool.xor (Bool.xor a c) (Bool.xor b d) →
    v ≠ Bool.xor G1 (Bool.xor a d) ∨ v ≠ Bool.xor G2 (Bool.xor b c) := by
  decide

lemma bool_bwd : ∀ g1 g2 a b : Bool, Bool.xor g1 (Bool.xor a false) = false →
    Bool.xor g2 (Bool.xor b false) = true →
    Bool.xor g1 g2 ≠ Bool.xor a b ∧ Bool.xor g2 g1 ≠ Bool.xor b a := by
  decide

lemma sum_fiber {α T : Type*} [Fintype α] [Fintype T] [DecidableEq T] (τ : α → T) (g : T → ℕ) :
    ∑ x, g (τ x) = ∑ t, (Finset.univ.filter (fun x => τ x = t)).card * g t := by
  rw [← Finset.sum_fiberwise' Finset.univ τ g]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.sum_const, smul_eq_mul]

lemma sum_fiber2 {α T : Type*} [Fintype α] [Fintype T] [DecidableEq T] (τ : α → T)
    (F : T → T → ℕ) :
    ∑ x, ∑ y, F (τ x) (τ y) = ∑ s, ∑ t, (Finset.univ.filter (fun x => τ x = s)).card *
      (Finset.univ.filter (fun x => τ x = t)).card * F s t := by
  calc ∑ x, ∑ y, F (τ x) (τ y)
      = ∑ s, (Finset.univ.filter (fun x => τ x = s)).card * ∑ y, F s (τ y) :=
        sum_fiber τ (fun s => ∑ y, F s (τ y))
    _ = ∑ s, (Finset.univ.filter (fun x => τ x = s)).card *
          ∑ t, (Finset.univ.filter (fun x => τ x = t)).card * F s t := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [sum_fiber τ (F s)]
    _ = _ := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [Nat.mul_assoc]

lemma sum_sigma_fin {T : Type*} [Fintype T] (w : T → ℕ) (g : T → ℕ) :
    ∑ x : (Σ t : T, Fin (w t)), g x.1 = ∑ t, w t * g t := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  show ∑ _y : Fin (w t), g t = w t * g t
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

lemma exists_equiv_fiber {α β ι : Type*} [Fintype α] [Fintype β] [DecidableEq ι]
    (f : α → ι) (g : β → ι)
    (h : ∀ i, Fintype.card {a // f a = i} = Fintype.card {b // g b = i}) :
    ∃ e : α ≃ β, ∀ a, g (e a) = f a := by
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight fun i => Fintype.equivOfCardEq (h i)).trans
      (Equiv.sigmaFiberEquiv g)), fun a => ?_⟩
  exact (Fintype.equivOfCardEq (h (f a)) ⟨a, rfl⟩).property

lemma pair_cases {α : Type*} [DecidableEq α] {x y x' y' : α}
    (h : ({x, y} : Finset α) = {x', y'}) : (x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x) := by
  have hs := congrArg (fun s : Finset α => (s : Set α)) h
  simp only [Finset.coe_insert, Finset.coe_singleton] at hs
  rcases Set.pair_eq_pair_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h2.symm, h1.symm⟩

lemma fwd (n b q : ℕ) (hn : 0 < n) (G : Fin n → Fin n → Bool) (E : ℕ)
    (π : Equiv.Perm (Fin (n * b))) (rf cf : Fin (n * b) → Bool)
    (R C : Fin q → Finset (Fin (n * b)))
    (out : Finset (Fin (n * b)) → (Fin q → Bool) → Bool)
    (hE : ((Finset.univ : Finset (Fin (n * b) × Fin (n * b))).filter (fun z =>
      out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
        Bool.xor (G (typ n b hn z.1) (typ n b hn (π z.2)))
          (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ E) :
    ∃ w : TT n q → ℕ,
      (∀ i : Fin n, (∑ t : TT n q, if t.1 = i then w t else 0) = b) ∧
      (∀ j : Fin n, (∑ t : TT n q, if t.2.1 = j then w t else 0) = b) ∧
      (∑ s : TT n q, ∑ t : TT n q, if s.2.2.1 = t.2.2.1 ∧
          Bool.xor (G s.1 t.2.1) (G t.1 s.2.1) ≠ Bool.xor s.2.2.2 t.2.2.2
          then w s * w t else 0) ≤ 2 * E := by
  let τ : Fin (n * b) → TT n q := fun l =>
    (typ n b hn l, typ n b hn (π l),
      fun j => enc (decide (l ∈ R j)) (decide (π l ∈ C j)), Bool.xor (rf l) (cf (π l)))
  refine ⟨fun t => (Finset.univ.filter (fun l => τ l = t)).card, ?_, ?_, ?_⟩
  · intro i
    calc (∑ t : TT n q, if t.1 = i then (Finset.univ.filter (fun l => τ l = t)).card else 0)
        = ∑ t : TT n q, (Finset.univ.filter (fun l => τ l = t)).card *
            (if t.1 = i then 1 else 0) := by
          simp only [mul_ite, mul_one, mul_zero]
      _ = ∑ l, (if (τ l).1 = i then 1 else 0) := (sum_fiber τ _).symm
      _ = (Finset.univ.filter (fun x : Fin (n * b) => typ n b hn x = i)).card :=
          (Finset.card_filter _ _).symm
      _ = b := card_filter_typ n b hn i
  · intro i
    calc (∑ t : TT n q, if t.2.1 = i then (Finset.univ.filter (fun l => τ l = t)).card else 0)
        = ∑ t : TT n q, (Finset.univ.filter (fun l => τ l = t)).card *
            (if t.2.1 = i then 1 else 0) := by
          simp only [mul_ite, mul_one, mul_zero]
      _ = ∑ l, (if (τ l).2.1 = i then 1 else 0) := (sum_fiber τ _).symm
      _ = (Finset.univ.filter (fun x : Fin (n * b) => typ n b hn (π x) = i)).card :=
          (Finset.card_filter _ _).symm
      _ = b := card_filter_typ_perm n b hn π i
  · let Err : Finset (Fin (n * b) × Fin (n * b)) :=
      (Finset.univ : Finset (Fin (n * b) × Fin (n * b))).filter (fun z =>
        out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
          Bool.xor (G (typ n b hn z.1) (typ n b hn (π z.2)))
            (Bool.xor (rf z.1) (cf (π z.2))))
    have hsub : (Finset.univ : Finset (Fin (n * b) × Fin (n * b))).filter (fun z =>
        (τ z.1).2.2.1 = (τ z.2).2.2.1 ∧
          Bool.xor (G (τ z.1).1 (τ z.2).2.1) (G (τ z.2).1 (τ z.1).2.1) ≠
            Bool.xor (τ z.1).2.2.2 (τ z.2).2.2.2) ⊆ Err ∪ Err.image Prod.swap := by
      rintro ⟨x, y⟩ hz
      obtain ⟨hw, hG⟩ := (Finset.mem_filter.mp hz).2
      have hobs : (fun j => decide (x ∈ R j ∨ π y ∈ C j)) =
          (fun j => decide (y ∈ R j ∨ π x ∈ C j)) := by
        funext j
        have hwj : enc (decide (x ∈ R j)) (decide (π x ∈ C j)) =
            enc (decide (y ∈ R j)) (decide (π y ∈ C j)) := congrFun hw j
        rw [Bool.decide_or, Bool.decide_or]
        exact enc_agree _ _ _ _ hwj
      rcases bool_fwd (G (typ n b hn x) (typ n b hn (π y))) (G (typ n b hn y) (typ n b hn (π x)))
          (rf x) (rf y) (cf (π x)) (cf (π y))
          (out {x, y} (fun j => decide (x ∈ R j ∨ π y ∈ C j))) hG with h1 | h2
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
      · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(y, x), ?_, rfl⟩)
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have hpair : ({y, x} : Finset (Fin (n * b))) = {x, y} := Finset.pair_comm y x
        change out {y, x} (fun j => decide (y ∈ R j ∨ π x ∈ C j)) ≠ _
        rw [hpair, ← hobs]
        exact h2
    calc (∑ s : TT n q, ∑ t : TT n q, if s.2.2.1 = t.2.2.1 ∧
          Bool.xor (G s.1 t.2.1) (G t.1 s.2.1) ≠ Bool.xor s.2.2.2 t.2.2.2
          then (Finset.univ.filter (fun l => τ l = s)).card *
            (Finset.univ.filter (fun l => τ l = t)).card else 0)
        = ∑ s : TT n q, ∑ t : TT n q, (Finset.univ.filter (fun l => τ l = s)).card *
            (Finset.univ.filter (fun l => τ l = t)).card *
            (if s.2.2.1 = t.2.2.1 ∧
              Bool.xor (G s.1 t.2.1) (G t.1 s.2.1) ≠ Bool.xor s.2.2.2 t.2.2.2 then 1 else 0) := by
          simp only [mul_ite, mul_one, mul_zero]
      _ = ∑ x, ∑ y, (if (τ x).2.2.1 = (τ y).2.2.1 ∧
              Bool.xor (G (τ x).1 (τ y).2.1) (G (τ y).1 (τ x).2.1) ≠
                Bool.xor (τ x).2.2.2 (τ y).2.2.2 then 1 else 0) :=
          (sum_fiber2 τ (fun s t => if s.2.2.1 = t.2.2.1 ∧
              Bool.xor (G s.1 t.2.1) (G t.1 s.2.1) ≠ Bool.xor s.2.2.2 t.2.2.2 then 1 else 0)).symm
      _ = ((Finset.univ : Finset (Fin (n * b) × Fin (n * b))).filter (fun z =>
            (τ z.1).2.2.1 = (τ z.2).2.2.1 ∧
              Bool.xor (G (τ z.1).1 (τ z.2).2.1) (G (τ z.2).1 (τ z.1).2.1) ≠
                Bool.xor (τ z.1).2.2.2 (τ z.2).2.2.2)).card := by
          rw [Finset.card_filter, Fintype.sum_prod_type]
      _ ≤ (Err ∪ Err.image Prod.swap).card := Finset.card_le_card hsub
      _ ≤ Err.card + (Err.image Prod.swap).card := Finset.card_union_le _ _
      _ ≤ E + E := Nat.add_le_add hE (Finset.card_image_le.trans hE)
      _ = 2 * E := (Nat.two_mul E).symm

lemma bwd (n b q : ℕ) (hn : 0 < n) (G : Fin n → Fin n → Bool) (E : ℕ) (w : TT n q → ℕ)
    (h1 : ∀ i : Fin n, (∑ t : TT n q, if t.1 = i then w t else 0) = b)
    (h2 : ∀ j : Fin n, (∑ t : TT n q, if t.2.1 = j then w t else 0) = b)
    (h3 : (∑ s : TT n q, ∑ t : TT n q, if s.2.2.1 = t.2.2.1 ∧
          Bool.xor (G s.1 t.2.1) (G t.1 s.2.1) ≠ Bool.xor s.2.2.2 t.2.2.2
          then w s * w t else 0) ≤ 2 * E) :
    ∃ (π : Equiv.Perm (Fin (n * b))) (rf cf : Fin (n * b) → Bool)
      (R C : Fin q → Finset (Fin (n * b)))
      (out : Finset (Fin (n * b)) → (Fin q → Bool) → Bool),
      ((Finset.univ : Finset (Fin (n * b) × Fin (n * b))).filter (fun z =>
        out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
          Bool.xor (G (typ n b hn z.1) (typ n b hn (π z.2)))
            (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ E := by
  classical
  have hX1 : ∀ i, Fintype.card {x : (Σ t : TT n q, Fin (w t)) // x.1.1 = i} =
      Fintype.card {l : Fin (n * b) // typ n b hn l = i} := by
    intro i
    rw [Fintype.card_subtype, Fintype.card_subtype, card_filter_typ n b hn i, Finset.card_filter]
    calc ∑ x : (Σ t : TT n q, Fin (w t)), (if x.1.1 = i then 1 else 0)
        = ∑ t : TT n q, w t * (if t.1 = i then 1 else 0) :=
          sum_sigma_fin w (fun t => if t.1 = i then 1 else 0)
      _ = ∑ t : TT n q, (if t.1 = i then w t else 0) := by simp only [mul_ite, mul_one, mul_zero]
      _ = b := h1 i
  have hX2 : ∀ i, Fintype.card {x : (Σ t : TT n q, Fin (w t)) // x.1.2.1 = i} =
      Fintype.card {l : Fin (n * b) // typ n b hn l = i} := by
    intro i
    rw [Fintype.card_subtype, Fintype.card_subtype, card_filter_typ n b hn i, Finset.card_filter]
    calc ∑ x : (Σ t : TT n q, Fin (w t)), (if x.1.2.1 = i then 1 else 0)
        = ∑ t : TT n q, w t * (if t.2.1 = i then 1 else 0) :=
          sum_sigma_fin w (fun t => if t.2.1 = i then 1 else 0)
      _ = ∑ t : TT n q, (if t.2.1 = i then w t else 0) := by
          simp only [mul_ite, mul_one, mul_zero]
      _ = b := h2 i
  obtain ⟨ρ, hρ⟩ := exists_equiv_fiber (fun x : (Σ t : TT n q, Fin (w t)) => x.1.1)
    (typ n b hn) hX1
  obtain ⟨κ, hκ⟩ := exists_equiv_fiber (fun x : (Σ t : TT n q, Fin (w t)) => x.1.2.1)
    (typ n b hn) hX2
  let π : Equiv.Perm (Fin (n * b)) := ρ.symm.trans κ
  let τ : Fin (n * b) → TT n q := fun l => (ρ.symm l).1
  have hτ1 : ∀ l, typ n b hn l = (τ l).1 := by
    intro l
    have := hρ (ρ.symm l)
    rwa [Equiv.apply_symm_apply] at this
  have hτ2 : ∀ l, typ n b hn (π l) = (τ l).2.1 := fun l => hκ (ρ.symm l)
  have hcnt : ∀ t, (Finset.univ.filter (fun l => τ l = t)).card = w t := by
    intro t
    rw [Finset.card_filter]
    calc ∑ l, (if τ l = t then 1 else 0)
        = ∑ x : (Σ s : TT n q, Fin (w s)), (if x.1 = t then 1 else 0) :=
          Equiv.sum_comp ρ.symm (fun x : (Σ s : TT n q, Fin (w s)) => if x.1 = t then 1 else 0)
      _ = ∑ s : TT n q, w s * (if s = t then 1 else 0) :=
          sum_sigma_fin w (fun s => if s = t then 1 else 0)
      _ = w t := by simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true]
  let rf : Fin (n * b) → Bool := fun l => (τ l).2.2.2
  let cf : Fin (n * b) → Bool := fun _ => false
  let R : Fin q → Finset (Fin (n * b)) := fun j => Finset.univ.filter (fun l => (τ l).2.2.1 j = 1)
  let C : Fin q → Finset (Fin (n * b)) := fun j =>
    Finset.univ.filter (fun m => (τ (π.symm m)).2.2.1 j = 2)
  let obsF : Fin (n * b) → Fin (n * b) → Fin q → Bool := fun x y j =>
    decide (x ∈ R j ∨ π y ∈ C j)
  let tgt : Fin (n * b) → Fin (n * b) → Bool := fun x y =>
    Bool.xor (G (typ n b hn x) (typ n b hn (π y))) (Bool.xor (rf x) (cf (π y)))
  let out : Finset (Fin (n * b)) → (Fin q → Bool) → Bool := fun S o =>
    decide (∃ x y : Fin (n * b), S = {x, y} ∧ obsF x y = o ∧ tgt x y = true)
  refine ⟨π, rf, cf, R, C, out, ?_⟩
  let Err : Finset (Fin (n * b) × Fin (n * b)) :=
    (Finset.univ : Finset (Fin (n * b) × Fin (n * b))).filter (fun z =>
      out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
        Bool.xor (G (typ n b hn z.1) (typ n b hn (π z.2)))
          (Bool.xor (rf z.1) (cf (π z.2))))
  change Err.card ≤ E
  have hErr : ∀ x y, (x, y) ∈ Err →
      obsF x y = obsF y x ∧ tgt x y = false ∧ tgt y x = true := by
    intro x y h
    have h' : out {x, y} (obsF x y) ≠ tgt x y := (Finset.mem_filter.mp h).2
    cases ht : tgt x y with
    | true =>
      exfalso
      apply h'
      rw [ht]
      exact decide_eq_true ⟨x, y, rfl, rfl, ht⟩
    | false =>
      rw [ht] at h'
      have hout : out {x, y} (obsF x y) = true := by
        cases hv : out {x, y} (obsF x y) with
        | true => rfl
        | false => exact absurd hv h'
      obtain ⟨x', y', hS, ho, htt⟩ := of_decide_eq_true hout
      rcases pair_cases hS with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [ht] at htt
        exact absurd htt Bool.false_ne_true
      · exact ⟨ho.symm, rfl, htt⟩
  have hmemR : ∀ l j, l ∈ R j ↔ (τ l).2.2.1 j = 1 := by
    intro l j
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmemC : ∀ l j, π l ∈ C j ↔ (τ l).2.2.1 j = 2 := by
    intro l j
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
  have htgt : ∀ x y, tgt x y = Bool.xor (G (τ x).1 (τ y).2.1) (Bool.xor (τ x).2.2.2 false) := by
    intro x y
    show Bool.xor (G (typ n b hn x) (typ n b hn (π y))) (Bool.xor (τ x).2.2.2 false) = _
    rw [hτ1 x, hτ2 y]
  have hcond : ∀ x y, (x, y) ∈ Err →
      ((τ x).2.2.1 = (τ y).2.2.1 ∧
        Bool.xor (G (τ x).1 (τ y).2.1) (G (τ y).1 (τ x).2.1) ≠ Bool.xor (τ x).2.2.2 (τ y).2.2.2) ∧
      ((τ y).2.2.1 = (τ x).2.2.1 ∧
        Bool.xor (G (τ y).1 (τ x).2.1) (G (τ x).1 (τ y).2.1) ≠ Bool.xor (τ y).2.2.2 (τ x).2.2.2) := by
    intro x y h
    obtain ⟨ho, hf, htr⟩ := hErr x y h
    have hword : (τ x).2.2.1 = (τ y).2.2.1 := by
      funext j
      have hj : decide (x ∈ R j ∨ π y ∈ C j) = decide (y ∈ R j ∨ π x ∈ C j) := congrFun ho j
      have hj' : decide ((τ x).2.2.1 j = 1 ∨ (τ y).2.2.1 j = 2) =
          decide ((τ y).2.2.1 j = 1 ∨ (τ x).2.2.1 j = 2) := by
        simpa only [hmemR, hmemC] using hj
      exact fin3_agree _ _ hj'
    rw [htgt] at hf htr
    obtain ⟨hA, hB⟩ := bool_bwd _ _ _ _ hf htr
    exact ⟨⟨hword, hA⟩, ⟨hword.symm, hB⟩⟩
  let Bad : Finset (Fin (n * b) × Fin (n * b)) :=
    (Finset.univ : Finset (Fin (n * b) × Fin (n * b))).filter (fun z =>
      (τ z.1).2.2.1 = (τ z.2).2.2.1 ∧
        Bool.xor (G (τ z.1).1 (τ z.2).2.1) (G (τ z.2).1 (τ z.1).2.1) ≠
          Bool.xor (τ z.1).2.2.2 (τ z.2).2.2.2)
  have hBad : Bad.card ≤ 2 * E := by
    calc Bad.card
        = ∑ x, ∑ y, (if (τ x).2.2.1 = (τ y).2.2.1 ∧
              Bool.xor (G (τ x).1 (τ y).2.1) (G (τ y).1 (τ x).2.1) ≠
                Bool.xor (τ x).2.2.2 (τ y).2.2.2 then 1 else 0) := by
          rw [Finset.card_filter, Fintype.sum_prod_type]
      _ = ∑ s : TT n q, ∑ t : TT n q, (Finset.univ.filter (fun l => τ l = s)).card *
            (Finset.univ.filter (fun l => τ l = t)).card *
            (if s.2.2.1 = t.2.2.1 ∧
              Bool.xor (G s.1 t.2.1) (G t.1 s.2.1) ≠ Bool.xor s.2.2.2 t.2.2.2 then 1 else 0) :=
          sum_fiber2 τ (fun s t => if s.2.2.1 = t.2.2.1 ∧
              Bool.xor (G s.1 t.2.1) (G t.1 s.2.1) ≠ Bool.xor s.2.2.2 t.2.2.2 then 1 else 0)
      _ = ∑ s : TT n q, ∑ t : TT n q, if s.2.2.1 = t.2.2.1 ∧
          Bool.xor (G s.1 t.2.1) (G t.1 s.2.1) ≠ Bool.xor s.2.2.2 t.2.2.2
          then w s * w t else 0 := by
          simp only [hcnt, mul_ite, mul_one, mul_zero]
      _ ≤ 2 * E := h3
  have hsub : Err ∪ Err.image Prod.swap ⊆ Bad := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨x, y⟩ := z
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcond x y hz).1⟩
    · obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcond x y hxy).2⟩
  have hdisj : Disjoint Err (Err.image Prod.swap) := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    obtain ⟨⟨x', y'⟩, h2', he⟩ := Finset.mem_image.mp h2
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have a1 := (hErr _ _ h1).2.2
    have a2 := (hErr _ _ h2').2.1
    rw [a1] at a2
    exact absurd a2 (by decide)
  have hcard : Err.card + Err.card ≤ 2 * E := by
    calc Err.card + Err.card = Err.card + (Err.image Prod.swap).card := by
          rw [Finset.card_image_of_injective _ Prod.swap_injective]
      _ = (Err ∪ Err.image Prod.swap).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ Bad.card := Finset.card_le_card hsub
      _ ≤ 2 * E := hBad
  omega

end PEqualNP.Outside.L_meta_25731

theorem PEqualNP.Outside.L_meta_25731 : ∀ (n b q : ℕ) (hn : 0 < n), 0 < b →
  let fits := fun (s : ℕ) (G : Fin s → Fin s → Bool) (budget : ℕ) =>
    ∃ (π : Equiv.Perm (Fin s)) (rf cf : Fin s → Bool) (R C : Fin q → Finset (Fin s))
      (out : Finset (Fin s) → (Fin q → Bool) → Bool),
      ((Finset.univ : Finset (Fin s × Fin s)).filter (fun z =>
        out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
          Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ budget
  let typ := fun label : Fin (n*b) => (⟨label.val % n, Nat.mod_lt _ hn⟩ : Fin n)
  let T := Fin n × Fin n × (Fin q → Fin 3) × Bool
  ∀ (G : Fin n → Fin n → Bool) (E : ℕ),
    fits (n*b) (fun i j => G (typ i) (typ j)) E ↔
      ∃ w : T → ℕ,
        (∀ i : Fin n, (∑ t : T, if t.1 = i then w t else 0) = b) ∧
        (∀ j : Fin n, (∑ t : T, if t.2.1 = j then w t else 0) = b) ∧
        (∑ s : T, ∑ t : T, if s.2.2.1 = t.2.2.1 ∧
          Bool.xor (G s.1 t.2.1) (G t.1 s.2.1) ≠ Bool.xor s.2.2.2 t.2.2.2
          then w s * w t else 0) ≤ 2*E := by
  intro n b q hn _hb fits typ T G E
  constructor
  · rintro ⟨π, rf, cf, R, C, out, hE⟩
    exact PEqualNP.Outside.L_meta_25731.fwd n b q hn G E π rf cf R C out hE
  · rintro ⟨w, h1, h2, h3⟩
    exact PEqualNP.Outside.L_meta_25731.bwd n b q hn G E w h1 h2 h3

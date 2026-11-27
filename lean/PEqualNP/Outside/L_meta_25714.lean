import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod

namespace PEqualNP.Outside.L_meta_25714

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

lemma card_filter_mem_eq {α β : Type*} [DecidableEq β]
    (A : Finset α) (f : α → β) (S : Finset β) (k : ℕ)
    (hf : ∀ y ∈ S, (A.filter (fun x => f x = y)).card = k) :
    (A.filter (fun x => f x ∈ S)).card = S.card * k := by
  have hfib : (A.filter (fun x => f x ∈ S)).card =
      ∑ y ∈ S, ((A.filter (fun x => f x ∈ S)).filter (fun x => f x = y)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => (Finset.mem_filter.mp hx).2)
  rw [hfib]
  have hterm : ∀ y ∈ S,
      ((A.filter (fun x => f x ∈ S)).filter (fun x => f x = y)).card = k := by
    intro y hy
    have heq : (A.filter (fun x => f x ∈ S)).filter (fun x => f x = y) =
        A.filter (fun x => f x = y) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hxA, _⟩, hfx⟩
        exact ⟨hxA, hfx⟩
      · rintro ⟨hxA, hfx⟩
        exact ⟨⟨hxA, hfx ▸ hy⟩, hfx⟩
    rw [heq]
    exact hf y hy
  exact Finset.sum_const_nat hterm

lemma exists_transversal {α : Type*} [DecidableEq α] {n k : ℕ}
    (A : Finset α) (l r : α → Fin n)
    (hl : ∀ u, (A.filter (fun x => l x = u)).card = k + 1)
    (hr : ∀ v, (A.filter (fun x => r x = v)).card = k + 1) :
    ∃ g : Fin n → α,
      (∀ u, g u ∈ A) ∧
      (∀ u, l (g u) = u) ∧
      Function.Injective (fun u => r (g u)) := by
  let t : Fin n → Finset (Fin n) := fun u => (A.filter (fun x => l x = u)).image r
  have hall : ∀ S : Finset (Fin n), S.card ≤ (S.biUnion t).card := by
    intro S
    have h1 : (A.filter (fun x => l x ∈ S)).card = S.card * (k + 1) :=
      card_filter_mem_eq A l S (k + 1) (fun u _ => hl u)
    have h2 : (A.filter (fun x => r x ∈ S.biUnion t)).card = (S.biUnion t).card * (k + 1) :=
      card_filter_mem_eq A r (S.biUnion t) (k + 1) (fun v _ => hr v)
    have hsub : A.filter (fun x => l x ∈ S) ⊆ A.filter (fun x => r x ∈ S.biUnion t) := by
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxA, hxl⟩
      refine Finset.mem_filter.mpr ⟨hxA, Finset.mem_biUnion.mpr ⟨l x, hxl, ?_⟩⟩
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxA, rfl⟩, rfl⟩
    have hle : S.card * (k + 1) ≤ (S.biUnion t).card * (k + 1) := by
      rw [← h1, ← h2]
      exact Finset.card_le_card hsub
    exact Nat.le_of_mul_le_mul_right hle (Nat.succ_pos k)
  obtain ⟨m, hminj, hmmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  have hex : ∀ u : Fin n, ∃ x : α, x ∈ A ∧ l x = u ∧ r x = m u := by
    intro u
    rcases Finset.mem_image.mp (hmmem u) with ⟨x, hx, hrx⟩
    rcases Finset.mem_filter.mp hx with ⟨hxA, hlx⟩
    exact ⟨x, hxA, hlx, hrx⟩
  refine ⟨fun u => Classical.choose (hex u),
    fun u => (Classical.choose_spec (hex u)).1,
    fun u => (Classical.choose_spec (hex u)).2.1, ?_⟩
  intro u₁ u₂ h
  have h1 := (Classical.choose_spec (hex u₁)).2.2
  have h2 := (Classical.choose_spec (hex u₂)).2.2
  exact hminj (h1.symm.trans (h.trans h2))

lemma exists_decomp {α : Type*} [DecidableEq α] {n : ℕ} :
    ∀ (k : ℕ) (A : Finset α) (l r : α → Fin n),
      (∀ u, (A.filter (fun x => l x = u)).card = k) →
      (∀ v, (A.filter (fun x => r x = v)).card = k) →
      ∃ f : Fin k → Fin n → α,
        (∀ t u, f t u ∈ A) ∧
        (∀ t u, l (f t u) = u) ∧
        (∀ t, Function.Injective (fun u => r (f t u))) ∧
        (∀ t₁ t₂ u₁ u₂, f t₁ u₁ = f t₂ u₂ → t₁ = t₂ ∧ u₁ = u₂) := by
  intro k
  induction k with
  | zero =>
    intro A l r _ _
    exact ⟨fun t => Fin.elim0 t, fun t => Fin.elim0 t, fun t => Fin.elim0 t,
      fun t => Fin.elim0 t, fun t₁ => Fin.elim0 t₁⟩
  | succ k ih =>
    intro A l r hl hr
    obtain ⟨g, hgA, hgl, hgr⟩ := exists_transversal A l r hl hr
    let M : Finset α := Finset.univ.image g
    let A' : Finset α := A \ M
    have hl' : ∀ u, (A'.filter (fun x => l x = u)).card = k := by
      intro u
      have heq : A'.filter (fun x => l x = u) = (A.filter (fun x => l x = u)).erase (g u) := by
        ext x
        simp only [A', M, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ,
          true_and, Finset.mem_erase, not_exists]
        constructor
        · rintro ⟨⟨hxA, hnot⟩, hlx⟩
          exact ⟨fun hxeq => hnot u hxeq.symm, hxA, hlx⟩
        · rintro ⟨hne, hxA, hlx⟩
          refine ⟨⟨hxA, ?_⟩, hlx⟩
          intro u' hgu'
          have hu : u' = u := by
            calc u' = l (g u') := (hgl u').symm
            _ = l x := congrArg l hgu'
            _ = u := hlx
          exact hne (hu ▸ hgu'.symm)
      rw [heq, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hgA u, hgl u⟩), hl u]
      exact Nat.add_sub_cancel k 1
    have hr' : ∀ v, (A'.filter (fun x => r x = v)).card = k := by
      intro v
      obtain ⟨u₀, hu₀⟩ := (Finite.injective_iff_surjective.mp hgr) v
      have heq : A'.filter (fun x => r x = v) = (A.filter (fun x => r x = v)).erase (g u₀) := by
        ext x
        simp only [A', M, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ,
          true_and, Finset.mem_erase, not_exists]
        constructor
        · rintro ⟨⟨hxA, hnot⟩, hrx⟩
          exact ⟨fun hxeq => hnot u₀ hxeq.symm, hxA, hrx⟩
        · rintro ⟨hne, hxA, hrx⟩
          refine ⟨⟨hxA, ?_⟩, hrx⟩
          intro u' hgu'
          have hu : u' = u₀ := hgr ((congrArg r hgu').trans (hrx.trans hu₀.symm))
          exact hne (hu ▸ hgu'.symm)
      rw [heq, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hgA u₀, hu₀⟩), hr v]
      exact Nat.add_sub_cancel k 1
    obtain ⟨f', hf'A', hf'l, hf'r, hf'inj⟩ := ih A' l r hl' hr'
    let f : Fin (k + 1) → Fin n → α := Fin.cases g f'
    refine ⟨f, ?_, ?_, ?_, ?_⟩
    · intro t u
      refine Fin.cases ?_ ?_ t
      · exact hgA u
      · intro t'
        exact (Finset.mem_sdiff.mp (hf'A' t' u)).1
    · intro t u
      refine Fin.cases ?_ ?_ t
      · exact hgl u
      · intro t'
        exact hf'l t' u
    · intro t
      refine Fin.cases ?_ ?_ t
      · exact hgr
      · intro t'
        exact hf'r t'
    · intro t₁ t₂ u₁ u₂
      refine Fin.cases ?_ ?_ t₁
      · refine Fin.cases ?_ ?_ t₂
        · intro h0
          have hu : u₁ = u₂ := by
            calc u₁ = l (g u₁) := (hgl u₁).symm
            _ = l (g u₂) := congrArg l h0
            _ = u₂ := hgl u₂
          exact ⟨rfl, hu⟩
        · intro t₂' h0
          have hmemM : f' t₂' u₂ ∈ M := Finset.mem_image.mpr ⟨u₁, Finset.mem_univ _, h0⟩
          exact absurd hmemM (Finset.mem_sdiff.mp (hf'A' t₂' u₂)).2
      · intro t₁'
        refine Fin.cases ?_ ?_ t₂
        · intro h0
          have hmemM : f' t₁' u₁ ∈ M := Finset.mem_image.mpr ⟨u₂, Finset.mem_univ _, h0.symm⟩
          exact absurd hmemM (Finset.mem_sdiff.mp (hf'A' t₁' u₁)).2
        · intro t₂' h0
          obtain ⟨ht, hu⟩ := hf'inj t₁' t₂' u₁ u₂ h0
          exact ⟨congrArg Fin.succ ht, hu⟩

lemma exists_le_div_of_sum_le {b E : ℕ} (hb : 0 < b) (c : Fin b → ℕ)
    (hsum : ∑ t : Fin b, c t ≤ E) : ∃ t : Fin b, c t ≤ E / b := by
  by_contra h
  have hall : ∀ t : Fin b, E / b + 1 ≤ c t := by
    intro t
    have hnot : ¬ c t ≤ E / b := fun hle => h ⟨t, hle⟩
    exact Nat.lt_of_not_ge hnot
  have h1 : b * (E / b + 1) ≤ ∑ t : Fin b, c t := by
    have hconst : ∑ _t : Fin b, (E / b + 1) = b * (E / b + 1) := by
      rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ, Fintype.card_fin]
    rw [← hconst]
    exact Finset.sum_le_sum (fun t _ => hall t)
  have h2 : b * (E / b + 1) ≤ E := Nat.le_trans h1 hsum
  have h3 : E < b * (E / b + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    calc E = b * (E / b) + E % b := (Nat.div_add_mod E b).symm
      _ < b * (E / b) + b := Nat.add_lt_add_left (Nat.mod_lt E hb) (b * (E / b))
  exact Nat.not_lt.mpr h2 h3

def liftFun (n b : ℕ) (hn : 0 < n) (σ : Fin n → Fin n) (x : Fin (n * b)) : Fin (n * b) :=
  emb n b (σ (typ n b hn x)) ⟨x.val / n, Nat.div_lt_of_lt_mul x.isLt⟩

lemma typ_liftFun (n b : ℕ) (hn : 0 < n) (σ : Fin n → Fin n) (x : Fin (n * b)) :
    typ n b hn (liftFun n b hn σ x) = σ (typ n b hn x) :=
  typ_emb n b hn _ _

lemma div_liftFun (n b : ℕ) (hn : 0 < n) (σ : Fin n → Fin n) (x : Fin (n * b)) :
    (liftFun n b hn σ x).val / n = x.val / n := by
  change ((σ (typ n b hn x)).val + (x.val / n) * n) / n = x.val / n
  rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt (σ (typ n b hn x)).isLt, Nat.zero_add]

lemma liftFun_comp (n b : ℕ) (hn : 0 < n) (τ σ : Fin n → Fin n) (x : Fin (n * b)) :
    liftFun n b hn τ (liftFun n b hn σ x) = liftFun n b hn (τ ∘ σ) x := by
  apply Fin.ext
  change (τ (typ n b hn (liftFun n b hn σ x))).val + ((liftFun n b hn σ x).val / n) * n =
    (τ (σ (typ n b hn x))).val + (x.val / n) * n
  rw [typ_liftFun, div_liftFun]

lemma liftFun_id (n b : ℕ) (hn : 0 < n) (x : Fin (n * b)) :
    liftFun n b hn id x = x := by
  apply Fin.ext
  change x.val % n + (x.val / n) * n = x.val
  rw [Nat.mul_comm (x.val / n) n]
  exact Nat.mod_add_div x.val n

def liftPerm (n b : ℕ) (hn : 0 < n) (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n * b)) where
  toFun := liftFun n b hn π
  invFun := liftFun n b hn π.symm
  left_inv x := by
    rw [liftFun_comp]
    have hcomp : (⇑π.symm ∘ ⇑π) = id := funext (fun u => π.symm_apply_apply u)
    rw [hcomp, liftFun_id]
  right_inv x := by
    rw [liftFun_comp]
    have hcomp : (⇑π ∘ ⇑π.symm) = id := funext (fun u => π.apply_symm_apply u)
    rw [hcomp, liftFun_id]

lemma typ_liftPerm (n b : ℕ) (hn : 0 < n) (π : Equiv.Perm (Fin n)) (x : Fin (n * b)) :
    typ n b hn (liftPerm n b hn π x) = π (typ n b hn x) :=
  typ_liftFun n b hn π x

lemma dir1 (n b q : ℕ) (hn : 0 < n) (hb : 0 < b) (G : Fin n → Fin n → Bool) (E : ℕ)
    (π : Equiv.Perm (Fin (n * b))) (rf cf : Fin (n * b) → Bool)
    (R C : Fin q → Finset (Fin (n * b)))
    (out : Finset (Fin (n * b)) → (Fin q → Bool) → Bool)
    (hE : ((Finset.univ : Finset (Fin (n * b) × Fin (n * b))).filter (fun z =>
      out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
        Bool.xor (G (typ n b hn z.1) (typ n b hn (π z.2)))
          (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ E) :
    ∃ (π' : Equiv.Perm (Fin n)) (rf' cf' : Fin n → Bool) (R' C' : Fin q → Finset (Fin n))
      (out' : Finset (Fin n) → (Fin q → Bool) → Bool),
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun z =>
        out' {z.1, z.2} (fun j => decide (z.1 ∈ R' j ∨ π' z.2 ∈ C' j)) ≠
          Bool.xor (G z.1 (π' z.2)) (Bool.xor (rf' z.1) (cf' (π' z.2))))).card ≤ E / b := by
  obtain ⟨f, _, hfl, hfr, hfinj⟩ :=
    exists_decomp b (Finset.univ : Finset (Fin (n * b))) (typ n b hn)
      (fun x => typ n b hn (π x))
      (card_filter_typ n b hn)
      (card_filter_typ_perm n b hn π)
  let πt : Fin b → Equiv.Perm (Fin n) := fun t =>
    Equiv.ofBijective (fun u => typ n b hn (π (f t u)))
      (Finite.injective_iff_bijective.mp (hfr t))
  let rft : Fin b → Fin n → Bool := fun t u => rf (f t u)
  let cft : Fin b → Fin n → Bool := fun t v => cf (π (f t ((πt t).symm v)))
  let Rt : Fin b → Fin q → Finset (Fin n) := fun t j =>
    Finset.univ.filter (fun u => f t u ∈ R j)
  let Ct : Fin b → Fin q → Finset (Fin n) := fun t j =>
    Finset.univ.filter (fun v => π (f t ((πt t).symm v)) ∈ C j)
  let outt : Fin b → Finset (Fin n) → (Fin q → Bool) → Bool := fun t S obs =>
    out (S.image (f t)) obs
  let Err : Finset (Fin (n * b) × Fin (n * b)) :=
    Finset.univ.filter (fun z =>
      out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
        Bool.xor (G (typ n b hn z.1) (typ n b hn (π z.2)))
          (Bool.xor (rf z.1) (cf (π z.2))))
  let Errt : Fin b → Finset (Fin n × Fin n) := fun t =>
    Finset.univ.filter (fun z =>
      outt t {z.1, z.2} (fun j => decide (z.1 ∈ Rt t j ∨ πt t z.2 ∈ Ct t j)) ≠
        Bool.xor (G z.1 (πt t z.2)) (Bool.xor (rft t z.1) (cft t (πt t z.2))))
  let φ : Fin b → Fin n × Fin n → Fin (n * b) × Fin (n * b) := fun t p => (f t p.1, f t p.2)
  have hmem : ∀ t p, p ∈ Errt t ↔ φ t p ∈ Err := by
    intro t p
    simp only [Errt, Err, φ, Finset.mem_filter, Finset.mem_univ, true_and]
    have hobs : (fun j => decide (p.1 ∈ Rt t j ∨ πt t p.2 ∈ Ct t j)) =
        (fun j => decide (f t p.1 ∈ R j ∨ π (f t p.2) ∈ C j)) := by
      funext j
      apply decide_eq_decide.mpr
      simp only [Rt, Ct, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
    have hpair : ({p.1, p.2} : Finset (Fin n)).image (f t) = {f t p.1, f t p.2} := by
      rw [Finset.image_insert, Finset.image_singleton]
    have hπ : πt t p.2 = typ n b hn (π (f t p.2)) := rfl
    have hcf : cft t (πt t p.2) = cf (π (f t p.2)) := by
      simp only [cft, Equiv.symm_apply_apply]
    have hrf : rft t p.1 = rf (f t p.1) := rfl
    have hG : G p.1 (πt t p.2) = G (typ n b hn (f t p.1)) (typ n b hn (π (f t p.2))) := by
      rw [hfl t p.1, hπ]
    change (out (({p.1, p.2} : Finset (Fin n)).image (f t))
        (fun j => decide (p.1 ∈ Rt t j ∨ πt t p.2 ∈ Ct t j)) ≠
        Bool.xor (G p.1 (πt t p.2)) (Bool.xor (rft t p.1) (cft t (πt t p.2)))) ↔ _
    rw [hpair, hobs, hG, hrf, hcf]
  have hφinj : ∀ t, Function.Injective (φ t) := by
    intro t p₁ p₂ h
    have h1 : f t p₁.1 = f t p₂.1 := congrArg Prod.fst h
    have h2 : f t p₁.2 = f t p₂.2 := congrArg Prod.snd h
    exact Prod.ext (hfinj t t p₁.1 p₂.1 h1).2 (hfinj t t p₁.2 p₂.2 h2).2
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin b))
      (fun t => (Errt t).image (φ t)) := by
    intro t₁ _ t₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    rcases Finset.mem_image.mp hz₁ with ⟨p₁, _, rfl⟩
    rcases Finset.mem_image.mp hz₂ with ⟨p₂, _, h⟩
    have h1 : f t₂ p₂.1 = f t₁ p₁.1 := congrArg Prod.fst h
    exact hne (hfinj t₂ t₁ p₂.1 p₁.1 h1).1.symm
  have hsub : Finset.univ.biUnion (fun t => (Errt t).image (φ t)) ⊆ Err := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨t, _, hzt⟩
    rcases Finset.mem_image.mp hzt with ⟨p, hp, rfl⟩
    exact (hmem t p).mp hp
  have hsum : ∑ t : Fin b, (Errt t).card ≤ E := by
    calc ∑ t : Fin b, (Errt t).card
      _ = ∑ t : Fin b, ((Errt t).image (φ t)).card := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        exact (Finset.card_image_of_injective _ (hφinj t)).symm
      _ = (Finset.univ.biUnion (fun t => (Errt t).image (φ t))).card :=
        (Finset.card_biUnion hdisj).symm
      _ ≤ Err.card := Finset.card_le_card hsub
      _ ≤ E := hE
  obtain ⟨t, ht⟩ := exists_le_div_of_sum_le hb (fun t => (Errt t).card) hsum
  exact ⟨πt t, rft t, cft t, Rt t, Ct t, outt t, ht⟩

lemma dir2 (n b q : ℕ) (hn : 0 < n) (G : Fin n → Fin n → Bool) (E : ℕ)
    (π : Equiv.Perm (Fin n)) (rf cf : Fin n → Bool)
    (R C : Fin q → Finset (Fin n))
    (out : Finset (Fin n) → (Fin q → Bool) → Bool)
    (hE : ((Finset.univ : Finset (Fin n × Fin n)).filter (fun z =>
      out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
        Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ E) :
    ∃ (π' : Equiv.Perm (Fin (n * b))) (rf' cf' : Fin (n * b) → Bool)
      (R' C' : Fin q → Finset (Fin (n * b)))
      (out' : Finset (Fin (n * b)) → (Fin q → Bool) → Bool),
      ((Finset.univ : Finset (Fin (n * b) × Fin (n * b))).filter (fun z =>
        out' {z.1, z.2} (fun j => decide (z.1 ∈ R' j ∨ π' z.2 ∈ C' j)) ≠
          Bool.xor (G (typ n b hn z.1) (typ n b hn (π' z.2)))
            (Bool.xor (rf' z.1) (cf' (π' z.2))))).card ≤ b ^ 2 * E := by
  let π' : Equiv.Perm (Fin (n * b)) := liftPerm n b hn π
  let rf' : Fin (n * b) → Bool := fun x => rf (typ n b hn x)
  let cf' : Fin (n * b) → Bool := fun x => cf (typ n b hn x)
  let R' : Fin q → Finset (Fin (n * b)) := fun j =>
    Finset.univ.filter (fun x => typ n b hn x ∈ R j)
  let C' : Fin q → Finset (Fin (n * b)) := fun j =>
    Finset.univ.filter (fun x => typ n b hn x ∈ C j)
  let out' : Finset (Fin (n * b)) → (Fin q → Bool) → Bool := fun S obs =>
    out (S.image (typ n b hn)) obs
  refine ⟨π', rf', cf', R', C', out', ?_⟩
  let ErrBase : Finset (Fin n × Fin n) :=
    Finset.univ.filter (fun z =>
      out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
        Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))
  let ErrCopy : Finset (Fin (n * b) × Fin (n * b)) :=
    Finset.univ.filter (fun z =>
      out' {z.1, z.2} (fun j => decide (z.1 ∈ R' j ∨ π' z.2 ∈ C' j)) ≠
        Bool.xor (G (typ n b hn z.1) (typ n b hn (π' z.2)))
          (Bool.xor (rf' z.1) (cf' (π' z.2))))
  let proj : Fin (n * b) × Fin (n * b) → Fin n × Fin n :=
    fun z => (typ n b hn z.1, typ n b hn z.2)
  have hmem : ∀ z, z ∈ ErrCopy ↔ proj z ∈ ErrBase := by
    intro z
    simp only [ErrCopy, ErrBase, proj, Finset.mem_filter, Finset.mem_univ, true_and]
    have hπ : typ n b hn (π' z.2) = π (typ n b hn z.2) := typ_liftPerm n b hn π z.2
    have hobs : (fun j => decide (z.1 ∈ R' j ∨ π' z.2 ∈ C' j)) =
        (fun j => decide (typ n b hn z.1 ∈ R j ∨ π (typ n b hn z.2) ∈ C j)) := by
      funext j
      apply decide_eq_decide.mpr
      simp only [R', C', Finset.mem_filter, Finset.mem_univ, true_and, hπ]
    have hpair : ({z.1, z.2} : Finset (Fin (n * b))).image (typ n b hn) =
        {typ n b hn z.1, typ n b hn z.2} := by
      rw [Finset.image_insert, Finset.image_singleton]
    change (out (({z.1, z.2} : Finset (Fin (n * b))).image (typ n b hn))
        (fun j => decide (z.1 ∈ R' j ∨ π' z.2 ∈ C' j)) ≠
        Bool.xor (G (typ n b hn z.1) (typ n b hn (π' z.2)))
          (Bool.xor (rf (typ n b hn z.1)) (cf (typ n b hn (π' z.2))))) ↔ _
    rw [hpair, hobs, hπ]
  have hfib : ErrCopy.card = ∑ p ∈ ErrBase, (ErrCopy.filter (fun z => proj z = p)).card :=
    Finset.card_eq_sum_card_fiberwise (fun z hz => (hmem z).mp hz)
  have hterm : ∀ p ∈ ErrBase, (ErrCopy.filter (fun z => proj z = p)).card = b * b := by
    intro p hp
    have heq : ErrCopy.filter (fun z => proj z = p) =
        (Finset.univ.filter (fun x : Fin (n * b) => typ n b hn x = p.1)) ×ˢ
        (Finset.univ.filter (fun y : Fin (n * b) => typ n b hn y = p.2)) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, hxy⟩
        exact ⟨congrArg Prod.fst hxy, congrArg Prod.snd hxy⟩
      · rintro ⟨hx, hy⟩
        have hpxy : proj (x, y) = p := Prod.ext hx hy
        exact ⟨(hmem (x, y)).mpr (hpxy ▸ hp), hpxy⟩
    rw [heq, Finset.card_product, card_filter_typ, card_filter_typ]
  change ErrCopy.card ≤ b ^ 2 * E
  rw [hfib, Finset.sum_const_nat hterm, ← pow_two,
    Nat.mul_comm ErrBase.card (b ^ 2)]
  exact Nat.mul_le_mul_left (b ^ 2) hE

end PEqualNP.Outside.L_meta_25714

theorem PEqualNP.Outside.L_meta_25714 : ∀ (n b q : ℕ) (hn : 0 < n), 0 < b →
  let fits := fun (s : ℕ) (G : Fin s → Fin s → Bool) (e : ℕ) =>
    ∃ (π : Equiv.Perm (Fin s)) (rf cf : Fin s → Bool) (R C : Fin q → Finset (Fin s))
      (out : Finset (Fin s) → (Fin q → Bool) → Bool),
      ((Finset.univ : Finset (Fin s × Fin s)).filter (fun z =>
        out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
          Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ e
  let typ := fun i : Fin (n*b) => (⟨i.val % n, Nat.mod_lt _ hn⟩ : Fin n)
  ∀ (G : Fin n → Fin n → Bool) (E : ℕ),
    let copied := fun i j : Fin (n*b) => G (typ i) (typ j)
    (fits (n*b) copied E → fits n G (E/b)) ∧
      (fits n G E → fits (n*b) copied (b^2*E)) := by
  intro n b q hn hb fits typ G E copied
  constructor
  · rintro ⟨π, rf, cf, R, C, out, hE⟩
    exact PEqualNP.Outside.L_meta_25714.dir1 n b q hn hb G E π rf cf R C out hE
  · rintro ⟨π, rf, cf, R, C, out, hE⟩
    exact PEqualNP.Outside.L_meta_25714.dir2 n b q hn G E π rf cf R C out hE

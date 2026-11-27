import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_850
open scoped BigOperators

abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F

def ix {n : ℕ} (hn : 0 < n) (k : ℕ) : Fin n := ⟨k % n, Nat.mod_lt _ hn⟩
def next {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n := ix hn (i.val+1)

def good {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m) (U : Submodule F (Vec n)) : Prop :=
  (∀ x ∈ U, ∀ a : Fin m, (∑ i, h i a * x i) = 0) ∧
  (∀ x ∈ U, ∀ y ∈ U, ∀ i : Fin n, x i * y (next hn i) = x (next hn i) * y i)

noncomputable def active {n : ℕ} (U : Submodule F (Vec n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∃ x ∈ U, x i ≠ 0)

noncomputable def block {n : ℕ} (hn : 0 < n) (base : Fin n) (t : ℕ) (p : Fin n × Fin n) : Finset (Fin n) := by
  classical
  exact ((Finset.range p.2.val).filter (fun k => p.1.val ≤ k)).image (fun k => ix hn (base.val+t+1+k))

def separated {n : ℕ} (I : Finset (Fin n × Fin n)) : Prop :=
  ∀ ⦃p⦄, p ∈ I → ∀ ⦃q⦄, q ∈ I → p ≠ q → p.2 < q.1 ∨ q.2 < p.1

noncomputable def partialSum {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m) (base : Fin n) (t : ℕ) (p : Fin n) : Vec m :=
  ∑ k ∈ Finset.range p.val, h (ix hn (base.val+t+1+k))

end PEqualNP.Outside.L_lib_850

namespace PEqualNP.Outside.L_lib_850

open scoped BigOperators

variable {n m : ℕ}

def offsetSite (hn : 0 < n) (base : Fin n) (t k : ℕ) : Fin n :=
  ix hn (base.val + t + 1 + k)

theorem next_offsetSite (hn : 0 < n) (base : Fin n) (t k : ℕ) :
    next hn (offsetSite hn base t k) = offsetSite hn base t (k + 1) := by
  apply Fin.ext
  change ((base.val + t + 1 + k) % n + 1) % n = (base.val + t + 1 + (k + 1)) % n
  have h := (Nat.mod_modEq (base.val + t + 1 + k) n).add_right 1
  simpa only [Nat.ModEq, Nat.add_assoc] using h

theorem ix_add_left_inj (hn : 0 < n) (a : ℕ) {j k : ℕ} (hj : j < n) (hk : k < n)
    (h : ix hn (a + j) = ix hn (a + k)) : j = k := by
  have hm : a + j ≡ a + k [MOD n] := congrArg Fin.val h
  exact (Nat.ModEq.add_left_cancel' a hm).eq_of_lt_of_lt hj hk

theorem offsetSite_inj (hn : 0 < n) (base : Fin n) (t : ℕ) {j k : ℕ}
    (hj : j < n) (hk : k < n) (h : offsetSite hn base t j = offsetSite hn base t k) :
    j = k :=
  ix_add_left_inj hn (base.val + t + 1) hj hk h

theorem offsetSite_cut (hn : 0 < n) (base : Fin n) (t : ℕ) :
    offsetSite hn base t (n - 1) = ix hn (base.val + t) := by
  apply Fin.ext
  change (base.val + t + 1 + (n - 1)) % n = (base.val + t) % n
  rw [show base.val + t + 1 + (n - 1) = (base.val + t) + n by omega]
  exact Nat.add_modEq_right

theorem mem_block_iff (hn : 0 < n) (base : Fin n) (t : ℕ) {p : Fin n × Fin n}
    {i : Fin n} :
    i ∈ block hn base t p ↔ ∃ k : ℕ, p.1.val ≤ k ∧ k < p.2.val ∧ offsetSite hn base t k = i := by
  classical
  simp only [block, offsetSite, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun ⟨k, ⟨hr, hl⟩, h⟩ => ⟨k, hl, hr, h⟩,
    fun ⟨k, hl, hr, h⟩ => ⟨k, ⟨hr, hl⟩, h⟩⟩

theorem offsetSite_mem_block_iff (hn : 0 < n) (base : Fin n) (t : ℕ) {k : ℕ}
    {p : Fin n × Fin n} (hk : k < n) :
    offsetSite hn base t k ∈ block hn base t p ↔ p.1.val ≤ k ∧ k < p.2.val := by
  rw [mem_block_iff hn base t]
  refine ⟨?_, fun ⟨hl, hr⟩ => ⟨k, hl, hr, rfl⟩⟩
  rintro ⟨j, hl, hr, h⟩
  have he := offsetSite_inj hn base t (hr.trans p.2.isLt) hk h
  simpa only [he] using And.intro hl hr

theorem cut_not_mem_block (hn : 0 < n) (base : Fin n) (t : ℕ) (p : Fin n × Fin n) :
    ix hn (base.val + t) ∉ block hn base t p := by
  have hk : n - 1 < n := by omega
  rw [← offsetSite_cut hn base t, offsetSite_mem_block_iff hn base t hk]
  have := p.2.isLt
  omega

theorem block_nonempty (hn : 0 < n) (base : Fin n) (t : ℕ) {p : Fin n × Fin n}
    (hp : p.1 < p.2) : (block hn base t p).Nonempty :=
  ⟨offsetSite hn base t p.1.val, (mem_block_iff hn base t).2 ⟨p.1.val, le_rfl, hp, rfl⟩⟩

theorem block_disjoint (hn : 0 < n) (base : Fin n) (t : ℕ)
    {I : Finset (Fin n × Fin n)} (hsep : separated I) {p q : Fin n × Fin n}
    (hp : p ∈ I) (hq : q ∈ I) (hpq : p ≠ q) :
    Disjoint (block hn base t p) (block hn base t q) := by
  refine Finset.disjoint_left.2 ?_
  intro i hi hj
  obtain ⟨k, hkl, hkr, hk⟩ := (mem_block_iff hn base t).1 hi
  obtain ⟨l, hll, hlr, hl⟩ := (mem_block_iff hn base t).1 hj
  have he := offsetSite_inj hn base t (hkr.trans p.2.isLt) (hlr.trans q.2.isLt) (hk.trans hl.symm)
  rcases hsep hp hq hpq with h | h
  · change p.2.val < q.1.val at h
    omega
  · change q.2.val < p.1.val at h
    omega

theorem block_eq_of_next_mem (hn : 0 < n) (base : Fin n) (t : ℕ)
    {I : Finset (Fin n × Fin n)} (hsep : separated I) {p q : Fin n × Fin n}
    (hp : p ∈ I) (hq : q ∈ I) {i : Fin n}
    (hi : i ∈ block hn base t p) (hj : next hn i ∈ block hn base t q) : p = q := by
  obtain ⟨k, hkl, hkr, hk⟩ := (mem_block_iff hn base t).1 hi
  obtain ⟨l, hll, hlr, hl⟩ := (mem_block_iff hn base t).1 hj
  have hkn : k + 1 < n := (Nat.succ_le_of_lt hkr).trans_lt p.2.isLt
  have hnext : next hn i = offsetSite hn base t (k + 1) := by
    rw [← hk, next_offsetSite]
  have he := offsetSite_inj hn base t hkn (hlr.trans q.2.isLt) (hnext.symm.trans hl.symm)
  by_contra hpq
  rcases hsep hp hq hpq with h | h
  · change p.2.val < q.1.val at h
    omega
  · change q.2.val < p.1.val at h
    omega

private structure OffsetRun (A : ℕ → Prop) (l r : ℕ) : Prop where
  lt : l < r
  inside : ∀ k, l ≤ k → k < r → A k
  before : 0 < l → ¬ A (l - 1)
  after : ¬ A r

private theorem exists_offsetRun (A : ℕ → Prop) {b k : ℕ} (hkb : k ≤ b)
    (hb : ¬ A b) (hk : A k) : ∃ l r : ℕ, l ≤ k ∧ k < r ∧ r ≤ b ∧ OffsetRun A l r := by
  classical

  let L : ℕ → Prop := fun l => l ≤ k ∧ ∀ j : ℕ, l ≤ j → j ≤ k → A j
  have hL : ∃ l, L l := by
    refine ⟨k, le_rfl, ?_⟩
    intro j hkj hjk
    simpa only [le_antisymm hjk hkj] using hk
  let R : ℕ → Prop := fun r => k ≤ r ∧ ¬ A r
  have hR : ∃ r, R r := ⟨b, hkb, hb⟩
  let l := Nat.find hL
  let r := Nat.find hR
  have hl : L l := Nat.find_spec hL
  have hr : R r := Nat.find_spec hR
  have hlk : l ≤ k := hl.1
  have hkr : k < r := lt_of_le_of_ne hr.1 (fun he => hr.2 (he ▸ hk))
  have hrb : r ≤ b := Nat.find_min' hR (show R b from ⟨hkb, hb⟩)
  refine ⟨l, r, hlk, hkr, hrb, ⟨hlk.trans_lt hkr, ?_, ?_, hr.2⟩⟩
  · intro j hlj hjr
    by_cases hjk : j ≤ k
    · exact hl.2 j hlj hjk
    · by_contra hj
      exact Nat.find_min hR hjr ⟨(lt_of_not_ge hjk).le, hj⟩
  · intro hlpos hprev
    have hlt : l - 1 < l := by omega
    apply Nat.find_min hL hlt
    refine ⟨hlt.le.trans hlk, ?_⟩
    intro j hj hjk
    by_cases hlj : l ≤ j
    · exact hl.2 j hlj hjk
    · have he : j = l - 1 := by omega
      simpa only [he] using hprev

private theorem OffsetRun.lt_right_of_lt_left {A : ℕ → Prop} {l r l' r' : ℕ}
    (hp : OffsetRun A l r) (hq : OffsetRun A l' r') (hlt : l < l') : r < l' := by
  by_contra! h
  exact hq.before (by omega) (hp.inside (l' - 1) (by omega) (by omega))

private theorem OffsetRun.right_eq_of_left_eq {A : ℕ → Prop} {l r l' r' : ℕ}
    (hp : OffsetRun A l r) (hq : OffsetRun A l' r') (he : l = l') : r = r' := by
  subst l'
  exact le_antisymm
    (le_of_not_gt fun h => hq.after (hp.inside r' hq.lt.le h))
    (le_of_not_gt fun h => hp.after (hq.inside r hp.lt.le h))

theorem exists_separated_blocks (hn : 0 < n) (base : Fin n) (t : ℕ) (S : Finset (Fin n))
    (hcut : ix hn (base.val + t) ∉ S) :
    ∃ I : Finset (Fin n × Fin n), separated I ∧ (∀ p ∈ I, p.1 < p.2) ∧
      I.biUnion (block hn base t) = S := by
  classical
  let A : ℕ → Prop := fun k => offsetSite hn base t k ∈ S
  have hAcut : ¬ A (n - 1) := by
    change offsetSite hn base t (n - 1) ∉ S
    rwa [offsetSite_cut]
  let I : Finset (Fin n × Fin n) := Finset.univ.filter fun p => OffsetRun A p.1.val p.2.val
  have hI (p : Fin n × Fin n) : p ∈ I ↔ OffsetRun A p.1.val p.2.val := by simp [I]
  refine ⟨I, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    have hp' := (hI p).1 hp
    have hq' := (hI q).1 hq
    rcases lt_trichotomy p.1 q.1 with h | h | h
    · exact Or.inl (OffsetRun.lt_right_of_lt_left hp' hq' h)
    · exfalso
      apply hpq
      refine Prod.ext h (Fin.ext ?_)
      exact OffsetRun.right_eq_of_left_eq hp' hq' (congrArg Fin.val h)
    · exact Or.inr (OffsetRun.lt_right_of_lt_left hq' hp' h)
  · intro p hp
    exact ((hI p).1 hp).lt
  · ext i
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨p, hp, hi⟩
      obtain ⟨k, hl, hr, rfl⟩ := (mem_block_iff hn base t).1 hi
      exact ((hI p).1 hp).inside k hl hr
    · intro hi
      have hinj : Function.Injective (fun k : Fin n => offsetSite hn base t k.val) :=
        fun a b h => Fin.ext (offsetSite_inj hn base t a.isLt b.isLt h)
      obtain ⟨k, hk⟩ := Finite.surjective_of_injective hinj i
      change offsetSite hn base t k.val = i at hk
      have hAk : A k.val := by
        change offsetSite hn base t k.val ∈ S
        rwa [hk]
      have hklt := k.isLt
      have hkb : k.val ≤ n - 1 := by omega
      obtain ⟨l, r, hlk, hkr, hrbound, hrun⟩ := exists_offsetRun A hkb hAcut hAk
      let p : Fin n × Fin n := (⟨l, by omega⟩, ⟨r, by omega⟩)
      exact ⟨p, (hI p).2 hrun, (mem_block_iff hn base t).2 ⟨k.val, hlk, hkr, hk⟩⟩

private theorem block_eq_image_Ico (hn : 0 < n) (base : Fin n) (t : ℕ)
    (p : Fin n × Fin n) :
    block hn base t p = (Finset.Ico p.1.val p.2.val).image (offsetSite hn base t) := by
  classical
  have hset : ((Finset.range p.2.val).filter (fun k => p.1.val ≤ k)) =
      Finset.Ico p.1.val p.2.val := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, and_comm]
  unfold block
  rw [hset]
  rfl

private theorem offsetSite_injOn_Ico (hn : 0 < n) (base : Fin n) (t : ℕ)
    (p : Fin n × Fin n) :
    Set.InjOn (offsetSite hn base t) (↑(Finset.Ico p.1.val p.2.val) : Set ℕ) := by
  intro j hj k hk he
  exact offsetSite_inj hn base t ((Finset.mem_Ico.1 hj).2.trans p.2.isLt)
    ((Finset.mem_Ico.1 hk).2.trans p.2.isLt) he

theorem block_card (hn : 0 < n) (base : Fin n) (t : ℕ) (p : Fin n × Fin n) :
    (block hn base t p).card = p.2.val - p.1.val := by
  classical
  rw [block_eq_image_Ico, Finset.card_image_of_injOn (offsetSite_injOn_Ico hn base t p), Nat.card_Ico]

theorem sum_block_eq_partialSum_sub (hn : 0 < n) (h : Fin n → Vec m) (base : Fin n) (t : ℕ)
    {p : Fin n × Fin n} (hp : p.1 ≤ p.2) :
    (∑ i ∈ block hn base t p, h i) = partialSum hn h base t p.2 - partialSum hn h base t p.1 := by
  classical
  rw [block_eq_image_Ico, Finset.sum_image (offsetSite_injOn_Ico hn base t p)]
  exact Finset.sum_Ico_eq_sub (fun k => h (offsetSite hn base t k)) hp

end PEqualNP.Outside.L_lib_850

namespace PEqualNP.Outside.L_lib_850
open scoped BigOperators

variable {n m : ℕ} {K : Type*} [Fintype K]

noncomputable def emb (B : K → Finset (Fin n)) : (K → F) →ₗ[F] Vec n where
  toFun c i := ∑ k, if i ∈ B k then c k else 0
  map_add' c d := by
    funext i
    change (∑ k, if i ∈ B k then c k + d k else 0) =
      (∑ k, if i ∈ B k then c k else 0) + (∑ k, if i ∈ B k then d k else 0)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp
  map_smul' a c := by
    funext i
    change (∑ k, if i ∈ B k then a * c k else 0) =
      a * (∑ k, if i ∈ B k then c k else 0)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp

theorem emb_apply (B : K → Finset (Fin n)) (c : K → F) (i : Fin n) :
    emb B c i = ∑ k, if i ∈ B k then c k else 0 := rfl

theorem emb_apply_of_mem {B : K → Finset (Fin n)}
    (hdisj : Pairwise (fun k l => Disjoint (B k) (B l)))
    (c : K → F) {k : K} {i : Fin n} (hi : i ∈ B k) : emb B c i = c k := by
  rw [emb_apply, Finset.sum_eq_single k]
  · rw [if_pos hi]
  · intro l _ hlk
    exact if_neg (fun hil => Finset.disjoint_left.mp (hdisj hlk) hil hi)
  · simp

theorem emb_apply_of_no_mem {B : K → Finset (Fin n)}
    (c : K → F) {i : Fin n} (hi : ∀ k, i ∉ B k) : emb B c i = 0 := by
  simp [emb_apply, hi]

theorem emb_injective {B : K → Finset (Fin n)} (hne : ∀ k, (B k).Nonempty)
    (hdisj : Pairwise (fun k l => Disjoint (B k) (B l))) : Function.Injective (emb B) := by
  intro c d hcd
  funext k
  obtain ⟨i, hi⟩ := hne k
  simpa only [emb_apply_of_mem hdisj c hi, emb_apply_of_mem hdisj d hi]
    using congrFun hcd i

theorem mem_range_emb_iff {B : K → Finset (Fin n)} (hne : ∀ k, (B k).Nonempty)
    (hdisj : Pairwise (fun k l => Disjoint (B k) (B l))) {x : Vec n} :
    x ∈ LinearMap.range (emb B) ↔
      (∀ k i j, i ∈ B k → j ∈ B k → x i = x j) ∧
      (∀ i, (∀ k, i ∉ B k) → x i = 0) := by
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨?_, fun i hi => emb_apply_of_no_mem c hi⟩
    intro k i j hi hj
    rw [emb_apply_of_mem hdisj c hi, emb_apply_of_mem hdisj c hj]
  · rintro ⟨hconst, hzero⟩
    classical
    choose p hp using (show ∀ k, ∃ i, i ∈ B k from hne)
    let c : K → F := fun k => x (p k)
    refine ⟨c, ?_⟩
    funext i
    by_cases hi : ∃ k, i ∈ B k
    · obtain ⟨k, hik⟩ := hi
      rw [emb_apply_of_mem hdisj c hik]
      exact hconst k (p k) i (hp k) hik
    · have hi' (k : K) : i ∉ B k := fun hik => hi ⟨k, hik⟩
      rw [emb_apply_of_no_mem c hi', hzero i hi']

noncomputable def H (h : Fin n → Vec m) : Vec n →ₗ[F] Vec m where
  toFun x := ∑ i, x i • h i
  map_add' x y := by
    change (∑ i, (x i + y i) • h i) = (∑ i, x i • h i) + (∑ i, y i • h i)
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by
    change (∑ i, (a * x i) • h i) = a • (∑ i, x i • h i)
    simp only [mul_smul, Finset.smul_sum]

theorem H_apply (h : Fin n → Vec m) (x : Vec n) : H h x = ∑ i, x i • h i := rfl

theorem H_apply_coord (h : Fin n → Vec m) (x : Vec n) (a : Fin m) :
    H h x a = ∑ i, h i a * x i := by
  simp only [H_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => mul_comm (x i) (h i a))

noncomputable def column (B : K → Finset (Fin n)) (h : Fin n → Vec m) (k : K) : Vec m :=
  ∑ i ∈ B k, h i

theorem comp_emb_apply (B : K → Finset (Fin n)) (h : Fin n → Vec m) (c : K → F) :
    ((H h).comp (emb B)) c = ∑ k, c k • column B h k := by
  change (∑ i, (∑ k, if i ∈ B k then c k else 0) • h i) = _
  simp only [Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_mem, Finset.univ_inter, column, Finset.smul_sum]

theorem comp_emb_apply_single [DecidableEq K] (B : K → Finset (Fin n)) (h : Fin n → Vec m)
    (k : K) (a : F) : ((H h).comp (emb B)) (Pi.single k a) = a • column B h k := by
  rw [comp_emb_apply, Fintype.sum_single_smul]

noncomputable def columnSpace (B : K → Finset (Fin n)) (h : Fin n → Vec m) :
    Submodule F (Vec m) := LinearMap.range ((H h).comp (emb B))

theorem column_mem_columnSpace (B : K → Finset (Fin n)) (h : Fin n → Vec m) (k : K) :
    column B h k ∈ columnSpace B h := by
  classical
  change column B h k ∈ LinearMap.range ((H h).comp (emb B))
  exact LinearMap.mem_range.mpr ⟨Pi.single k (1 : F), by rw [comp_emb_apply_single, one_smul]⟩

theorem columnSpace_le_iff (B : K → Finset (Fin n)) (h : Fin n → Vec m)
    (D' : Submodule F (Vec m)) : columnSpace B h ≤ D' ↔ ∀ k, column B h k ∈ D' := by
  constructor
  · intro hle k
    exact hle (column_mem_columnSpace B h k)
  · intro hcol x hx
    change x ∈ LinearMap.range ((H h).comp (emb B)) at hx
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hx
    rw [comp_emb_apply]
    exact D'.sum_mem (fun k _ => D'.smul_mem (c k) (hcol k))

theorem columnSpace_eq_span (B : K → Finset (Fin n)) (h : Fin n → Vec m) :
    columnSpace B h = Submodule.span F (Set.range (column B h)) := by
  apply le_antisymm
  · exact (columnSpace_le_iff B h _).mpr (fun k => Submodule.subset_span ⟨k, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact column_mem_columnSpace B h k

def blocksSeparated (hn : 0 < n) (B : K → Finset (Fin n)) : Prop :=
  ∀ ⦃k l : K⦄ ⦃i : Fin n⦄, i ∈ B k → next hn i ∈ B l → k = l

theorem emb_next_balance {hn : 0 < n} {B : K → Finset (Fin n)}
    (hdisj : Pairwise (fun k l => Disjoint (B k) (B l))) (hsep : blocksSeparated hn B)
    (c d : K → F) (i : Fin n) :
    emb B c i * emb B d (next hn i) = emb B c (next hn i) * emb B d i := by
  classical
  by_cases hi : ∃ k, i ∈ B k
  · obtain ⟨k, hik⟩ := hi
    by_cases hj : ∃ l, next hn i ∈ B l
    · obtain ⟨l, hjl⟩ := hj
      have hkl : k = l := hsep hik hjl
      subst l
      rw [emb_apply_of_mem hdisj c hik, emb_apply_of_mem hdisj d hik,
        emb_apply_of_mem hdisj c hjl, emb_apply_of_mem hdisj d hjl]
    · have hj' (l : K) : next hn i ∉ B l := fun hjl => hj ⟨l, hjl⟩
      simp only [emb_apply_of_no_mem c hj', emb_apply_of_no_mem d hj', mul_zero, zero_mul]
  · have hi' (k : K) : i ∉ B k := fun hik => hi ⟨k, hik⟩
    simp only [emb_apply_of_no_mem c hi', emb_apply_of_no_mem d hi', mul_zero, zero_mul]

noncomputable def kernelCode (B : K → Finset (Fin n)) (h : Fin n → Vec m) :
    Submodule F (Vec n) := ((H h).comp (emb B)).ker.map (emb B)

theorem mem_kernelCode_iff {B : K → Finset (Fin n)} {h : Fin n → Vec m} {x : Vec n} :
    x ∈ kernelCode B h ↔ ∃ c : K → F, (∑ k, c k • column B h k) = 0 ∧ emb B c = x := by
  simp only [kernelCode, Submodule.mem_map, LinearMap.mem_ker, comp_emb_apply]

theorem kernelCode_eq_range_inf_ker (B : K → Finset (Fin n)) (h : Fin n → Vec m) :
    kernelCode B h = LinearMap.range (emb B) ⊓ (H h).ker := by
  ext x
  simp only [kernelCode, Submodule.mem_map, LinearMap.mem_ker, LinearMap.comp_apply,
    Submodule.mem_inf, LinearMap.mem_range]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c, rfl⟩, hc⟩
  · rintro ⟨⟨c, rfl⟩, hc⟩
    exact ⟨c, hc, rfl⟩

theorem kernelCode_good {hn : 0 < n} {B : K → Finset (Fin n)} {h : Fin n → Vec m}
    (hdisj : Pairwise (fun k l => Disjoint (B k) (B l))) (hsep : blocksSeparated hn B) :
    good hn h (kernelCode B h) := by
  have hmem (x : Vec n) (hx : x ∈ kernelCode B h) :
      (∃ c : K → F, emb B c = x) ∧ H h x = 0 := by
    simpa only [kernelCode_eq_range_inf_ker, Submodule.mem_inf,
      LinearMap.mem_range, LinearMap.mem_ker] using hx
  constructor
  · intro x hx a
    simpa only [H_apply_coord, Pi.zero_apply] using congrFun (hmem x hx).2 a
  · intro x hx y hy i
    obtain ⟨c, rfl⟩ := (hmem x hx).1
    obtain ⟨d, rfl⟩ := (hmem y hy).1
    exact emb_next_balance hdisj hsep c d i

theorem finrank_kernelCode_add_finrank_columnSpace {B : K → Finset (Fin n)} (h : Fin n → Vec m)
    (hne : ∀ k, (B k).Nonempty) (hdisj : Pairwise (fun k l => Disjoint (B k) (B l))) :
    Module.finrank F (kernelCode B h) + Module.finrank F (columnSpace B h) = Fintype.card K := by
  change Module.finrank F (((H h).comp (emb B)).ker.map (emb B)) +
    Module.finrank F (LinearMap.range ((H h).comp (emb B))) = Fintype.card K
  rw [← (Submodule.equivMapOfInjective (emb B) (emb_injective hne hdisj)
    ((H h).comp (emb B)).ker).finrank_eq, Nat.add_comm]
  simpa only [Module.finrank_fintype_fun_eq_card] using
    LinearMap.finrank_range_add_finrank_ker ((H h).comp (emb B))

theorem finrank_kernelCode {B : K → Finset (Fin n)} (h : Fin n → Vec m)
    (hne : ∀ k, (B k).Nonempty) (hdisj : Pairwise (fun k l => Disjoint (B k) (B l))) :
    Module.finrank F (kernelCode B h) = Fintype.card K - Module.finrank F (columnSpace B h) := by
  have hr := finrank_kernelCode_add_finrank_columnSpace h hne hdisj
  omega

theorem le_finrank_kernelCode_of_columns_mem {B : K → Finset (Fin n)} {h : Fin n → Vec m}
    (hne : ∀ k, (B k).Nonempty) (hdisj : Pairwise (fun k l => Disjoint (B k) (B l)))
    {D' : Submodule F (Vec m)} (hcol : ∀ k, column B h k ∈ D') :
    Fintype.card K - Module.finrank F D' ≤ Module.finrank F (kernelCode B h) := by
  have hle : Module.finrank F (columnSpace B h) ≤ Module.finrank F D' :=
    Submodule.finrank_mono ((columnSpace_le_iff B h D').mpr hcol)
  rw [finrank_kernelCode h hne hdisj]
  omega

end PEqualNP.Outside.L_lib_850

namespace PEqualNP.Outside.L_lib_850
open scoped BigOperators

theorem mem_active {n : ℕ} {U : Submodule F (Vec n)} {i : Fin n} :
    i ∈ active U ↔ ∃ x ∈ U, x i ≠ 0 := by
  classical
  simp [active]

theorem active_zero {n : ℕ} {U : Submodule F (Vec n)} {i : Fin n}
    (hi : i ∉ active U) {x : Vec n} (hx : x ∈ U) : x i = 0 := by
  by_contra hn
  exact hi (mem_active.mpr ⟨x,hx,hn⟩)

theorem eq_one_of_ne_zero (a : F) (h : a ≠ 0) : a = 1 := by
  revert a
  decide +kernel

theorem active_next_eq {n m : ℕ} {hn : 0 < n} {h : Fin n → Vec m} {U : Submodule F (Vec n)}
    (hg : good hn h U) {i : Fin n} (hi : i ∈ active U) (hi' : next hn i ∈ active U)
    {x : Vec n} (hx : x ∈ U) : x i = x (next hn i) := by
  obtain ⟨u, hu, hui⟩ := mem_active.mp hi
  obtain ⟨v, hv, hvj⟩ := mem_active.mp hi'
  have he := hg.2 u hu v hv i
  rw [eq_one_of_ne_zero _ hui, eq_one_of_ne_zero _ hvj, one_mul] at he
  have huj : u (next hn i) = 1 := eq_one_of_ne_zero _ (by
    intro hh; rw [hh, zero_mul] at he; exact one_ne_zero he)
  have hz := hg.2 x hx u hu i
  simpa [eq_one_of_ne_zero _ hui, huj] using hz

theorem next_ix {n : ℕ} (hn : 0 < n) (k : ℕ) : next hn (ix hn k) = ix hn (k+1) := by
  apply Fin.ext
  exact Nat.mod_add_mod k n 1

theorem all_eq_of_next {n : ℕ} (hn : 0 < n) (x : Vec n)
    (h : ∀ i, x i = x (next hn i)) (i j : Fin n) : x i = x j := by
  have e (k : ℕ) : x (ix hn k) = x (ix hn 0) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hd := h (ix hn k)
      rw [next_ix] at hd
      exact hd.symm.trans ih
  have hi : ix hn i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hj : ix hn j.val = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
  exact (hi ▸ e i.val).trans (hj ▸ e j.val).symm

noncomputable def optVal {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m) : ℕ := by
  classical
  letI : Fintype (Submodule F (Vec n)) := Fintype.ofFinite _
  exact Finset.univ.sup (fun U : Submodule F (Vec n) => if good hn h U then Module.finrank F U else 0)

theorem good_bot {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m) : good hn h ⊥ := by
  constructor
  · intro x hx a
    have hx' : x = 0 := by simpa using hx
    rw [hx']
    simp
  · intro x hx y hy i
    have hx' : x = 0 := by simpa using hx
    rw [hx']
    simp

theorem opt_ge_dim {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m)
    {U : Submodule F (Vec n)} (hg : good hn h U) : Module.finrank F U ≤ optVal hn h := by
  classical
  letI : Fintype (Submodule F (Vec n)) := Fintype.ofFinite _
  unfold optVal
  have le := Finset.le_sup (s := (Finset.univ : Finset (Submodule F (Vec n))))
    (f := fun U => if good hn h U then Module.finrank F U else 0) (b := U) (Finset.mem_univ U)
  simpa [hg] using le

theorem exists_opt {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m) :
    ∃ U : Submodule F (Vec n), good hn h U ∧ Module.finrank F U = optVal hn h := by
  classical
  letI : Fintype (Submodule F (Vec n)) := Fintype.ofFinite _
  obtain ⟨U, hu, hm⟩ := Finset.exists_max_image (Finset.univ : Finset (Submodule F (Vec n)))
    (fun U => if good hn h U then Module.finrank F U else 0) (by exact ⟨⊥, Finset.mem_univ _⟩)
  have ho : optVal hn h = if good hn h U then Module.finrank F U else 0 := by
    unfold optVal
    exact le_antisymm (Finset.sup_le hm) (Finset.le_sup
      (f := fun V => if good hn h V then Module.finrank F V else 0) hu)
  by_cases hg : good hn h U
  · exact ⟨U,hg,by simpa [hg] using ho.symm⟩
  · refine ⟨⊥, good_bot hn h, ?_⟩
    simp [ho, hg]

theorem minSupport_opt {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m) :
    ∃ U : Submodule F (Vec n), good hn h U ∧ Module.finrank F U = optVal hn h ∧
      ∀ V : Submodule F (Vec n), good hn h V → Module.finrank F U ≤ Module.finrank F V →
      (active U).card ≤ (active V).card := by
  classical
  letI : Fintype (Submodule F (Vec n)) := Fintype.ofFinite _
  let Q := Finset.univ.filter (fun U : Submodule F (Vec n) => good hn h U ∧ Module.finrank F U = optVal hn h)
  have hQ : Q.Nonempty := by
    obtain ⟨U, hg, hd⟩ := exists_opt hn h
    exact ⟨U, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg, hd⟩⟩
  obtain ⟨U, hU, hmin⟩ := Finset.exists_min_image Q (fun U => (active U).card) hQ
  obtain ⟨hg,hd⟩ := (Finset.mem_filter.mp hU).2
  exact ⟨U,hg,hd,fun V hv hdim => hmin V (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hv, le_antisymm (opt_ge_dim hn h hv) (hd ▸ hdim)⟩)⟩

noncomputable def repeatMap (n : ℕ) : F →ₗ[F] Vec n := LinearMap.pi fun _ => LinearMap.id

theorem repeatMap_apply (n : ℕ) (a : F) (i : Fin n) : repeatMap n a i = a := rfl

theorem repeatMap_inj {n : ℕ} (hn : 0 < n) : Function.Injective (repeatMap n) := by
  intro x y h
  exact congrFun h ⟨0,hn⟩

theorem repeat_good {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m) (hs : (∑ i, h i) = 0) :
    good hn h (LinearMap.range (repeatMap n)) := by
  constructor
  · rintro x ⟨a,rfl⟩ j
    have hh := congrFun hs j
    simp only [Finset.sum_apply, Pi.zero_apply] at hh
    simp only [repeatMap_apply, ← Finset.sum_mul, hh, zero_mul]
  · rintro x ⟨a,rfl⟩ y ⟨b,rfl⟩ i
    rfl

theorem repeat_le_opt {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m) :
    (if (∑ i, h i) = 0 then 1 else 0) ≤ optVal hn h := by
  split_ifs with hsum
  · have hd : Module.finrank F (LinearMap.range (repeatMap n)) = 1 := by
      rw [LinearMap.finrank_range_of_inj (repeatMap_inj hn), Module.finrank_self]
    exact hd ▸ opt_ge_dim hn h (repeat_good hn h hsum)
  · exact Nat.zero_le _

theorem full_le_repeat {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m) {U : Submodule F (Vec n)}
    (hg : good hn h U) (hfull : active U = Finset.univ) :
    Module.finrank F U ≤ if (∑ i, h i) = 0 then 1 else 0 := by
  let z : Fin n := ⟨0, hn⟩
  have hh (i : Fin n) : i ∈ active U := by simp [hfull]
  have hconst (x : Vec n) (hx : x ∈ U) (i : Fin n) : x i = x z :=
    all_eq_of_next hn x (fun i => active_next_eq hg (hh i) (hh _) hx) i z
  have hsub : U ≤ LinearMap.range (repeatMap n) := by
    intro x hx
    exact ⟨x z, funext (fun i => (hconst x hx i).symm)⟩
  obtain ⟨x,hx,hz⟩ := mem_active.mp (hh z)
  have hs : (∑ i, h i) = 0 := by
    ext j
    have he := hg.1 x hx j
    simp_rw [hconst x hx _, eq_one_of_ne_zero _ hz, mul_one] at he
    simpa only [Finset.sum_apply, Pi.zero_apply] using he
  rw [if_pos hs]
  have hdim := Submodule.finrank_mono hsub
  rwa [LinearMap.finrank_range_of_inj (repeatMap_inj hn), Module.finrank_self] at hdim

end PEqualNP.Outside.L_lib_850

namespace PEqualNP.Outside.L_lib_850

private theorem anchor_inj {n : ℕ} (hn : 0 < n) (a : ℕ) {k j : ℕ}
    (hk : k < n) (hj : j < n) (eq : ix hn (a+k) = ix hn (a+j)) : k = j := by
  have hmod : (a+k) ≡ (a+j) [MOD n] := congrArg Fin.val eq
  have h' : k ≡ j [MOD n] := hmod.add_left_cancel' a
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hj] using h'

private theorem block_at {n : ℕ} (hn : 0 < n) (base : Fin n) (t : ℕ) (p : Fin n × Fin n)
    {k : ℕ} (hl : p.1.val ≤ k) (hr : k < p.2.val) : ix hn (base.val+t+1+k) ∈ block hn base t p := by
  classical
  exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, hl⟩)

private theorem block_card' {n : ℕ} (hn : 0 < n) (base : Fin n) (t : ℕ) (p : Fin n × Fin n) :
    (block hn base t p).card = p.2.val-p.1.val := by
  classical
  change (((Finset.range p.2.val).filter (fun k => p.1.val ≤ k)).image _).card = _
  rw [Finset.card_image_of_injOn]
  · have he : (Finset.range p.2.val).filter (fun k => p.1.val ≤ k) = Finset.Ico p.1.val p.2.val := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      exact and_comm
    rw [he, Nat.card_Ico]
  · intro i hi j hj e
    exact anchor_inj hn _
      ((Finset.mem_range.mp (Finset.mem_filter.mp hi).1).trans p.2.isLt)
      ((Finset.mem_range.mp (Finset.mem_filter.mp hj).1).trans p.2.isLt) e

def runCompat {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) (x : Vec n) : Prop :=
  (∀ i ∉ S, x i = 0) ∧ (∀ i ∈ S, next hn i ∈ S → x i = x (next hn i))

theorem good_runCompat {n m : ℕ} {hn : 0 < n} {h : Fin n → Vec m} {U : Submodule F (Vec n)}
    (hg : good hn h U) {x : Vec n} (hx : x ∈ U) : runCompat hn (active U) x :=
  ⟨fun _ hi => active_zero hi hx, fun _ hi hj => active_next_eq hg hi hj hx⟩

theorem const_on_block {n : ℕ} {hn : 0 < n} {S : Finset (Fin n)} {x : Vec n}
    (hx : runCompat hn S x) (base : Fin n) (t : ℕ) (p : Fin n × Fin n)
    (hs : block hn base t p ⊆ S) {i j : Fin n}
    (hi : i ∈ block hn base t p) (hj : j ∈ block hn base t p) : x i = x j := by
  classical
  let c := base.val+t+1
  have reach (d : ℕ) (hd : p.1.val+d < p.2.val) :
      x (ix hn (c+p.1.val)) = x (ix hn (c+(p.1.val+d))) := by
    induction d with
    | zero => rfl
    | succ d ih =>
      have hp : p.1.val+d < p.2.val := by omega
      have heq : next hn (ix hn (c+(p.1.val+d))) = ix hn (c+(p.1.val+(d+1))) := by
        rw [next_ix]
        congr 1
      have h1 := hs (block_at hn base t p (k := p.1.val+d) (by omega) hp)
      have h2 := hs (block_at hn base t p (k := p.1.val+(d+1)) (by omega) hd)
      exact (ih hp).trans (hx.2 _ h1 (heq.symm ▸ h2) |>.trans (congrArg x heq))
  have eqBase (v : Fin n) (hv : v ∈ block hn base t p) : x (ix hn (c+p.1.val)) = x v := by
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hh,hl⟩ := Finset.mem_filter.mp hk
    have hr := Finset.mem_range.mp hh
    have e : p.1.val + (k-p.1.val) = k := Nat.add_sub_of_le hl
    simpa only [e] using reach (k-p.1.val) (by rw [e]; exact hr)
  exact (eqBase i hi).symm.trans (eqBase j hj)

theorem near_cut {n : ℕ} (hn : 0 < n) (base : Fin n) (t w : ℕ) (S : Finset (Fin n))
    (hOld : t < n) (hcut : ix hn (base.val+t) ∉ S) (I : Finset (Fin n × Fin n))
    (hcover : I.biUnion (block hn base t) = S)
    (hsep : ∀ {p q}, p ∈ I → q ∈ I → ∀ {i}, i ∈ block hn base t p →
      next hn i ∈ block hn base t q → p = q)
    (hcard : ∀ p ∈ I, (block hn base t p).card ≤ w) :
    ∃ j < min n (w+1), ix hn (base.val+j) ∉ S := by
  classical
  by_cases hn' : n ≤ w+1
  · exact ⟨t, by rwa [Nat.min_eq_left hn'], hcut⟩
  rw [Nat.min_eq_right (by omega)]
  by_contra! hbad
  obtain ⟨p,hp,hzero⟩ := Finset.mem_biUnion.mp (by rw [hcover]; exact hbad 0 (by omega))
  have h' (j : ℕ) (hj : j < w+1) : ix hn (base.val+j) ∈ block hn base t p := by
    induction j with
    | zero => exact hzero
    | succ j ih =>
      obtain ⟨q,hq,hm⟩ := Finset.mem_biUnion.mp (by rw [hcover]; exact hbad (j+1) hj)
      have heq : next hn (ix hn (base.val+j)) = ix hn (base.val+(j+1)) := by
        rw [next_ix, Nat.add_assoc]
      have eq := hsep hp hq (ih (by omega)) (heq.symm ▸ hm)
      simpa only [eq] using hm
  have hc : w+1 ≤ (block hn base t p).card := by
    rw [← Finset.card_range (n := w+1)]
    apply Finset.card_le_card_of_injOn (fun k => ix hn (base.val+k))
    · intro k hk
      exact h' k (Finset.mem_range.mp hk)
    · intro k hk j hj eq
      have hk' := Finset.mem_range.mp hk
      have hj' := Finset.mem_range.mp hj
      exact anchor_inj hn _ (by omega) (by omega) eq
  have he := hcard p hp
  omega

end PEqualNP.Outside.L_lib_850

namespace PEqualNP.Outside.L_lib_850
open scoped BigOperators

private theorem shorten_binary (x : F) : x = 0 ∨ x = 1 := by
  by_cases h : x = 0
  · exact Or.inl h
  · exact Or.inr (eq_one_of_ne_zero x h)

theorem exists_zero_sum_ssubset {n m : ℕ} (h : Fin n → Vec m) (D : Submodule F (Vec m))
    (B : Finset (Fin n)) (hcard : m - Module.finrank F D + 1 < B.card) :
    ∃ V : Finset (Fin n), V.Nonempty ∧ V ⊂ B ∧ (∑ i ∈ V, h i) ∈ D := by
  classical
  have hB : B.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨b, hb⟩ := hB
  let C := B.erase b
  let L : (↥C → F) →ₗ[F] Vec m ⧸ D :=
    Fintype.linearCombination F (fun j : ↥C => D.mkQ (h j))
  have hL : ¬ Function.Injective L := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hm : Module.finrank F (Vec m) = m := by simp [Vec, Module.finrank_pi]
    rw [Submodule.finrank_quotient (R := F), hm, Module.finrank_pi, Fintype.card_coe] at hle
    have hC : C.card = B.card - 1 := Finset.card_erase_of_mem hb
    omega
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot'] at hL
  push Not at hL
  obtain ⟨c, hc, hc₀⟩ := hL
  let f : Fin n → F := fun i => if hi : i ∈ C then c ⟨i, hi⟩ else 0
  let V := C.filter (fun i => f i ≠ 0)
  have hV : V ⊆ C := Finset.filter_subset _ _
  refine ⟨V, ?_, ?_, ?_⟩
  · have hcn : ∃ j : ↥C, c j ≠ 0 := by
      by_contra! hcz
      exact hc₀ (funext hcz)
    obtain ⟨j, hj⟩ := hcn
    exact ⟨j, Finset.mem_filter.mpr ⟨j.property, by simpa [f, j.property] using hj⟩⟩
  · have hVB : V ⊆ B := hV.trans (Finset.erase_subset b B)
    exact (Finset.ssubset_iff_of_subset hVB).mpr ⟨b, hb, fun hv =>
      (Finset.notMem_erase b B) (hV hv)⟩
  · have hsum : (∑ i ∈ V, h i) = ∑ j : ↥C, c j • h j := by
      calc
        (∑ i ∈ V, h i) = ∑ i ∈ C, f i • h i := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun i _ => ?_
          rcases shorten_binary (f i) with h0 | h1
          · simp [h0]
          · simp [h1]
        _ = ∑ j : ↥C, c j • h j := by
          rw [← Finset.sum_coe_sort]
          exact Finset.sum_congr rfl fun j _ => by simp [f, j.property]
    apply (Submodule.Quotient.mk_eq_zero D).mp
    change D.mkQ (∑ i ∈ V, h i) = 0
    rw [hsum, map_sum]
    simpa only [L, Fintype.linearCombination_apply, map_smul] using hc

private theorem shorten_mem_active {n : ℕ} {U : Submodule F (Vec n)} {i : Fin n} :
    i ∈ active U ↔ ∃ x ∈ U, x i ≠ 0 := by
  classical
  simp [active]

theorem good_eq_next_of_active {n m : ℕ} {hn : 0 < n} {h : Fin n → Vec m}
    {U : Submodule F (Vec n)} (hU : good hn h U) {i : Fin n}
    (hi : i ∈ active U) (hj : next hn i ∈ active U) {x : Vec n} (hx : x ∈ U) :
    x i = x (next hn i) := by
  obtain ⟨v, hv, hvi⟩ := shorten_mem_active.mp hi
  obtain ⟨w, hw, hwj⟩ := shorten_mem_active.mp hj
  have hv1 := (shorten_binary (v i)).resolve_left hvi
  have hw1 := (shorten_binary (w (next hn i))).resolve_left hwj
  have hvj : v (next hn i) = 1 := by
    rcases shorten_binary (v (next hn i)) with h0 | h1
    · have hcross := hU.2 v hv w hw i
      simp [hv1, hw1, h0] at hcross
    · exact h1
  simpa [hv1, hvj] using hU.2 x hx v hv i

private def shorten_indicator {n : ℕ} (B : Finset (Fin n)) : Vec n :=
  fun i => if i ∈ B then 1 else 0

private theorem shorten_syndrome_apply {n m : ℕ} (h : Fin n → Vec m) (x : Vec n) (a : Fin m) :
    Fintype.linearCombination F h x a = ∑ i, h i a * x i := by
  rw [Fintype.linearCombination_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

private theorem shorten_syndrome_indicator {n m : ℕ} (h : Fin n → Vec m) (B : Finset (Fin n)) :
    Fintype.linearCombination F h (shorten_indicator B) = ∑ i ∈ B, h i := by
  classical
  simp only [Fintype.linearCombination_apply, shorten_indicator, ite_smul, one_smul, zero_smul]
  rw [← Finset.sum_filter]
  simp

theorem exists_good_shorten {n m : ℕ} {ι : Type*} {I : Finset ι} {hn : 0 < n}
    {h : Fin n → Vec m} {U : Submodule F (Vec n)} (hU : good hn h U)
    (S : ↥I → Finset (Fin n))
    (hdisj : ∀ ⦃q r : ↥I⦄, q ≠ r → Disjoint (S q) (S r))
    (hsep : ∀ ⦃q r : ↥I⦄, q ≠ r → ∀ ⦃i⦄, i ∈ S q → next hn i ∉ S r)
    (hcover : ∀ i, i ∈ active U ↔ ∃ q : ↥I, i ∈ S q)
    (hconst : ∀ x ∈ U, ∀ q : ↥I, ∀ ⦃i j⦄, i ∈ S q → j ∈ S q → x i = x j)
    (p : ↥I) {V : Finset (Fin n)} (hVn : V.Nonempty) (hV : V ⊂ S p)
    (hspan : (∑ i ∈ V, h i) ∈ Submodule.span F (Set.range (fun q : ↥I => ∑ i ∈ S q, h i))) :
    ∃ U' : Submodule F (Vec n), good hn h U' ∧ Module.finrank F U ≤ Module.finrank F U' ∧
      active U' ⊂ active U := by
  classical
  let A : Vec n →ₗ[F] Vec m := Fintype.linearCombination F h
  let v (q : ↥I) : Vec m := ∑ i ∈ S q, h i
  have hc' : (∑ i ∈ V, h i) ∈ LinearMap.range (Fintype.linearCombination F v) := by
    simpa only [Fintype.range_linearCombination] using hspan
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hc'
  let z : Vec n := ∑ q : ↥I, c q • shorten_indicator (S q)
  have hzA : A z = ∑ i ∈ V, h i := by
    change A (∑ q : ↥I, c q • shorten_indicator (S q)) = _
    rw [map_sum]
    simp_rw [map_smul, show ∀ q : ↥I, A (shorten_indicator (S q)) = v q from
      fun q => shorten_syndrome_indicator h (S q)]
    exact hc
  have hz (q : ↥I) (i : Fin n) (hi : i ∈ S q) : z i = c q := by
    dsimp only [z]
    rw [Finset.sum_apply, Finset.sum_eq_single q]
    · simp [shorten_indicator, hi]
    · intro r _ hr
      have hri : i ∉ S r := fun hir => (Finset.disjoint_left.mp (hdisj hr)) hir hi
      simp [shorten_indicator, hri]
    · simp
  let w : Vec n := shorten_indicator V - z
  have hwA : A w = 0 := by
    change A (shorten_indicator V - z) = 0
    rw [map_sub, show A (shorten_indicator V) = ∑ i ∈ V, h i from
      shorten_syndrome_indicator h V, hzA, sub_self]
  have hw (q : ↥I) (i : Fin n) (hi : i ∈ S q) : w i = shorten_indicator V i - c q := by
    change shorten_indicator V i - z i = _
    rw [hz q i hi]
  have hVsub := (Finset.ssubset_iff_subset_ne.mp hV).1
  obtain ⟨a, ha⟩ := hVn
  obtain ⟨a', ha', ha'V⟩ := Finset.exists_of_ssubset hV
  have haS := hVsub ha

  obtain ⟨b, hb, hwb, d, hd, hwd⟩ :
      ∃ b ∈ S p, w b = 0 ∧ ∃ d ∈ S p, w d = 1 := by
    rcases shorten_binary (c p) with h0 | h1
    · exact ⟨a', ha', by simp [hw p a' ha', shorten_indicator, ha'V, h0],
        a, haS, by simp [hw p a haS, shorten_indicator, ha, h0]⟩
    · exact ⟨a, haS, by simp [hw p a haS, shorten_indicator, ha, h1],
        a', ha', by rw [hw p a' ha', h1]; simp [shorten_indicator, ha'V, show -(1 : F) = 1 by decide]⟩
  let T : Vec n →ₗ[F] Vec n :=
    LinearMap.id - (LinearMap.proj b : Vec n →ₗ[F] F).smulRight w
  have hT (x : Vec n) (i : Fin n) : T x i = x i - x b * w i := rfl
  have hTb (x : Vec n) : T x b = x b := by simp [hT, hwb]
  have hTinj : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hxb : x b = 0 := by simpa only [hTb, Pi.zero_apply] using congrFun hx b
    funext i
    simpa [hT, hxb] using congrFun hx i
  have hT_off (x : Vec n) (hx : x ∈ U) (i : Fin n) (hi : i ∉ active U) : T x i = 0 := by
    have hx0 : x i = 0 := by
      by_contra hxi
      exact hi (shorten_mem_active.mpr ⟨x, hx, hxi⟩)
    have hsnot (q : ↥I) : i ∉ S q := fun hq => hi ((hcover i).mpr ⟨q, hq⟩)
    have hz0 : z i = 0 := by simp [z, shorten_indicator, hsnot]
    have hvnot : i ∉ V := fun hvi => hsnot p (hVsub hvi)
    have hw0 : w i = 0 := by
      change shorten_indicator V i - z i = 0
      simp [shorten_indicator, hvnot, hz0]
    simp [hT, hx0, hw0]
  have hT_p (x : Vec n) (hx : x ∈ U) (i : Fin n) (hi : i ∈ S p) :
      T x i = x b * (1 - w i) := by
    rw [hT, hconst x hx p hi hb, mul_sub, mul_one]
  have hT_other (x : Vec n) (hx : x ∈ U) (q : ↥I) (hqp : q ≠ p)
      {i j : Fin n} (hi : i ∈ S q) (hj : j ∈ S q) : T x i = T x j := by
    have hnot (k : Fin n) (hk : k ∈ S q) : k ∉ V := fun hkV =>
      (Finset.disjoint_left.mp (hdisj hqp)) hk (hVsub hkV)
    simp only [hT, hw q i hi, hw q j hj, shorten_indicator, if_neg (hnot i hi), if_neg (hnot j hj),
      hconst x hx q hi hj]
  let U' := LinearMap.range (T.domRestrict U)
  have hpre {y : Vec n} (hy : y ∈ U') : ∃ x ∈ U, T x = y := by
    change y ∈ LinearMap.range (T.domRestrict U) at hy
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hy
    exact ⟨x, x.property, hx⟩
  refine ⟨U', ⟨?_, ?_⟩, ?_, ?_⟩
  · intro y hy a
    obtain ⟨x, hx, rfl⟩ := hpre hy
    have hAx : A x = 0 := by
      funext k
      exact (shorten_syndrome_apply h x k).trans (hU.1 x hx k)
    have hAT : A (T x) = 0 := by
      change A (x - x b • w) = 0
      simp [hAx, hwA]
    simpa only [A, shorten_syndrome_apply, Pi.zero_apply] using congrFun hAT a
  · intro u hu v' hv' i
    obtain ⟨x, hx, rfl⟩ := hpre hu
    obtain ⟨y, hy, rfl⟩ := hpre hv'
    by_cases hi : i ∈ active U
    · by_cases hj : next hn i ∈ active U
      · obtain ⟨q, hiq⟩ := (hcover i).mp hi
        obtain ⟨r, hjr⟩ := (hcover (next hn i)).mp hj
        have hqr : q = r := by
          by_contra hqr
          exact hsep hqr hiq hjr
        subst r
        by_cases hqp : q = p
        · subst q
          rw [hT_p x hx i hiq, hT_p x hx _ hjr, hT_p y hy i hiq, hT_p y hy _ hjr]
          ring
        · rw [hT_other x hx q hqp hiq hjr, hT_other y hy q hqp hiq hjr]
      · simp [hT_off x hx _ hj, hT_off y hy _ hj]
    · simp [hT_off x hx _ hi, hT_off y hy _ hi]
  · apply LinearMap.finrank_le_finrank_of_injective (f := (T.domRestrict U).rangeRestrict)
    intro x y hxy
    apply Subtype.ext
    exact hTinj (congrArg (fun e : U' => (e : Vec n)) hxy)
  · have hsub : active U' ⊆ active U := by
      intro i hi
      by_contra hni
      obtain ⟨y, hy, hyi⟩ := shorten_mem_active.mp hi
      obtain ⟨x, hx, rfl⟩ := hpre hy
      exact hyi (hT_off x hx i hni)
    apply (Finset.ssubset_iff_of_subset hsub).mpr
    refine ⟨d, (hcover d).mpr ⟨p, hd⟩, ?_⟩
    intro hda
    obtain ⟨y, hy, hyd⟩ := shorten_mem_active.mp hda
    obtain ⟨x, hx, rfl⟩ := hpre hy
    exact hyd (by rw [hT_p x hx d hd, hwd, sub_self, mul_zero])

end PEqualNP.Outside.L_lib_850

namespace PEqualNP.Outside.L_lib_850

private def hits {n : ℕ} (I : Finset (Fin n × Fin n)) (P : Finset (Fin n)) : Prop :=
  ∀ p ∈ I, ∃ v ∈ P, p.1 ≤ v ∧ v ≤ p.2

private theorem pack_le_hits {n : ℕ} {I M : Finset (Fin n × Fin n)} {P : Finset (Fin n)}
    (hMI : M ⊆ I) (hM : separated M) (hP : hits I P) : M.card ≤ P.card := by
  classical
  let pick (p : ↥M) : Fin n := Classical.choose (hP p.val (hMI p.property))
  have prop (p : ↥M) : pick p ∈ P ∧ p.val.1 ≤ pick p ∧ pick p ≤ p.val.2 :=
    Classical.choose_spec (hP p.val (hMI p.property))
  let f (p : ↥M) : ↥P := ⟨pick p, (prop p).1⟩
  apply Finset.card_le_card_of_injective (f := f)
  intro p q he
  have eq : pick p = pick q := congrArg Subtype.val he
  apply Subtype.ext
  by_contra hn
  obtain hh | hh := hM p.property q.property hn
  · exact (not_lt_of_ge ((prop q).2.1.trans (eq ▸ (prop p).2.2))) hh
  · exact (not_lt_of_ge ((prop p).2.1.trans (eq.symm ▸ (prop q).2.2))) hh

private theorem greedy {n : ℕ} (I : Finset (Fin n × Fin n)) (hv : ∀ p ∈ I, p.1 ≤ p.2) :
    ∃ M ⊆ I, separated M ∧ hits I (M.image Prod.snd) := by
  classical
  refine Finset.strongInductionOn
    (p := fun J => (∀ p ∈ J, p.1 ≤ p.2) → ∃ M ⊆ J, separated M ∧ hits J (M.image Prod.snd))
    I ?_ hv
  intro J ih hJ
  rcases J.eq_empty_or_nonempty with he | he
  · subst J
    exact ⟨∅, Finset.empty_subset _, by simp [separated], by simp [hits]⟩
  · obtain ⟨p,hp,hmin⟩ := Finset.exists_min_image J Prod.snd he
    let R := J.filter (fun q => p.2 < q.1)
    have hr : R ⊆ J := Finset.filter_subset _ _
    have hn : p ∉ R := fun h => (not_lt_of_ge (hJ p hp)) (Finset.mem_filter.mp h).2
    have hlt : R ⊂ J := (Finset.ssubset_iff_of_subset hr).2 ⟨p,hp,hn⟩
    obtain ⟨M, hMR, hsep, hhit⟩ := ih R hlt (fun q hq => hJ q (hr hq))
    have gap (q : Fin n × Fin n) (hq : q ∈ M) : p.2 < q.1 :=
      (Finset.mem_filter.mp (hMR hq)).2
    refine ⟨insert p M, ?_, ?_, ?_⟩
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hp
      · exact hr (hMR hq)
    · intro q hq r hr hne
      rcases Finset.mem_insert.mp hq with rfl | hq
      · rcases Finset.mem_insert.mp hr with rfl | hr
        · contradiction
        · exact Or.inl (gap r hr)
      · rcases Finset.mem_insert.mp hr with eq | hr
        · subst r
          exact Or.inr (gap q hq)
        · exact hsep hq hr hne
    · intro q hq
      by_cases hq' : p.2 < q.1
      · obtain ⟨v, hv, hl, hu⟩ := hhit q (Finset.mem_filter.mpr ⟨hq,hq'⟩)
        obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hv
        exact ⟨r.2, Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem hr), hl,hu⟩
      · exact ⟨p.2, Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _),
          le_of_not_gt hq', hmin q hq⟩

noncomputable def minimumHits {n : ℕ} (I : Finset (Fin n × Fin n)) : ℕ :=
  sInf {s : ℕ | ∃ P : Finset (Fin n), P.card = s ∧ hits I P}

theorem minimumHits_by_pack {n : ℕ} (I : Finset (Fin n × Fin n))
    (hv : ∀ p ∈ I, p.1 ≤ p.2) : ∃ M ⊆ I, separated M ∧ M.card = minimumHits I := by
  classical
  obtain ⟨M, hM, hp, hh⟩ := greedy I hv
  let H := M.image Prod.snd
  have hcard : M.card = H.card := le_antisymm (pack_le_hits hM hp hh) Finset.card_image_le
  have hH : H.card ∈ {s : ℕ | ∃ P : Finset (Fin n), P.card = s ∧ hits I P} := ⟨H,rfl,hh⟩
  refine ⟨M,hM,hp,?_⟩
  apply le_antisymm
  · unfold minimumHits
    obtain ⟨P, hP, hc⟩ := Nat.sInf_mem ⟨_,hH⟩
    rw [← hP]
    exact pack_le_hits hM hp hc
  · exact (Nat.sInf_le hH).trans_eq hcard.symm

theorem pack_le_minimumHits {n : ℕ} {I M : Finset (Fin n × Fin n)}
    (hv : ∀ p ∈ I, p.1 ≤ p.2) (hMI : M ⊆ I) (hM : separated M) : M.card ≤ minimumHits I := by
  classical
  have hne : {s : ℕ | ∃ P : Finset (Fin n), P.card = s ∧ hits I P}.Nonempty := by
    exact ⟨_, Finset.univ, rfl, fun p hp => ⟨p.1, Finset.mem_univ _, le_rfl, hv p hp⟩⟩
  unfold minimumHits
  obtain ⟨P, hP, hc⟩ := Nat.sInf_mem hne
  rw [← hP]
  exact pack_le_hits hMI hM hc

end PEqualNP.Outside.L_lib_850

namespace PEqualNP.Outside.L_lib_850
open scoped BigOperators

noncomputable def intervals {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m) (base : Fin n)
    (t : ℕ) (D : Submodule F (Vec m)) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun p => p.1 < p.2 ∧ p.2.val-p.1.val ≤ m-Module.finrank F D+1 ∧
    partialSum hn h base t p.2 - partialSum hn h base t p.1 ∈ D

theorem mem_intervals {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m) (base : Fin n)
    (t : ℕ) (D : Submodule F (Vec m)) (p : Fin n × Fin n) : p ∈ intervals hn h base t D ↔
      p.1 < p.2 ∧ p.2.val-p.1.val ≤ m-Module.finrank F D+1 ∧
        partialSum hn h base t p.2 - partialSum hn h base t p.1 ∈ D := by
  classical
  simp [intervals]

noncomputable def cutValue {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m) (base : Fin n)
    (D : Submodule F (Vec m)) (t : ℕ) : ℕ :=
  minimumHits (intervals hn h base t D) - Module.finrank F D

noncomputable def cutsMax {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m) (base : Fin n) : ℕ := by
  classical
  letI : Fintype (Submodule F (Vec m)) := Fintype.ofFinite _
  exact Finset.univ.sup fun D : Submodule F (Vec m) =>
    (Finset.range (min n (m-Module.finrank F D+2))).sup (cutValue hn h base D)

private noncomputable def B {n : ℕ} (hn : 0 < n) (base : Fin n) (t : ℕ)
    (I : Finset (Fin n × Fin n)) (p : ↥I) : Finset (Fin n) := block hn base t p.val

private theorem Bne {n : ℕ} (hn : 0 < n) (base : Fin n) (t : ℕ)
    {I : Finset (Fin n × Fin n)} (hv : ∀ p ∈ I, p.1 < p.2) (k : ↥I) : (B hn base t I k).Nonempty :=
  block_nonempty hn base t (hv k.val k.property)

private theorem Bdisj {n : ℕ} (hn : 0 < n) (base : Fin n) (t : ℕ)
    {I : Finset (Fin n × Fin n)} (hs : separated I) : Pairwise (fun k l => Disjoint (B hn base t I k) (B hn base t I l)) :=
  fun k l hkl => block_disjoint hn base t hs k.property l.property (fun e => hkl (Subtype.ext e))

private theorem Bsep {n : ℕ} (hn : 0 < n) (base : Fin n) (t : ℕ)
    {I : Finset (Fin n × Fin n)} (hs : separated I) : blocksSeparated hn (B hn base t I) :=
  fun {k l i} hi hj => Subtype.ext (block_eq_of_next_mem hn base t hs k.property l.property hi hj)

private theorem Bcover {n : ℕ} (hn : 0 < n) (base : Fin n) (t : ℕ)
    {I : Finset (Fin n × Fin n)} {S : Finset (Fin n)} (hc : I.biUnion (block hn base t) = S)
    (i : Fin n) : i ∈ S ↔ ∃ k : ↥I, i ∈ B hn base t I k := by
  rw [← hc, Finset.mem_biUnion]
  exact ⟨fun ⟨p,hp,hi⟩ => ⟨⟨p,hp⟩,hi⟩, fun ⟨p,hi⟩ => ⟨p.val,p.property,hi⟩⟩

private theorem Brange {n : ℕ} (hn : 0 < n) (base : Fin n) (t : ℕ)
    {I : Finset (Fin n × Fin n)} {S : Finset (Fin n)} (hc : I.biUnion (block hn base t) = S)
    (hv : ∀ p ∈ I, p.1 < p.2) (hs : separated I) {x : Vec n} :
    x ∈ LinearMap.range (emb (B hn base t I)) ↔ runCompat hn S x := by
  rw [mem_range_emb_iff (Bne hn base t hv) (Bdisj hn base t hs)]
  refine ⟨?_, ?_⟩
  · rintro ⟨hconst,hzero⟩
    refine ⟨fun i hi => hzero i (fun k hk => hi ((Bcover hn base t hc i).mpr ⟨k,hk⟩)), ?_⟩
    intro i hi hj
    obtain ⟨k,hk⟩ := (Bcover hn base t hc i).mp hi
    obtain ⟨l,hl⟩ := (Bcover hn base t hc (next hn i)).mp hj
    have eq : k = l := Bsep hn base t hs hk hl
    subst l
    exact hconst k i _ hk hl
  · intro hr
    refine ⟨?_, fun i hi => hr.1 i (fun ha => by obtain ⟨k,hk⟩ := (Bcover hn base t hc i).mp ha; exact hi k hk)⟩
    intro k i j hi hj
    exact const_on_block hr base t k.val (fun w hw => (Bcover hn base t hc w).mpr ⟨k,hw⟩) hi hj

private theorem cols_same {n m : ℕ} (h : Fin n → Vec m) {K L : Type} [Fintype K] [Fintype L]
    {A : K → Finset (Fin n)} {B' : L → Finset (Fin n)}
    (he : LinearMap.range (emb A) = LinearMap.range (emb B')) : columnSpace A h = columnSpace B' h := by
  unfold columnSpace
  rw [LinearMap.range_comp, LinearMap.range_comp, he]

private theorem good_le_kernelCode {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m)
    (base : Fin n) (t : ℕ) {I : Finset (Fin n × Fin n)} {U : Submodule F (Vec n)}
    (hg : good hn h U) (hc : I.biUnion (block hn base t) = active U)
    (hv : ∀ p ∈ I, p.1 < p.2) (hs : separated I) : U ≤ kernelCode (B hn base t I) h := by
  intro x hx
  rw [kernelCode_eq_range_inf_ker, Submodule.mem_inf, LinearMap.mem_ker]
  refine ⟨(Brange hn base t hc hv hs).mpr (good_runCompat hg hx), ?_⟩
  ext j
  rw [H_apply_coord, Pi.zero_apply]
  exact hg.1 x hx j

private theorem block_short {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m) (base : Fin n) (t : ℕ)
    {I : Finset (Fin n × Fin n)} {U : Submodule F (Vec n)} (hg : good hn h U)
    (hmin : ∀ V : Submodule F (Vec n), good hn h V → Module.finrank F U ≤ Module.finrank F V →
      (active U).card ≤ (active V).card)
    (hc : I.biUnion (block hn base t) = active U) (hs : separated I) (p : ↥I) :
    (B hn base t I p).card ≤ m-Module.finrank F (columnSpace (B hn base t I) h)+1 := by
  by_contra! hl
  obtain ⟨V,hVn,hVp,hD⟩ := exists_zero_sum_ssubset h _ (B hn base t I p) hl
  rw [columnSpace_eq_span] at hD
  obtain ⟨W,hw,hd,hss⟩ := exists_good_shorten hg (B hn base t I) (Bdisj hn base t hs)
    (fun {_q _r} hne {_i} hi hj => hne (Bsep hn base t hs hi hj)) (Bcover hn base t hc)
    (fun x hx k {_i _j} hi hj => const_on_block (good_runCompat hg hx) base t k.val
      (fun w hw => (Bcover hn base t hc w).mpr ⟨k,hw⟩) hi hj) p hVn hVp hD
  exact (not_lt_of_ge (hmin W hw hd)) (Finset.card_lt_card hss)

private theorem cut_le_opt {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m) (base : Fin n)
    (D : Submodule F (Vec m)) (t : ℕ) : cutValue hn h base D t ≤ optVal hn h := by
  classical
  let I := intervals hn h base t D
  have hv (p : Fin n × Fin n) (hp : p ∈ I) : p.1 < p.2 := ((mem_intervals hn h base t D p).mp hp).1
  obtain ⟨M,hMI,hs,hcard⟩ := minimumHits_by_pack I (fun p hp => (hv p hp).le)
  let b := B hn base t M
  have hcol (k : ↥M) : column b h k ∈ D := by
    have he := (mem_intervals hn h base t D k.val).mp (hMI k.property)
    change (∑ i ∈ block hn base t k.val, h i) ∈ D
    rw [sum_block_eq_partialSum_sub hn h base t he.1.le]
    exact he.2.2
  have hl := le_finrank_kernelCode_of_columns_mem (Bne hn base t (fun p hp => hv p (hMI hp)))
    (Bdisj hn base t hs) hcol
  rw [Fintype.card_coe, hcard] at hl
  exact hl.trans (opt_ge_dim hn h (kernelCode_good (Bdisj hn base t hs) (Bsep hn base t hs)))

theorem main_eq {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m) (base : Fin n) :
    optVal hn h = max (if (∑ i, h i) = 0 then 1 else 0) (cutsMax hn h base) := by
  classical
  letI : Fintype (Submodule F (Vec m)) := Fintype.ofFinite _
  apply le_antisymm
  · obtain ⟨U,hg,hd,hmin⟩ := minSupport_opt hn h
    rw [← hd]
    by_cases hfull : active U = Finset.univ
    · exact (full_le_repeat hn h hg hfull).trans (le_max_left _ _)
    obtain ⟨i, _, hi⟩ := (Finset.ssubset_iff_of_subset (Finset.subset_univ (active U))).1
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hfull⟩)
    have hinj : Function.Injective (fun j : Fin n => ix hn (base.val+j.val)) :=
      fun a b eq => Fin.ext (ix_add_left_inj hn base.val a.isLt b.isLt eq)
    obtain ⟨a, ha⟩ := Finite.surjective_of_injective hinj i
    change ix hn (base.val+a.val) = i at ha
    have hz : ix hn (base.val+a.val) ∉ active U := ha.symm ▸ hi
    obtain ⟨I,hs,hv,hc⟩ := exists_separated_blocks hn base a.val (active U) hz
    let D := columnSpace (B hn base a.val I) h
    let w := m-Module.finrank F D+1
    have hl : ∀ p ∈ I, (block hn base a.val p).card ≤ w :=
      fun p hp => block_short hn h base a.val hg hmin hc hs ⟨p,hp⟩
    obtain ⟨t,ht,hzt⟩ := near_cut hn base a.val w (active U) a.isLt hz I hc
      (fun {_p _q} hp hq {_i} hi hj => block_eq_of_next_mem hn base a.val hs hp hq hi hj) hl
    obtain ⟨J,hs',hv',hc'⟩ := exists_separated_blocks hn base t (active U) hzt
    have heq : LinearMap.range (emb (B hn base t J)) = LinearMap.range (emb (B hn base a.val I)) := by
      ext x
      rw [Brange hn base t hc' hv' hs', Brange hn base a.val hc hv hs]
    have hD : columnSpace (B hn base t J) h = D := cols_same h heq
    have hJI : J ⊆ intervals hn h base t D := by
      intro p hp
      apply (mem_intervals hn h base t D p).mpr
      refine ⟨hv' p hp, ?_, ?_⟩
      · have hb := block_short hn h base t hg hmin hc' hs' ⟨p,hp⟩
        rw [hD] at hb
        simpa only [B, block_card] using hb
      · rw [← sum_block_eq_partialSum_sub hn h base t (hv' p hp).le, ← hD]
        exact column_mem_columnSpace (B hn base t J) h ⟨p,hp⟩
    have hJ := pack_le_minimumHits (I := intervals hn h base t D)
      (fun p hp => ((mem_intervals hn h base t D p).mp hp).1.le) hJI hs'
    have hdim := Submodule.finrank_mono (good_le_kernelCode hn h base t hg hc' hv' hs')
    rw [finrank_kernelCode h (Bne hn base t hv') (Bdisj hn base t hs'), Fintype.card_coe, hD] at hdim
    have htop : cutValue hn h base D t ≤ cutsMax hn h base := by
      unfold cutsMax
      apply le_trans _ (Finset.le_sup (f := fun D : Submodule F (Vec m) =>
        (Finset.range (min n (m-Module.finrank F D+2))).sup (cutValue hn h base D)) (Finset.mem_univ D))
      exact Finset.le_sup (f := cutValue hn h base D) (Finset.mem_range.mpr (by simpa only [w, Nat.add_assoc] using ht))
    exact (hdim.trans ((Nat.sub_le_sub_right hJ _).trans htop)).trans (le_max_right _ _)
  · apply max_le
    · exact repeat_le_opt hn h
    · unfold cutsMax
      exact Finset.sup_le (fun D _ => Finset.sup_le (fun t _ => cut_le_opt hn h base D t))

theorem cutValue_eq_explicit {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m) (base : Fin n)
    (D : Submodule F (Vec m)) (t : ℕ) : cutValue hn h base D t =
      sInf {s : ℕ | ∃ P : Finset (Fin n), P.card = s ∧ ∀ l u : Fin n,
        l < u → u.val-l.val ≤ m-Module.finrank F D+1 →
        partialSum hn h base t u - partialSum hn h base t l ∈ D →
        ∃ v ∈ P, l ≤ v ∧ v ≤ u} - Module.finrank F D := by
  classical
  unfold cutValue minimumHits
  congr 2
  ext s
  refine ⟨?_, ?_⟩
  · rintro ⟨P, hp, hh⟩
    refine ⟨P, hp, fun l u hl hw hu => ?_⟩
    exact hh (l,u) ((mem_intervals hn h base t D (l,u)).mpr ⟨hl,hw,hu⟩)
  · rintro ⟨P,hp,hh⟩
    refine ⟨P,hp,?_⟩
    intro p hp'
    obtain ⟨hl,hw,hu⟩ := (mem_intervals hn h base t D p).mp hp'
    exact hh p.1 p.2 hl hw hu

end PEqualNP.Outside.L_lib_850

theorem PEqualNP.Outside.L_lib_850 : (∀ (n m : ℕ) (hn : 0 < n),
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let A := Fin m → F
  let W := Fin n → F
  letI : Fintype (Submodule F A) := Fintype.ofFinite _
  letI : Fintype (Submodule F W) := Fintype.ofFinite _
  let ix := fun i : ℕ => (⟨i % n, Nat.mod_lt _ hn⟩ : Fin n)
  ∀ (h : Fin n → A) (base : Fin n),
    let good := fun U : Submodule F W =>
      (∀ x ∈ U, ∀ a : Fin m, (∑ i, h i a * x i) = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ i : Fin n,
        x i * y (ix (i.val+1)) = x (ix (i.val+1)) * y i)
    let opt := (Finset.univ : Finset (Submodule F W)).sup
      (fun U => if good U then Module.finrank F U else 0)
    let repeatDim := if (∑ i : Fin n, h i) = 0 then 1 else 0
    let atCut := fun (D : Submodule F A) (t : ℕ) =>
      let r := Module.finrank F D
      let width := m-r+1
      let partialSum := fun p : Fin n =>
        ∑ k ∈ Finset.range p.val, h (ix (base.val+t+1+k))
      let covers := fun P : Finset (Fin n) => ∀ l u : Fin n,
        l < u → u.val-l.val ≤ width → partialSum u - partialSum l ∈ D →
        ∃ v ∈ P, l ≤ v ∧ v ≤ u
      let hits := sInf {s : ℕ | ∃ P : Finset (Fin n), P.card = s ∧ covers P}
      hits-r
    opt = max repeatDim ((Finset.univ : Finset (Submodule F A)).sup (fun D =>
      (Finset.range (min n (m - Module.finrank F D + 2))).sup (atCut D)))) := by
  intro n m hn
  dsimp only
  intro h base
  change L_lib_850.optVal hn h = _
  rw [L_lib_850.main_eq hn h base]
  congr 1
  · by_cases hs : (∑ i, h i) = 0 <;> simp [hs]
  · unfold L_lib_850.cutsMax
    apply Finset.sup_congr rfl
    intro D _
    apply Finset.sup_congr rfl
    intro t _
    exact L_lib_850.cutValue_eq_explicit hn h base D t

import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_866

abbrev F := ZMod 2
abbrev Vec (m : ℕ) := Fin m → F

private lemma zmod2_eq_one_of_ne_zero {x : F} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

private lemma zmod2_add_self (x : F) : x + x = 0 := by
  fin_cases x <;> decide

private lemma zmod2_add_eq_zero_iff {x y : F} : x + y = 0 ↔ x = y := by
  revert x y; decide

private lemma zmod2_mul_eq_one_iff {x y : F} : x * y = 1 ↔ x = 1 ∧ y = 1 := by
  revert x y; decide

private lemma zmod2_add_one_eq_of_ne {x y : F} : x ≠ y → x + 1 = y := by
  revert x y; decide

private lemma nat_mul_eq_cast_real {a b c : ℕ} (h : a * b = c) : (a : ℝ) * (b : ℝ) = (c : ℝ) := by
  exact_mod_cast h

private lemma nat_mul_le_cast_real {a b c : ℕ} (h : a * b ≤ c) : (a : ℝ) * (b : ℝ) ≤ (c : ℝ) := by
  exact_mod_cast h

private lemma nat_le_cast_real {a b : ℕ} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := by
  exact_mod_cast h

private lemma sum_div_real {ι : Type*} (s : Finset ι) (f : ι → ℝ) (c : ℝ) :
    (∑ i ∈ s, f i) / c = ∑ i ∈ s, f i / c := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

private lemma card_filter_eq {α : Type*} {f1 f2 : Fintype α} {p q : α → Prop}
    {dp : DecidablePred p} {dq : DecidablePred q} (h : ∀ x, p x ↔ q x) :
    (@Finset.filter α p dp (@Finset.univ α f1)).card =
    (@Finset.filter α q dq (@Finset.univ α f2)).card :=
  congrArg Finset.card (Finset.ext fun x => by simp only [Finset.mem_filter, Finset.mem_univ, true_and, h])

private lemma abs_sub_le_of_eq {x₁ x₂ y₁ y₂ B : ℝ} (hx : x₁ = x₂) (hy : y₁ = y₂)
    (h : |x₂ - y₂| ≤ B) : |x₁ - y₁| ≤ B := by
  rwa [hx, hy]

private lemma card_F : Fintype.card F = 2 := ZMod.card 2

private lemma card_Vec (m : ℕ) : Fintype.card (Vec m) = 2 ^ m := by
  simp [Vec]

private lemma card_fin_vec (n m : ℕ) : Fintype.card (Fin n → Vec m) = 2 ^ (m * n) := by
  rw [Fintype.card_fun, card_Vec, Fintype.card_fin, ← pow_mul]

def cnext {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

def cprev {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + n - 1) % n, Nat.mod_lt _ hn⟩

lemma cnext_cprev {n : ℕ} (hn : 0 < n) (i : Fin n) : cnext hn (cprev hn i) = i := by
  ext
  simp only [cnext, cprev]
  by_cases h0 : i.val = 0
  · have : (0 + n - 1) % n = n - 1 := by
      rw [zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h0, this, show n - 1 + 1 = n by omega, Nat.mod_self]
  · have hlt : i.val - 1 < n := by omega
    have h1 : (i.val + n - 1) % n = i.val - 1 := by
      rw [show i.val + n - 1 = (i.val - 1) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
    rw [h1, show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt i.isLt]

lemma cprev_cnext {n : ℕ} (hn : 0 < n) (i : Fin n) : cprev hn (cnext hn i) = i := by
  ext
  simp only [cnext, cprev]
  by_cases hlast : i.val + 1 = n
  · rw [hlast, Nat.mod_self, show 0 + n - 1 = n - 1 by omega, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hlt : i.val + 1 < n := by omega
    rw [Nat.mod_eq_of_lt hlt, show i.val + 1 + n - 1 = i.val + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt i.isLt]

lemma cnext_inj {n : ℕ} (hn : 0 < n) : Function.Injective (cnext hn) := fun _ _ h => by
  have := congrArg (cprev hn) h
  rwa [cprev_cnext, cprev_cnext] at this

lemma cprev_inj {n : ℕ} (hn : 0 < n) : Function.Injective (cprev hn) := fun _ _ h => by
  have := congrArg (cnext hn) h
  rwa [cnext_cprev, cnext_cprev] at this

lemma cnext_iter_val {n : ℕ} (hn : 0 < n) (i : Fin n) (d : ℕ) :
    ((cnext hn)^[d] i).val = (i.val + d) % n := by
  induction d with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ d ih =>
    rw [Function.iterate_succ_apply', cnext]
    dsimp only
    rw [ih, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, add_assoc]

lemma cprev_iter_val {n : ℕ} (hn : 0 < n) (i : Fin n) (d : ℕ) (hd : d ≤ n) :
    ((cprev hn)^[d] i).val = (i.val + n - d) % n := by
  induction d with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ d ih =>
    rw [Function.iterate_succ_apply', cprev]
    dsimp only
    rw [ih (by omega)]
    have h1 : ((i.val + n - d) % n + n - 1) % n = (i.val + n - (d + 1)) % n := by
      have hge : 1 ≤ i.val + n - d := by omega
      have hsub : (i.val + n - d) % n + n - 1 = (i.val + n - d) % n + (n - 1) := by omega
      rw [hsub, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have h2 : i.val + n - d + (n - 1) = (i.val + n - (d + 1)) + n := by omega
      rw [h2, Nat.add_mod_right]
    exact h1

lemma exists_cprev_iter {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    ∃ d < n, (cprev hn)^[d] i = j := by
  let d := (i.val + n - j.val) % n
  refine ⟨d, Nat.mod_lt _ hn, ?_⟩
  ext
  rw [cprev_iter_val hn i d (Nat.le_of_lt (Nat.mod_lt _ hn))]
  by_cases hle : j.val ≤ i.val
  · have hd : d = i.val - j.val := by
      dsimp only [d]
      rw [show i.val + n - j.val = (i.val - j.val) + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [hd, show i.val + n - (i.val - j.val) = j.val + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt j.isLt]
  · have hd : d = i.val + n - j.val := by
      dsimp only [d]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hd, show i.val + n - (i.val + n - j.val) = j.val by omega, Nat.mod_eq_of_lt j.isLt]

def starts {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter (fun i => cprev hn i ∉ S)

def ends {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter (fun i => cnext hn i ∉ S)

def nonTrans {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (i ∈ S) ↔ (cnext hn i ∈ S))

lemma card_starts_mul_two_le {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) :
    2 * (starts hn S).card ≤ n := by
  have hdisj : Disjoint (starts hn S) ((starts hn S).image (cprev hn)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_image] at hx2
    obtain ⟨y, hy, rfl⟩ := hx2
    exact (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hx1).1
  have himg : ((starts hn S).image (cprev hn)).card = (starts hn S).card :=
    Finset.card_image_of_injective _ (cprev_inj hn)
  have hun : (starts hn S ∪ (starts hn S).image (cprev hn)).card ≤ (Finset.univ : Finset (Fin n)).card :=
    Finset.card_le_univ _
  rw [Finset.card_union_of_disjoint hdisj, himg, Finset.card_univ, Fintype.card_fin] at hun
  omega

lemma card_ends_eq_card_starts {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) :
    (ends hn S).card = (starts hn S).card := by
  have h1 : S.image (cnext hn) \ S = (ends hn S).image (cnext hn) := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_image, ends, Finset.mem_filter]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hj⟩
      exact ⟨i, ⟨hi, hj⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hj⟩, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, hj⟩
  have h2 : S \ S.image (cnext hn) = starts hn S := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_image, starts, Finset.mem_filter]
    constructor
    · rintro ⟨hi, hni⟩
      refine ⟨hi, fun hp => hni ⟨cprev hn i, hp, cnext_cprev hn i⟩⟩
    · rintro ⟨hi, hp⟩
      refine ⟨hi, fun ⟨j, hj, hji⟩ => hp ?_⟩
      have : j = cprev hn i := by rw [← hji, cprev_cnext]
      rwa [← this]
  have hcard : (S.image (cnext hn)).card = S.card :=
    Finset.card_image_of_injective _ (cnext_inj hn)
  have hs1 := Finset.card_sdiff_add_card_inter (S.image (cnext hn)) S
  have hs2 := Finset.card_sdiff_add_card_inter S (S.image (cnext hn))
  rw [Finset.inter_comm] at hs2
  have heq : (S.image (cnext hn) \ S).card = (S \ S.image (cnext hn)).card := by omega
  rw [h1, h2, Finset.card_image_of_injective _ (cnext_inj hn)] at heq
  exact heq

lemma card_nonTrans {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) :
    (nonTrans hn S).card + 2 * (starts hn S).card = n := by
  have hcompl : (nonTrans hn S)ᶜ = ends hn S ∪ (starts hn S).image (cprev hn) := by
    ext i
    simp only [Finset.mem_compl, nonTrans, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, ends, Finset.mem_image, starts]
    constructor
    · intro h
      by_cases hi : i ∈ S
      · left; exact ⟨hi, fun hni => h ⟨fun _ => hni, fun _ => hi⟩⟩
      · right
        have hni : cnext hn i ∈ S := by
          by_contra hni; exact h ⟨fun h1 => absurd h1 hi, fun h2 => absurd h2 hni⟩
        exact ⟨cnext hn i, ⟨hni, by rwa [cprev_cnext]⟩, cprev_cnext hn i⟩
    · rintro (⟨hi, hni⟩ | ⟨j, ⟨hj, hpj⟩, rfl⟩)
      · intro h; exact hni (h.1 hi)
      · intro h; exact hpj (h.2 (by rwa [cnext_cprev]))
  have hdisj : Disjoint (ends hn S) ((starts hn S).image (cprev hn)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_image] at hx2
    obtain ⟨y, hy, rfl⟩ := hx2
    exact (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hx1).1
  have hc := Finset.card_add_card_compl (nonTrans hn S)
  rw [hcompl, Finset.card_union_of_disjoint hdisj, card_ends_eq_card_starts,
    Finset.card_image_of_injective _ (cprev_inj hn), Fintype.card_fin] at hc
  omega

lemma eq_of_nonTrans_eq {n : ℕ} (hn : 0 < n) {S T : Finset (Fin n)}
    (h0 : (⟨0, hn⟩ ∈ S) ↔ (⟨0, hn⟩ ∈ T))
    (hnt : nonTrans hn S = nonTrans hn T) : S = T := by
  have hstep : ∀ k (hk : k < n), (⟨k, hk⟩ ∈ S) ↔ (⟨k, hk⟩ ∈ T) := by
    intro k
    induction k with
    | zero => intro _; exact h0
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have hmem : (⟨k, hk'⟩ ∈ nonTrans hn S) ↔ (⟨k, hk'⟩ ∈ nonTrans hn T) := by rw [hnt]
      simp only [nonTrans, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      have hnx : cnext hn ⟨k, hk'⟩ = ⟨k + 1, hk⟩ := by
        ext; simp [cnext, Nat.mod_eq_of_lt hk]
      rw [hnx] at hmem
      have hprev := ih hk'
      tauto
  ext i
  exact hstep i.val i.isLt

lemma card_supports_with_starts {n : ℕ} (hn : 0 < n) (r : ℕ) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => (starts hn S).card = r)).card ≤
      2 * Nat.choose n (n - 2 * r) := by
  let f : Finset (Fin n) → Bool × Finset (Fin n) :=
    fun S => (decide (⟨0, hn⟩ ∈ S), nonTrans hn S)
  have hinj : Function.Injective f := by
    intro S T hST
    have h1 := congrArg Prod.fst hST
    have h2 := congrArg Prod.snd hST
    dsimp only [f] at h1 h2
    have h0 : (⟨0, hn⟩ ∈ S) ↔ (⟨0, hn⟩ ∈ T) := by
      constructor <;> intro h
      · exact of_decide_eq_true (h1 ▸ decide_eq_true h)
      · exact of_decide_eq_true (h1.symm ▸ decide_eq_true h)
    exact eq_of_nonTrans_eq hn h0 h2
  let src := (Finset.univ : Finset (Finset (Fin n))).filter (fun S => (starts hn S).card = r)
  let dst := (Finset.univ : Finset Bool) ×ˢ
    ((Finset.univ : Finset (Fin n)).powersetCard (n - 2 * r))
  have hsub : src.image f ⊆ dst := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨S, hS, rfl⟩ := hp
    rw [Finset.mem_filter] at hS
    rw [Finset.mem_product]
    refine ⟨Finset.mem_univ _, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩⟩
    dsimp only [f]
    have := card_nonTrans hn S
    rw [hS.2] at this
    omega
  calc src.card = (src.image f).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ dst.card := Finset.card_le_card hsub
    _ = 2 * Nat.choose n (n - 2 * r) := by
        simp [dst, Finset.card_product, Finset.card_powersetCard, Fintype.card_fin]

private lemma exists_not_mem_iter {n : ℕ} (hn : 0 < n) {S : Finset (Fin n)}
    (hS : S ≠ Finset.univ) (i : Fin n) :
    ∃ d : ℕ, (cprev hn)^[d + 1] i ∉ S := by
  have hex : ∃ z : Fin n, z ∉ S := by
    by_contra h
    push Not at h
    exact hS (Finset.eq_univ_iff_forall.mpr h)
  obtain ⟨z, hz⟩ := hex
  obtain ⟨d, _, hd⟩ := exists_cprev_iter hn (cprev hn i) z
  refine ⟨d, ?_⟩
  rw [Function.iterate_succ_apply, hd]
  exact hz

noncomputable def runDist {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) (i : Fin n) : ℕ :=
  @dite ℕ (∃ d : ℕ, (cprev hn)^[d + 1] i ∉ S) (Classical.propDecidable _)
    (fun h => Nat.find h) (fun _ => 0)

lemma runDist_eq_find {n : ℕ} (hn : 0 < n) {S : Finset (Fin n)} {i : Fin n}
    (hex : ∃ d : ℕ, (cprev hn)^[d + 1] i ∉ S) :
    runDist hn S i = Nat.find hex := by
  simp only [runDist, hex, ↓reduceDIte]

noncomputable def runHead {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) (i : Fin n) : Fin n :=
  (cprev hn)^[runDist hn S i] i

lemma runHead_mem_starts {n : ℕ} (hn : 0 < n) {S : Finset (Fin n)}
    (hS : S ≠ Finset.univ) {i : Fin n} (hi : i ∈ S) :
    runHead hn S i ∈ starts hn S := by
  have hex := exists_not_mem_iter hn hS i
  have hd_eq : runDist hn S i = Nat.find hex := runDist_eq_find hn hex
  have hspec : (cprev hn)^[runDist hn S i + 1] i ∉ S := hd_eq ▸ Nat.find_spec hex
  have hmem : (cprev hn)^[runDist hn S i] i ∈ S := by
    cases h0 : runDist hn S i with
    | zero => simpa using hi
    | succ d =>
      by_contra hnot
      have hlt : d < Nat.find hex := by omega
      exact Nat.find_min hex hlt hnot
  rw [starts, Finset.mem_filter]
  refine ⟨hmem, ?_⟩
  rw [runHead, ← Function.iterate_succ_apply' (cprev hn)]
  exact hspec

lemma runDist_self {n : ℕ} (hn : 0 < n) {S : Finset (Fin n)} {s : Fin n}
    (hs : s ∈ starts hn S) : runDist hn S s = 0 := by
  have h0 : (cprev hn)^[0 + 1] s ∉ S := by simpa using (Finset.mem_filter.mp hs).2
  have hex : ∃ d, (cprev hn)^[d + 1] s ∉ S := ⟨0, h0⟩
  rw [runDist_eq_find hn hex]
  exact Nat.eq_zero_of_le_zero (Nat.find_min' hex h0)

lemma runHead_self {n : ℕ} (hn : 0 < n) {S : Finset (Fin n)} {s : Fin n}
    (hs : s ∈ starts hn S) : runHead hn S s = s := by
  simp [runHead, runDist_self hn hs]

lemma runHead_cprev {n : ℕ} (hn : 0 < n) {S : Finset (Fin n)} (hS : S ≠ Finset.univ)
    {i : Fin n} (hp : cprev hn i ∈ S) :
    runHead hn S (cprev hn i) = runHead hn S i := by
  have hex1 := exists_not_mem_iter hn hS i
  have hex2 := exists_not_mem_iter hn hS (cprev hn i)
  have hpos : 0 < Nat.find hex1 := by
    by_contra h0
    have heq : Nat.find hex1 = 0 := by omega
    have hsp := Nat.find_spec hex1
    rw [heq] at hsp
    exact hsp (by simpa using hp)
  have hle1 : Nat.find hex2 ≤ Nat.find hex1 - 1 := by
    apply Nat.find_min' hex2
    have hsp := Nat.find_spec hex1
    have hstep : (cprev hn)^[Nat.find hex1 - 1 + 1] (cprev hn i) =
        (cprev hn)^[Nat.find hex1 + 1] i := by
      rw [← Function.iterate_succ_apply (cprev hn)]
      congr 1; omega
    rwa [hstep]
  have hle2 : Nat.find hex1 ≤ Nat.find hex2 + 1 := by
    apply Nat.find_min' hex1
    have hsp := Nat.find_spec hex2
    rwa [Function.iterate_succ_apply]
  have heq : Nat.find hex1 = Nat.find hex2 + 1 := by omega
  rw [runHead, runHead, runDist_eq_find hn hex1, runDist_eq_find hn hex2, heq, Function.iterate_succ_apply]

noncomputable def runOf {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) (s : Fin n) : Finset (Fin n) :=
  S.filter (fun i => runHead hn S i = s)

lemma self_mem_runOf {n : ℕ} (hn : 0 < n) {S : Finset (Fin n)} {s : Fin n}
    (hs : s ∈ starts hn S) : s ∈ runOf hn S s := by
  rw [runOf, Finset.mem_filter]
  exact ⟨(Finset.mem_filter.mp hs).1, runHead_self hn hs⟩

lemma runOf_inter_starts {n : ℕ} (hn : 0 < n) {S : Finset (Fin n)} {s t : Fin n}
    (ht : t ∈ starts hn S) : t ∈ runOf hn S s ↔ t = s := by
  rw [runOf, Finset.mem_filter, runHead_self hn ht]
  exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.mp ht).1, h⟩⟩

lemma runOf_disjoint {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) {s1 s2 : Fin n} (hne : s1 ≠ s2) :
    Disjoint (runOf hn S s1) (runOf hn S s2) := by
  rw [Finset.disjoint_left]
  intro i h1 h2
  exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)

lemma biUnion_runOf {n : ℕ} (hn : 0 < n) {S : Finset (Fin n)} (hS : S ≠ Finset.univ) :
    (starts hn S).biUnion (runOf hn S) = S := by
  ext i
  simp only [Finset.mem_biUnion, runOf, Finset.mem_filter]
  constructor
  · rintro ⟨_, _, hi, _⟩; exact hi
  · intro hi; exact ⟨runHead hn S i, runHead_mem_starts hn hS hi, hi, rfl⟩

def Iso {n : ℕ} (hn : 0 < n) (U : Submodule F (Fin n → F)) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ i : Fin n, x i * y (cnext hn i) = x (cnext hn i) * y i

noncomputable def suppU {n : ℕ} (U : Submodule F (Fin n → F)) : Finset (Fin n) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  Finset.univ.filter (fun i => ∃ x ∈ U, x i ≠ 0)

lemma mem_suppU {n : ℕ} {U : Submodule F (Fin n → F)} {i : Fin n} :
    i ∈ suppU U ↔ ∃ x ∈ U, x i ≠ 0 := by
  simp only [suppU, Finset.mem_filter, Finset.mem_univ, true_and]

lemma iso_eq_cnext {n : ℕ} (hn : 0 < n) {U : Submodule F (Fin n → F)} (hU : Iso hn U)
    {i : Fin n} (hi : i ∈ suppU U) (hni : cnext hn i ∈ suppU U) :
    ∀ x ∈ U, x i = x (cnext hn i) := by
  rw [mem_suppU] at hi hni
  obtain ⟨y, hyU, hyi⟩ := hi
  obtain ⟨z, hzU, hzni⟩ := hni
  have hy1 : y i = 1 := zmod2_eq_one_of_ne_zero hyi
  have hz1 : z (cnext hn i) = 1 := zmod2_eq_one_of_ne_zero hzni
  have hyz := hU y hyU z hzU i
  rw [hy1, hz1, one_mul] at hyz
  have hyn1 : y (cnext hn i) = 1 := (zmod2_mul_eq_one_iff.mp hyz.symm).1
  intro x hxU
  have hxy := hU x hxU y hyU i
  rw [hy1, hyn1, mul_one, mul_one] at hxy
  exact hxy

lemma iso_eq_cprev {n : ℕ} (hn : 0 < n) {U : Submodule F (Fin n → F)} (hU : Iso hn U)
    {i : Fin n} (hi : i ∈ suppU U) (hpi : cprev hn i ∈ suppU U) :
    ∀ x ∈ U, x i = x (cprev hn i) := by
  intro x hxU
  have h := iso_eq_cnext hn hU hpi (by rwa [cnext_cprev]) x hxU
  rw [cnext_cprev] at h
  exact h.symm

lemma finrank_le_one_of_suppU_univ {n : ℕ} (hn : 0 < n) {U : Submodule F (Fin n → F)}
    (hU : Iso hn U) (huniv : suppU U = Finset.univ) : Module.finrank F U ≤ 1 := by
  have hconst : ∀ x ∈ U, ∀ i : Fin n, x i = x ⟨0, hn⟩ := by
    intro x hxU i
    have hwalk : ∀ d (j : Fin n), x j = x ((cprev hn)^[d] j) := by
      intro d
      induction d with
      | zero => intro _; rfl
      | succ d ih =>
        intro j
        rw [Function.iterate_succ_apply]
        have h1 := iso_eq_cprev hn hU (huniv ▸ Finset.mem_univ j) (huniv ▸ Finset.mem_univ _) x hxU
        exact h1.trans (ih (cprev hn j))
    obtain ⟨d, _, hd⟩ := exists_cprev_iter hn i ⟨0, hn⟩
    rw [← hd]
    exact hwalk d i
  let ev0 : U →ₗ[F] F :=
    { toFun := fun x => x.val ⟨0, hn⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev0 := by
    intro x y hxy
    apply Subtype.ext
    funext i
    rw [hconst x.val x.2 i, hconst y.val y.2 i]
    exact hxy
  calc Module.finrank F U ≤ Module.finrank F F := LinearMap.finrank_le_finrank_of_injective hinj
    _ = 1 := Module.finrank_self F

lemma iso_eq_runHead {n : ℕ} (hn : 0 < n) {U : Submodule F (Fin n → F)} (hU : Iso hn U)
    (hne : suppU U ≠ Finset.univ) {x : Fin n → F} (hxU : x ∈ U) {i : Fin n} (hi : i ∈ suppU U) :
    x i = x (runHead hn (suppU U) i) := by
  have hex := exists_not_mem_iter hn hne i
  have hd_eq : runDist hn (suppU U) i = Nat.find hex := runDist_eq_find hn hex
  have hwalk : ∀ t ≤ Nat.find hex, (cprev hn)^[t] i ∈ suppU U ∧ x ((cprev hn)^[t] i) = x i := by
    intro t
    induction t with
    | zero => intro _; exact ⟨hi, rfl⟩
    | succ t ih =>
      intro hlt
      obtain ⟨hprev_mem, hprev_eq⟩ := ih (by omega)
      have hcur_mem : (cprev hn)^[t + 1] i ∈ suppU U := by
        by_contra hnot
        exact Nat.find_min hex (show t < Nat.find hex by omega) hnot
      have hstep := iso_eq_cprev hn hU hprev_mem
        (by rw [← Function.iterate_succ_apply' (cprev hn)]; exact hcur_mem) x hxU
      rw [← Function.iterate_succ_apply' (cprev hn)] at hstep
      exact ⟨hcur_mem, hstep.symm.trans hprev_eq⟩
  rw [runHead, hd_eq]
  exact (hwalk (Nat.find hex) le_rfl).2.symm

noncomputable def runSum {n m : ℕ} (hn : 0 < n) (h : Fin n → Vec m) (S : Finset (Fin n)) (s : Fin n) :
    Vec m :=
  ∑ i ∈ runOf hn S s, h i

def Hit {n m : ℕ} (hn : 0 < n) (S : Finset (Fin n)) (D : Submodule F (Vec m))
    (h : Fin n → Vec m) : Prop :=
  ∀ s ∈ starts hn S, runSum hn h S s ∈ D

lemma exists_submodule_ge_finrank {m : ℕ} (W : Submodule F (Vec m)) {t : ℕ}
    (ht : Module.finrank F W ≤ t) (htm : t ≤ m) :
    ∃ D : Submodule F (Vec m), W ≤ D ∧ Module.finrank F D = t := by
  have hdiff : ∀ d : ℕ, ∀ W : Submodule F (Vec m), Module.finrank F W + d = t →
      ∃ D : Submodule F (Vec m), W ≤ D ∧ Module.finrank F D = t := by
    intro d
    induction d with
    | zero =>
      intro W hW
      exact ⟨W, le_rfl, by omega⟩
    | succ d ih =>
      intro W hW
      have hlt : Module.finrank F W < Module.finrank F (Vec m) := by
        rw [Module.finrank_fin_fun]; omega
      have hne : W ≠ ⊤ := by
        intro htop
        rw [htop, finrank_top] at hlt
        exact lt_irrefl _ hlt
      have hex : ∃ v : Vec m, v ∉ W := by
        by_contra h
        push Not at h
        exact hne (eq_top_iff.mpr fun v _ => h v)
      obtain ⟨v, hv⟩ := hex
      let W' := W ⊔ Submodule.span F {v}
      have hdisj : W ⊓ Submodule.span F {v} = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Submodule.mem_inf, Submodule.mem_span_singleton] at hx
        obtain ⟨hxW, c, rfl⟩ := hx
        by_cases hc : c = 0
        · simp [hc]
        · have hc1 : c = 1 := zmod2_eq_one_of_ne_zero hc
          rw [hc1, one_smul] at hxW
          exact absurd hxW hv
      have hv0 : v ≠ 0 := fun h0 => hv (h0 ▸ W.zero_mem)
      have hspan1 : Module.finrank F (Submodule.span F {v}) = 1 := finrank_span_singleton hv0
      have hadd := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span F {v})
      rw [hdisj, finrank_bot, add_zero, hspan1] at hadd
      have hW' : Module.finrank F W' = Module.finrank F W + 1 := hadd
      obtain ⟨D, hWD, hD⟩ := ih W' (by omega)
      exact ⟨D, le_trans le_sup_left hWD, hD⟩
  exact hdiff (t - Module.finrank F W) W (by omega)

def cycleEvent {n m : ℕ} (hn : 0 < n) (a k : ℕ) (h : Fin n → Vec m) : Prop :=
  ∃ U : Submodule F (Fin n → F), a + k ≤ Module.finrank F U + m ∧
    (∀ x ∈ U, ∀ b : Fin m, (∑ i, h i b * x i) = 0) ∧
    Iso hn U

lemma cycleEvent_imp_hit {n m a k : ℕ} (hn : 0 < n) (hk : 1 ≤ k) (hkm : k ≤ m)
    (hna : n / 2 = a) (ha : m + 2 ≤ a + k) {h : Fin n → Vec m}
    (hev : cycleEvent hn a k h) :
    ∃ (S : Finset (Fin n)) (D : Submodule F (Vec m)),
      S ≠ Finset.univ ∧
      (starts hn S).card ≤ a ∧
      a - (starts hn S).card ≤ m - k ∧
      Module.finrank F D + (k + (a - (starts hn S).card)) = m ∧
      Hit hn S D h := by
  classical
  obtain ⟨U, hdim, hker, hiso⟩ := hev
  let S := suppU U
  have hSne : S ≠ Finset.univ := by
    intro huniv
    have := finrank_le_one_of_suppU_univ hn hiso huniv
    omega
  have hr_le : (starts hn S).card ≤ a := by
    have := card_starts_mul_two_le hn S
    omega
  let L : (starts hn S → F) →ₗ[F] Vec m :=
    { toFun := fun c => ∑ s : starts hn S, c s • runSum hn h S s.val
      map_add' := fun c1 c2 => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        simp only [Pi.smul_apply, smul_assoc, Finset.smul_sum, RingHom.id_apply] }
  let res : U →ₗ[F] LinearMap.ker L :=
    { toFun := fun x =>
        ⟨fun s => x.val s.val, by
          rw [LinearMap.mem_ker]
          ext b
          simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply,
            smul_eq_mul, Pi.zero_apply]
          have hsum_eq : (∑ s : starts hn S, x.val s.val * runSum hn h S s.val b) =
              ∑ i : Fin n, h i b * x.val i := by
            rw [← Finset.sum_subset (Finset.subset_univ S)]
            · conv_rhs => rw [← biUnion_runOf hn hSne]
              rw [Finset.sum_biUnion (fun s1 _ s2 _ hne => runOf_disjoint hn S hne)]
              rw [Finset.sum_coe_sort (starts hn S) (fun s => x.val s * runSum hn h S s b)]
              refine Finset.sum_congr rfl fun s hs => ?_
              rw [runSum, Finset.sum_apply, Finset.mul_sum]
              refine Finset.sum_congr rfl fun i hi => ?_
              have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
              have hrh : runHead hn S i = s := (Finset.mem_filter.mp hi).2
              rw [iso_eq_runHead hn hiso hSne x.2 hiS, hrh, mul_comm]
            · intro i _ hiS
              have hxi0 : x.val i = 0 := by
                by_contra hnz
                exact hiS (mem_suppU.mpr ⟨x.val, x.2, hnz⟩)
              simp [hxi0]
          rw [hsum_eq]
          exact hker x.val x.2 b⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hres_inj : Function.Injective res := by
    intro x y hxy
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S
    · rw [iso_eq_runHead hn hiso hSne x.2 hi, iso_eq_runHead hn hiso hSne y.2 hi]
      have hst : runHead hn S i ∈ starts hn S := runHead_mem_starts hn hSne hi
      exact congrFun (congrArg Subtype.val hxy) ⟨runHead hn S i, hst⟩
    · have hx0 : x.val i = 0 := by
        by_contra hnz; exact hi (mem_suppU.mpr ⟨x.val, x.2, hnz⟩)
      have hy0 : y.val i = 0 := by
        by_contra hnz; exact hi (mem_suppU.mpr ⟨y.val, y.2, hnz⟩)
      rw [hx0, hy0]
  have hU_le : Module.finrank F U ≤ Module.finrank F (LinearMap.ker L) :=
    LinearMap.finrank_le_finrank_of_injective hres_inj
  have hrn := LinearMap.finrank_range_add_finrank_ker L
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hrn
  have hgap : a - (starts hn S).card ≤ m - k := by omega
  have hrg : Module.finrank F (LinearMap.range L) ≤ m - (k + (a - (starts hn S).card)) := by omega
  obtain ⟨D, hWD, hD⟩ := exists_submodule_ge_finrank (LinearMap.range L) hrg (by omega)
  refine ⟨S, D, hSne, hr_le, hgap, by omega, ?_⟩
  intro s hs
  apply hWD
  refine ⟨Pi.single ⟨s, hs⟩ 1, ?_⟩
  simp only [L, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single ⟨s, hs⟩]
  · simp
  · intro t _ ht
    simp [Pi.single_eq_of_ne ht]
  · intro hnot; exact absurd (Finset.mem_univ _) hnot

lemma hit_imp_cycleEvent {n m a k : ℕ} (hn : 0 < n) {S : Finset (Fin n)} (hSne : S ≠ Finset.univ)
    (hcard : (starts hn S).card = a) {D : Submodule F (Vec m)} (hD : Module.finrank F D + k = m)
    {h : Fin n → Vec m} (hhit : Hit hn S D h) :
    cycleEvent hn a k h := by
  classical
  let L : (starts hn S → F) →ₗ[F] Vec m :=
    { toFun := fun c => ∑ s : starts hn S, c s • runSum hn h S s.val
      map_add' := fun c1 c2 => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        simp only [Pi.smul_apply, smul_assoc, Finset.smul_sum, RingHom.id_apply] }
  let extM : (starts hn S → F) →ₗ[F] (Fin n → F) :=
    { toFun := fun c i => if hi : i ∈ S then c ⟨runHead hn S i, runHead_mem_starts hn hSne hi⟩ else 0
      map_add' := fun c1 c2 => by funext i; simp only [Pi.add_apply]; split_ifs with hi <;> simp
      map_smul' := fun r c => by funext i; simp only [Pi.smul_apply]; split_ifs with hi <;> simp }
  have hext_inj : Function.Injective extM := by
    intro c1 c2 hc
    funext s
    have h1 := congrFun hc s.val
    have hsS : s.val ∈ S := (Finset.mem_filter.mp s.2).1
    simp only [extM, LinearMap.coe_mk, AddHom.coe_mk, hsS, ↓reduceDIte] at h1
    have hr : (⟨runHead hn S s.val, runHead_mem_starts hn hSne hsS⟩ : starts hn S) = s :=
      Subtype.ext (runHead_self hn s.2)
    rwa [hr] at h1
  let U : Submodule F (Fin n → F) := (LinearMap.ker L).map extM
  have hrg_le : LinearMap.range L ≤ D := by
    rintro _ ⟨c, rfl⟩
    exact Submodule.sum_mem D fun s _ => Submodule.smul_mem D _ (hhit s.val s.2)
  have hrg_dim : Module.finrank F (LinearMap.range L) ≤ Module.finrank F D :=
    Submodule.finrank_mono hrg_le
  have hrn := LinearMap.finrank_range_add_finrank_ker L
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hcard] at hrn
  have hU_dim : Module.finrank F U = Module.finrank F (LinearMap.ker L) :=
    (Submodule.equivMapOfInjective extM hext_inj (LinearMap.ker L)).finrank_eq.symm
  refine ⟨U, by omega, ?_, ?_⟩
  · intro x hxU b
    obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hxU
    have hLc : (L c) b = 0 := by rw [LinearMap.mem_ker.mp hc]; rfl
    rw [← hLc]
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    · have hbi : ∑ x ∈ S, h x b * extM c x =
          ∑ x ∈ (starts hn S).biUnion (runOf hn S), h x b * extM c x :=
        Finset.sum_congr (biUnion_runOf hn hSne).symm (fun _ _ => rfl)
      rw [hbi]
      rw [Finset.sum_biUnion (fun s1 _ s2 _ hne => runOf_disjoint hn S hne)]
      rw [← Finset.sum_attach (starts hn S), Finset.univ_eq_attach]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [runSum, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
      have hrh : runHead hn S i = s.val := (Finset.mem_filter.mp hi).2
      simp only [extM, LinearMap.coe_mk, AddHom.coe_mk, hiS, ↓reduceDIte]
      have heq : (⟨runHead hn S i, runHead_mem_starts hn hSne hiS⟩ : starts hn S) = s :=
        Subtype.ext hrh
      rw [heq, mul_comm]
    · intro i _ hiS
      simp [extM, hiS]
  · intro x hxU y hyU i
    obtain ⟨cx, _, rfl⟩ := Submodule.mem_map.mp hxU
    obtain ⟨cy, _, rfl⟩ := Submodule.mem_map.mp hyU
    by_cases hi : i ∈ S
    · by_cases hni : cnext hn i ∈ S
      · have hrh : runHead hn S (cnext hn i) = runHead hn S i := by
          have h1 := runHead_cprev hn hSne (i := cnext hn i) (by rwa [cprev_cnext])
          rw [cprev_cnext] at h1
          exact h1.symm
        have hsub : (⟨runHead hn S (cnext hn i), runHead_mem_starts hn hSne hni⟩ : starts hn S) =
            ⟨runHead hn S i, runHead_mem_starts hn hSne hi⟩ := Subtype.ext hrh
        simp only [extM, LinearMap.coe_mk, AddHom.coe_mk, hi, hni, ↓reduceDIte, hsub]
      · simp [extM, hni]
    · simp [extM, hi]

lemma card_fiber_surj {M N : Type*} [AddCommGroup M] [Module F M] [Fintype M] [DecidableEq M]
    [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N]
    (f : M →ₗ[F] N) (hsurj : Function.Surjective f) (y : N) :
    (Finset.univ.filter (fun x : M => f x = y)).card * Fintype.card N = Fintype.card M := by
  have hfib_eq : ∀ y1 y2 : N,
      (Finset.univ.filter (fun x : M => f x = y1)).card =
      (Finset.univ.filter (fun x : M => f x = y2)).card := by
    intro y1 y2
    obtain ⟨x1, rfl⟩ := hsurj y1
    obtain ⟨x2, rfl⟩ := hsurj y2
    refine Finset.card_bij (fun x _ => x + (x2 - x1)) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ _, by rw [map_add, map_sub, hx.2]; abel⟩
    · intro a _ b _ hab
      exact add_right_cancel hab
    · intro z hz
      rw [Finset.mem_filter] at hz
      refine ⟨z - (x2 - x1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by abel⟩
      rw [map_sub, map_sub, hz.2]; abel
  have hsum : ∑ z : N, (Finset.univ.filter (fun x : M => f x = z)).card = Fintype.card M := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp
    · intro a _ b _ hab
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact hab ((Finset.mem_filter.mp hx1).2.symm.trans (Finset.mem_filter.mp hx2).2)
  have hconst : ∑ z : N, (Finset.univ.filter (fun x : M => f x = z)).card =
      Fintype.card N * (Finset.univ.filter (fun x : M => f x = y)).card := by
    rw [Finset.sum_congr rfl (fun z _ => hfib_eq z y), Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [mul_comm]
  omega

lemma exists_surj_of_finrank {m d : ℕ} (D : Submodule F (Vec m))
    (hD : Module.finrank F D + d = m) :
    ∃ π : Vec m →ₗ[F] Vec d, Function.Surjective π ∧ LinearMap.ker π = D := by
  obtain ⟨E, hDE⟩ := Submodule.exists_isCompl D
  have hadd := Submodule.finrank_sup_add_finrank_inf_eq D E
  rw [hDE.sup_eq_top, hDE.inf_eq_bot, finrank_top, finrank_bot, add_zero,
    Module.finrank_fin_fun] at hadd
  have hE : Module.finrank F E = Module.finrank F (Vec d) := by
    rw [Module.finrank_fin_fun]; omega
  let e1 : (D × E) ≃ₗ[F] Vec m := Submodule.prodEquivOfIsCompl D E hDE
  let e2 : E ≃ₗ[F] Vec d := LinearEquiv.ofFinrankEq E (Vec d) hE
  let π : Vec m →ₗ[F] Vec d := e2.toLinearMap.comp ((LinearMap.snd F D E).comp e1.symm.toLinearMap)
  refine ⟨π, ?_, ?_⟩
  · intro y
    refine ⟨e1 (0, e2.symm y), ?_⟩
    simp [π]
  · ext v
    rw [LinearMap.mem_ker]
    constructor
    · intro hv
      have h2 : (e1.symm v).2 = 0 := e2.injective (by simpa [π] using hv)
      have hv_eq : v = e1 (e1.symm v) := (e1.apply_symm_apply v).symm
      rw [hv_eq]
      change ((e1.symm v).1 : Vec m) + ((e1.symm v).2 : Vec m) ∈ D
      rw [h2, Submodule.coe_zero, add_zero]
      exact (e1.symm v).1.2
    · intro hv
      have hv_eq : e1.symm v = (⟨v, hv⟩, 0) := by
        apply e1.injective
        rw [e1.apply_symm_apply]
        change v = v + 0
        simp
      simp [π, hv_eq]

noncomputable def runSumMap {n : ℕ} (hn : 0 < n) (W : Type*) [AddCommGroup W] [Module F W]
    (S : Finset (Fin n)) : (Fin n → W) →ₗ[F] (starts hn S → W) :=
  { toFun := fun v s => ∑ i ∈ runOf hn S s.val, v i
    map_add' := fun _ _ => by funext s; simp only [Pi.add_apply, Finset.sum_add_distrib]
    map_smul' := fun r v => by
      funext s
      simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum] }

lemma surj_runSumMap {n : ℕ} (hn : 0 < n) (W : Type*) [AddCommGroup W] [Module F W]
    (S : Finset (Fin n)) : Function.Surjective (runSumMap hn W S) := by
  intro w
  refine ⟨fun i => if hi : i ∈ starts hn S then w ⟨i, hi⟩ else 0, ?_⟩
  funext s
  dsimp only [runSumMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single s.val]
  · simp only [s.2, ↓reduceDIte]
  · intro i hi hne
    by_cases hst : i ∈ starts hn S
    · exfalso
      exact hne ((runOf_inter_starts hn hst).mp hi)
    · simp only [hst, ↓reduceDIte]
  · intro hnot
    exact absurd (self_mem_runOf hn s.2) hnot

lemma card_hit {n m d : ℕ} (hn : 0 < n) (S : Finset (Fin n)) (D : Submodule F (Vec m))
    (hD : Module.finrank F D + d = m) [DecidablePred (Hit hn S D)] :
    ((Finset.univ : Finset (Fin n → Vec m)).filter (Hit hn S D)).card *
      2 ^ (d * (starts hn S).card) = 2 ^ (m * n) := by
  obtain ⟨π, hsurj, hker⟩ := exists_surj_of_finrank D hD
  let T := runSumMap hn (Vec d) S
  let compπ : (Fin n → Vec m) →ₗ[F] (Fin n → Vec d) :=
    { toFun := fun h i => π (h i)
      map_add' := fun _ _ => by funext i; exact map_add π _ _
      map_smul' := fun _ _ => by funext i; exact map_smul π _ _ }
  have hcomp_surj : Function.Surjective compπ := fun v =>
    ⟨fun i => Classical.choose (hsurj (v i)), funext fun i => Classical.choose_spec (hsurj (v i))⟩
  have hT_surj : Function.Surjective T := surj_runSumMap hn (Vec d) S
  let L := T.comp compπ
  have hL_surj : Function.Surjective L := hT_surj.comp hcomp_surj
  have hfilt : (Finset.univ.filter (Hit hn S D)) = Finset.univ.filter (fun h => L h = 0) := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Hit, L, LinearMap.comp_apply, T,
      runSumMap, compπ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [funext_iff]
    simp only [Pi.zero_apply, Subtype.forall]
    refine forall₂_congr fun s _ => ?_
    rw [runSum, ← map_sum π, ← LinearMap.mem_ker, hker]
  rw [hfilt]
  have hfib := card_fiber_surj L hL_surj 0
  simp only [Fintype.card_fun, card_F, Fintype.card_fin, Fintype.card_coe, ← pow_mul] at hfib
  exact hfib

lemma card_hit_inter_ne {n m k : ℕ} (hn : 0 < n) (S1 S2 : Finset (Fin n))
    {D1 D2 : Submodule F (Vec m)}
    (hD1 : Module.finrank F D1 + k = m) (hD2 : Module.finrank F D2 + k = m) (hne : D1 ≠ D2)
    [DecidablePred (fun h : Fin n → Vec m => Hit hn S1 D1 h ∧ Hit hn S2 D2 h)] :
    ((Finset.univ : Finset (Fin n → Vec m)).filter (fun h => Hit hn S1 D1 h ∧ Hit hn S2 D2 h)).card *
      2 ^ (k * (starts hn S1).card + (starts hn S2).card) ≤ 2 ^ (m * n) := by
  obtain ⟨π1, hsurj1, hker1⟩ := exists_surj_of_finrank D1 hD1
  obtain ⟨π2, _, hker2⟩ := exists_surj_of_finrank D2 hD2
  have hex_v : ∃ v ∈ D1, v ∉ D2 := by
    by_contra h
    push Not at h
    have hle : D1 ≤ D2 := h
    have heq := Submodule.eq_of_le_of_finrank_eq hle (by omega)
    exact hne heq
  obtain ⟨v, hv1, hv2⟩ := hex_v
  have hv2_ne : π2 v ≠ 0 := fun h0 => hv2 (hker2 ▸ LinearMap.mem_ker.mpr h0)
  have hex_c : ∃ c : Fin k, π2 v c ≠ 0 := by
    by_contra h; push Not at h; exact hv2_ne (funext h)
  obtain ⟨c, hc⟩ := hex_c
  have hc1 : π2 v c = 1 := zmod2_eq_one_of_ne_zero hc
  let φ : Vec m →ₗ[F] F := (LinearMap.proj c).comp π2
  have hφ_v : φ v = 1 := hc1
  have hπ1_v : π1 v = 0 := LinearMap.mem_ker.mp (hker1.symm ▸ hv1)
  have hD2_ker : D2 ≤ LinearMap.ker φ := by
    intro w hw
    rw [LinearMap.mem_ker]
    have h0 : π2 w = 0 := LinearMap.mem_ker.mp (hker2.symm ▸ hw)
    simp [φ, h0]
  let Ψ : Vec m →ₗ[F] Vec k × F := π1.prod φ
  have hΨ_surj : Function.Surjective Ψ := by
    rintro ⟨u, b⟩
    obtain ⟨w, hw⟩ := hsurj1 u
    by_cases hbw : φ w = b
    · exact ⟨w, Prod.ext hw hbw⟩
    · refine ⟨w + v, Prod.ext ?_ ?_⟩
      · simp [Ψ, hw, hπ1_v]
      · change φ (w + v) = b
        rw [map_add, hφ_v]
        exact zmod2_add_one_eq_of_ne hbw
  let T1 := runSumMap hn (Vec k) S1
  let T2 := runSumMap hn F S2
  let Φ : (Fin n → Vec m) →ₗ[F] (Fin n → Vec k) × (Fin n → F) :=
    { toFun := fun h => (fun i => π1 (h i), fun i => φ (h i))
      map_add' := fun _ _ => by ext i <;> simp [map_add]
      map_smul' := fun _ _ => by ext i <;> simp [map_smul] }
  have hΦ_surj : Function.Surjective Φ := by
    rintro ⟨f1, f2⟩
    refine ⟨fun i => Classical.choose (hΨ_surj (f1 i, f2 i)), ?_⟩
    apply Prod.ext <;> funext i
    · exact congrArg Prod.fst (Classical.choose_spec (hΨ_surj (f1 i, f2 i)))
    · exact congrArg Prod.snd (Classical.choose_spec (hΨ_surj (f1 i, f2 i)))
  let L : (Fin n → Vec m) →ₗ[F] (starts hn S1 → Vec k) × (starts hn S2 → F) :=
    (T1.prodMap T2).comp Φ
  have hL_surj : Function.Surjective L :=
    (Function.Surjective.prodMap (surj_runSumMap hn (Vec k) S1) (surj_runSumMap hn F S2)).comp hΦ_surj
  have hsub : Finset.univ.filter (fun h => Hit hn S1 D1 h ∧ Hit hn S2 D2 h) ⊆
      Finset.univ.filter (fun h => L h = 0) := by
    intro h hh
    rw [Finset.mem_filter] at hh ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Prod.ext <;> funext s
    · simp only [L, LinearMap.comp_apply, LinearMap.prodMap_apply, Φ, T1, runSumMap, LinearMap.coe_mk,
        AddHom.coe_mk, Prod.fst_zero, Pi.zero_apply]
      rw [← map_sum π1, ← LinearMap.mem_ker, hker1]
      exact hh.2.1 s.val s.2
    · simp only [L, LinearMap.comp_apply, LinearMap.prodMap_apply, Φ, T2, runSumMap, LinearMap.coe_mk,
        AddHom.coe_mk, Prod.snd_zero, Pi.zero_apply]
      rw [← map_sum φ, ← LinearMap.mem_ker]
      exact hD2_ker (hh.2.2 s.val s.2)
  have hfib := card_fiber_surj L hL_surj 0
  simp only [Fintype.card_prod, Fintype.card_fun, card_F, Fintype.card_fin,
    Fintype.card_coe, ← pow_mul, ← pow_add] at hfib
  calc (Finset.univ.filter (fun h => Hit hn S1 D1 h ∧ Hit hn S2 D2 h)).card *
        2 ^ (k * (starts hn S1).card + (starts hn S2).card)
      ≤ (Finset.univ.filter (fun h => L h = 0)).card *
        2 ^ (k * (starts hn S1).card + (starts hn S2).card) :=
          Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ = 2 ^ (m * n) := hfib

lemma card_hit_disjoint_supps {n m k : ℕ} (hn : 0 < n) {S1 S2 : Finset (Fin n)}
    (hdisj : Disjoint S1 S2) (_h1ne : S1 ≠ Finset.univ) (_h2ne : S2 ≠ Finset.univ)
    {D1 D2 : Submodule F (Vec m)}
    (hD1 : Module.finrank F D1 + k = m) (hD2 : Module.finrank F D2 + k = m)
    [DecidablePred (fun h : Fin n → Vec m => Hit hn S1 D1 h ∧ Hit hn S2 D2 h)] :
    ((Finset.univ : Finset (Fin n → Vec m)).filter (fun h => Hit hn S1 D1 h ∧ Hit hn S2 D2 h)).card *
      2 ^ (k * (starts hn S1).card + k * (starts hn S2).card) = 2 ^ (m * n) := by
  obtain ⟨π1, hsurj1, hker1⟩ := exists_surj_of_finrank D1 hD1
  obtain ⟨π2, hsurj2, hker2⟩ := exists_surj_of_finrank D2 hD2
  let L : (Fin n → Vec m) →ₗ[F] (starts hn S1 → Vec k) × (starts hn S2 → Vec k) :=
    { toFun := fun h =>
        (fun s => ∑ i ∈ runOf hn S1 s.val, π1 (h i),
         fun s => ∑ i ∈ runOf hn S2 s.val, π2 (h i))
      map_add' := fun _ _ => by
        apply Prod.ext <;>
          (funext s; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, Finset.sum_add_distrib])
      map_smul' := fun r h => by
        apply Prod.ext
        · funext s
          change ∑ x ∈ runOf hn S1 s.val, π1 (r • h x) = r • ∑ i ∈ runOf hn S1 s.val, π1 (h i)
          simp only [map_smul, Finset.smul_sum]
        · funext s
          change ∑ x ∈ runOf hn S2 s.val, π2 (r • h x) = r • ∑ i ∈ runOf hn S2 s.val, π2 (h i)
          simp only [map_smul, Finset.smul_sum] }
  have hL_surj : Function.Surjective L := by
    rintro ⟨w1, w2⟩
    refine ⟨fun i =>
      if h1 : i ∈ starts hn S1 then Classical.choose (hsurj1 (w1 ⟨i, h1⟩))
      else if h2 : i ∈ starts hn S2 then Classical.choose (hsurj2 (w2 ⟨i, h2⟩))
      else 0, ?_⟩
    apply Prod.ext <;> funext s
    · dsimp only [L, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single s.val]
      · simp only [s.2, ↓reduceDIte, Classical.choose_spec (hsurj1 (w1 s))]
      · intro i hi hne
        have hiS1 : i ∈ S1 := (Finset.mem_filter.mp hi).1
        have hnot1 : i ∉ starts hn S1 := fun hs1 => hne ((runOf_inter_starts hn hs1).mp hi)
        have hnot2 : i ∉ starts hn S2 := fun hs2 =>
          Finset.disjoint_left.mp hdisj hiS1 (Finset.mem_filter.mp hs2).1
        simp only [hnot1, hnot2, ↓reduceDIte, map_zero]
      · intro hnot; exact absurd (self_mem_runOf hn s.2) hnot
    · dsimp only [L, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single s.val]
      · have hnot1 : s.val ∉ starts hn S1 := fun hs1 =>
          Finset.disjoint_left.mp hdisj (Finset.mem_filter.mp hs1).1 (Finset.mem_filter.mp s.2).1
        simp only [hnot1, s.2, ↓reduceDIte, Classical.choose_spec (hsurj2 (w2 s))]
      · intro i hi hne
        have hiS2 : i ∈ S2 := (Finset.mem_filter.mp hi).1
        have hnot2 : i ∉ starts hn S2 := fun hs2 => hne ((runOf_inter_starts hn hs2).mp hi)
        have hnot1 : i ∉ starts hn S1 := fun hs1 =>
          Finset.disjoint_left.mp hdisj (Finset.mem_filter.mp hs1).1 hiS2
        simp only [hnot1, hnot2, ↓reduceDIte, map_zero]
      · intro hnot; exact absurd (self_mem_runOf hn s.2) hnot
  have hfilt : Finset.univ.filter (fun h => Hit hn S1 D1 h ∧ Hit hn S2 D2 h) =
      Finset.univ.filter (fun h => L h = 0) := by
    ext h
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Hit, L, LinearMap.coe_mk, AddHom.coe_mk,
      Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
    rw [funext_iff, funext_iff]
    simp only [Pi.zero_apply, Subtype.forall]
    refine and_congr (forall₂_congr fun s _ => ?_) (forall₂_congr fun s _ => ?_)
    · rw [runSum, ← map_sum π1, ← LinearMap.mem_ker, hker1]
    · rw [runSum, ← map_sum π2, ← LinearMap.mem_ker, hker2]
  rw [hfilt]
  have hfib := card_fiber_surj L hL_surj 0
  simp only [Fintype.card_prod, Fintype.card_fun, card_F, Fintype.card_fin,
    Fintype.card_coe, ← pow_mul, ← pow_add] at hfib
  exact hfib

private lemma mul_choose_succ_eq (n r : ℕ) :
    (r + 1) * Nat.choose (n + 1) (r + 1) = (n + 1) * Nat.choose n r := by
  induction n generalizing r with
  | zero =>
    cases r with
    | zero => simp
    | succ r => simp [Nat.choose_eq_zero_of_lt (by omega : 1 < r + 1 + 1)]
  | succ n ih =>
    cases r with
    | zero => simp
    | succ r =>
      rw [Nat.choose_succ_succ (n + 1) (r + 1), mul_add]
      have h1 := ih r
      have h2 := ih (r + 1)
      have h3 : (r + 2) * Nat.choose (n + 1) (r + 1) =
          (r + 1) * Nat.choose (n + 1) (r + 1) + Nat.choose (n + 1) (r + 1) := by ring
      rw [h3, h1, h2]
      have h4 : (n + 1) * Nat.choose n r + Nat.choose (n + 1) (r + 1) +
          (n + 1) * Nat.choose n (r + 1) =
          (n + 1) * (Nat.choose n r + Nat.choose n (r + 1)) + Nat.choose (n + 1) (r + 1) := by ring
      rw [h4, ← Nat.choose_succ_succ n r]
      ring

lemma nat_choose_le_pow (n r : ℕ) : Nat.choose n r ≤ n ^ r := by
  induction r generalizing n with
  | zero => simp
  | succ r ih =>
    cases n with
    | zero => simp
    | succ n =>
      calc Nat.choose (n + 1) (r + 1)
          ≤ (n + 1) * Nat.choose n r := by
            calc Nat.choose (n + 1) (r + 1)
                ≤ (r + 1) * Nat.choose (n + 1) (r + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos r)
              _ = (n + 1) * Nat.choose n r := mul_choose_succ_eq n r
        _ ≤ (n + 1) * (n + 1) ^ r := Nat.mul_le_mul_left _ (le_trans (ih n) (Nat.pow_le_pow_left (Nat.le_succ n) r))
        _ = (n + 1) ^ (r + 1) := by rw [pow_succ']

def tailEv {n m : ℕ} (hn : 0 < n) (a k : ℕ) (h : Fin n → Vec m) : Prop :=
  ∃ (S : Finset (Fin n)) (D : Submodule F (Vec m)),
    S ≠ Finset.univ ∧ (starts hn S).card < a ∧
    a - (starts hn S).card ≤ m - k ∧
    Module.finrank F D + (k + (a - (starts hn S).card)) = m ∧
    Hit hn S D h

lemma tail_card_bound {n m a k : ℕ} (hn : 0 < n) (hkm : k ≤ m) (hn_le : n ≤ 2 * a + 1)
    (ha_ge : m ≤ a) [Fintype (Submodule F (Vec m))] [DecidablePred (tailEv (m := m) hn a k)] :
    (((Finset.univ : Finset (Fin n → Vec m)).filter (tailEv (m := m) hn a k)).card : ℝ) / (2 : ℝ) ^ (m * n) ≤
      ((Fintype.card (Submodule F (Vec m)) : ℝ) * (2 * (m + 1) : ℝ) * (2 : ℝ) ^ (m * m)) *
        ((n : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ (k * a + a)) := by
  classical
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (m * n) := by positivity
  let badPairs (s : ℕ) : Finset (Finset (Fin n) × Submodule F (Vec m)) :=
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => (starts hn S).card = a - s)) ×ˢ
    ((Finset.univ : Finset (Submodule F (Vec m))).filter (fun D : Submodule F (Vec m) => Module.finrank F D + (k + s) = m))
  have hsub : (Finset.univ : Finset (Fin n → Vec m)).filter (tailEv (m := m) hn a k) ⊆
      (Finset.Icc 1 (m - k)).biUnion (fun s =>
        (badPairs s).biUnion (fun SD => Finset.univ.filter (Hit hn SD.1 SD.2))) := by
    intro h hh
    rw [Finset.mem_filter] at hh
    obtain ⟨S, D, _, hlt, hgap, hD, hhit⟩ := hh.2
    rw [Finset.mem_biUnion]
    refine ⟨a - (starts hn S).card, Finset.mem_Icc.mpr ⟨by omega, hgap⟩, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨(S, D), Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hD⟩⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhit⟩⟩
  have hcard_le : (((Finset.univ : Finset (Fin n → Vec m)).filter (tailEv (m := m) hn a k)).card : ℝ) / (2 : ℝ) ^ (m * n) ≤
      ∑ s ∈ Finset.Icc 1 (m - k),
        ∑ SD ∈ badPairs s,
          (((Finset.univ : Finset (Fin n → Vec m)).filter (Hit hn SD.1 SD.2)).card : ℝ) /
            (2 : ℝ) ^ (m * n) := by
    have h1 : ((Finset.univ : Finset (Fin n → Vec m)).filter (tailEv (m := m) hn a k)).card ≤
        ∑ s ∈ Finset.Icc 1 (m - k),
          ∑ SD ∈ badPairs s, ((Finset.univ.filter (Hit hn SD.1 SD.2)).card) := by
      calc ((Finset.univ : Finset (Fin n → Vec m)).filter (tailEv (m := m) hn a k)).card
          ≤ ((Finset.Icc 1 (m - k)).biUnion (fun s =>
              (badPairs s).biUnion (fun SD => Finset.univ.filter (Hit hn SD.1 SD.2)))).card :=
            Finset.card_le_card hsub
        _ ≤ ∑ s ∈ Finset.Icc 1 (m - k),
              ((badPairs s).biUnion (fun SD => Finset.univ.filter (Hit hn SD.1 SD.2))).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ s ∈ Finset.Icc 1 (m - k),
              ∑ SD ∈ badPairs s, (Finset.univ.filter (Hit hn SD.1 SD.2)).card :=
            Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le
    have h1r : (((Finset.univ : Finset (Fin n → Vec m)).filter (tailEv (m := m) hn a k)).card : ℝ) ≤
        ∑ s ∈ Finset.Icc 1 (m - k),
          ∑ SD ∈ badPairs s, ((Finset.univ.filter (Hit hn SD.1 SD.2)).card : ℝ) := by
      simpa only [Nat.cast_sum] using nat_le_cast_real h1
    calc (((Finset.univ : Finset (Fin n → Vec m)).filter (tailEv (m := m) hn a k)).card : ℝ) / (2 : ℝ) ^ (m * n)
        ≤ (∑ s ∈ Finset.Icc 1 (m - k),
            ∑ SD ∈ badPairs s, ((Finset.univ.filter (Hit hn SD.1 SD.2)).card : ℝ)) /
            (2 : ℝ) ^ (m * n) := div_le_div_of_nonneg_right h1r h2pos.le
      _ = _ := by
          rw [sum_div_real]
          refine Finset.sum_congr rfl fun _ _ => sum_div_real _ _ _
  refine le_trans hcard_le ?_
  have hterm : ∀ s ∈ Finset.Icc 1 (m - k),
      ∑ SD ∈ badPairs s,
        (((Finset.univ : Finset (Fin n → Vec m)).filter (Hit hn SD.1 SD.2)).card : ℝ) /
          (2 : ℝ) ^ (m * n) ≤
      ((Fintype.card (Submodule F (Vec m)) : ℝ) * 2 * (2 : ℝ) ^ (m * m)) *
        ((n : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ (k * a + a)) := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    have h1 : ∀ SD ∈ badPairs s,
        (((Finset.univ : Finset (Fin n → Vec m)).filter (Hit hn SD.1 SD.2)).card : ℝ) /
          (2 : ℝ) ^ (m * n) = 1 / (2 : ℝ) ^ ((k + s) * (a - s)) := by
      intro SD hSD
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hSD
      have hc := card_hit hn SD.1 SD.2 hSD.2.2
      rw [hSD.1.2] at hc
      have hcr : (((Finset.univ.filter (Hit hn SD.1 SD.2)).card : ℝ) *
          (2 : ℝ) ^ ((k + s) * (a - s))) = (2 : ℝ) ^ (m * n) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using nat_mul_eq_cast_real hc
      have hp1 : (0 : ℝ) < (2 : ℝ) ^ ((k + s) * (a - s)) := by positivity
      rw [div_eq_div_iff h2pos.ne' hp1.ne', one_mul, hcr]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    have hbp : (badPairs s).card ≤
        (2 * n ^ (2 * m + 1)) * Fintype.card (Submodule F (Vec m)) := by
      rw [Finset.card_product]
      apply Nat.mul_le_mul
      · calc ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => (starts hn S).card = a - s)).card
            ≤ 2 * Nat.choose n (n - 2 * (a - s)) := card_supports_with_starts hn (a - s)
          _ ≤ 2 * n ^ (n - 2 * (a - s)) := Nat.mul_le_mul_left 2 (nat_choose_le_pow _ _)
          _ ≤ 2 * n ^ (2 * m + 1) := by
              apply Nat.mul_le_mul_left 2
              apply Nat.pow_le_pow_right hn
              omega
      · exact Finset.card_le_univ _
    have hexp : k * a + a ≤ (k + s) * (a - s) + m * m := by
      have hs1 : 1 ≤ s := hs.1
      have hsm : s ≤ m := by omega
      have hks : k + s ≤ m := by omega
      have hmul : (k + s) * (a - s) + (k + s) * s = (k + s) * a := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
      have h1 : k * a + a ≤ (k + s) * a := by
        have : k + 1 ≤ k + s := by omega
        calc k * a + a = (k + 1) * a := by ring
          _ ≤ (k + s) * a := Nat.mul_le_mul_right a this
      have h2 : (k + s) * s ≤ m * m := Nat.mul_le_mul hks hsm
      omega
    have hpow_le : (2 : ℝ) ^ (k * a + a) ≤ (2 : ℝ) ^ ((k + s) * (a - s)) * (2 : ℝ) ^ (m * m) := by
      rw [← pow_add]
      exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) hexp
    have hdiv_le : (1 : ℝ) / (2 : ℝ) ^ ((k + s) * (a - s)) ≤
        (2 : ℝ) ^ (m * m) / (2 : ℝ) ^ (k * a + a) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      linarith
    have hbp_r : ((badPairs s).card : ℝ) ≤
        2 * (n : ℝ) ^ (2 * m + 1) * (Fintype.card (Submodule F (Vec m)) : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using nat_le_cast_real hbp
    calc ((badPairs s).card : ℝ) * (1 / (2 : ℝ) ^ ((k + s) * (a - s)))
        ≤ (2 * (n : ℝ) ^ (2 * m + 1) * (Fintype.card (Submodule F (Vec m)) : ℝ)) *
            ((2 : ℝ) ^ (m * m) / (2 : ℝ) ^ (k * a + a)) := by
          apply mul_le_mul hbp_r hdiv_le (by positivity) (by positivity)
      _ = ((Fintype.card (Submodule F (Vec m)) : ℝ) * 2 * (2 : ℝ) ^ (m * m)) *
            ((n : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ (k * a + a)) := by ring
  calc ∑ s ∈ Finset.Icc 1 (m - k),
        ∑ SD ∈ badPairs s,
          (((Finset.univ : Finset (Fin n → Vec m)).filter (Hit hn SD.1 SD.2)).card : ℝ) /
            (2 : ℝ) ^ (m * n)
      ≤ ∑ _s ∈ Finset.Icc 1 (m - k),
          ((Fintype.card (Submodule F (Vec m)) : ℝ) * 2 * (2 : ℝ) ^ (m * m)) *
            ((n : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ (k * a + a)) :=
        Finset.sum_le_sum hterm
    _ = ((Finset.Icc 1 (m - k)).card : ℝ) *
          (((Fintype.card (Submodule F (Vec m)) : ℝ) * 2 * (2 : ℝ) ^ (m * m)) *
            ((n : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ (k * a + a))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((m + 1 : ℕ) : ℝ) *
          (((Fintype.card (Submodule F (Vec m)) : ℝ) * 2 * (2 : ℝ) ^ (m * m)) *
            ((n : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ (k * a + a))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have : (Finset.Icc 1 (m - k)).card ≤ m + 1 := by simp; omega
        exact_mod_cast this
    _ = ((Fintype.card (Submodule F (Vec m)) : ℝ) * (2 * (m + 1) : ℝ) * (2 : ℝ) ^ (m * m)) *
          ((n : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ (k * a + a)) := by push_cast; ring

lemma nat_succ_le_two_pow (q : ℕ) : q + 1 ≤ 2 ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
    have : 2 ^ (q + 1) = 2 ^ q + 2 ^ q := by ring
    omega

lemma nat_pow_le_const_mul_two_pow (n d : ℕ) :
    n ^ (d + 1) ≤ (d + 1) ^ (d + 1) * 2 ^ n := by
  let q := n / (d + 1)
  have hnq : n ≤ (d + 1) * (q + 1) := by
    have hdiv : (d + 1) * q + n % (d + 1) = n := Nat.div_add_mod n (d + 1)
    have hlt := Nat.mod_lt n (show 0 < d + 1 by omega)
    have hmul : (d + 1) * (q + 1) = (d + 1) * q + (d + 1) := by ring
    omega
  have h1 : n ≤ (d + 1) * 2 ^ q := le_trans hnq (Nat.mul_le_mul_left _ (nat_succ_le_two_pow q))
  have h2 : (d + 1) * q ≤ n := Nat.mul_div_le n (d + 1)
  calc n ^ (d + 1) ≤ ((d + 1) * 2 ^ q) ^ (d + 1) := Nat.pow_le_pow_left h1 (d + 1)
    _ = (d + 1) ^ (d + 1) * (2 ^ q) ^ (d + 1) := mul_pow _ _ _
    _ = (d + 1) ^ (d + 1) * 2 ^ (q * (d + 1)) := by rw [← pow_mul]
    _ ≤ (d + 1) ^ (d + 1) * 2 ^ n :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by rw [mul_comm]; exact h2))

lemma tendsto_of_poly_bound {L : ℝ} {f : ℕ → ℝ} (d : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∃ N0 : ℕ, ∀ t ≥ N0, |f t - L| ≤ C * ((t + 2 : ℕ) : ℝ) ^ d / (2 : ℝ) ^ (t + 2)) :
    Filter.Tendsto f Filter.atTop (nhds L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N0, hN0⟩ := hbound
  obtain ⟨N1, hN1⟩ := exists_nat_gt (C * ((d + 1 : ℕ) : ℝ) ^ (d + 1) / ε)
  refine ⟨max N0 N1, fun t ht => ?_⟩
  rw [Real.dist_eq]
  have ht0 : N0 ≤ t := le_trans (le_max_left _ _) ht
  have ht1 : N1 ≤ t := le_trans (le_max_right _ _) ht
  refine lt_of_le_of_lt (hN0 t ht0) ?_
  have hpow : ((t + 2 : ℕ) : ℝ) ^ (d + 1) ≤ ((d + 1 : ℕ) : ℝ) ^ (d + 1) * (2 : ℝ) ^ (t + 2) := by
    exact_mod_cast nat_pow_le_const_mul_two_pow (t + 2) d
  have ht2_pos : (0 : ℝ) < ((t + 2 : ℕ) : ℝ) := by positivity
  have h2_pos : (0 : ℝ) < (2 : ℝ) ^ (t + 2) := by positivity
  have hdiv : ((t + 2 : ℕ) : ℝ) ^ d / (2 : ℝ) ^ (t + 2) ≤
      ((d + 1 : ℕ) : ℝ) ^ (d + 1) / ((t + 2 : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ h2_pos ht2_pos]
    calc ((t + 2 : ℕ) : ℝ) ^ d * ((t + 2 : ℕ) : ℝ) = ((t + 2 : ℕ) : ℝ) ^ (d + 1) := by
          rw [pow_succ]
      _ ≤ ((d + 1 : ℕ) : ℝ) ^ (d + 1) * (2 : ℝ) ^ (t + 2) := hpow
  have hlt_t2 : C * ((d + 1 : ℕ) : ℝ) ^ (d + 1) / ε < ((t + 2 : ℕ) : ℝ) := by
    have : (N1 : ℝ) < ((t + 2 : ℕ) : ℝ) := by exact_mod_cast (show N1 < t + 2 by omega)
    exact lt_trans hN1 this
  calc C * ((t + 2 : ℕ) : ℝ) ^ d / (2 : ℝ) ^ (t + 2)
      = C * (((t + 2 : ℕ) : ℝ) ^ d / (2 : ℝ) ^ (t + 2)) := by ring
    _ ≤ C * (((d + 1 : ℕ) : ℝ) ^ (d + 1) / ((t + 2 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv hC
    _ = C * ((d + 1 : ℕ) : ℝ) ^ (d + 1) / ((t + 2 : ℕ) : ℝ) := by ring
    _ < ε := by
        rw [div_lt_iff₀ ht2_pos]
        rw [div_lt_iff₀ hε] at hlt_t2
        linarith

def evenSupp (a : ℕ) : Finset (Fin (2 * a)) :=
  Finset.univ.filter (fun i => i.val % 2 = 0)

def oddSupp (a : ℕ) : Finset (Fin (2 * a)) :=
  Finset.univ.filter (fun i => i.val % 2 = 1)

lemma evenSupp_disjoint_oddSupp (a : ℕ) : Disjoint (evenSupp a) (oddSupp a) := by
  rw [Finset.disjoint_left]
  intro i h1 h2
  rw [evenSupp, Finset.mem_filter] at h1
  rw [oddSupp, Finset.mem_filter] at h2
  omega

lemma evenSupp_ne_univ {a : ℕ} (ha : 0 < a) : evenSupp a ≠ Finset.univ := by
  intro h
  have h1 : (⟨1, by omega⟩ : Fin (2 * a)) ∈ evenSupp a := h ▸ Finset.mem_univ _
  simp only [evenSupp, Finset.mem_filter] at h1
  omega

lemma oddSupp_ne_univ {a : ℕ} (ha : 0 < a) : oddSupp a ≠ Finset.univ := by
  intro h
  have h0 : (⟨0, by omega⟩ : Fin (2 * a)) ∈ oddSupp a := h ▸ Finset.mem_univ _
  simp only [oddSupp, Finset.mem_filter] at h0
  omega

lemma starts_evenSupp {a : ℕ} (ha : 0 < a) :
    starts (Nat.mul_pos (by omega) ha) (evenSupp a) = evenSupp a := by
  ext i
  simp only [starts, evenSupp, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
  intro hev
  simp only [cprev]
  have hilt := i.isLt
  by_cases h0 : i.val = 0
  · rw [h0, show 0 + 2 * a - 1 = 2 * a - 1 by omega, Nat.mod_eq_of_lt (by omega : 2 * a - 1 < 2 * a)]
    omega
  · rw [show i.val + 2 * a - 1 = (i.val - 1) + 2 * a by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : i.val - 1 < 2 * a)]
    omega

lemma starts_oddSupp {a : ℕ} (ha : 0 < a) :
    starts (Nat.mul_pos (by omega) ha) (oddSupp a) = oddSupp a := by
  ext i
  simp only [starts, oddSupp, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
  intro hodd
  simp only [cprev]
  have hilt := i.isLt
  rw [show i.val + 2 * a - 1 = (i.val - 1) + 2 * a by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega : i.val - 1 < 2 * a)]
  omega

lemma card_evenSupp (a : ℕ) : (evenSupp a).card = a := by
  have hbij : (evenSupp a).card = (Finset.univ : Finset (Fin a)).card := by
    refine Finset.card_bij (fun i _ => ⟨i.val / 2, by omega⟩) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro x hx y hy hxy
      rw [evenSupp, Finset.mem_filter] at hx hy
      have hv := congrArg Fin.val hxy
      dsimp only at hv
      ext; omega
    · intro j _
      refine ⟨⟨2 * j.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, ?_⟩
      ext; dsimp only; omega
  simpa using hbij

lemma card_oddSupp (a : ℕ) : (oddSupp a).card = a := by
  have hbij : (oddSupp a).card = (Finset.univ : Finset (Fin a)).card := by
    refine Finset.card_bij (fun i _ => ⟨i.val / 2, by omega⟩) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro x hx y hy hxy
      rw [oddSupp, Finset.mem_filter] at hx hy
      have hv := congrArg Fin.val hxy
      dsimp only at hv
      ext; omega
    · intro j _
      refine ⟨⟨2 * j.val + 1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, ?_⟩
      ext; dsimp only; omega
  simpa using hbij

lemma eq_even_or_odd_of_starts_eq {a : ℕ} (ha : 0 < a) (S : Finset (Fin (2 * a)))
    (hcard : (starts (Nat.mul_pos (by omega) ha) S).card = a) :
    S = evenSupp a ∨ S = oddSupp a := by
  let hn := Nat.mul_pos (show 0 < 2 by omega) ha
  have hntS : nonTrans hn S = ∅ := by
    have := card_nonTrans hn S
    rw [hcard] at this
    exact Finset.card_eq_zero.mp (by omega)
  have hntE : nonTrans hn (evenSupp a) = ∅ := by
    have := card_nonTrans hn (evenSupp a)
    rw [starts_evenSupp ha, card_evenSupp] at this
    exact Finset.card_eq_zero.mp (by omega)
  have hntO : nonTrans hn (oddSupp a) = ∅ := by
    have := card_nonTrans hn (oddSupp a)
    rw [starts_oddSupp ha, card_oddSupp] at this
    exact Finset.card_eq_zero.mp (by omega)
  by_cases h0 : (⟨0, hn⟩ : Fin (2 * a)) ∈ S
  · left
    apply eq_of_nonTrans_eq hn _ (hntS.trans hntE.symm)
    simp [evenSupp, h0]
  · right
    apply eq_of_nonTrans_eq hn _ (hntS.trans hntO.symm)
    simp [oddSupp, h0]

lemma bonferroni_lower {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (I : Finset ι) (A : ι → Finset α) :
    ∑ i ∈ I, (A i).card ≤ (I.biUnion A).card +
      ∑ i ∈ I, ∑ j ∈ I.filter (fun j => j ≠ i), (A i ∩ A j).card := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert x I hx ih =>
    rw [Finset.sum_insert hx, Finset.biUnion_insert]
    have hun := Finset.card_union_add_card_inter (A x) (I.biUnion A)
    have hinter : (A x ∩ I.biUnion A).card ≤ ∑ j ∈ I, (A x ∩ A j).card := by
      rw [Finset.inter_biUnion]
      exact Finset.card_biUnion_le
    have hsum1 : (∑ j ∈ (insert x I).filter (fun j => j ≠ x), (A x ∩ A j).card) =
        ∑ j ∈ I, (A x ∩ A j).card := by
      congr 1; ext j; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hj, hne⟩
        · exact absurd rfl hne
        · exact hj
      · intro hj; exact ⟨Or.inr hj, fun h => hx (h ▸ hj)⟩
    have hsum2 : ∑ i ∈ I, ∑ j ∈ I.filter (fun j => j ≠ i), (A i ∩ A j).card ≤
        ∑ i ∈ I, ∑ j ∈ (insert x I).filter (fun j => j ≠ i), (A i ∩ A j).card := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset ?_
      intro j hj; simp only [Finset.mem_filter, Finset.mem_insert] at hj ⊢
      exact ⟨Or.inr hj.1, hj.2⟩
    rw [Finset.sum_insert hx, hsum1]
    omega

abbrev oddPos (a : ℕ) : 0 < 2 * a + 1 := Nat.succ_pos (2 * a)

def oddOff (a : ℕ) (i j : Fin (2 * a + 1)) : ℕ :=
  (i.val + (2 * a + 1) - j.val) % (2 * a + 1)

def suppP (a : ℕ) (j : Fin (2 * a + 1)) : Finset (Fin (2 * a + 1)) :=
  Finset.univ.filter (fun i => oddOff a i j ≠ 0 ∧ oddOff a i j % 2 = 0)

def suppQ (a : ℕ) (j : Fin (2 * a + 1)) : Finset (Fin (2 * a + 1)) :=
  Finset.univ.filter (fun i => oddOff a i j = 0 ∨ oddOff a i j % 2 = 1)

lemma oddOff_self (a : ℕ) (j : Fin (2 * a + 1)) : oddOff a j j = 0 := by
  simp only [oddOff, show j.val + (2 * a + 1) - j.val = 2 * a + 1 by omega, Nat.mod_self]

lemma oddOff_cnext (a : ℕ) (i j : Fin (2 * a + 1)) :
    oddOff a (cnext (oddPos a) i) j = (oddOff a i j + 1) % (2 * a + 1) := by
  simp only [oddOff, cnext]
  have hilt := i.isLt; have hjlt := j.isLt
  by_cases hlast : i.val + 1 = 2 * a + 1
  · rw [hlast, Nat.mod_self, show 0 + (2 * a + 1) - j.val = 2 * a + 1 - j.val by omega,
      show i.val + (2 * a + 1) - j.val = (2 * a - j.val) + (2 * a + 1) by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : 2 * a - j.val < 2 * a + 1),
      show 2 * a - j.val + 1 = 2 * a + 1 - j.val by omega]
  · rw [Nat.mod_eq_of_lt (by omega : i.val + 1 < 2 * a + 1)]
    conv_rhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [show i.val + (2 * a + 1) - j.val + 1 = i.val + 1 + (2 * a + 1) - j.val by omega]

lemma oddOff_cprev (a : ℕ) (i j : Fin (2 * a + 1)) :
    oddOff a (cprev (oddPos a) i) j = (oddOff a i j + 2 * a) % (2 * a + 1) := by
  have h := oddOff_cnext a (cprev (oddPos a) i) j
  rw [cnext_cprev] at h
  have h1 : (oddOff a (cprev (oddPos a) i) j + 1 + 2 * a) % (2 * a + 1) =
      (oddOff a i j + 2 * a) % (2 * a + 1) := by
    rw [h]
    conv_rhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have hlt : oddOff a (cprev (oddPos a) i) j < 2 * a + 1 := Nat.mod_lt _ (oddPos a)
  rw [show oddOff a (cprev (oddPos a) i) j + 1 + 2 * a =
      oddOff a (cprev (oddPos a) i) j + (2 * a + 1) by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt hlt] at h1
  exact h1

lemma oddOff_cnext_eq_cprev (a : ℕ) (x y : Fin (2 * a + 1)) :
    oddOff a (cnext (oddPos a) x) y = oddOff a x (cprev (oddPos a) y) := by
  rw [oddOff_cnext]
  simp only [oddOff, cprev]
  have hxlt := x.isLt; have hylt := y.isLt
  by_cases hy0 : y.val = 0
  · rw [hy0, show 0 + (2 * a + 1) - 1 = 2 * a by omega,
      Nat.mod_eq_of_lt (by omega : 2 * a < 2 * a + 1),
      show x.val + (2 * a + 1) - 0 = x.val + (2 * a + 1) by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hxlt,
      show x.val + (2 * a + 1) - 2 * a = x.val + 1 by omega]
  · rw [show y.val + (2 * a + 1) - 1 = (y.val - 1) + (2 * a + 1) by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : y.val - 1 < 2 * a + 1)]
    conv_lhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [show x.val + (2 * a + 1) - y.val + 1 = x.val + (2 * a + 1) - (y.val - 1) by omega]

lemma oddOff_cnext_right (a : ℕ) (x y : Fin (2 * a + 1)) :
    oddOff a x (cnext (oddPos a) y) = (oddOff a x y + 2 * a) % (2 * a + 1) := by
  have h := oddOff_cnext_eq_cprev a (cprev (oddPos a) x) (cnext (oddPos a) y)
  rw [cnext_cprev, cprev_cnext] at h
  rw [h, oddOff_cprev]

lemma oddOff_eq_iff (a : ℕ) (i j : Fin (2 * a + 1)) : oddOff a i j = 0 ↔ i = j := by
  constructor
  · intro h
    simp only [oddOff] at h
    have hlt := i.isLt; have hjlt := j.isLt
    by_cases hle : j.val ≤ i.val
    · rw [show i.val + (2 * a + 1) - j.val = (i.val - j.val) + (2 * a + 1) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i.val - j.val < 2 * a + 1)] at h
      ext; omega
    · rw [Nat.mod_eq_of_lt (by omega : i.val + (2 * a + 1) - j.val < 2 * a + 1)] at h
      omega
  · rintro rfl; exact oddOff_self a i

lemma oddOff_eq_one_iff (a : ℕ) (ha : 0 < a) (i j : Fin (2 * a + 1)) :
    oddOff a i j = 1 ↔ i = cnext (oddPos a) j := by
  have h := oddOff_cprev a i j
  constructor
  · intro h1
    have hp : oddOff a (cprev (oddPos a) i) j = 0 := by
      rw [h, h1, show 1 + 2 * a = 2 * a + 1 by omega, Nat.mod_self]
    have heq := (oddOff_eq_iff a _ j).mp hp
    rw [← heq, cnext_cprev]
  · rintro rfl
    rw [oddOff_cnext, oddOff_self, zero_add, Nat.mod_eq_of_lt (by omega : 1 < 2 * a + 1)]

lemma nonTrans_suppP {a : ℕ} (ha : 0 < a) (j : Fin (2 * a + 1)) :
    nonTrans (oddPos a) (suppP a j) = {j} := by
  ext i
  simp only [nonTrans, suppP, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [oddOff_cnext]
  have hlt : oddOff a i j < 2 * a + 1 := Nat.mod_lt _ (oddPos a)
  constructor
  · intro h
    by_contra hne
    have h0 : oddOff a i j ≠ 0 := fun hz => hne ((oddOff_eq_iff a i j).mp hz)
    by_cases h2a : oddOff a i j = 2 * a
    · rw [h2a, Nat.mod_self] at h
      have : (2 * a ≠ 0 ∧ (2 * a) % 2 = 0) := ⟨by omega, by omega⟩
      exact (h.1 this).1 rfl
    · rw [Nat.mod_eq_of_lt (by omega : oddOff a i j + 1 < 2 * a + 1)] at h
      by_cases hev : oddOff a i j % 2 = 0
      · have h2 := h.1 ⟨h0, hev⟩; omega
      · have h2 := h.2 ⟨by omega, by omega⟩; omega
  · rintro rfl
    rw [oddOff_self, zero_add, Nat.mod_eq_of_lt (by omega : 1 < 2 * a + 1)]
    constructor <;> intro h <;> omega

lemma nonTrans_suppQ {a : ℕ} (ha : 0 < a) (j : Fin (2 * a + 1)) :
    nonTrans (oddPos a) (suppQ a j) = {j} := by
  have hcompl : suppQ a j = (suppP a j)ᶜ := by
    ext i
    simp only [suppQ, suppP, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hnt : nonTrans (oddPos a) (suppP a j)ᶜ = nonTrans (oddPos a) (suppP a j) := by
    ext i
    simp only [nonTrans, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    tauto
  rw [hcompl, hnt, nonTrans_suppP ha j]

lemma starts_suppP {a : ℕ} (_ha : 0 < a) (j : Fin (2 * a + 1)) :
    starts (oddPos a) (suppP a j) = suppP a j := by
  ext i
  simp only [starts, suppP, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
  intro ⟨h0, hev⟩
  rw [oddOff_cprev]
  have hlt : oddOff a i j < 2 * a + 1 := Nat.mod_lt _ (oddPos a)
  have hmod : (oddOff a i j + 2 * a) % (2 * a + 1) = oddOff a i j - 1 := by
    rw [show oddOff a i j + 2 * a = (oddOff a i j - 1) + (2 * a + 1) by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : oddOff a i j - 1 < 2 * a + 1)]
  rw [hmod]
  intro ⟨_, h2⟩
  omega

lemma card_suppP {a : ℕ} (ha : 0 < a) (j : Fin (2 * a + 1)) : (suppP a j).card = a := by
  have h := card_nonTrans (oddPos a) (suppP a j)
  rw [nonTrans_suppP ha j, Finset.card_singleton, starts_suppP ha j] at h
  omega

lemma card_starts_suppQ {a : ℕ} (ha : 0 < a) (j : Fin (2 * a + 1)) :
    (starts (oddPos a) (suppQ a j)).card = a := by
  have h := card_nonTrans (oddPos a) (suppQ a j)
  rw [nonTrans_suppQ ha j, Finset.card_singleton] at h
  omega

lemma suppP_ne_univ {a : ℕ} (j : Fin (2 * a + 1)) : suppP a j ≠ Finset.univ := by
  intro h
  have hj : j ∈ suppP a j := h ▸ Finset.mem_univ j
  rw [suppP, Finset.mem_filter, oddOff_self] at hj
  exact hj.2.1 rfl

lemma suppQ_ne_univ {a : ℕ} (ha : 0 < a) (j : Fin (2 * a + 1)) : suppQ a j ≠ Finset.univ := by
  intro h
  let i := cnext (oddPos a) (cnext (oddPos a) j)
  have hi : i ∈ suppQ a j := h ▸ Finset.mem_univ i
  rw [suppQ, Finset.mem_filter] at hi
  have hoff : oddOff a i j = 2 := by
    simp only [i, oddOff_cnext, oddOff_self, zero_add]
    rw [Nat.mod_eq_of_lt (by omega : 1 < 2 * a + 1), Nat.mod_eq_of_lt (by omega : 1 + 1 < 2 * a + 1)]
  rw [hoff] at hi
  omega

lemma eq_suppP_or_suppQ {a : ℕ} (ha : 0 < a) (S : Finset (Fin (2 * a + 1)))
    (hcard : (starts (oddPos a) S).card = a) :
    ∃ j : Fin (2 * a + 1), S = suppP a j ∨ S = suppQ a j := by
  have hn : 0 < 2 * a + 1 := oddPos a
  have hnt1 : (nonTrans hn S).card = 1 := by
    have := card_nonTrans hn S
    omega
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hnt1
  refine ⟨j, ?_⟩
  have h0_iff : ∀ T : Finset (Fin (2 * a + 1)), nonTrans hn T = {j} →
      (j ∈ S ↔ j ∈ T) → S = T := by
    intro T hntT hj_iff
    have hwalk : ∀ d < 2 * a + 1, ((cnext hn)^[d] j ∈ S) ↔ ((cnext hn)^[d] j ∈ T) := by
      intro d
      induction d with
      | zero => intro _; simpa using hj_iff
      | succ d ih =>
        intro hd
        rw [Function.iterate_succ_apply']
        have hprev := ih (by omega)
        by_cases hd0 : d = 0
        · subst hd0
          have h1 : j ∈ nonTrans hn S := by rw [hj]; exact Finset.mem_singleton_self j
          have h2 : j ∈ nonTrans hn T := by rw [hntT]; exact Finset.mem_singleton_self j
          simp only [nonTrans, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          simpa using (h1.symm.trans (hj_iff.trans h2))
        · have hne_j : (cnext hn)^[d] j ≠ j := by
            intro heq
            have hv := congrArg Fin.val heq
            rw [cnext_iter_val hn] at hv
            have hjlt := j.isLt
            have hlt : d < 2 * a + 1 := by omega
            have : (j.val + d) % (2 * a + 1) ≠ j.val := by
              by_cases hsum : j.val + d < 2 * a + 1
              · rw [Nat.mod_eq_of_lt hsum]; omega
              · rw [show j.val + d = (j.val + d - (2 * a + 1)) + (2 * a + 1) by omega,
                  Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : j.val + d - (2 * a + 1) < 2 * a + 1)]
                omega
            exact this hv
          have hnotS : (cnext hn)^[d] j ∉ nonTrans hn S := by
            rw [hj, Finset.mem_singleton]; exact hne_j
          have hnotT : (cnext hn)^[d] j ∉ nonTrans hn T := by
            rw [hntT, Finset.mem_singleton]; exact hne_j
          simp only [nonTrans, Finset.mem_filter, Finset.mem_univ, true_and] at hnotS hnotT
          tauto
    ext i
    let d' := oddOff a i j
    have hd'_lt : d' < 2 * a + 1 := Nat.mod_lt _ hn
    have hiter : (cnext hn)^[d'] j = i := by
      ext
      rw [cnext_iter_val hn]
      simp only [d', oddOff]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have hsum : j.val + (i.val + (2 * a + 1) - j.val) = i.val + (2 * a + 1) := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
    rw [← hiter]
    exact hwalk d' hd'_lt
  by_cases hjS : j ∈ S
  · right
    apply h0_iff (suppQ a j) (nonTrans_suppQ ha j)
    simp [suppQ, oddOff_self, hjS]
  · left
    apply h0_iff (suppP a j) (nonTrans_suppP ha j)
    simp [suppP, oddOff_self, hjS]

lemma runOf_suppP {a : ℕ} (ha : 0 < a) (j s : Fin (2 * a + 1)) (hs : s ∈ suppP a j) :
    runOf (oddPos a) (suppP a j) s = {s} := by
  have hn : 0 < 2 * a + 1 := oddPos a
  ext i
  rw [runOf, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hi, hrh⟩
    have hist : i ∈ starts hn (suppP a j) := by rwa [starts_suppP ha j]
    rw [runHead_self hn hist] at hrh
    exact hrh
  · rintro rfl
    exact ⟨hs, runHead_self hn (by rwa [starts_suppP ha j])⟩

lemma starts_suppQ {a : ℕ} (ha : 0 < a) (j : Fin (2 * a + 1)) :
    starts (oddPos a) (suppQ a j) =
      (suppQ a j).erase (cnext (oddPos a) j) := by
  have hn : 0 < 2 * a + 1 := oddPos a
  ext i
  simp only [starts, Finset.mem_filter, Finset.mem_erase, suppQ, Finset.mem_univ, true_and]
  rw [oddOff_cprev]
  have hlt : oddOff a i j < 2 * a + 1 := Nat.mod_lt _ hn
  constructor
  · rintro ⟨hi, hp⟩
    refine ⟨?_, hi⟩
    intro heq
    have h1 := (oddOff_eq_one_iff a ha i j).mpr heq
    rw [h1, show 1 + 2 * a = 2 * a + 1 by omega, Nat.mod_self] at hp
    exact hp (Or.inl rfl)
  · rintro ⟨hne, hi⟩
    refine ⟨hi, ?_⟩
    by_cases h0 : oddOff a i j = 0
    · rw [h0, zero_add, Nat.mod_eq_of_lt (by omega : 2 * a < 2 * a + 1)]; omega
    · have hne1 : oddOff a i j ≠ 1 := fun h1 => hne ((oddOff_eq_one_iff a ha i j).mp h1)
      have hmod : (oddOff a i j + 2 * a) % (2 * a + 1) = oddOff a i j - 1 := by
        rw [show oddOff a i j + 2 * a = (oddOff a i j - 1) + (2 * a + 1) by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : oddOff a i j - 1 < 2 * a + 1)]
      rw [hmod]
      omega

lemma runOf_suppQ_j {a : ℕ} (ha : 0 < a) (j : Fin (2 * a + 1)) :
    runOf (oddPos a) (suppQ a j) j = {j, cnext (oddPos a) j} := by
  have hn : 0 < 2 * a + 1 := oddPos a
  have hj_st : j ∈ starts hn (suppQ a j) := by
    rw [starts_suppQ ha j, Finset.mem_erase, suppQ, Finset.mem_filter]
    refine ⟨?_, Finset.mem_univ _, Or.inl (oddOff_self a j)⟩
    intro h
    have := (oddOff_eq_one_iff a ha j j).mpr h
    rw [oddOff_self] at this; omega
  have hnj_mem : cnext hn j ∈ suppQ a j := by
    rw [suppQ, Finset.mem_filter, oddOff_cnext, oddOff_self, zero_add,
      Nat.mod_eq_of_lt (by omega : 1 < 2 * a + 1)]
    exact ⟨Finset.mem_univ _, Or.inr rfl⟩
  have hnj_rh : runHead hn (suppQ a j) (cnext hn j) = j := by
    have h1 := runHead_cprev hn (suppQ_ne_univ ha j) (i := cnext hn j)
      (by rw [cprev_cnext]; exact (Finset.mem_filter.mp hj_st).1)
    rw [cprev_cnext, runHead_self hn hj_st] at h1
    exact h1.symm
  ext i
  rw [runOf, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hi, hrh⟩
    by_cases hnj : i = cnext hn j
    · exact Or.inr hnj
    · left
      have hist : i ∈ starts hn (suppQ a j) := by
        rw [starts_suppQ ha j, Finset.mem_erase]; exact ⟨hnj, hi⟩
      rw [runHead_self hn hist] at hrh
      exact hrh
  · rintro (rfl | rfl)
    · exact ⟨(Finset.mem_filter.mp hj_st).1, runHead_self hn hj_st⟩
    · exact ⟨hnj_mem, hnj_rh⟩

lemma runOf_suppQ_ne {a : ℕ} (ha : 0 < a) (j s : Fin (2 * a + 1))
    (hs : s ∈ starts (oddPos a) (suppQ a j)) (hne : s ≠ j) :
    runOf (oddPos a) (suppQ a j) s = {s} := by
  have hn : 0 < 2 * a + 1 := oddPos a
  ext i
  rw [runOf, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hi, hrh⟩
    by_cases hnj : i = cnext hn j
    · subst hnj
      have h1 : cnext hn j ∈ runOf hn (suppQ a j) j := by
        rw [runOf_suppQ_j ha j]; simp
      have h2 := (Finset.mem_filter.mp h1).2
      exact absurd (h2.symm.trans hrh).symm hne
    · have hist : i ∈ starts hn (suppQ a j) := by
        rw [starts_suppQ ha j, Finset.mem_erase]; exact ⟨hnj, hi⟩
      rw [runHead_self hn hist] at hrh
      exact hrh
  · rintro rfl
    exact ⟨(Finset.mem_filter.mp hs).1, runHead_self hn hs⟩

def hitP (a k : ℕ) (j : Fin (2 * a + 1)) (v : Fin (2 * a + 1) → Vec k) : Prop :=
  ∀ i ∈ suppP a j, v i = 0

def hitQ (a k : ℕ) (j : Fin (2 * a + 1)) (v : Fin (2 * a + 1) → Vec k) : Prop :=
  v j = v (cnext (oddPos a) j) ∧
  ∀ i ∈ suppQ a j, i ≠ j → i ≠ cnext (oddPos a) j → v i = 0

lemma hitP_step_prev2 {a k : ℕ} (ha : 0 < a) {j : Fin (2 * a + 1)}
    {v : Fin (2 * a + 1) → Vec k} (hp : hitP a k j v) (hj0 : v j = 0) :
    hitP a k (cprev (oddPos a) (cprev (oddPos a) j)) v := by
  have hn : 0 < 2 * a + 1 := oddPos a
  let j' := cprev hn (cprev hn j)
  intro i hi
  rw [suppP, Finset.mem_filter] at hi
  have hj'_off : oddOff a i j' = (oddOff a i j + 2) % (2 * a + 1) := by
    have h1 : oddOff a (cnext hn (cnext hn i)) j = oddOff a i j' := by
      dsimp only [j']
      rw [oddOff_cnext_eq_cprev, oddOff_cnext_eq_cprev]
    rw [← h1, oddOff_cnext, oddOff_cnext, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, add_assoc]
  have hlt : oddOff a i j < 2 * a + 1 := Nat.mod_lt _ hn
  by_cases h0 : oddOff a i j = 0
  · rw [(oddOff_eq_iff a i j).mp h0]; exact hj0
  · by_cases hbig : oddOff a i j + 2 < 2 * a + 1
    · rw [hj'_off, Nat.mod_eq_of_lt hbig] at hi
      apply hp i
      rw [suppP, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h0, by omega⟩
    · have hcase : oddOff a i j = 2 * a - 1 ∨ oddOff a i j = 2 * a := by omega
      rcases hcase with hc | hc
      · rw [hj'_off, hc, show 2 * a - 1 + 2 = 2 * a + 1 by omega, Nat.mod_self] at hi
        exact absurd rfl hi.2.1
      · rw [hj'_off, hc, show 2 * a + 2 = 1 + (2 * a + 1) by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega : 1 < 2 * a + 1)] at hi
        omega

lemma odd_setA_disjoint {a k : ℕ} (_ha : 0 < a) {j1 j2 : Fin (2 * a + 1)} (hne : j1 ≠ j2)
    {v : Fin (2 * a + 1) → Vec k}
    (h1 : hitP a k j1 v ∧ v j1 ≠ 0) (h2 : hitP a k j2 v ∧ v j2 ≠ 0) : False := by
  have hd0 : oddOff a j2 j1 ≠ 0 := fun h0 => hne ((oddOff_eq_iff a j2 j1).mp h0).symm
  by_cases hev : oddOff a j2 j1 % 2 = 0
  · have hmem : j2 ∈ suppP a j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd0, hev⟩
    exact h2.2 (h1.1 j2 hmem)
  · have hsum : oddOff a j1 j2 + oddOff a j2 j1 = 2 * a + 1 := by
      have hlt1 : oddOff a j1 j2 < 2 * a + 1 := Nat.mod_lt _ (oddPos a)
      have hlt2 : oddOff a j2 j1 < 2 * a + 1 := Nat.mod_lt _ (oddPos a)
      have h01 : oddOff a j1 j2 ≠ 0 := fun h0 => hne ((oddOff_eq_iff a j1 j2).mp h0)
      have hmod : (oddOff a j1 j2 + oddOff a j2 j1) % (2 * a + 1) = 0 := by
        simp only [oddOff]
        rw [← Nat.add_mod]
        have : j1.val + (2 * a + 1) - j2.val + (j2.val + (2 * a + 1) - j1.val) =
            2 * (2 * a + 1) := by omega
        rw [this, Nat.mul_mod_left]
      have hdiv := Nat.div_add_mod (oddOff a j1 j2 + oddOff a j2 j1) (2 * a + 1)
      rw [hmod, add_zero] at hdiv
      generalize (oddOff a j1 j2 + oddOff a j2 j1) / (2 * a + 1) = q at hdiv
      have hq : q = 1 := by
        have hq1 : 1 ≤ q := by
          by_contra h0
          have hz : q = 0 := by omega
          rw [hz, mul_zero] at hdiv; omega
        have hq2 : q ≤ 1 := by
          by_contra h2
          have h2' : 2 ≤ q := by omega
          have hmul := Nat.mul_le_mul_left (2 * a + 1) h2'
          rw [hdiv] at hmul
          omega
        omega
      rw [hq, mul_one] at hdiv
      exact hdiv.symm
    have h01 : oddOff a j1 j2 ≠ 0 := fun h0 => hne ((oddOff_eq_iff a j1 j2).mp h0)
    have hmem : j1 ∈ suppP a j2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h01, by omega⟩
    exact h1.2 (h2.1 j1 hmem)

lemma odd_setB_inter_empty {a k : ℕ} (ha : 0 < a) {j1 j2 : Fin (2 * a + 1)}
    (hne : j1 ≠ j2) (hne1 : j2 ≠ cnext (oddPos a) j1)
    (hne2 : j1 ≠ cnext (oddPos a) j2)
    {v : Fin (2 * a + 1) → Vec k}
    (h1 : hitQ a k j1 v ∧ v j1 ≠ 0) (h2 : hitQ a k j2 v ∧ v j2 ≠ 0) : False := by
  have hn : 0 < 2 * a + 1 := oddPos a
  have hd0 : oddOff a j2 j1 ≠ 0 := fun h0 => hne ((oddOff_eq_iff a j2 j1).mp h0).symm
  have hd1 : oddOff a j2 j1 ≠ 1 := fun h => hne1 ((oddOff_eq_one_iff a ha j2 j1).mp h)
  have hd2a : oddOff a j2 j1 ≠ 2 * a := by
    intro h
    have hnx : oddOff a (cnext hn j2) j1 = 0 := by rw [oddOff_cnext, h, Nat.mod_self]
    exact hne2 ((oddOff_eq_iff a _ j1).mp hnx).symm
  have hlt : oddOff a j2 j1 < 2 * a + 1 := Nat.mod_lt _ hn
  by_cases hodd : oddOff a j2 j1 % 2 = 1
  · have hmem : j2 ∈ suppQ a j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hodd⟩
    exact h2.2 (h1.1.2 j2 hmem hne.symm hne1)
  · have hnx_off : oddOff a (cnext hn j2) j1 = oddOff a j2 j1 + 1 := by
      rw [oddOff_cnext, Nat.mod_eq_of_lt (by omega : oddOff a j2 j1 + 1 < 2 * a + 1)]
    have hmem : cnext hn j2 ∈ suppQ a j1 :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (by omega)⟩
    have h0 : v (cnext hn j2) = 0 := h1.1.2 (cnext hn j2) hmem
      (fun h => hne2 h.symm) (fun h => hne (cnext_inj hn h).symm)
    rw [← h2.1.1] at h0
    exact h2.2 h0

lemma odd_setA_inter_setB_empty {a k : ℕ} (_ha : 0 < a) {j1 j2 : Fin (2 * a + 1)} (hne : j1 ≠ j2)
    {v : Fin (2 * a + 1) → Vec k}
    (h1 : hitP a k j1 v ∧ v j1 ≠ 0) (h2 : hitQ a k j2 v ∧ v j2 ≠ 0) : False := by
  have hn : 0 < 2 * a + 1 := oddPos a
  have hd0 : oddOff a j2 j1 ≠ 0 := fun h0 => hne ((oddOff_eq_iff a j2 j1).mp h0).symm
  have hlt : oddOff a j2 j1 < 2 * a + 1 := Nat.mod_lt _ hn
  by_cases hev : oddOff a j2 j1 % 2 = 0
  · exact h2.2 (h1.1 j2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd0, hev⟩))
  · have hnx_off : oddOff a (cnext hn j2) j1 = oddOff a j2 j1 + 1 := by
      rw [oddOff_cnext, Nat.mod_eq_of_lt (by omega : oddOff a j2 j1 + 1 < 2 * a + 1)]
    have h0 : v (cnext hn j2) = 0 := h1.1 (cnext hn j2)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, by omega⟩)
    rw [← h2.1.1] at h0
    exact h2.2 h0

lemma odd_fixed_D_bounds {a m k : ℕ} (ha : 2 ≤ a) (_hk : 1 ≤ k) (hkm : k ≤ m)
    (D : Submodule F (Vec m)) (hD : Module.finrank F D + k = m)
    [DecidablePred (fun h : Fin (2 * a + 1) → Vec m =>
      ∃ j : Fin (2 * a + 1), Hit (oddPos a) (suppP a j) D h ∨ Hit (oddPos a) (suppQ a j) D h)] :
    let ED : Finset (Fin (2 * a + 1) → Vec m) :=
      Finset.univ.filter (fun h => ∃ j : Fin (2 * a + 1), Hit (oddPos a) (suppP a j) D h ∨ Hit (oddPos a) (suppQ a j) D h)
    (2 * (2 * a + 1) * (2 ^ k - 1) * (2 ^ k) ^ a - 2 * (2 * a + 1) * 2 ^ k) * 2 ^ ((m - k) * (2 * a + 1)) ≤
      ED.card ∧
    ED.card ≤ (1 + 2 * (2 * a + 1) * (2 ^ k - 1) * (2 ^ k) ^ a) * 2 ^ ((m - k) * (2 * a + 1)) := by
  dsimp only
  have hn : 0 < 2 * a + 1 := oddPos a
  have ha0 : 0 < a := by omega
  obtain ⟨π, hsurj, hker⟩ := exists_surj_of_finrank D hD
  let compπ : (Fin (2 * a + 1) → Vec m) →ₗ[F] (Fin (2 * a + 1) → Vec k) :=
    { toFun := fun h i => π (h i)
      map_add' := fun _ _ => by funext i; exact map_add π _ _
      map_smul' := fun _ _ => by funext i; exact map_smul π _ _ }
  have hcomp_surj : Function.Surjective compπ := fun v =>
    ⟨fun i => Classical.choose (hsurj (v i)), funext fun i => Classical.choose_spec (hsurj (v i))⟩
  have hfib_card : ∀ v : Fin (2 * a + 1) → Vec k,
      (Finset.univ.filter (fun h => compπ h = v)).card = 2 ^ ((m - k) * (2 * a + 1)) := by
    intro v
    have hf := card_fiber_surj compπ hcomp_surj v
    rw [card_fin_vec, card_fin_vec] at hf
    have hmul : (m - k) * (2 * a + 1) + k * (2 * a + 1) = m * (2 * a + 1) := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hkm]
    rw [← hmul, pow_add] at hf
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hf
  have hHitP_iff : ∀ h j, Hit hn (suppP a j) D h ↔ hitP a k j (compπ h) := by
    intro h j
    simp only [Hit, hitP, starts_suppP ha0 j]
    refine forall₂_congr fun s hs => ?_
    rw [runSum, runOf_suppP ha0 j s hs, Finset.sum_singleton, ← hker, LinearMap.mem_ker]
    rfl
  have hHitQ_iff : ∀ h j, Hit hn (suppQ a j) D h ↔ hitQ a k j (compπ h) := by
    intro h j
    simp only [Hit, hitQ, starts_suppQ ha0 j, Finset.mem_erase]
    constructor
    · intro hhit
      have hj_st : j ∈ starts hn (suppQ a j) := by
        rw [starts_suppQ ha0 j, Finset.mem_erase, suppQ, Finset.mem_filter]
        refine ⟨fun h => by have := (oddOff_eq_one_iff a ha0 j j).mpr h; rw [oddOff_self] at this; omega,
          Finset.mem_univ _, Or.inl (oddOff_self a j)⟩
      have h1 := hhit j (by simpa [starts_suppQ ha0 j] using hj_st)
      rw [runSum, runOf_suppQ_j ha0 j, Finset.sum_pair (by
        intro h; have := (oddOff_eq_one_iff a ha0 j j).mpr h; rw [oddOff_self] at this; omega),
        ← hker, LinearMap.mem_ker, map_add] at h1
      refine ⟨?_, ?_⟩
      · funext c
        have hc := congrFun h1 c
        exact zmod2_add_eq_zero_iff.mp hc
      · intro i hi hnej hnenj
        have hist : i ∈ starts hn (suppQ a j) := by
          rw [starts_suppQ ha0 j, Finset.mem_erase]; exact ⟨hnenj, hi⟩
        have h2 := hhit i ⟨hnenj, hi⟩
        rw [runSum, runOf_suppQ_ne ha0 j i hist hnej, Finset.sum_singleton, ← hker,
          LinearMap.mem_ker] at h2
        exact h2
    · rintro ⟨heq, hrest⟩ s ⟨hnenj, hs⟩
      by_cases hsj : s = j
      · subst hsj
        rw [runSum, runOf_suppQ_j ha0 s, Finset.sum_pair (by
          intro h; have := (oddOff_eq_one_iff a ha0 s s).mpr h; rw [oddOff_self] at this; omega),
          ← hker, LinearMap.mem_ker, map_add]
        funext c
        exact zmod2_add_eq_zero_iff.mpr (congrFun heq c)
      · have hist : s ∈ starts hn (suppQ a j) := by
          rw [starts_suppQ ha0 j, Finset.mem_erase]; exact ⟨hnenj, hs⟩
        rw [runSum, runOf_suppQ_ne ha0 j s hist hsj, Finset.sum_singleton, ← hker,
          LinearMap.mem_ker]
        exact hrest s hs hsj hnenj
  classical
  let Vev : Finset (Fin (2 * a + 1) → Vec k) :=
    Finset.univ.filter (fun v => ∃ j, hitP a k j v ∨ hitQ a k j v)
  have hED_eq : (Finset.univ.filter (fun h => ∃ j, Hit (oddPos a) (suppP a j) D h ∨ Hit (oddPos a) (suppQ a j) D h)).card =
      Vev.card * 2 ^ ((m - k) * (2 * a + 1)) := by
    have hbiU : Finset.univ.filter (fun h => ∃ j, Hit (oddPos a) (suppP a j) D h ∨ Hit (oddPos a) (suppQ a j) D h) =
        Vev.biUnion (fun v => Finset.univ.filter (fun h => compπ h = v)) := by
      ext h
      rw [Finset.mem_filter, Finset.mem_biUnion]
      simp only [Finset.mem_univ, true_and, Finset.mem_filter, Vev]
      constructor
      · intro hh
        refine ⟨compπ h, ?_, rfl⟩
        rcases hh with ⟨j, hp | hq⟩
        · exact ⟨j, Or.inl ((hHitP_iff h j).mp hp)⟩
        · exact ⟨j, Or.inr ((hHitQ_iff h j).mp hq)⟩
      · rintro ⟨v, ⟨j, hp | hq⟩, rfl⟩
        · exact ⟨j, Or.inl ((hHitP_iff h j).mpr hp)⟩
        · exact ⟨j, Or.inr ((hHitQ_iff h j).mpr hq)⟩
    rw [hbiU, Finset.card_biUnion]
    · simp only [hfib_card, Finset.sum_const, smul_eq_mul]
    · intro v1 _ v2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro h h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  rw [hED_eq]
  let setA (j : Fin (2 * a + 1)) : Finset (Fin (2 * a + 1) → Vec k) :=
    Finset.univ.filter (fun v => hitP a k j v ∧ v j ≠ 0)
  let setB (j : Fin (2 * a + 1)) : Finset (Fin (2 * a + 1) → Vec k) :=
    Finset.univ.filter (fun v => hitQ a k j v ∧ v j ≠ 0)
  have hcardA : ∀ j, (setA j).card = (2 ^ k - 1) * (2 ^ k) ^ a := by
    intro j
    let rest := (Finset.univ : Finset (Fin (2 * a + 1))) \ insert j (suppP a j)
    have hj_not : j ∉ suppP a j := by simp [suppP, oddOff_self]
    have hrest_card : rest.card = a := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
        Finset.card_insert_of_notMem hj_not, card_suppP ha0 j]
      omega
    let tgt := ((Finset.univ : Finset (Vec k)).erase 0) ×ˢ (Finset.univ : Finset (rest → Vec k))
    have hbij : (setA j).card = tgt.card := by
      refine Finset.card_bij
        (fun v _ => (v j, fun r : rest => v r.val)) ?_ ?_ ?_
      · intro v hv
        rw [Finset.mem_filter] at hv
        exact Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨hv.2.2, Finset.mem_univ _⟩, Finset.mem_univ _⟩
      · intro v1 hv1 v2 hv2 heq
        rw [Finset.mem_filter] at hv1 hv2
        have h1 := congrArg Prod.fst heq
        have h2 := congrArg Prod.snd heq
        funext i
        by_cases hij : i = j
        · rw [hij]; exact h1
        · by_cases hiP : i ∈ suppP a j
          · rw [hv1.2.1 i hiP, hv2.2.1 i hiP]
          · have hir : i ∈ rest := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hij, hiP]⟩
            exact congrFun h2 ⟨i, hir⟩
      · rintro ⟨w0, wr⟩ hmem
        rw [Finset.mem_product, Finset.mem_erase] at hmem
        refine ⟨fun i => if i = j then w0 else if hi : i ∈ rest then wr ⟨i, hi⟩ else 0, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_, by simp [hmem.1.1]⟩
          intro i hiP
          have hij : i ≠ j := fun h => hj_not (h ▸ hiP)
          have hir : i ∉ rest := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_of_mem hiP)
          simp [hij, hir]
        · apply Prod.ext
          · simp
          · funext ⟨i, hi⟩
            have hij : i ≠ j := fun h => (Finset.mem_sdiff.mp hi).2 (h ▸ Finset.mem_insert_self _ _)
            simp [hij, hi]
    simp only [hbij, tgt, Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fun, card_F, Fintype.card_fin, Fintype.card_coe, hrest_card]
  have hcardB : ∀ j, (setB j).card = (2 ^ k - 1) * (2 ^ k) ^ a := by
    intro j
    let rest := suppP a j
    have hj_not : j ∉ rest := by simp [rest, suppP, oddOff_self]
    have hnj_not : cnext hn j ∉ rest := by
      simp only [rest, suppP, Finset.mem_filter, Finset.mem_univ, true_and, oddOff_cnext,
        oddOff_self, zero_add, Nat.mod_eq_of_lt (by omega : 1 < 2 * a + 1)]
      omega
    have hne_jnj : j ≠ cnext hn j := by
      intro h; have := (oddOff_eq_one_iff a ha0 j j).mpr h; rw [oddOff_self] at this; omega
    let tgt := ((Finset.univ : Finset (Vec k)).erase 0) ×ˢ (Finset.univ : Finset (rest → Vec k))
    have hbij : (setB j).card = tgt.card := by
      refine Finset.card_bij
        (fun v _ => (v j, fun r : rest => v r.val)) ?_ ?_ ?_
      · intro v hv
        rw [Finset.mem_filter] at hv
        exact Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨hv.2.2, Finset.mem_univ _⟩, Finset.mem_univ _⟩
      · intro v1 hv1 v2 hv2 heq
        rw [Finset.mem_filter] at hv1 hv2
        have h1 := congrArg Prod.fst heq
        have h2 := congrArg Prod.snd heq
        funext i
        by_cases hij : i = j
        · rw [hij]; exact h1
        · by_cases hinj : i = cnext hn j
          · rw [hinj, ← hv1.2.1.1, ← hv2.2.1.1]; exact h1
          · by_cases hiP : i ∈ rest
            · exact congrFun h2 ⟨i, hiP⟩
            · have hiQ : i ∈ suppQ a j := by
                simp only [rest, suppP, Finset.mem_filter, Finset.mem_univ, true_and] at hiP
                simp only [suppQ, Finset.mem_filter, Finset.mem_univ, true_and]
                omega
              rw [hv1.2.1.2 i hiQ hij hinj, hv2.2.1.2 i hiQ hij hinj]
      · rintro ⟨w0, wr⟩ hmem
        rw [Finset.mem_product, Finset.mem_erase] at hmem
        refine ⟨fun i => if i = j ∨ i = cnext hn j then w0 else if hi : i ∈ rest then wr ⟨i, hi⟩ else 0,
          ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ⟨by simp, ?_⟩, by simp [hmem.1.1]⟩
          intro i hiQ hij hinj
          have hir : i ∉ rest := by
            simp only [suppQ, Finset.mem_filter, Finset.mem_univ, true_and] at hiQ
            simp only [rest, suppP, Finset.mem_filter, Finset.mem_univ, true_and]
            omega
          simp [hij, hinj, hir]
        · apply Prod.ext
          · simp
          · funext ⟨i, hi⟩
            have hij : i ≠ j := fun h => hj_not (h ▸ hi)
            have hinj : i ≠ cnext hn j := fun h => hnj_not (h ▸ hi)
            simp [hij, hinj, hi]
    simp only [hbij, tgt, rest, Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fun, card_F, Fintype.card_fin, Fintype.card_coe, card_suppP ha0 j]
  constructor
  · let setB' (j : Fin (2 * a + 1)) := setB j \ (setA j ∪ setB (cnext hn j))
    have hsub_A : Finset.univ.biUnion setA ⊆ Vev := by
      intro v hv
      rw [Finset.mem_biUnion] at hv
      obtain ⟨j, _, hj⟩ := hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, Or.inl (Finset.mem_filter.mp hj).2.1⟩
    have hsub_B' : Finset.univ.biUnion setB' ⊆ Vev := by
      intro v hv
      rw [Finset.mem_biUnion] at hv
      obtain ⟨j, _, hj⟩ := hv
      have hB := (Finset.mem_sdiff.mp hj).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, Or.inr (Finset.mem_filter.mp hB).2.1⟩
    have hdisj_AB : Disjoint (Finset.univ.biUnion setA) (Finset.univ.biUnion setB') := by
      rw [Finset.disjoint_left]
      intro v hvA hvB
      rw [Finset.mem_biUnion] at hvA hvB
      obtain ⟨j1, _, h1⟩ := hvA
      obtain ⟨j2, _, h2⟩ := hvB
      have h2B := (Finset.mem_sdiff.mp h2).1
      have h2not := (Finset.mem_sdiff.mp h2).2
      by_cases heq : j1 = j2
      · subst heq; exact h2not (Finset.mem_union_left _ h1)
      · exact odd_setA_inter_setB_empty ha0 heq (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2B).2
    have hdisj_A : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin (2 * a + 1)))) setA := by
      intro j1 _ j2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro v h1 h2
      exact odd_setA_disjoint ha0 hne (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    have hdisj_B' : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin (2 * a + 1)))) setB' := by
      intro j1 _ j2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro v h1 h2
      have h1B := (Finset.mem_sdiff.mp h1).1
      have h1not := (Finset.mem_sdiff.mp h1).2
      have h2B := (Finset.mem_sdiff.mp h2).1
      have h2not := (Finset.mem_sdiff.mp h2).2
      by_cases h12 : j2 = cnext hn j1
      · subst h12; exact h1not (Finset.mem_union_right _ h2B)
      · by_cases h21 : j1 = cnext hn j2
        · subst h21; exact h2not (Finset.mem_union_right _ h1B)
        · exact odd_setB_inter_empty ha0 hne h12 h21 (Finset.mem_filter.mp h1B).2 (Finset.mem_filter.mp h2B).2
    have hcapAB : ∀ j, (setB j ∩ setA j).card ≤ 2 ^ k := by
      intro j
      have hinj : ∀ v1 ∈ setB j ∩ setA j, ∀ v2 ∈ setB j ∩ setA j, v1 j = v2 j → v1 = v2 := by
        intro v1 h1 v2 h2 heq
        rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at h1 h2
        funext i
        by_cases hij : i = j
        · rw [hij]; exact heq
        · by_cases hinj : i = cnext hn j
          · rw [hinj, ← h1.1.2.1.1, ← h2.1.2.1.1]; exact heq
          · by_cases hiP : i ∈ suppP a j
            · rw [h1.2.2.1 i hiP, h2.2.2.1 i hiP]
            · have hiQ : i ∈ suppQ a j := by
                simp only [suppP, Finset.mem_filter, Finset.mem_univ, true_and] at hiP
                simp only [suppQ, Finset.mem_filter, Finset.mem_univ, true_and]; omega
              rw [h1.1.2.1.2 i hiQ hij hinj, h2.1.2.1.2 i hiQ hij hinj]
      calc (setB j ∩ setA j).card = ((setB j ∩ setA j).image (fun v => v j)).card :=
            (Finset.card_image_of_injOn fun v1 h1 v2 h2 heq => hinj v1 h1 v2 h2 heq).symm
        _ ≤ (Finset.univ : Finset (Vec k)).card := Finset.card_le_univ _
        _ = 2 ^ k := by rw [Finset.card_univ, card_Vec]
    have hcapBB : ∀ j, (setB j ∩ setB (cnext hn j)).card ≤ 2 ^ k := by
      intro j
      have hinj : ∀ v1 ∈ setB j ∩ setB (cnext hn j), ∀ v2 ∈ setB j ∩ setB (cnext hn j),
          v1 j = v2 j → v1 = v2 := by
        intro v1 h1 v2 h2 heq
        rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at h1 h2
        funext i
        by_cases hij : i = j
        · rw [hij]; exact heq
        · by_cases hinj : i = cnext hn j
          · rw [hinj, ← h1.1.2.1.1, ← h2.1.2.1.1]; exact heq
          · by_cases hi2 : i = cnext hn (cnext hn j)
            · rw [hi2, ← h1.2.2.1.1, ← h2.2.2.1.1, ← h1.1.2.1.1, ← h2.1.2.1.1]; exact heq
            · by_cases hiQ1 : i ∈ suppQ a j
              · rw [h1.1.2.1.2 i hiQ1 hij hinj, h2.1.2.1.2 i hiQ1 hij hinj]
              · have hiQ2 : i ∈ suppQ a (cnext hn j) := by
                  simp only [suppQ, Finset.mem_filter, Finset.mem_univ, true_and] at hiQ1 ⊢
                  have hne0 : oddOff a i j ≠ 0 := fun h => hij ((oddOff_eq_iff a i j).mp h)
                  have hne1 : oddOff a i j ≠ 1 := fun h => hinj ((oddOff_eq_one_iff a ha0 i j).mp h)
                  have hlt : oddOff a i j < 2 * a + 1 := Nat.mod_lt _ hn
                  have hsh : oddOff a i (cnext hn j) = oddOff a i j - 1 := by
                    rw [oddOff_cnext_right,
                      show oddOff a i j + 2 * a = (oddOff a i j - 1) + (2 * a + 1) by omega,
                      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : oddOff a i j - 1 < 2 * a + 1)]
                  rw [hsh]; omega
                rw [h1.2.2.1.2 i hiQ2 hinj hi2, h2.2.2.1.2 i hiQ2 hinj hi2]
      calc (setB j ∩ setB (cnext hn j)).card =
            ((setB j ∩ setB (cnext hn j)).image (fun v => v j)).card :=
            (Finset.card_image_of_injOn fun v1 h1 v2 h2 heq => hinj v1 h1 v2 h2 heq).symm
        _ ≤ (Finset.univ : Finset (Vec k)).card := Finset.card_le_univ _
        _ = 2 ^ k := by rw [Finset.card_univ, card_Vec]
    have hcardB' : ∀ j, (2 ^ k - 1) * (2 ^ k) ^ a ≤ (setB' j).card + 2 * 2 ^ k := by
      intro j
      have hsd := Finset.card_sdiff_add_card_inter (setB j) (setA j ∪ setB (cnext hn j))
      have hint : (setB j ∩ (setA j ∪ setB (cnext hn j))).card ≤ 2 * 2 ^ k := by
        rw [Finset.inter_union_distrib_left]
        calc (setB j ∩ setA j ∪ setB j ∩ setB (cnext hn j)).card
            ≤ (setB j ∩ setA j).card + (setB j ∩ setB (cnext hn j)).card := Finset.card_union_le _ _
          _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add (hcapAB j) (hcapBB j)
          _ = 2 * 2 ^ k := by ring
      rw [hcardB j] at hsd
      change (setB' j).card + (setB j ∩ (setA j ∪ setB (cnext hn j))).card = _ at hsd
      omega
    have hVev_lo : 2 * (2 * a + 1) * (2 ^ k - 1) * (2 ^ k) ^ a - 2 * (2 * a + 1) * 2 ^ k ≤ Vev.card := by
      have hun_sub : Finset.univ.biUnion setA ∪ Finset.univ.biUnion setB' ⊆ Vev :=
        Finset.union_subset hsub_A hsub_B'
      have hcard_un := Finset.card_le_card hun_sub
      rw [Finset.card_union_of_disjoint hdisj_AB, Finset.card_biUnion hdisj_A,
        Finset.card_biUnion hdisj_B'] at hcard_un
      have hsumA : ∑ j : Fin (2 * a + 1), (setA j).card = (2 * a + 1) * ((2 ^ k - 1) * (2 ^ k) ^ a) := by
        simp [hcardA]
      have hsumB' : (2 * a + 1) * ((2 ^ k - 1) * (2 ^ k) ^ a) ≤
          (∑ j : Fin (2 * a + 1), (setB' j).card) + (2 * a + 1) * (2 * 2 ^ k) := by
        calc (2 * a + 1) * ((2 ^ k - 1) * (2 ^ k) ^ a)
            = ∑ _j : Fin (2 * a + 1), ((2 ^ k - 1) * (2 ^ k) ^ a) := by simp
          _ ≤ ∑ j : Fin (2 * a + 1), ((setB' j).card + 2 * 2 ^ k) :=
              Finset.sum_le_sum fun j _ => hcardB' j
          _ = (∑ j : Fin (2 * a + 1), (setB' j).card) + (2 * a + 1) * (2 * 2 ^ k) := by
              rw [Finset.sum_add_distrib]; simp
      rw [hsumA] at hcard_un
      have hmul_eq1 : 2 * (2 * a + 1) * (2 ^ k - 1) * (2 ^ k) ^ a =
          (2 * a + 1) * ((2 ^ k - 1) * (2 ^ k) ^ a) + (2 * a + 1) * ((2 ^ k - 1) * (2 ^ k) ^ a) := by ring
      have hmul_eq2 : 2 * (2 * a + 1) * 2 ^ k = (2 * a + 1) * (2 * 2 ^ k) := by ring
      omega
    exact Nat.mul_le_mul_right _ hVev_lo
  · have hhitP_cov : ∀ v j, hitP a k j v → v ≠ 0 → ∃ j', v ∈ setA j' := by
      intro v j hp hnz
      let step2 : Fin (2 * a + 1) → Fin (2 * a + 1) := fun x => cprev hn (cprev hn x)
      have hwalk : ∀ t : ℕ, (∀ s < t, v (step2^[s] j) = 0) → hitP a k (step2^[t] j) v := by
        intro t
        induction t with
        | zero => intro _; exact hp
        | succ t ih =>
          intro hall
          have hprev := ih (fun s hs => hall s (by omega))
          rw [Function.iterate_succ_apply']
          exact hitP_step_prev2 ha0 hprev (hall t (by omega))
      have hex_nz : ∃ t < 2 * a + 1, v (step2^[t] j) ≠ 0 := by
        by_contra h
        push Not at h
        apply hnz
        funext i
        have hstep_val : ∀ t, (step2^[t] j).val = (j.val + (2 * a + 1) * 2 * t - 2 * t) % (2 * a + 1) := by
          intro t
          induction t with
          | zero => simp [Nat.mod_eq_of_lt j.isLt]
          | succ t ih =>
            rw [Function.iterate_succ_apply']
            have h1 : ∀ x : Fin (2 * a + 1), (step2 x).val = (x.val + (2 * a - 1)) % (2 * a + 1) := by
              intro x
              simp only [step2, cprev]
              rw [show (x.val + (2 * a + 1) - 1) % (2 * a + 1) + (2 * a + 1) - 1 =
                  (x.val + (2 * a + 1) - 1) % (2 * a + 1) + 2 * a by omega,
                Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
                show x.val + (2 * a + 1) - 1 + 2 * a = (x.val + (2 * a - 1)) + (2 * a + 1) by omega,
                Nat.add_mod_right]
            rw [h1, ih, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            have hdist : (2 * a + 1) * 2 * (t + 1) = (2 * a + 1) * 2 * t + 2 * (2 * a + 1) := by ring
            have hge : 2 * t ≤ (2 * a + 1) * 2 * t := by
              calc 2 * t = 1 * (2 * t) := (one_mul _).symm
                _ ≤ (2 * a + 1) * (2 * t) := Nat.mul_le_mul_right _ (by omega)
                _ = (2 * a + 1) * 2 * t := by ring
            have : (j.val + (2 * a + 1) * 2 * t - 2 * t + (2 * a - 1)) + (2 * a + 1) =
                j.val + (2 * a + 1) * 2 * (t + 1) - 2 * (t + 1) := by omega
            rw [← Nat.add_mod_right _ (2 * a + 1), this]
        let d := oddOff a i j
        have hd_lt : d < 2 * a + 1 := Nat.mod_lt _ hn
        let t := if d % 2 = 0 then (2 * a + 1 - d / 2) % (2 * a + 1) else (2 * a + 1 - d) / 2
        have ht_lt : t < 2 * a + 1 := by
          dsimp only [t]
          split_ifs
          · exact Nat.mod_lt _ hn
          · omega
        have heq_i : step2^[t] j = i := by
          ext
          rw [hstep_val t]
          have h2t : (j.val + (2 * a + 1) * 2 * t - 2 * t) % (2 * a + 1) = i.val := by
            have hmod : (2 * t + d) % (2 * a + 1) = 0 := by
              dsimp only [t]
              split_ifs with hev
              · by_cases hd0 : d = 0
                · simp [hd0]
                · rw [Nat.mod_eq_of_lt (by omega : 2 * a + 1 - d / 2 < 2 * a + 1)]
                  rw [show 2 * (2 * a + 1 - d / 2) + d = 2 * (2 * a + 1) by omega, Nat.mul_mod_left]
              · rw [show 2 * ((2 * a + 1 - d) / 2) + d = 2 * a + 1 by omega, Nat.mod_self]
            have hsum : (j.val + (2 * a + 1) * 2 * t - 2 * t + (2 * t + d)) % (2 * a + 1) =
                (j.val + d) % (2 * a + 1) := by
              have hassoc : (2 * a + 1) * 2 * t = (2 * a + 1) * (2 * t) := by ring
              have hge : 2 * t ≤ (2 * a + 1) * (2 * t) := Nat.le_mul_of_pos_left _ (by omega)
              rw [show j.val + (2 * a + 1) * 2 * t - 2 * t + (2 * t + d) =
                  (j.val + d) + (2 * a + 1) * (2 * t) by omega, Nat.add_mul_mod_self_left]
            rw [Nat.add_mod, hmod, add_zero, Nat.mod_mod] at hsum
            rw [hsum]
            simp only [d, oddOff]
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
              show j.val + (i.val + (2 * a + 1) - j.val) = i.val + (2 * a + 1) by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
          exact h2t
        rw [← heq_i]
        exact h t ht_lt
      let t0 := Nat.find hex_nz
      have ht0_spec := Nat.find_spec hex_nz
      refine ⟨step2^[t0] j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ht0_spec.2⟩⟩
      exact hwalk t0 (fun s hs => by
        by_contra hns
        exact Nat.find_min hex_nz hs ⟨by omega, hns⟩)
    have hVev_sub : Vev ⊆ {0} ∪ Finset.univ.biUnion setA ∪ Finset.univ.biUnion setB := by
      intro v hv
      rw [Finset.mem_filter] at hv
      by_cases hv0 : v = 0
      · subst hv0; simp
      · obtain ⟨j, hp | hq⟩ := hv.2
        · obtain ⟨j', hj'⟩ := hhitP_cov v j hp hv0
          exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j', Finset.mem_univ _, hj'⟩))
        · by_cases hvj : v j = 0
          · have hp_nx : hitP a k (cnext hn j) v := by
              intro i hiP
              rw [suppP, Finset.mem_filter] at hiP
              by_cases hij : i = j
              · rw [hij]; exact hvj
              · have hinj : i ≠ cnext hn j := fun h => hiP.2.1 (by rw [h, oddOff_self])
                have hiQ : i ∈ suppQ a j := by
                  rw [oddOff_cnext_right] at hiP
                  have hne0 : oddOff a i j ≠ 0 := fun h => hij ((oddOff_eq_iff a i j).mp h)
                  have hlt : oddOff a i j < 2 * a + 1 := Nat.mod_lt _ hn
                  have hmod : (oddOff a i j + 2 * a) % (2 * a + 1) = oddOff a i j - 1 := by
                    rw [show oddOff a i j + 2 * a = (oddOff a i j - 1) + (2 * a + 1) by omega,
                      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : oddOff a i j - 1 < 2 * a + 1)]
                  rw [hmod] at hiP
                  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (by omega)⟩
                exact hq.2 i hiQ hij hinj
            obtain ⟨j', hj'⟩ := hhitP_cov v (cnext hn j) hp_nx hv0
            exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j', Finset.mem_univ _, hj'⟩))
          · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq, hvj⟩⟩)
    have hVev_hi : Vev.card ≤ 1 + 2 * (2 * a + 1) * (2 ^ k - 1) * (2 ^ k) ^ a := by
      calc Vev.card ≤ ({0} ∪ Finset.univ.biUnion setA ∪ Finset.univ.biUnion setB).card :=
            Finset.card_le_card hVev_sub
        _ ≤ ({0} ∪ Finset.univ.biUnion setA).card + (Finset.univ.biUnion setB).card :=
            Finset.card_union_le _ _
        _ ≤ ({0} : Finset _).card + (Finset.univ.biUnion setA).card + (Finset.univ.biUnion setB).card :=
            Nat.add_le_add_right (Finset.card_union_le _ _) _
        _ ≤ 1 + (∑ j : Fin (2 * a + 1), (setA j).card) + (∑ j : Fin (2 * a + 1), (setB j).card) := by
            rw [Finset.card_singleton]
            exact Nat.add_le_add (Nat.add_le_add_left Finset.card_biUnion_le 1) Finset.card_biUnion_le
        _ = 1 + 2 * (2 * a + 1) * (2 ^ k - 1) * (2 ^ k) ^ a := by
            simp only [hcardA, hcardB, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
            ring
    exact Nat.mul_le_mul_right _ hVev_hi

theorem main_proof_even (m k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) :
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let A := Fin m → F
  letI : Fintype (Submodule F A) := Fintype.ofFinite _
  let countD := ((Finset.univ : Finset (Submodule F A)).filter
    (fun D : Submodule F A => Module.finrank F D + k = m)).card
  let prob := fun (n a : ℕ) (hn : 0 < n) =>
    let next := fun i : Fin n => (⟨(i.val+1) % n, Nat.mod_lt _ hn⟩ : Fin n)
    let event := fun h : Fin n → A =>
      ∃ U : Submodule F (Fin n → F), a+k ≤ Module.finrank F U + m ∧
        (∀ x ∈ U, ∀ b : Fin m, (∑ i, h i b * x i) = 0) ∧
        (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
    (((Finset.univ : Finset (Fin n → A)).filter event).card : ℝ) / (2:ℝ)^(m*n)
  Filter.Tendsto (fun t : ℕ => let a := t+2
       (2:ℝ)^(k*a) * prob (2*a) a (Nat.mul_pos (Nat.succ_pos 1) (Nat.succ_pos (t+1))))
     Filter.atTop (nhds (2*(countD:ℝ))) := by
  classical
  let _ : Fintype (Submodule F (Vec m)) := Fintype.ofFinite _
  let Ds : Finset (Submodule F (Vec m)) :=
    Finset.univ.filter (fun D : Submodule F (Vec m) => Module.finrank F D + k = m)
  let countD : ℕ := Ds.card
  let C_tail : ℝ := (Fintype.card (Submodule F (Vec m)) : ℝ) * (2 * (m + 1) : ℝ) * (2 : ℝ) ^ (m * m)
  have hC_tail_nn : 0 ≤ C_tail := by positivity
  let C_ev : ℝ := C_tail * (3 : ℝ) ^ (2 * m + 1) + 4 * (countD : ℝ) ^ 2
  apply tendsto_of_poly_bound (2 * m + 1) C_ev (by positivity)
  refine ⟨m + 2, fun t ht => ?_⟩
  dsimp only
  set a := t + 2
  have ha_ge : m + 2 ≤ a := by omega
  have ha0 : 0 < a := by omega
  have hn : 0 < 2 * a := Nat.mul_pos (Nat.succ_pos 1) (Nat.succ_pos (t + 1))
  let evSet := (Finset.univ : Finset (Fin (2 * a) → Vec m)).filter (cycleEvent hn a k)
  let mainIdx := (Finset.univ : Finset Bool) ×ˢ Ds
  let mainCell : Bool × Submodule F (Vec m) → Finset (Fin (2 * a) → Vec m) :=
    fun p => Finset.univ.filter (Hit hn (if p.1 then evenSupp a else oddSupp a) p.2)
  let mainSet := mainIdx.biUnion mainCell
  let tailSet := (Finset.univ : Finset (Fin (2 * a) → Vec m)).filter (tailEv hn a k)
  have hmain_sub : mainSet ⊆ evSet := by
    intro h hh
    rw [Finset.mem_biUnion] at hh
    obtain ⟨⟨b, D⟩, hp, hmem⟩ := hh
    rw [Finset.mem_product] at hp
    rw [Finset.mem_filter] at hmem
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hD : Module.finrank F D + k = m := (Finset.mem_filter.mp hp.2).2
    cases b
    · exact hit_imp_cycleEvent hn (oddSupp_ne_univ ha0) (by rw [starts_oddSupp ha0, card_oddSupp]) hD hmem.2
    · exact hit_imp_cycleEvent hn (evenSupp_ne_univ ha0) (by rw [starts_evenSupp ha0, card_evenSupp]) hD hmem.2
  have hev_sub : evSet ⊆ mainSet ∪ tailSet := by
    intro h hh
    rw [Finset.mem_filter] at hh
    obtain ⟨S, D, hSne, hrle, hgap, hD, hhit⟩ :=
      cycleEvent_imp_hit hn hk hkm (by omega) (by omega) hh.2
    by_cases hra : (starts hn S).card = a
    · rw [hra, Nat.sub_self, add_zero] at hD
      apply Finset.mem_union_left
      rw [Finset.mem_biUnion]
      rcases eq_even_or_odd_of_starts_eq ha0 S hra with rfl | rfl
      · refine ⟨(true, D), Finset.mem_product.mpr ⟨Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hD⟩⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhit⟩⟩
      · refine ⟨(false, D), Finset.mem_product.mpr ⟨Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hD⟩⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhit⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, S, D, hSne, by omega, hgap, hD, hhit⟩
  have h2mn_pos : (0 : ℝ) < (2 : ℝ) ^ (m * (2 * a)) := by positivity
  have h2ka_pos : (0 : ℝ) < (2 : ℝ) ^ (k * a) := by positivity
  have hcell_prob : ∀ p ∈ mainIdx,
      ((mainCell p).card : ℝ) / (2 : ℝ) ^ (m * (2 * a)) = 1 / (2 : ℝ) ^ (k * a) := by
    rintro ⟨b, D⟩ hp
    have hD : Module.finrank F D + k = m := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).2
    have hst : (starts hn (if b then evenSupp a else oddSupp a)).card = a := by
      cases b <;> simp [starts_evenSupp ha0, starts_oddSupp ha0, card_evenSupp, card_oddSupp]
    have hc := card_hit hn (if b then evenSupp a else oddSupp a) D hD
    rw [hst] at hc
    have hcard_eq : (mainCell (b, D)).card =
        (Finset.univ.filter (Hit hn (if b then evenSupp a else oddSupp a) D)).card :=
      congrArg Finset.card (Finset.ext fun _ => by simp [mainCell])
    rw [← hcard_eq] at hc
    have hcr : ((mainCell (b, D)).card : ℝ) * (2 : ℝ) ^ (k * a) = (2 : ℝ) ^ (m * (2 * a)) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using nat_mul_eq_cast_real hc
    rw [div_eq_div_iff h2mn_pos.ne' h2ka_pos.ne', one_mul, hcr]
  have hsum_cells : ∑ p ∈ mainIdx, ((mainCell p).card : ℝ) / (2 : ℝ) ^ (m * (2 * a)) =
      2 * (countD : ℝ) / (2 : ℝ) ^ (k * a) := by
    rw [Finset.sum_congr rfl hcell_prob, Finset.sum_const, nsmul_eq_mul]
    simp only [mainIdx, Finset.card_product, Finset.card_univ, Fintype.card_bool, countD]
    push_cast; ring
  have hinter_prob : ∀ p ∈ mainIdx, ∀ q ∈ mainIdx.filter (fun q => q ≠ p),
      (((mainCell p ∩ mainCell q).card : ℝ) / (2 : ℝ) ^ (m * (2 * a))) ≤
        1 / (2 : ℝ) ^ (k * a + a) := by
    rintro ⟨b1, D1⟩ hp ⟨b2, D2⟩ hq
    rw [Finset.mem_filter] at hq
    have hD1 : Module.finrank F D1 + k = m := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).2
    have hD2 : Module.finrank F D2 + k = m := (Finset.mem_filter.mp (Finset.mem_product.mp hq.1).2).2
    have hfilt_eq : mainCell (b1, D1) ∩ mainCell (b2, D2) =
        Finset.univ.filter (fun h => Hit hn (if b1 then evenSupp a else oddSupp a) D1 h ∧
          Hit hn (if b2 then evenSupp a else oddSupp a) D2 h) := by
      ext h; simp [mainCell]
    rw [hfilt_eq]
    have hst1 : (starts hn (if b1 then evenSupp a else oddSupp a)).card = a := by
      cases b1 <;> simp [starts_evenSupp ha0, starts_oddSupp ha0, card_evenSupp, card_oddSupp]
    have hst2 : (starts hn (if b2 then evenSupp a else oddSupp a)).card = a := by
      cases b2 <;> simp [starts_evenSupp ha0, starts_oddSupp ha0, card_evenSupp, card_oddSupp]
    by_cases hDeq : D1 = D2
    · subst hDeq
      have hbne : b1 ≠ b2 := fun hb => hq.2 (by rw [hb])
      have hdisj : Disjoint (if b1 then evenSupp a else oddSupp a)
          (if b2 then evenSupp a else oddSupp a) := by
        cases b1 <;> cases b2
        · exact absurd rfl hbne
        · exact (evenSupp_disjoint_oddSupp a).symm
        · exact evenSupp_disjoint_oddSupp a
        · exact absurd rfl hbne
      have h1ne : (if b1 then evenSupp a else oddSupp a) ≠ Finset.univ := by
        cases b1 <;> simp [evenSupp_ne_univ ha0, oddSupp_ne_univ ha0]
      have h2ne : (if b2 then evenSupp a else oddSupp a) ≠ Finset.univ := by
        cases b2 <;> simp [evenSupp_ne_univ ha0, oddSupp_ne_univ ha0]
      have hc := card_hit_disjoint_supps hn hdisj h1ne h2ne hD1 hD2
      rw [hst1, hst2] at hc
      have hle : (Finset.univ.filter (fun h => Hit hn (if b1 then evenSupp a else oddSupp a) D1 h ∧
          Hit hn (if b2 then evenSupp a else oddSupp a) D1 h)).card * 2 ^ (k * a + a) ≤
          2 ^ (m * (2 * a)) := by
        rw [← hc]
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_right (by omega)
        have : a ≤ k * a := Nat.le_mul_of_pos_left a hk
        omega
      have hler : ((Finset.univ.filter (fun h => Hit hn (if b1 then evenSupp a else oddSupp a) D1 h ∧
          Hit hn (if b2 then evenSupp a else oddSupp a) D1 h)).card : ℝ) *
          (2 : ℝ) ^ (k * a + a) ≤ (2 : ℝ) ^ (m * (2 * a)) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using nat_mul_le_cast_real hle
      rw [div_le_div_iff₀ h2mn_pos (by positivity), one_mul]
      exact hler
    · have hc' := card_hit_inter_ne hn (if b1 then evenSupp a else oddSupp a)
        (if b2 then evenSupp a else oddSupp a) hD1 hD2 hDeq
      rw [hst1, hst2] at hc'
      have hler : ((Finset.univ.filter (fun h => Hit hn (if b1 then evenSupp a else oddSupp a) D1 h ∧
          Hit hn (if b2 then evenSupp a else oddSupp a) D2 h)).card : ℝ) *
          (2 : ℝ) ^ (k * a + a) ≤ (2 : ℝ) ^ (m * (2 * a)) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using nat_mul_le_cast_real hc'
      rw [div_le_div_iff₀ h2mn_pos (by positivity), one_mul]
      exact hler

  have hupper : (2 : ℝ) ^ (k * a) * ((evSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a))) -
      2 * (countD : ℝ) ≤ C_tail * (3 : ℝ) ^ (2 * m + 1) * (a : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ a := by
    have hev_le : (evSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a)) ≤
        2 * (countD : ℝ) / (2 : ℝ) ^ (k * a) +
        (tailSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a)) := by
      have h1 : evSet.card ≤ (∑ p ∈ mainIdx, (mainCell p).card) + tailSet.card :=
        le_trans (Finset.card_le_card hev_sub)
          (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right Finset.card_biUnion_le _))
      have h1r : (evSet.card : ℝ) ≤ (∑ p ∈ mainIdx, ((mainCell p).card : ℝ)) + (tailSet.card : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_sum] using nat_le_cast_real h1
      have h2 : (evSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a)) ≤
          (∑ p ∈ mainIdx, ((mainCell p).card : ℝ) / (2 : ℝ) ^ (m * (2 * a))) +
          (tailSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a)) := by
        rw [← sum_div_real, ← add_div]
        exact div_le_div_of_nonneg_right h1r h2mn_pos.le
      rwa [hsum_cells] at h2
    have htail := tail_card_bound (n := 2 * a) (m := m) (a := a) hn hkm (by omega) (by omega)
    have h2a_le : ((2 * a : ℕ) : ℝ) ^ (2 * m + 1) ≤ (3 : ℝ) ^ (2 * m + 1) * (a : ℝ) ^ (2 * m + 1) := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      push_cast; linarith
    have hmul_tail : (2 : ℝ) ^ (k * a) * ((tailSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a))) ≤
        C_tail * (3 : ℝ) ^ (2 * m + 1) * (a : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ a := by
      calc (2 : ℝ) ^ (k * a) * ((tailSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a)))
          ≤ (2 : ℝ) ^ (k * a) * (C_tail * (((2 * a : ℕ) : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ (k * a + a))) :=
            mul_le_mul_of_nonneg_left htail h2ka_pos.le
        _ = C_tail * (((2 * a : ℕ) : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ a) := by
            rw [pow_add (2 : ℝ) (k * a) a]; field_simp
        _ ≤ C_tail * ((3 : ℝ) ^ (2 * m + 1) * (a : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ a) := by
            apply mul_le_mul_of_nonneg_left _ hC_tail_nn
            exact div_le_div_of_nonneg_right h2a_le (by positivity)
        _ = _ := by ring
    have hmul := mul_le_mul_of_nonneg_left hev_le h2ka_pos.le
    rw [mul_add ((2 : ℝ) ^ (k * a)), mul_div_cancel₀ _ h2ka_pos.ne'] at hmul
    linarith

  have hlower : 2 * (countD : ℝ) -
      (2 : ℝ) ^ (k * a) * ((evSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a))) ≤
      4 * (countD : ℝ) ^ 2 / (2 : ℝ) ^ a := by
    have hbonf := bonferroni_lower mainIdx mainCell
    have hmain_le : mainSet.card ≤ evSet.card := Finset.card_le_card hmain_sub
    have hbonf_r : (∑ p ∈ mainIdx, ((mainCell p).card : ℝ) / (2 : ℝ) ^ (m * (2 * a))) ≤
        (evSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a)) +
        ∑ p ∈ mainIdx, ∑ q ∈ mainIdx.filter (fun q => q ≠ p),
          ((mainCell p ∩ mainCell q).card : ℝ) / (2 : ℝ) ^ (m * (2 * a)) := by
      dsimp only [mainSet] at hmain_le
      have hnat : ∑ p ∈ mainIdx, (mainCell p).card ≤
          evSet.card + ∑ p ∈ mainIdx, ∑ q ∈ mainIdx.filter (fun q => q ≠ p),
            (mainCell p ∩ mainCell q).card := by omega
      have hr : (∑ p ∈ mainIdx, ((mainCell p).card : ℝ)) ≤
          (evSet.card : ℝ) + ∑ p ∈ mainIdx, ∑ q ∈ mainIdx.filter (fun q => q ≠ p),
            ((mainCell p ∩ mainCell q).card : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_sum] using nat_le_cast_real hnat
      have hdiv := div_le_div_of_nonneg_right hr h2mn_pos.le
      rw [sum_div_real, add_div, sum_div_real] at hdiv
      refine le_trans hdiv (add_le_add le_rfl (le_of_eq (Finset.sum_congr rfl fun _ _ => sum_div_real _ _ _)))
    rw [hsum_cells] at hbonf_r
    have hover : ∑ p ∈ mainIdx, ∑ q ∈ mainIdx.filter (fun q => q ≠ p),
        ((mainCell p ∩ mainCell q).card : ℝ) / (2 : ℝ) ^ (m * (2 * a)) ≤
        4 * (countD : ℝ) ^ 2 / (2 : ℝ) ^ (k * a + a) := by
      calc _ ≤ ∑ p ∈ mainIdx, ∑ _q ∈ mainIdx.filter (fun q => q ≠ p), (1 / (2 : ℝ) ^ (k * a + a)) :=
            Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => hinter_prob p hp q hq
        _ ≤ ∑ _p ∈ mainIdx, ∑ _q ∈ mainIdx, (1 / (2 : ℝ) ^ (k * a + a)) :=
            Finset.sum_le_sum fun _ _ => Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
        _ = ((mainIdx.card : ℝ) * (mainIdx.card : ℝ)) / (2 : ℝ) ^ (k * a + a) := by
            simp only [Finset.sum_const, nsmul_eq_mul]; ring
        _ = 4 * (countD : ℝ) ^ 2 / (2 : ℝ) ^ (k * a + a) := by
            simp only [mainIdx, Finset.card_product, Finset.card_univ, Fintype.card_bool, countD]
            push_cast; ring
    have hmul := mul_le_mul_of_nonneg_left (le_trans hbonf_r (add_le_add le_rfl hover)) h2ka_pos.le
    rw [mul_div_cancel₀ _ h2ka_pos.ne', mul_add] at hmul
    have hsimp : (2 : ℝ) ^ (k * a) * (4 * (countD : ℝ) ^ 2 / (2 : ℝ) ^ (k * a + a)) =
        4 * (countD : ℝ) ^ 2 / (2 : ℝ) ^ a := by
      rw [pow_add]; field_simp
    rw [hsimp] at hmul
    linarith
  have ha1 : (1 : ℝ) ≤ (a : ℝ) ^ (2 * m + 1) := one_le_pow₀ (by exact_mod_cast (show 1 ≤ a by omega))
  have hmain_bound : |(2 : ℝ) ^ (k * a) * ((evSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a))) - 2 * (countD : ℝ)| ≤
      C_ev * (a : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ a := by
    rw [abs_le]
    constructor
    · have : 4 * (countD : ℝ) ^ 2 / (2 : ℝ) ^ a ≤ C_ev * (a : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ a := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : 4 * (countD : ℝ) ^ 2 ≤ C_ev := by dsimp only [C_ev]; linarith [mul_nonneg hC_tail_nn (pow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) (2 * m + 1))]
        nlinarith
      linarith
    · have : C_tail * (3 : ℝ) ^ (2 * m + 1) * (a : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ a ≤
          C_ev * (a : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ a := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : C_tail * (3 : ℝ) ^ (2 * m + 1) ≤ C_ev := by dsimp only [C_ev]; linarith [sq_nonneg (countD : ℝ)]
        nlinarith
      linarith
  refine abs_sub_le_of_eq ?_ ?_ hmain_bound
  · exact congrArg (fun c : ℕ => (2 : ℝ) ^ (k * a) * ((c : ℝ) / (2 : ℝ) ^ (m * (2 * a))))
      (card_filter_eq (fun _ => Iff.rfl))
  · exact congrArg (fun c : ℕ => 2 * (c : ℝ)) (card_filter_eq (fun _ => Iff.rfl))

theorem main_proof_odd (m k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) :
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let A := Fin m → F
  letI : Fintype (Submodule F A) := Fintype.ofFinite _
  let countD := ((Finset.univ : Finset (Submodule F A)).filter
    (fun D : Submodule F A => Module.finrank F D + k = m)).card
  let prob := fun (n a : ℕ) (hn : 0 < n) =>
    let next := fun i : Fin n => (⟨(i.val+1) % n, Nat.mod_lt _ hn⟩ : Fin n)
    let event := fun h : Fin n → A =>
      ∃ U : Submodule F (Fin n → F), a+k ≤ Module.finrank F U + m ∧
        (∀ x ∈ U, ∀ b : Fin m, (∑ i, h i b * x i) = 0) ∧
        (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
    (((Finset.univ : Finset (Fin n → A)).filter event).card : ℝ) / (2:ℝ)^(m*n)
  Filter.Tendsto (fun t : ℕ => let a := t+2
       (2:ℝ)^(k*a) * prob (2*a+1) a (Nat.succ_pos (2*a)) / (2*(a:ℝ)+1))
     Filter.atTop (nhds (2*(1-1/(2:ℝ)^k)*(countD:ℝ))) := by
  classical
  let _ : Fintype (Submodule F (Vec m)) := Fintype.ofFinite _
  let Ds : Finset (Submodule F (Vec m)) :=
    Finset.univ.filter (fun D : Submodule F (Vec m) => Module.finrank F D + k = m)
  let countD : ℕ := Ds.card
  let C_tail : ℝ := (Fintype.card (Submodule F (Vec m)) : ℝ) * (2 * (m + 1) : ℝ) * (2 : ℝ) ^ (m * m)
  have hC_tail_nn : 0 ≤ C_tail := by positivity
  let C_odd : ℝ := C_tail * (3 : ℝ) ^ (2 * m + 1) + (countD : ℝ) * 2 + 4 * (countD : ℝ) ^ 2 * 9
  apply tendsto_of_poly_bound (2 * m + 2) C_odd (by positivity)
  refine ⟨m + 2, fun t ht => ?_⟩
  dsimp only
  set a := t + 2
  have ha_ge : m + 2 ≤ a := by omega
  have ha2 : 2 ≤ a := by omega
  have ha0 : 0 < a := by omega
  have hn : 0 < 2 * a + 1 := oddPos a
  let evSet := (Finset.univ : Finset (Fin (2 * a + 1) → Vec m)).filter (cycleEvent hn a k)
  let cellD (D : Submodule F (Vec m)) : Finset (Fin (2 * a + 1) → Vec m) :=
    Finset.univ.filter (fun h => ∃ j : Fin (2 * a + 1), Hit hn (suppP a j) D h ∨ Hit hn (suppQ a j) D h)
  let mainSet := Ds.biUnion cellD
  let tailSet := (Finset.univ : Finset (Fin (2 * a + 1) → Vec m)).filter (tailEv hn a k)
  have hmain_sub : mainSet ⊆ evSet := by
    intro h hh
    rw [Finset.mem_biUnion] at hh
    obtain ⟨D, hDmem, hmem⟩ := hh
    have hD : Module.finrank F D + k = m := (Finset.mem_filter.mp hDmem).2
    rw [Finset.mem_filter] at hmem
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨j, hp | hq⟩ := hmem.2
    · exact hit_imp_cycleEvent hn (suppP_ne_univ j) (by rw [starts_suppP ha0 j, card_suppP ha0 j]) hD hp
    · exact hit_imp_cycleEvent hn (suppQ_ne_univ ha0 j) (card_starts_suppQ ha0 j) hD hq
  have hev_sub : evSet ⊆ mainSet ∪ tailSet := by
    intro h hh
    rw [Finset.mem_filter] at hh
    obtain ⟨S, D, hSne, hrle, hgap, hD, hhit⟩ :=
      cycleEvent_imp_hit hn hk hkm (by omega) (by omega) hh.2
    by_cases hra : (starts hn S).card = a
    · rw [hra, Nat.sub_self, add_zero] at hD
      apply Finset.mem_union_left
      rw [Finset.mem_biUnion]
      obtain ⟨j, rfl | rfl⟩ := eq_suppP_or_suppQ ha0 S hra
      · exact ⟨D, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hD⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, Or.inl hhit⟩⟩
      · exact ⟨D, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hD⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, Or.inr hhit⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, S, D, hSne, by omega, hgap, hD, hhit⟩
  have h2mn_pos : (0 : ℝ) < (2 : ℝ) ^ (m * (2 * a + 1)) := by positivity
  have h2ka_pos : (0 : ℝ) < (2 : ℝ) ^ (k * a) := by positivity
  have h2a1_pos : (0 : ℝ) < (2 * (a : ℝ) + 1) := by positivity
  have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have h2k_ge1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
  have hpow_split : (2 : ℝ) ^ ((m - k) * (2 * a + 1)) / (2 : ℝ) ^ (m * (2 * a + 1)) =
      1 / ((2 : ℝ) ^ k * ((2 : ℝ) ^ k) ^ a * ((2 : ℝ) ^ k) ^ a) := by
    have hm1 : (m - k) * (2 * a + 1) + k * (2 * a + 1) = m * (2 * a + 1) := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hkm]
    have hm2 : k * (2 * a + 1) = k + k * a + k * a := by ring
    simp only [← hm1, hm2, pow_add, pow_mul]
    field_simp
  have hcellD_hi : ∀ D ∈ Ds,
      (2 : ℝ) ^ (k * a) * ((cellD D).card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1)) / (2 * (a : ℝ) + 1) ≤
        2 * (1 - 1 / (2 : ℝ) ^ k) + 1 / (2 : ℝ) ^ a := by
    intro D hDm
    have hD : Module.finrank F D + k = m := (Finset.mem_filter.mp hDm).2
    have hbd := (odd_fixed_D_bounds ha2 hk hkm D hD).2
    have hbdr : ((cellD D).card : ℝ) ≤
        (1 + 2 * (2 * (a : ℝ) + 1) * ((2 : ℝ) ^ k - 1) * ((2 : ℝ) ^ k) ^ a) *
          (2 : ℝ) ^ ((m - k) * (2 * a + 1)) := by
      have hsub_cast : ((2 ^ k - 1 : ℕ) : ℝ) = (2 : ℝ) ^ k - 1 := by
        rw [Nat.cast_sub h2k_ge1]; push_cast; rfl
      have h2a1_cast : ((2 * a + 1 : ℕ) : ℝ) = 2 * (a : ℝ) + 1 := by push_cast; rfl
      have h1 := nat_le_cast_real hbd
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat,
        hsub_cast, h2a1_cast] using h1
    have h2ka_eq : (2 : ℝ) ^ (k * a) = ((2 : ℝ) ^ k) ^ a := by rw [pow_mul]
    have h2a_le_2ka : (2 : ℝ) ^ a ≤ ((2 : ℝ) ^ k) ^ a := by
      rw [← pow_mul]
      exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.le_mul_of_pos_left a hk)
    calc (2 : ℝ) ^ (k * a) * ((cellD D).card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1)) / (2 * (a : ℝ) + 1)
        = (2 : ℝ) ^ (k * a) * (((cellD D).card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1) := by ring
      _ ≤ (2 : ℝ) ^ (k * a) *
            ((1 + 2 * (2 * (a : ℝ) + 1) * ((2 : ℝ) ^ k - 1) * ((2 : ℝ) ^ k) ^ a) *
              ((2 : ℝ) ^ ((m - k) * (2 * a + 1)) / (2 : ℝ) ^ (m * (2 * a + 1)))) / (2 * (a : ℝ) + 1) := by
          gcongr; rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hbdr h2mn_pos.le
      _ = 2 * (1 - 1 / (2 : ℝ) ^ k) +
            1 / ((2 * (a : ℝ) + 1) * (2 : ℝ) ^ k * ((2 : ℝ) ^ k) ^ a) := by
          rw [hpow_split, h2ka_eq]; field_simp; ring
      _ ≤ 2 * (1 - 1 / (2 : ℝ) ^ k) + 1 / (2 : ℝ) ^ a := by
          gcongr
          have h1 : (1 : ℝ) ≤ (2 * (a : ℝ) + 1) * (2 : ℝ) ^ k := by
            have : (1 : ℝ) ≤ 2 * (a : ℝ) + 1 := by linarith
            have : (1 : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast h2k_ge1
            nlinarith
          nlinarith
  have hcellD_lo : ∀ D ∈ Ds,
      2 * (1 - 1 / (2 : ℝ) ^ k) - 2 / (2 : ℝ) ^ a ≤
        (2 : ℝ) ^ (k * a) * ((cellD D).card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1)) / (2 * (a : ℝ) + 1) := by
    intro D hDm
    have hD : Module.finrank F D + k = m := (Finset.mem_filter.mp hDm).2
    have hbd := (odd_fixed_D_bounds ha2 hk hkm D hD).1
    have hge_sub : 2 * (2 * a + 1) * 2 ^ k ≤ 2 * (2 * a + 1) * (2 ^ k - 1) * (2 ^ k) ^ a := by
      have h1 : 1 ≤ 2 ^ k - 1 := by
        have : 2 ≤ 2 ^ k := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by omega) hk)
        omega
      have h2 : 2 ^ k ≤ (2 ^ k) ^ a :=
        le_trans (by simp : 2 ^ k ≤ (2 ^ k) ^ 1) (Nat.pow_le_pow_right h2k_ge1 (by omega))
      calc 2 * (2 * a + 1) * 2 ^ k = 2 * (2 * a + 1) * 1 * 2 ^ k := by ring
        _ ≤ 2 * (2 * a + 1) * (2 ^ k - 1) * (2 ^ k) ^ a :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
    have hbdr : (2 * (2 * (a : ℝ) + 1) * ((2 : ℝ) ^ k - 1) * ((2 : ℝ) ^ k) ^ a -
          2 * (2 * (a : ℝ) + 1) * (2 : ℝ) ^ k) * (2 : ℝ) ^ ((m - k) * (2 * a + 1)) ≤
          ((cellD D).card : ℝ) := by
      have hsub_cast : ((2 ^ k - 1 : ℕ) : ℝ) = (2 : ℝ) ^ k - 1 := by
        rw [Nat.cast_sub h2k_ge1]; push_cast; rfl
      have h2a1_cast : ((2 * a + 1 : ℕ) : ℝ) = 2 * (a : ℝ) + 1 := by push_cast; rfl
      have h1 := nat_le_cast_real hbd
      rw [Nat.cast_mul, Nat.cast_sub hge_sub] at h1
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hsub_cast, h2a1_cast] using h1
    have h2ka_eq : (2 : ℝ) ^ (k * a) = ((2 : ℝ) ^ k) ^ a := by rw [pow_mul]
    have h2a_le_2ka : (2 : ℝ) ^ a ≤ ((2 : ℝ) ^ k) ^ a := by
      rw [← pow_mul]
      exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.le_mul_of_pos_left a hk)
    calc 2 * (1 - 1 / (2 : ℝ) ^ k) - 2 / (2 : ℝ) ^ a
        ≤ 2 * (1 - 1 / (2 : ℝ) ^ k) - 2 / ((2 : ℝ) ^ k) ^ a := by
          gcongr
      _ = (2 : ℝ) ^ (k * a) *
            ((2 * (2 * (a : ℝ) + 1) * ((2 : ℝ) ^ k - 1) * ((2 : ℝ) ^ k) ^ a -
              2 * (2 * (a : ℝ) + 1) * (2 : ℝ) ^ k) *
              ((2 : ℝ) ^ ((m - k) * (2 * a + 1)) / (2 : ℝ) ^ (m * (2 * a + 1)))) / (2 * (a : ℝ) + 1) := by
          rw [hpow_split, h2ka_eq]; field_simp
      _ ≤ (2 : ℝ) ^ (k * a) * (((cellD D).card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1) := by
          gcongr; rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hbdr h2mn_pos.le
      _ = _ := by ring

  have hcellD_inter : ∀ D1 ∈ Ds, ∀ D2 ∈ Ds.filter (fun D => D ≠ D1),
      ((cellD D1 ∩ cellD D2).card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1)) ≤
        4 * (2 * (a : ℝ) + 1) ^ 2 / (2 : ℝ) ^ (k * a + a) := by
    intro D1 h1m D2 h2m
    rw [Finset.mem_filter] at h2m
    have hD1 : Module.finrank F D1 + k = m := (Finset.mem_filter.mp h1m).2
    have hD2 : Module.finrank F D2 + k = m := (Finset.mem_filter.mp h2m.1).2
    have hne : D1 ≠ D2 := h2m.2.symm
    let idx := ((Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset (Fin (2 * a + 1)))) ×ˢ
               ((Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset (Fin (2 * a + 1))))
    let suppOf : Bool × Fin (2 * a + 1) → Finset (Fin (2 * a + 1)) :=
      fun p => if p.1 then suppP a p.2 else suppQ a p.2
    have hsub_inter : cellD D1 ∩ cellD D2 ⊆
        idx.biUnion (fun pq => Finset.univ.filter (fun h =>
          Hit hn (suppOf pq.1) D1 h ∧ Hit hn (suppOf pq.2) D2 h)) := by
      intro h hh
      rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hh
      obtain ⟨j1, h1⟩ := hh.1.2
      obtain ⟨j2, h2⟩ := hh.2.2
      rw [Finset.mem_biUnion]
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact ⟨((true, j1), (true, j2)), by simp [idx], Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩⟩
      · exact ⟨((true, j1), (false, j2)), by simp [idx], Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩⟩
      · exact ⟨((false, j1), (true, j2)), by simp [idx], Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩⟩
      · exact ⟨((false, j1), (false, j2)), by simp [idx], Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩⟩
    have hterm_le : ∀ pq ∈ idx,
        ((Finset.univ.filter (fun h => Hit hn (suppOf pq.1) D1 h ∧ Hit hn (suppOf pq.2) D2 h)).card : ℝ) /
          (2 : ℝ) ^ (m * (2 * a + 1)) ≤ 1 / (2 : ℝ) ^ (k * a + a) := by
      rintro ⟨⟨b1, j1⟩, ⟨b2, j2⟩⟩ _
      have hst1 : (starts hn (suppOf (b1, j1))).card = a := by
        cases b1
        · exact card_starts_suppQ ha0 j1
        · simp only [suppOf, ↓reduceIte, starts_suppP ha0 j1, card_suppP ha0 j1]
      have hst2 : (starts hn (suppOf (b2, j2))).card = a := by
        cases b2
        · exact card_starts_suppQ ha0 j2
        · simp only [suppOf, ↓reduceIte, starts_suppP ha0 j2, card_suppP ha0 j2]
      have hc := card_hit_inter_ne hn (suppOf (b1, j1)) (suppOf (b2, j2)) hD1 hD2 hne
      rw [hst1, hst2] at hc
      have hcr : ((Finset.univ.filter (fun h => Hit hn (suppOf (b1, j1)) D1 h ∧
          Hit hn (suppOf (b2, j2)) D2 h)).card : ℝ) * (2 : ℝ) ^ (k * a + a) ≤
          (2 : ℝ) ^ (m * (2 * a + 1)) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using nat_mul_le_cast_real hc
      rw [div_le_div_iff₀ h2mn_pos (by positivity), one_mul]
      exact hcr
    have hcard_inter_r : ((cellD D1 ∩ cellD D2).card : ℝ) ≤
        ∑ pq ∈ idx, ((Finset.univ.filter (fun h => Hit hn (suppOf pq.1) D1 h ∧
          Hit hn (suppOf pq.2) D2 h)).card : ℝ) := by
      simpa only [Nat.cast_sum] using nat_le_cast_real
        (le_trans (Finset.card_le_card hsub_inter) Finset.card_biUnion_le)
    calc ((cellD D1 ∩ cellD D2).card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1))
        ≤ (∑ pq ∈ idx, ((Finset.univ.filter (fun h => Hit hn (suppOf pq.1) D1 h ∧
            Hit hn (suppOf pq.2) D2 h)).card : ℝ)) / (2 : ℝ) ^ (m * (2 * a + 1)) :=
          div_le_div_of_nonneg_right hcard_inter_r h2mn_pos.le
      _ = ∑ pq ∈ idx, ((Finset.univ.filter (fun h => Hit hn (suppOf pq.1) D1 h ∧
            Hit hn (suppOf pq.2) D2 h)).card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1)) := sum_div_real _ _ _
      _ ≤ ∑ _pq ∈ idx, (1 / (2 : ℝ) ^ (k * a + a)) := Finset.sum_le_sum hterm_le
      _ = (idx.card : ℝ) / (2 : ℝ) ^ (k * a + a) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ = 4 * (2 * (a : ℝ) + 1) ^ 2 / (2 : ℝ) ^ (k * a + a) := by
          simp only [idx, Finset.card_product, Finset.card_univ, Fintype.card_bool, Fintype.card_fin]
          push_cast; ring

  have h2a1_le_3a : (2 * (a : ℝ) + 1) ≤ 3 * (a : ℝ) := by
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 1 ≤ a by omega)
    linarith
  have hupper : (2 : ℝ) ^ (k * a) * ((evSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1) -
      2 * (1 - 1 / (2 : ℝ) ^ k) * (countD : ℝ) ≤
      (C_tail * (3 : ℝ) ^ (2 * m + 1) + (countD : ℝ)) * (a : ℝ) ^ (2 * m + 2) / (2 : ℝ) ^ a := by
    have h1 : evSet.card ≤ (∑ D ∈ Ds, (cellD D).card) + tailSet.card :=
      le_trans (Finset.card_le_card hev_sub)
        (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right Finset.card_biUnion_le _))
    have h2 : (2 : ℝ) ^ (k * a) * ((evSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1) ≤
        (∑ D ∈ Ds, (2 : ℝ) ^ (k * a) * ((cellD D).card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1)) / (2 * (a : ℝ) + 1)) +
        (2 : ℝ) ^ (k * a) * ((tailSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1) := by
      have hr : (evSet.card : ℝ) ≤ (∑ D ∈ Ds, ((cellD D).card : ℝ)) + (tailSet.card : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_sum] using nat_le_cast_real h1
      have hmul : (2 : ℝ) ^ (k * a) * ((evSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1) ≤
          (2 : ℝ) ^ (k * a) * (((∑ D ∈ Ds, ((cellD D).card : ℝ)) + (tailSet.card : ℝ)) /
            (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1) := by gcongr
      refine le_trans hmul (le_of_eq ?_)
      rw [add_div, mul_add, add_div, sum_div_real, Finset.mul_sum, sum_div_real]
      congr 1
      refine Finset.sum_congr rfl fun _ _ => by ring
    have hsum_hi : ∑ D ∈ Ds, (2 : ℝ) ^ (k * a) * ((cellD D).card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1)) / (2 * (a : ℝ) + 1) ≤
        2 * (1 - 1 / (2 : ℝ) ^ k) * (countD : ℝ) + (countD : ℝ) / (2 : ℝ) ^ a := by
      calc _ ≤ ∑ _D ∈ Ds, (2 * (1 - 1 / (2 : ℝ) ^ k) + 1 / (2 : ℝ) ^ a) :=
            Finset.sum_le_sum hcellD_hi
        _ = (countD : ℝ) * (2 * (1 - 1 / (2 : ℝ) ^ k) + 1 / (2 : ℝ) ^ a) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = _ := by ring
    have htail := tail_card_bound (n := 2 * a + 1) (m := m) (a := a) hn hkm le_rfl (by omega)
    have h2a1_pow : ((2 * a + 1 : ℕ) : ℝ) ^ (2 * m + 1) ≤ (3 : ℝ) ^ (2 * m + 1) * (a : ℝ) ^ (2 * m + 1) := by
      rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity); push_cast; linarith
    have htail_hi : (2 : ℝ) ^ (k * a) * ((tailSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1) ≤
        C_tail * (3 : ℝ) ^ (2 * m + 1) * (a : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ a := by
      have hge1 : (1 : ℝ) ≤ 2 * (a : ℝ) + 1 := by linarith
      calc _ ≤ (2 : ℝ) ^ (k * a) * ((tailSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1))) :=
            div_le_self (by positivity) hge1
        _ ≤ (2 : ℝ) ^ (k * a) * (C_tail * (((2 * a + 1 : ℕ) : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ (k * a + a))) :=
            mul_le_mul_of_nonneg_left htail h2ka_pos.le
        _ = C_tail * (((2 * a + 1 : ℕ) : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ a) := by
            rw [pow_add (2 : ℝ) (k * a) a]; field_simp
        _ ≤ C_tail * ((3 : ℝ) ^ (2 * m + 1) * (a : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ a) := by
            apply mul_le_mul_of_nonneg_left _ hC_tail_nn
            exact div_le_div_of_nonneg_right h2a1_pow (by positivity)
        _ = _ := by ring
    have ha_pow1 : (a : ℝ) ^ (2 * m + 1) ≤ (a : ℝ) ^ (2 * m + 2) := by
      have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 1 ≤ a by omega)
      calc (a : ℝ) ^ (2 * m + 1) = (a : ℝ) ^ (2 * m + 1) * 1 := (mul_one _).symm
        _ ≤ (a : ℝ) ^ (2 * m + 1) * (a : ℝ) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = (a : ℝ) ^ (2 * m + 2) := by rw [← pow_succ]
    have h1_le_pow : (1 : ℝ) ≤ (a : ℝ) ^ (2 * m + 2) :=
      one_le_pow₀ (by exact_mod_cast (show 1 ≤ a by omega))
    have hcomb : (countD : ℝ) / (2 : ℝ) ^ a +
        C_tail * (3 : ℝ) ^ (2 * m + 1) * (a : ℝ) ^ (2 * m + 1) / (2 : ℝ) ^ a ≤
        (C_tail * (3 : ℝ) ^ (2 * m + 1) + (countD : ℝ)) * (a : ℝ) ^ (2 * m + 2) / (2 : ℝ) ^ a := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 ≤ C_tail * (3 : ℝ) ^ (2 * m + 1) := by positivity
      nlinarith
    linarith
  have hlower : 2 * (1 - 1 / (2 : ℝ) ^ k) * (countD : ℝ) -
      (2 : ℝ) ^ (k * a) * ((evSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1) ≤
      ((countD : ℝ) * 2 + 4 * (countD : ℝ) ^ 2 * 9) * (a : ℝ) ^ (2 * m + 2) / (2 : ℝ) ^ a := by
    have hbonf := bonferroni_lower Ds cellD
    have hmain_le : mainSet.card ≤ evSet.card := Finset.card_le_card hmain_sub
    dsimp only [mainSet] at hmain_le
    have hnat : ∑ D ∈ Ds, (cellD D).card ≤
        evSet.card + ∑ D1 ∈ Ds, ∑ D2 ∈ Ds.filter (fun D => D ≠ D1), (cellD D1 ∩ cellD D2).card := by
      omega
    have hr : (∑ D ∈ Ds, (2 : ℝ) ^ (k * a) * ((cellD D).card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1)) / (2 * (a : ℝ) + 1)) ≤
        (2 : ℝ) ^ (k * a) * ((evSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1) +
        (2 : ℝ) ^ (k * a) * (∑ D1 ∈ Ds, ∑ D2 ∈ Ds.filter (fun D => D ≠ D1),
          ((cellD D1 ∩ cellD D2).card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1) := by
      have hcast : (∑ D ∈ Ds, ((cellD D).card : ℝ)) ≤
          (evSet.card : ℝ) + ∑ D1 ∈ Ds, ∑ D2 ∈ Ds.filter (fun D => D ≠ D1),
            ((cellD D1 ∩ cellD D2).card : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_sum] using nat_le_cast_real hnat
      have hsc : (2 : ℝ) ^ (k * a) * ((∑ D ∈ Ds, ((cellD D).card : ℝ)) / (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1) ≤
          (2 : ℝ) ^ (k * a) * (((evSet.card : ℝ) + ∑ D1 ∈ Ds, ∑ D2 ∈ Ds.filter (fun D => D ≠ D1),
            ((cellD D1 ∩ cellD D2).card : ℝ)) / (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1) := by
        gcongr
      have hlhs : (2 : ℝ) ^ (k * a) * ((∑ D ∈ Ds, ((cellD D).card : ℝ)) / (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1) =
          ∑ D ∈ Ds, (2 : ℝ) ^ (k * a) * ((cellD D).card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1)) / (2 * (a : ℝ) + 1) := by
        rw [sum_div_real, Finset.mul_sum, sum_div_real]
        refine Finset.sum_congr rfl fun _ _ => by ring
      have hrhs : (2 : ℝ) ^ (k * a) * (((evSet.card : ℝ) + ∑ D1 ∈ Ds, ∑ D2 ∈ Ds.filter (fun D => D ≠ D1),
            ((cellD D1 ∩ cellD D2).card : ℝ)) / (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1) =
          (2 : ℝ) ^ (k * a) * ((evSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1) +
          (2 : ℝ) ^ (k * a) * (∑ D1 ∈ Ds, ∑ D2 ∈ Ds.filter (fun D => D ≠ D1),
            ((cellD D1 ∩ cellD D2).card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1) := by
        rw [add_div, mul_add, add_div, sum_div_real]
        congr 2
        congr 1
        refine Finset.sum_congr rfl fun _ _ => sum_div_real _ _ _
      rwa [hlhs, hrhs] at hsc
    have hsum_lo : 2 * (1 - 1 / (2 : ℝ) ^ k) * (countD : ℝ) - (countD : ℝ) * 2 / (2 : ℝ) ^ a ≤
        ∑ D ∈ Ds, (2 : ℝ) ^ (k * a) * ((cellD D).card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1)) / (2 * (a : ℝ) + 1) := by
      calc _ = (countD : ℝ) * (2 * (1 - 1 / (2 : ℝ) ^ k) - 2 / (2 : ℝ) ^ a) := by ring
        _ = ∑ _D ∈ Ds, (2 * (1 - 1 / (2 : ℝ) ^ k) - 2 / (2 : ℝ) ^ a) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hcellD_lo
    have hover : (2 : ℝ) ^ (k * a) * (∑ D1 ∈ Ds, ∑ D2 ∈ Ds.filter (fun D => D ≠ D1),
          ((cellD D1 ∩ cellD D2).card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1) ≤
        4 * (countD : ℝ) ^ 2 * (2 * (a : ℝ) + 1) / (2 : ℝ) ^ a := by
      have hsum_ov : ∑ D1 ∈ Ds, ∑ D2 ∈ Ds.filter (fun D => D ≠ D1),
          ((cellD D1 ∩ cellD D2).card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1)) ≤
          (countD : ℝ) ^ 2 * (4 * (2 * (a : ℝ) + 1) ^ 2 / (2 : ℝ) ^ (k * a + a)) := by
        calc _ ≤ ∑ D1 ∈ Ds, ∑ _D2 ∈ Ds.filter (fun D => D ≠ D1),
              (4 * (2 * (a : ℝ) + 1) ^ 2 / (2 : ℝ) ^ (k * a + a)) :=
              Finset.sum_le_sum fun D1 h1 => Finset.sum_le_sum fun D2 h2 => hcellD_inter D1 h1 D2 h2
          _ ≤ ∑ _D1 ∈ Ds, ∑ _D2 ∈ Ds, (4 * (2 * (a : ℝ) + 1) ^ 2 / (2 : ℝ) ^ (k * a + a)) :=
              Finset.sum_le_sum fun _ _ => Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
          _ = (countD : ℝ) ^ 2 * (4 * (2 * (a : ℝ) + 1) ^ 2 / (2 : ℝ) ^ (k * a + a)) := by
              simp only [Finset.sum_const, nsmul_eq_mul, countD]; ring
      calc _ ≤ (2 : ℝ) ^ (k * a) * ((countD : ℝ) ^ 2 * (4 * (2 * (a : ℝ) + 1) ^ 2 / (2 : ℝ) ^ (k * a + a))) /
              (2 * (a : ℝ) + 1) := by gcongr
        _ = 4 * (countD : ℝ) ^ 2 * (2 * (a : ℝ) + 1) / (2 : ℝ) ^ a := by
              rw [pow_add]; field_simp
    have h1_le_pow : (1 : ℝ) ≤ (a : ℝ) ^ (2 * m + 2) :=
      one_le_pow₀ (by exact_mod_cast (show 1 ≤ a by omega))
    have ha_le_pow : (a : ℝ) ≤ (a : ℝ) ^ (2 * m + 2) := by
      have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 1 ≤ a by omega)
      calc (a : ℝ) = (a : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (a : ℝ) ^ (2 * m + 2) := pow_le_pow_right₀ ha1 (by omega)
    have hcomb : (countD : ℝ) * 2 / (2 : ℝ) ^ a +
        4 * (countD : ℝ) ^ 2 * (2 * (a : ℝ) + 1) / (2 : ℝ) ^ a ≤
        ((countD : ℝ) * 2 + 4 * (countD : ℝ) ^ 2 * 9) * (a : ℝ) ^ (2 * m + 2) / (2 : ℝ) ^ a := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 2 * (a : ℝ) + 1 ≤ 9 * (a : ℝ) ^ (2 * m + 2) := by linarith
      have hnn : 0 ≤ 4 * (countD : ℝ) ^ 2 := by positivity
      nlinarith
    linarith
  have hmain_bound : |(2 : ℝ) ^ (k * a) * ((evSet.card : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1) -
      2 * (1 - 1 / (2 : ℝ) ^ k) * (countD : ℝ)| ≤
      C_odd * (a : ℝ) ^ (2 * m + 2) / (2 : ℝ) ^ a := by
    rw [abs_le]
    constructor
    · have : ((countD : ℝ) * 2 + 4 * (countD : ℝ) ^ 2 * 9) * (a : ℝ) ^ (2 * m + 2) / (2 : ℝ) ^ a ≤
          C_odd * (a : ℝ) ^ (2 * m + 2) / (2 : ℝ) ^ a := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : (countD : ℝ) * 2 + 4 * (countD : ℝ) ^ 2 * 9 ≤ C_odd := by
          dsimp only [C_odd]; linarith [mul_nonneg hC_tail_nn (pow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) (2 * m + 1))]
        nlinarith [pow_nonneg (show (0 : ℝ) ≤ (a : ℝ) by positivity) (2 * m + 2)]
      linarith
    · have : (C_tail * (3 : ℝ) ^ (2 * m + 1) + (countD : ℝ)) * (a : ℝ) ^ (2 * m + 2) / (2 : ℝ) ^ a ≤
          C_odd * (a : ℝ) ^ (2 * m + 2) / (2 : ℝ) ^ a := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : C_tail * (3 : ℝ) ^ (2 * m + 1) + (countD : ℝ) ≤ C_odd := by
          dsimp only [C_odd]
          have h1 : (0 : ℝ) ≤ (countD : ℝ) := by positivity
          have h2 : (0 : ℝ) ≤ 4 * (countD : ℝ) ^ 2 * 9 := by positivity
          linarith
        nlinarith [pow_nonneg (show (0 : ℝ) ≤ (a : ℝ) by positivity) (2 * m + 2)]
      linarith
  refine abs_sub_le_of_eq ?_ ?_ hmain_bound
  · exact congrArg (fun c : ℕ => (2 : ℝ) ^ (k * a) * ((c : ℝ) / (2 : ℝ) ^ (m * (2 * a + 1))) / (2 * (a : ℝ) + 1))
      (card_filter_eq (fun _ => Iff.rfl))
  · exact congrArg (fun c : ℕ => 2 * (1 - 1 / (2 : ℝ) ^ k) * (c : ℝ))
      (card_filter_eq (fun _ => Iff.rfl))

theorem main_proof : ∀ (m k : ℕ), 1 ≤ k → k ≤ m →
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let A := Fin m → F
  letI : Fintype (Submodule F A) := Fintype.ofFinite _
  let countD := ((Finset.univ : Finset (Submodule F A)).filter
    (fun D : Submodule F A => Module.finrank F D + k = m)).card
  let prob := fun (n a : ℕ) (hn : 0 < n) =>
    let next := fun i : Fin n => (⟨(i.val+1) % n, Nat.mod_lt _ hn⟩ : Fin n)
    let event := fun h : Fin n → A =>
      ∃ U : Submodule F (Fin n → F), a+k ≤ Module.finrank F U + m ∧
        (∀ x ∈ U, ∀ b : Fin m, (∑ i, h i b * x i) = 0) ∧
        (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
    (((Finset.univ : Finset (Fin n → A)).filter event).card : ℝ) / (2:ℝ)^(m*n)
  (Filter.Tendsto (fun t : ℕ => let a := t+2
       (2:ℝ)^(k*a) * prob (2*a) a (Nat.mul_pos (Nat.succ_pos 1) (Nat.succ_pos (t+1))))
     Filter.atTop (nhds (2*(countD:ℝ)))) ∧
  (Filter.Tendsto (fun t : ℕ => let a := t+2
       (2:ℝ)^(k*a) * prob (2*a+1) a (Nat.succ_pos (2*a)) / (2*(a:ℝ)+1))
     Filter.atTop (nhds (2*(1-1/(2:ℝ)^k)*(countD:ℝ)))) :=
  fun m k hk hkm => ⟨main_proof_even m k hk hkm, main_proof_odd m k hk hkm⟩

end PEqualNP.Outside.L_lib_866

theorem PEqualNP.Outside.L_lib_866 : (∀ (m k : ℕ), 1 ≤ k → k ≤ m →
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let A := Fin m → F
  letI : Fintype (Submodule F A) := Fintype.ofFinite _
  let countD := ((Finset.univ : Finset (Submodule F A)).filter
    (fun D : Submodule F A => Module.finrank F D + k = m)).card
  let prob := fun (n a : ℕ) (hn : 0 < n) =>
    let next := fun i : Fin n => (⟨(i.val+1) % n, Nat.mod_lt _ hn⟩ : Fin n)
    let event := fun h : Fin n → A =>
      ∃ U : Submodule F (Fin n → F), a+k ≤ Module.finrank F U + m ∧
        (∀ x ∈ U, ∀ b : Fin m, (∑ i, h i b * x i) = 0) ∧
        (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
    (((Finset.univ : Finset (Fin n → A)).filter event).card : ℝ) / (2:ℝ)^(m*n)
  (Filter.Tendsto (fun t : ℕ => let a := t+2
       (2:ℝ)^(k*a) * prob (2*a) a (Nat.mul_pos (Nat.succ_pos 1) (Nat.succ_pos (t+1))))
     Filter.atTop (nhds (2*(countD:ℝ)))) ∧
  (Filter.Tendsto (fun t : ℕ => let a := t+2
       (2:ℝ)^(k*a) * prob (2*a+1) a (Nat.succ_pos (2*a)) / (2*(a:ℝ)+1))
     Filter.atTop (nhds (2*(1-1/(2:ℝ)^k)*(countD:ℝ))))) :=
  PEqualNP.Outside.L_lib_866.main_proof

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1173_aux

open scoped BigOperators Classical

lemma getElem?_finRange_lt {k m : ℕ} (h : m < k) :
    (List.finRange k)[m]? = some ⟨m, h⟩ := by
  rw [List.getElem?_eq_getElem (by simp [h]), List.getElem_finRange]
  rfl

/-! ### Part A: Basic definitions and single-block polarization bound -/

def satBlock {n : ℕ} (x : Finset (Fin n)) (σ : Fin n → Fin n → Bool × Bool) : Prop :=
  ∀ u v : Fin n, u < v → (decide (u ∈ x), decide (v ∈ x)) ≠ σ u v

def satWord {n r : ℕ} (x : Fin r → Finset (Fin n)) (s : Fin r → Fin n → Fin n → Bool × Bool) : Prop :=
  ∀ j : Fin r, satBlock (x j) (s j)

noncomputable def replyOf {n r : ℕ} (A : Finset (Fin r → Finset (Fin n)))
    (s : Fin r → Fin n → Fin n → Bool × Bool) : Bool :=
  A.toList.any (fun x =>
    (Finset.univ : Finset (Fin r)).toList.all (fun j =>
      (Finset.univ : Finset (Fin n)).toList.all (fun u =>
        (Finset.univ : Finset (Fin n)).toList.all (fun v =>
          !(decide (u < v)) || ((decide (u ∈ x j), decide (v ∈ x j)) != s j u v)))))

lemma replyOf_eq_true_iff {n r : ℕ} (A : Finset (Fin r → Finset (Fin n)))
    (s : Fin r → Fin n → Fin n → Bool × Bool) :
    replyOf A s = true ↔ ∃ x ∈ A, satWord x s := by
  simp only [replyOf, satWord, satBlock, List.any_eq_true, List.all_eq_true,
    Finset.mem_toList, Finset.mem_univ, forall_true_left, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, bne_iff_ne]
  refine exists_congr fun x => and_congr_right fun _ => ?_
  refine forall_congr' fun j => forall_congr' fun u => forall_congr' fun v => ?_
  tauto

lemma polarization_bound_aux {n : ℕ} : ∀ (k : ℕ) (V : Finset (Fin n))
    (S : Finset (Finset (Fin n))),
    V.card ≤ k →
    (∀ x ∈ S, ∀ y ∈ S, (∀ u ∈ V, u ∈ x ↔ u ∈ y) → x = y) →
    (∀ u ∈ V, ∀ v ∈ V, u ≠ v → ∃ a b : Bool, ∀ x ∈ S, (decide (u ∈ x), decide (v ∈ x)) ≠ (a, b)) →
    S.card ≤ V.card + 1 := by
  classical
  intro k
  induction k with
  | zero =>
    intro V S hV hdet _
    have hV0 : V = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hV0] at hdet ⊢
    by_cases hS : S.Nonempty
    · rcases hS with ⟨x₀, hx₀⟩
      have hsub : S ⊆ {x₀} := by
        intro x hx
        rw [Finset.mem_singleton]
        exact hdet x hx x₀ hx₀ (fun _ hu => absurd hu (Finset.notMem_empty _))
      calc S.card ≤ ({x₀} : Finset _).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton x₀
        _ = (∅ : Finset (Fin n)).card + 1 := by simp
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS]; simp
  | succ k ih =>
    intro V S hV hdet hmiss
    by_cases hVne : V.Nonempty
    · rcases hVne with ⟨w, hw⟩
      let V' := V.erase w
      have hV'card : V'.card = V.card - 1 := Finset.card_erase_of_mem hw
      let S₀ := S.filter (fun x => w ∉ x)
      let S₁ := S.filter (fun x => w ∈ x)
      have hScard : S.card = S₀.card + S₁.card := by
        have hdisj : Disjoint S₀ S₁ := by
          rw [Finset.disjoint_left]; intro x h0 h1
          exact (Finset.mem_filter.mp h0).2 (Finset.mem_filter.mp h1).2
        have hun : S = S₀ ∪ S₁ := by
          ext x; by_cases hx : w ∈ x <;> simp [S₀, S₁, hx]
        rw [hun, Finset.card_union_of_disjoint hdisj]
      -- For each u in V', pick a missed pair (a_u, b_u) on (u, w)
      have hpair : ∀ u : Fin n, u ∈ V' → ∃ p : Bool × Bool,
          ∀ x ∈ S, (decide (u ∈ x), decide (w ∈ x)) ≠ p := by
        intro u hu
        have huV : u ∈ V := (Finset.mem_erase.mp hu).2
        have hne : u ≠ w := (Finset.mem_erase.mp hu).1
        rcases hmiss u huV w hw hne with ⟨a, b, hab⟩
        exact ⟨(a, b), hab⟩
      let pick : Fin n → Bool × Bool := fun u =>
        if hu : u ∈ V' then Classical.choose (hpair u hu) else (false, false)
      have hpick : ∀ u ∈ V', ∀ x ∈ S, (decide (u ∈ x), decide (w ∈ x)) ≠ pick u := by
        intro u hu
        dsimp only [pick]
        rw [dif_pos hu]
        exact Classical.choose_spec (hpair u hu)
      let I₀ := V'.filter (fun u => (pick u).2 = false)
      let I₁ := V'.filter (fun u => (pick u).2 = true)
      have hI_card : I₀.card + I₁.card = V'.card := by
        have hdisj : Disjoint I₀ I₁ := by
          rw [Finset.disjoint_left]; intro u h0 h1
          have hb0 := (Finset.mem_filter.mp h0).2
          have hb1 := (Finset.mem_filter.mp h1).2
          rw [hb0] at hb1; exact Bool.false_ne_true hb1
        have hun : I₀ ∪ I₁ = V' := by
          ext u; cases h : (pick u).2 <;> simp [I₀, I₁, h]
        rw [← Finset.card_union_of_disjoint hdisj, hun]
      have hS₀_le : S₀.card ≤ I₁.card + 1 := by
        apply ih I₁ S₀ (by have := Finset.card_le_card (Finset.filter_subset (fun u => (pick u).2 = true) V'); omega)
        · intro x hx y hy hag
          have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
          have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
          have hxw : w ∉ x := (Finset.mem_filter.mp hx).2
          have hyw : w ∉ y := (Finset.mem_filter.mp hy).2
          apply hdet x hxS y hyS
          intro u huV
          by_cases huw : u = w
          · subst huw; simp [hxw, hyw]
          · have huV' : u ∈ V' := Finset.mem_erase.mpr ⟨huw, huV⟩
            cases hb : (pick u).2
            · have hpx := hpick u huV' x hxS
              have hpy := hpick u huV' y hyS
              have hwx : decide (w ∈ x) = false := by simp [hxw]
              have hwy : decide (w ∈ y) = false := by simp [hyw]
              have hneqx : decide (u ∈ x) ≠ (pick u).1 := by
                intro heq; apply hpx; exact Prod.ext heq (by rw [hwx, hb])
              have hneqy : decide (u ∈ y) ≠ (pick u).1 := by
                intro heq; apply hpy; exact Prod.ext heq (by rw [hwy, hb])
              have heq_dec : decide (u ∈ x) = decide (u ∈ y) := by
                generalize decide (u ∈ x) = a at hneqx ⊢
                generalize decide (u ∈ y) = b at hneqy ⊢
                generalize (pick u).1 = p at hneqx hneqy
                cases a <;> cases b <;> cases p <;> first | rfl | exact absurd rfl hneqx | exact absurd rfl hneqy
              exact decide_eq_decide.mp heq_dec
            · exact hag u (Finset.mem_filter.mpr ⟨huV', hb⟩)
        · intro u hu v hv hne
          rcases hmiss u (Finset.mem_erase.mp (Finset.mem_filter.mp hu).1).2
            v (Finset.mem_erase.mp (Finset.mem_filter.mp hv).1).2 hne with ⟨a, b, hab⟩
          exact ⟨a, b, fun x hx => hab x (Finset.mem_filter.mp hx).1⟩
      have hS₁_le : S₁.card ≤ I₀.card + 1 := by
        apply ih I₀ S₁ (by have := Finset.card_le_card (Finset.filter_subset (fun u => (pick u).2 = false) V'); omega)
        · intro x hx y hy hag
          have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
          have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
          have hxw : w ∈ x := (Finset.mem_filter.mp hx).2
          have hyw : w ∈ y := (Finset.mem_filter.mp hy).2
          apply hdet x hxS y hyS
          intro u huV
          by_cases huw : u = w
          · subst huw; simp [hxw, hyw]
          · have huV' : u ∈ V' := Finset.mem_erase.mpr ⟨huw, huV⟩
            cases hb : (pick u).2
            · exact hag u (Finset.mem_filter.mpr ⟨huV', hb⟩)
            · have hpx := hpick u huV' x hxS
              have hpy := hpick u huV' y hyS
              have hwx : decide (w ∈ x) = true := by simp [hxw]
              have hwy : decide (w ∈ y) = true := by simp [hyw]
              have hneqx : decide (u ∈ x) ≠ (pick u).1 := by
                intro heq; apply hpx; exact Prod.ext heq (by rw [hwx, hb])
              have hneqy : decide (u ∈ y) ≠ (pick u).1 := by
                intro heq; apply hpy; exact Prod.ext heq (by rw [hwy, hb])
              have heq_dec : decide (u ∈ x) = decide (u ∈ y) := by
                generalize decide (u ∈ x) = a at hneqx ⊢
                generalize decide (u ∈ y) = b at hneqy ⊢
                generalize (pick u).1 = p at hneqx hneqy
                cases a <;> cases b <;> cases p <;> first | rfl | exact absurd rfl hneqx | exact absurd rfl hneqy
              exact decide_eq_decide.mp heq_dec
        · intro u hu v hv hne
          rcases hmiss u (Finset.mem_erase.mp (Finset.mem_filter.mp hu).1).2
            v (Finset.mem_erase.mp (Finset.mem_filter.mp hv).1).2 hne with ⟨a, b, hab⟩
          exact ⟨a, b, fun x hx => hab x (Finset.mem_filter.mp hx).1⟩
      have hVpos : 1 ≤ V.card := Finset.card_pos.mpr ⟨w, hw⟩
      omega
    · have hV0 : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hVne
      rw [hV0] at hdet ⊢
      by_cases hS : S.Nonempty
      · rcases hS with ⟨x₀, hx₀⟩
        have hsub : S ⊆ {x₀} := by
          intro x hx
          rw [Finset.mem_singleton]
          exact hdet x hx x₀ hx₀ (fun _ hu => absurd hu (Finset.notMem_empty _))
        calc S.card ≤ ({x₀} : Finset _).card := Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton x₀
          _ = (∅ : Finset (Fin n)).card + 1 := by simp
      · rw [Finset.not_nonempty_iff_eq_empty.mp hS]; simp

lemma card_satBlock_le {n : ℕ} (σ : Fin n → Fin n → Bool × Bool) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => satBlock x σ)).card ≤ n + 1 := by
  classical
  have h := polarization_bound_aux n (Finset.univ : Finset (Fin n))
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => satBlock x σ))
    (by simp)
    (fun x _ y _ hag => by ext u; exact hag u (Finset.mem_univ u))
    (fun u _ v _ hne => by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · refine ⟨(σ u v).1, (σ u v).2, fun x hx => ?_⟩
        exact (Finset.mem_filter.mp hx).2 u v hlt
      · refine ⟨(σ v u).2, (σ v u).1, fun x hx hEq => ?_⟩
        have h1 := (Finset.mem_filter.mp hx).2 v u hgt
        apply h1
        exact Prod.ext (congrArg Prod.snd hEq) (congrArg Prod.fst hEq))
  simpa using h

lemma card_satWord_le {n r : ℕ} (s : Fin r → Fin n → Fin n → Bool × Bool) :
    ((Finset.univ : Finset (Fin r → Finset (Fin n))).filter (fun x => satWord x s)).card ≤
    (n + 1) ^ r := by
  classical
  have heq : (Finset.univ : Finset (Fin r → Finset (Fin n))).filter (fun x => satWord x s) =
      Fintype.piFinset (fun j => (Finset.univ : Finset (Finset (Fin n))).filter (fun y => satBlock y (s j))) := by
    ext x
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    simp [satWord]
  rw [heq, Fintype.card_piFinset]
  calc (Finset.univ : Finset (Fin r)).prod
        (fun j => ((Finset.univ : Finset (Finset (Fin n))).filter (fun y => satBlock y (s j))).card)
      ≤ (Finset.univ : Finset (Fin r)).prod (fun _ => n + 1) :=
        Finset.prod_le_prod' fun j _ => card_satBlock_le (s j)
    _ = (n + 1) ^ r := by simp

/-! ### Part B: Hamming-ball signing and Hamming code tiling -/

def ballSigning {n : ℕ} (c : Finset (Fin n)) : Fin n → Fin n → Bool × Bool :=
  fun u v => (!(decide (u ∈ c)), !(decide (v ∈ c)))

lemma satBlock_ballSigning_of_eq {n : ℕ} (c : Finset (Fin n)) :
    satBlock c (ballSigning c) := by
  intro u v _ h
  have h1 := congrArg Prod.fst h
  dsimp only [ballSigning] at h1
  cases hb : decide (u ∈ c) <;> simp [hb] at h1

lemma satBlock_ballSigning_of_flip {n : ℕ} (c : Finset (Fin n)) (u₀ : Fin n) :
    satBlock (symmDiff c {u₀}) (ballSigning c) := by
  intro u v huv h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  dsimp only [ballSigning] at h1 h2
  have hu : u = u₀ := by
    by_contra hne
    have hm : u ∈ symmDiff c {u₀} ↔ u ∈ c := by
      simp [Finset.mem_symmDiff, hne]
    by_cases huc : u ∈ c <;> simp [huc, hm] at h1
  have hv : v = u₀ := by
    by_contra hne
    have hm : v ∈ symmDiff c {u₀} ↔ v ∈ c := by
      simp [Finset.mem_symmDiff, hne]
    by_cases hvc : v ∈ c <;> simp [hvc, hm] at h2
  rw [hu, hv] at huv
  exact lt_irrefl _ huv

lemma satBlock_ballSigning_iff {n : ℕ} (c x : Finset (Fin n)) :
    satBlock x (ballSigning c) ↔ x = c ∨ ∃ u₀ : Fin n, x = symmDiff c {u₀} := by
  constructor
  · intro hsat
    let diff := symmDiff x c
    by_cases h0 : diff.card = 0
    · left
      have hd0 : symmDiff x c = ∅ := Finset.card_eq_zero.mp h0
      exact symmDiff_eq_bot.mp hd0
    · right
      have hne : diff.Nonempty := Finset.card_pos.mp (by omega)
      rcases hne with ⟨u₀, hu₀⟩
      refine ⟨u₀, ?_⟩
      ext u
      by_cases hu : u = u₀
      · subst hu
        dsimp only [diff] at hu₀
        simp only [Finset.mem_symmDiff, Finset.mem_singleton] at hu₀ ⊢
        tauto
      · have hnotd : u ∉ diff := by
          intro huD
          have hpair : ∀ a b : Fin n, a < b → a ∈ diff → b ∈ diff → False := by
            intro a b hab ha hb
            apply hsat a b hab
            dsimp only [ballSigning]
            simp only [diff, Finset.mem_symmDiff] at ha hb
            apply Prod.ext
            · by_cases hax : a ∈ x <;> by_cases hac : a ∈ c <;> simp_all
            · by_cases hbx : b ∈ x <;> by_cases hbc : b ∈ c <;> simp_all
          rcases lt_or_gt_of_ne hu with hlt | hgt
          · exact hpair u u₀ hlt huD hu₀
          · exact hpair u₀ u hgt hu₀ huD
        simp only [diff, Finset.mem_symmDiff, Finset.mem_singleton] at hnotd ⊢
        tauto
  · rintro (rfl | ⟨u₀, rfl⟩)
    · exact satBlock_ballSigning_of_eq x
    · exact satBlock_ballSigning_of_flip c u₀

lemma card_ball {n : ℕ} (c : Finset (Fin n)) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => satBlock x (ballSigning c))).card =
    n + 1 := by
  classical
  let f : Option (Fin n) → Finset (Fin n) := fun o =>
    match o with
    | none => c
    | some u₀ => symmDiff c {u₀}
  have hbij : ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => satBlock x (ballSigning c))).card =
      (Finset.univ : Finset (Option (Fin n))).card := by
    refine (Finset.card_bij (fun o _ => f o) ?_ ?_ ?_).symm
    · intro o _
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      cases o with
      | none => exact satBlock_ballSigning_of_eq c
      | some u₀ => exact satBlock_ballSigning_of_flip c u₀
    · intro o₁ _ o₂ _ hEq
      cases o₁ with
      | none =>
        cases o₂ with
        | none => rfl
        | some u₂ =>
          exfalso
          have hmem := Finset.ext_iff.mp hEq u₂
          simp [f, Finset.mem_symmDiff] at hmem
      | some u₁ =>
        cases o₂ with
        | none =>
          exfalso
          have hmem := Finset.ext_iff.mp hEq u₁
          simp [f, Finset.mem_symmDiff] at hmem
        | some u₂ =>
          congr 1
          by_contra hne
          have hmem := Finset.ext_iff.mp hEq u₁
          simp [f, Finset.mem_symmDiff, hne] at hmem
    · intro x hx
      rcases (satBlock_ballSigning_iff c x).mp (Finset.mem_filter.mp hx).2 with rfl | ⟨u₀, rfl⟩
      · exact ⟨none, Finset.mem_univ _, rfl⟩
      · exact ⟨some u₀, Finset.mem_univ _, rfl⟩
  rw [hbij]
  simp

def synBit {t : ℕ} (x : Finset (Fin (2 ^ t - 1))) (b : Fin t) : Bool :=
  decide ((x.filter (fun u => (u.val + 1).testBit b.val)).card % 2 = 1)

def synVal {t : ℕ} (x : Finset (Fin (2 ^ t - 1))) : ℕ :=
  (Finset.univ : Finset (Fin t)).sum (fun b => (synBit x b).toNat * 2 ^ b.val)

def hammingCode (t : ℕ) : Finset (Finset (Fin (2 ^ t - 1))) :=
  (Finset.univ : Finset (Finset (Fin (2 ^ t - 1)))).filter (fun c => ∀ b : Fin t, synBit c b = false)

lemma synBit_symmDiff_singleton {t : ℕ} (x : Finset (Fin (2 ^ t - 1)))
    (u₀ : Fin (2 ^ t - 1)) (b : Fin t) :
    synBit (symmDiff x {u₀}) b = (synBit x b != (u₀.val + 1).testBit b.val) := by
  classical
  dsimp only [synBit]
  by_cases hbit : (u₀.val + 1).testBit b.val = true
  · by_cases hu : u₀ ∈ x
    · have heq : (symmDiff x {u₀}).filter (fun u => (u.val + 1).testBit b.val) =
          (x.filter (fun u => (u.val + 1).testBit b.val)).erase u₀ := by
        ext u
        by_cases hu0 : u = u₀
        · subst hu0; simp [Finset.mem_symmDiff, hu]
        · simp [Finset.mem_symmDiff, hu0]
      have hmem : u₀ ∈ x.filter (fun u => (u.val + 1).testBit b.val) :=
        Finset.mem_filter.mpr ⟨hu, hbit⟩
      have hpos : 0 < (x.filter (fun u => (u.val + 1).testBit b.val)).card :=
        Finset.card_pos.mpr ⟨u₀, hmem⟩
      rw [heq, Finset.card_erase_of_mem hmem, hbit]
      by_cases hp : (x.filter (fun u => (u.val + 1).testBit b.val)).card % 2 = 1
      · simp [hp]; omega
      · simp [hp]; omega
    · have heq : (symmDiff x {u₀}).filter (fun u => (u.val + 1).testBit b.val) =
          insert u₀ (x.filter (fun u => (u.val + 1).testBit b.val)) := by
        ext u
        by_cases hu0 : u = u₀
        · subst hu0; simp [Finset.mem_symmDiff, hu, hbit]
        · simp [Finset.mem_symmDiff, hu0]
      have hnot : u₀ ∉ x.filter (fun u => (u.val + 1).testBit b.val) := by simp [hu]
      rw [heq, Finset.card_insert_of_notMem hnot, hbit]
      by_cases hp : (x.filter (fun u => (u.val + 1).testBit b.val)).card % 2 = 1
      · simp [hp]; omega
      · simp [hp]; omega
  · have hbf : (u₀.val + 1).testBit b.val = false := Bool.eq_false_iff.mpr hbit
    have heq : (symmDiff x {u₀}).filter (fun u => (u.val + 1).testBit b.val) =
        x.filter (fun u => (u.val + 1).testBit b.val) := by
      ext u
      by_cases hu0 : u = u₀
      · subst hu0; simp [hbf]
      · simp [Finset.mem_symmDiff, hu0]
    rw [heq, hbf, Bool.bne_false]

lemma sum_bits_lt_two_pow : ∀ (t : ℕ) (f : Fin t → Bool),
    (Finset.univ : Finset (Fin t)).sum (fun b => (f b).toNat * 2 ^ b.val) < 2 ^ t := by
  intro t
  induction t with
  | zero => intro f; simp
  | succ t ih =>
    intro f
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    have h1 := ih (fun b : Fin t => f b.castSucc)
    have hlast : (f (Fin.last t)).toNat * 2 ^ t ≤ 2 ^ t := by
      cases f (Fin.last t) <;> simp
    rw [pow_succ]
    omega

lemma testBit_sum_bits : ∀ (t : ℕ) (f : Fin t → Bool) (i : Fin t),
    ((Finset.univ : Finset (Fin t)).sum (fun b => (f b).toNat * 2 ^ b.val)).testBit i.val = f i := by
  intro t
  induction t with
  | zero => intro _ i; exact Fin.elim0 i
  | succ t ih =>
    intro f i
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    set lo := (Finset.univ : Finset (Fin t)).sum (fun b => (f b.castSucc).toNat * 2 ^ b.val)
    have hlo : lo < 2 ^ t := sum_bits_lt_two_pow t (fun b => f b.castSucc)
    by_cases hilt : i.val < t
    · let i' : Fin t := ⟨i.val, hilt⟩
      have hi_eq : i = i'.castSucc := Fin.ext rfl
      rw [hi_eq, Fin.coe_castSucc]
      have hdiv : (lo + (f (Fin.last t)).toNat * 2 ^ t) / 2 ^ i'.val =
          lo / 2 ^ i'.val + (f (Fin.last t)).toNat * 2 ^ (t - i'.val) := by
        have hpow : 2 ^ t = 2 ^ (t - i'.val) * 2 ^ i'.val := by
          rw [← pow_add]; congr 1; omega
        rw [hpow, ← mul_assoc, Nat.add_mul_div_right _ _ (by positivity)]
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
      have hmod2 : (lo / 2 ^ i'.val + (f (Fin.last t)).toNat * 2 ^ (t - i'.val)) % 2 =
          (lo / 2 ^ i'.val) % 2 := by
        have h2dvd : 2 ∣ 2 ^ (t - i'.val) := dvd_pow_self 2 (by omega)
        rcases h2dvd with ⟨q, hq⟩
        rw [hq, ← mul_assoc, mul_comm _ 2, mul_assoc, Nat.add_mul_mod_self_left]
      rw [Nat.one_and_eq_mod_two, hmod2, ← Nat.one_and_eq_mod_two, ← Nat.shiftRight_eq_div_pow]
      exact ih (fun b => f b.castSucc) i'
    · have hit : i = Fin.last t := Fin.ext (by simp only [Fin.val_last]; omega)
      rw [hit, Fin.val_last, Nat.testBit, Nat.shiftRight_eq_div_pow]
      have hdiv : (lo + (f (Fin.last t)).toNat * 2 ^ t) / 2 ^ t = (f (Fin.last t)).toNat := by
        rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlo, zero_add]
      rw [hdiv]
      cases f (Fin.last t) <;> rfl

lemma eq_of_testBit_eq_lt {t a b : ℕ} (ha : a < 2 ^ t) (hb : b < 2 ^ t)
    (h : ∀ i : Fin t, a.testBit i.val = b.testBit i.val) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < t
  · exact h ⟨k, hk⟩
  · have hle : 2 ^ t ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hle),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hle)]

lemma hammingCode_cover {t : ℕ} (x : Finset (Fin (2 ^ t - 1))) :
    ∃ c ∈ hammingCode t, satBlock x (ballSigning c) := by
  classical
  by_cases hv : synVal x = 0
  · refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun b => ?_⟩, satBlock_ballSigning_of_eq x⟩
    have htb := testBit_sum_bits t (synBit x) b
    change (synVal x).testBit b.val = synBit x b at htb
    rw [hv, Nat.zero_testBit] at htb
    exact htb.symm
  · have hlt : synVal x < 2 ^ t := sum_bits_lt_two_pow t (synBit x)
    let u₀ : Fin (2 ^ t - 1) := ⟨synVal x - 1, by omega⟩
    let c := symmDiff x {u₀}
    have hc : c ∈ hammingCode t := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun b => ?_⟩
      rw [synBit_symmDiff_singleton]
      have huval : u₀.val + 1 = synVal x := by dsimp only [u₀]; omega
      rw [huval]
      have htb := testBit_sum_bits t (synBit x) b
      change (synVal x).testBit b.val = synBit x b at htb
      rw [htb, bne_self_eq_false]
    have hx_eq : x = symmDiff c {u₀} := by
      dsimp only [c]
      rw [symmDiff_symmDiff_cancel_right]
    refine ⟨c, hc, ?_⟩
    rw [hx_eq]
    exact satBlock_ballSigning_of_flip c u₀

lemma hammingCode_disjoint {t : ℕ} {c₁ c₂ : Finset (Fin (2 ^ t - 1))}
    (h1 : c₁ ∈ hammingCode t) (h2 : c₂ ∈ hammingCode t) (hne : c₁ ≠ c₂)
    (x : Finset (Fin (2 ^ t - 1))) :
    ¬ (satBlock x (ballSigning c₁) ∧ satBlock x (ballSigning c₂)) := by
  rintro ⟨hs1, hs2⟩
  have hc1 : ∀ b : Fin t, synBit c₁ b = false := (Finset.mem_filter.mp h1).2
  have hc2 : ∀ b : Fin t, synBit c₂ b = false := (Finset.mem_filter.mp h2).2
  rcases (satBlock_ballSigning_iff c₁ x).mp hs1 with rfl | ⟨u₁, rfl⟩
  · rcases (satBlock_ballSigning_iff c₂ x).mp hs2 with heq | ⟨u₂, heq⟩
    · exact hne heq
    · have h0 : ∀ b : Fin t, (u₂.val + 1).testBit b.val = (0 : ℕ).testBit b.val := by
        intro b
        have hb := congrArg (fun s => synBit s b) heq
        rw [hc1 b, synBit_symmDiff_singleton, hc2 b, Bool.false_bne] at hb
        rw [← hb, Nat.zero_testBit]
      have hu0 : u₂.val + 1 = 0 := eq_of_testBit_eq_lt (by omega) (by positivity) h0
      omega
  · rcases (satBlock_ballSigning_iff c₂ (symmDiff c₁ {u₁})).mp hs2 with heq | ⟨u₂, heq⟩
    · have h0 : ∀ b : Fin t, (u₁.val + 1).testBit b.val = (0 : ℕ).testBit b.val := by
        intro b
        have hb := congrArg (fun s => synBit s b) heq
        rw [synBit_symmDiff_singleton, hc1 b, Bool.false_bne, hc2 b] at hb
        rw [hb, Nat.zero_testBit]
      have hu0 : u₁.val + 1 = 0 := eq_of_testBit_eq_lt (by omega) (by positivity) h0
      omega
    · have hbit : ∀ b : Fin t, (u₁.val + 1).testBit b.val = (u₂.val + 1).testBit b.val := by
        intro b
        have hb := congrArg (fun s => synBit s b) heq
        rw [synBit_symmDiff_singleton, synBit_symmDiff_singleton, hc1 b, hc2 b,
            Bool.false_bne, Bool.false_bne] at hb
        exact hb
      have hueq : u₁.val + 1 = u₂.val + 1 := eq_of_testBit_eq_lt (by omega) (by omega) hbit
      have hu : u₁ = u₂ := Fin.ext (by omega)
      subst hu
      apply hne
      have := congrArg (fun s => symmDiff s {u₁}) heq
      simpa [symmDiff_symmDiff_cancel_right] using this

lemma card_hammingCode (t : ℕ) (ht : 0 < t) :
    (hammingCode t).card = 2 ^ (2 ^ t - 1 - t) := by
  classical
  let ball (c : Finset (Fin (2 ^ t - 1))) : Finset (Finset (Fin (2 ^ t - 1))) :=
    Finset.univ.filter (fun x => satBlock x (ballSigning c))
  have hun : (hammingCode t).biUnion ball = Finset.univ := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true, ball, Finset.mem_filter, true_and]
    exact hammingCode_cover x
  have hdisj : Set.PairwiseDisjoint (hammingCode t : Set _) ball := by
    intro c₁ h1 c₂ h2 hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx1 hx2
    exact hammingCode_disjoint (Finset.mem_coe.mp h1) (Finset.mem_coe.mp h2) hne x
      ⟨(Finset.mem_filter.mp hx1).2, (Finset.mem_filter.mp hx2).2⟩
  have hcard_un : ((hammingCode t).biUnion ball).card = (hammingCode t).card * 2 ^ t := by
    rw [Finset.card_biUnion hdisj]
    have hpow : 2 ^ t - 1 + 1 = 2 ^ t := by
      have : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega); omega
    calc (hammingCode t).sum (fun c => (ball c).card)
        = (hammingCode t).sum (fun _ => 2 ^ t) :=
          Finset.sum_congr rfl fun c _ => by dsimp only [ball]; rw [card_ball, hpow]
      _ = (hammingCode t).card * 2 ^ t := by rw [Finset.sum_const, smul_eq_mul]
  rw [hun, Finset.card_univ, Fintype.card_finset, Fintype.card_fin] at hcard_un
  have ht_le : t ≤ 2 ^ t - 1 := by
    have : t < 2 ^ t := Nat.lt_two_pow_self
    omega
  have hpow_eq : 2 ^ (2 ^ t - 1) = 2 ^ (2 ^ t - 1 - t) * 2 ^ t := by
    rw [← pow_add]; congr 1; omega
  rw [hpow_eq] at hcard_un
  exact (Nat.mul_right_cancel (by positivity : 0 < 2 ^ t) hcard_un).symm

/-! ### Part C: Upper bounds (adaptive and fixed) -/

def stepState (m e : ℕ) (st : ℕ × ℕ) (bit : Bool) : ℕ × ℕ :=
  if bit = false ∧ st.1 < m then
    if st.2 + 1 = e + 1 then (st.1 + 1, 0) else (st.1, st.2 + 1)
  else st

def stateOf (m e : ℕ) (h : List Bool) : ℕ × ℕ :=
  h.foldl (stepState m e) (0, 0)

lemma stateOf_props (m e : ℕ) (h : List Bool) :
    (stateOf m e h).1 ≤ m ∧
    ((stateOf m e h).1 < m → (stateOf m e h).2 < e + 1) ∧
    ((stateOf m e h).1 = m → (stateOf m e h).2 = 0) ∧
    (stateOf m e h).1 * (e + 1) + (stateOf m e h).2 = min (m * (e + 1)) (h.count false) := by
  induction h using List.reverseRecOn with
  | nil => simp [stateOf]
  | append_singleton l bit ih =>
    rcases ih with ⟨h1, h2, h3, h4⟩
    have hstep : stateOf m e (l ++ [bit]) = stepState m e (stateOf m e l) bit := by
      simp [stateOf, List.foldl_concat]
    rw [hstep, List.count_append, List.count_singleton]
    dsimp only [stepState]
    cases bit
    · simp only [beq_self_eq_true, ite_true, true_and]
      by_cases hlt : (stateOf m e l).1 < m
      · simp only [hlt, ite_true]
        have hf := h2 hlt
        by_cases hfull : (stateOf m e l).2 + 1 = e + 1
        · simp only [hfull, ite_true]
          refine ⟨by omega, fun _ => by omega, fun _ => trivial, ?_⟩
          have hmul : ((stateOf m e l).1 + 1) * (e + 1) = (stateOf m e l).1 * (e + 1) + (e + 1) := by ring
          have hle_m : (stateOf m e l).1 + 1 ≤ m := by omega
          have hle_prod : ((stateOf m e l).1 + 1) * (e + 1) ≤ m * (e + 1) := Nat.mul_le_mul_right _ hle_m
          omega
        · simp only [hfull, ite_false]
          refine ⟨by omega, fun _ => by omega, fun heq => by omega, ?_⟩
          have hle_m : (stateOf m e l).1 + 1 ≤ m := by omega
          have hle_prod : ((stateOf m e l).1 + 1) * (e + 1) ≤ m * (e + 1) := Nat.mul_le_mul_right _ hle_m
          have hmul : ((stateOf m e l).1 + 1) * (e + 1) = (stateOf m e l).1 * (e + 1) + (e + 1) := by ring
          omega
      · simp only [hlt, ite_false]
        have heqm : (stateOf m e l).1 = m := by omega
        have hz := h3 heqm
        refine ⟨h1, fun hf => False.elim hf, h3, ?_⟩
        rw [heqm, hz, add_zero] at h4 ⊢
        omega
    · simp only [Bool.false_eq_true, false_and, ite_false, beq_iff_eq, Nat.add_zero]
      exact ⟨h1, h2, h3, h4⟩

lemma count_false_add_true (h : List Bool) : h.count false + h.count true = h.length := by
  induction h with
  | nil => simp
  | cons b l ih => cases b <;> simp <;> omega

lemma adaptive_upper (t r e k : ℕ) (ht : 0 < t)
    (hk : (e + 1) * 2 ^ (r * (2 ^ t - 1 - t)) + e ≤ k) :
    ∃ (ask : Fin k → List Bool → (Fin r → Fin (2 ^ t - 1) → Fin (2 ^ t - 1) → Bool × Bool))
      (answer : List Bool → Bool),
      ∀ (A : Finset (Fin r → Finset (Fin (2 ^ t - 1)))) (flips : Finset (Fin k)), flips.card ≤ e →
        answer ((List.finRange k).foldl (fun hist j =>
          hist ++ [replyOf A (ask j hist) != decide (j ∈ flips)]) ([] : List Bool)) = decide A.Nonempty := by
  classical
  let M := 2 ^ (r * (2 ^ t - 1 - t))
  have hM_pos : 0 < M := by positivity
  let centers : Finset (Fin r → Finset (Fin (2 ^ t - 1))) :=
    Fintype.piFinset (fun _ : Fin r => hammingCode t)
  have hC_card : centers.card = M := by
    rw [Fintype.card_piFinset]
    simp only [card_hammingCode t ht, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    dsimp only [M]
    rw [← pow_mul, mul_comm]
  let eC : Fin M ≃ {C // C ∈ centers} := (Fintype.equivFinOfCardEq (by simp [hC_card])).symm
  let probe : Fin M → (Fin r → Fin (2 ^ t - 1) → Fin (2 ^ t - 1) → Bool × Bool) :=
    fun i j => ballSigning ((eC i).1 j)
  have hcover : ∀ x : Fin r → Finset (Fin (2 ^ t - 1)), ∃ i : Fin M, satWord x (probe i) := by
    intro x
    let C : Fin r → Finset (Fin (2 ^ t - 1)) := fun j => Classical.choose (hammingCode_cover (x j))
    have hCmem : C ∈ centers := by
      rw [Fintype.mem_piFinset]
      intro j; exact (Classical.choose_spec (hammingCode_cover (x j))).1
    refine ⟨eC.symm ⟨C, hCmem⟩, fun j => ?_⟩
    dsimp only [probe]
    simp only [Equiv.apply_symm_apply]
    exact (Classical.choose_spec (hammingCode_cover (x j))).2
  let ask : Fin k → List Bool → (Fin r → Fin (2 ^ t - 1) → Fin (2 ^ t - 1) → Bool × Bool) :=
    fun _ h =>
      let idx := (stateOf M e h).1
      if hi : idx < M then probe ⟨idx, hi⟩ else probe ⟨0, hM_pos⟩
  let answer : List Bool → Bool := fun h => decide ((stateOf M e h).1 < M)
  refine ⟨ask, answer, fun A flips hflips => ?_⟩
  by_cases hAne : A.Nonempty
  · rcases hAne with ⟨x, hxA⟩
    rcases hcover x with ⟨iStar, hiStar_sat⟩
    have hiStar_true : replyOf A (probe iStar) = true :=
      (replyOf_eq_true_iff A (probe iStar)).mpr ⟨x, hxA, hiStar_sat⟩
    have hinv : ∀ l : List (Fin k), l.Nodup →
        let h := l.foldl (fun h j => h ++ [replyOf A (ask j h) != decide (j ∈ flips)]) []
        (stateOf M e h).1 < iStar.val ∨
          ((stateOf M e h).1 = iStar.val ∧
            (stateOf M e h).2 ≤ (l.filter (fun j => decide (j ∈ flips))).length) := by
      intro l
      induction l using List.reverseRecOn with
      | nil =>
        intro _
        by_cases h0 : 0 < iStar.val
        · exact Or.inl h0
        · right; simp [stateOf]; omega
      | append_singleton l j ih =>
        intro hnodup
        have hih := ih (List.nodup_append.mp hnodup).1
        set h := l.foldl (fun h j => h ++ [replyOf A (ask j h) != decide (j ∈ flips)]) []
        have hfold : (l ++ [j]).foldl (fun h j => h ++ [replyOf A (ask j h) != decide (j ∈ flips)]) [] =
            h ++ [replyOf A (ask j h) != decide (j ∈ flips)] := List.foldl_concat ..
        change (stateOf M e ((l ++ [j]).foldl _ [])).1 < iStar.val ∨ _
        rw [hfold]
        have hst_step : stateOf M e (h ++ [replyOf A (ask j h) != decide (j ∈ flips)]) =
            stepState M e (stateOf M e h) (replyOf A (ask j h) != decide (j ∈ flips)) := by
          simp [stateOf, List.foldl_concat]
        rw [hst_step]
        have hfilt : ((l ++ [j]).filter (fun t => decide (t ∈ flips))).length =
            (l.filter (fun t => decide (t ∈ flips))).length + if j ∈ flips then 1 else 0 := by
          rw [List.filter_append, List.length_append]
          by_cases hj : j ∈ flips <;> simp [hj]
        rw [hfilt]
        rcases hih with hlt | ⟨heq, hle⟩
        · dsimp only [stepState]
          by_cases hc1 : (replyOf A (ask j h) != decide (j ∈ flips)) = false ∧ (stateOf M e h).1 < M
          · rw [if_pos hc1]
            by_cases hc2 : (stateOf M e h).2 + 1 = e + 1
            · rw [if_pos hc2]
              by_cases hlt' : (stateOf M e h).1 + 1 < iStar.val
              · exact Or.inl hlt'
              · exact Or.inr ⟨by omega, by omega⟩
            · rw [if_neg hc2]; exact Or.inl hlt
          · rw [if_neg hc1]; exact Or.inl hlt
        · have hi_lt_M : (stateOf M e h).1 < M := by omega
          have hask : ask j h = probe iStar := by
            dsimp only [ask]; rw [dif_pos hi_lt_M]; congr 1; exact Fin.ext heq
          rw [hask, hiStar_true]
          by_cases hj : j ∈ flips
          · simp only [hj, decide_true, bne_self_eq_false, ite_true]
            have hflips_le : (l.filter (fun t => decide (t ∈ flips))).length + 1 ≤ e := by
              have hsub : ((l ++ [j]).filter (fun t => decide (t ∈ flips))).toFinset ⊆ flips := by
                intro t ht
                simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at ht
                exact ht.2
              have hnd_f : ((l ++ [j]).filter (fun t => decide (t ∈ flips))).Nodup :=
                List.Nodup.filter _ hnodup
              have hle_e : ((l ++ [j]).filter (fun t => decide (t ∈ flips))).length ≤ e := by
                rw [← List.toFinset_card_of_nodup hnd_f]
                exact le_trans (Finset.card_le_card hsub) hflips
              rw [hfilt, if_pos hj] at hle_e
              exact hle_e
            dsimp only [stepState]
            have hnotfull : (stateOf M e h).2 + 1 ≠ e + 1 := by omega
            simp only [hi_lt_M, and_self, ite_true, hnotfull, ite_false]
            exact Or.inr ⟨heq, by omega⟩
          · simp only [hj, decide_false, Bool.bne_false, ite_false]
            dsimp only [stepState]
            simp only [Bool.true_eq_false, false_and, ite_false]
            exact Or.inr ⟨heq, by omega⟩
    have hfin := hinv (List.finRange k) (List.nodup_finRange k)
    have hlt_M : (stateOf M e ((List.finRange k).foldl
        (fun h j => h ++ [replyOf A (ask j h) != decide (j ∈ flips)]) [])).1 < M := by
      rcases hfin with h1 | ⟨h1, _⟩ <;> omega
    have hAne' : A.Nonempty := ⟨x, hxA⟩
    simp [answer, hAne', hlt_M]
  · have hA0 : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAne
    subst hA0
    have hall_false : ∀ (j : Fin k) (h : List Bool), replyOf ∅ (ask j h) = false := by
      intro j h
      rw [Bool.eq_false_iff, ne_eq, replyOf_eq_true_iff]
      rintro ⟨x, hx, _⟩; exact Finset.notMem_empty x hx
    have hcnt : ∀ l : List (Fin k),
        let h := l.foldl (fun h j => h ++ [replyOf ∅ (ask j h) != decide (j ∈ flips)]) []
        h.length = l.length ∧ h.count true = (l.filter (fun j => decide (j ∈ flips))).length := by
      intro l
      induction l using List.reverseRecOn with
      | nil => simp
      | append_singleton l j ih =>
        set h := l.foldl (fun h j => h ++ [replyOf ∅ (ask j h) != decide (j ∈ flips)]) []
        have hfold : (l ++ [j]).foldl (fun h j => h ++ [replyOf ∅ (ask j h) != decide (j ∈ flips)]) [] =
            h ++ [replyOf ∅ (ask j h) != decide (j ∈ flips)] := List.foldl_concat ..
        dsimp only
        rw [hfold, hall_false j h, Bool.false_bne, List.length_append, List.length_singleton,
            List.length_append, List.length_singleton, List.count_append, List.count_singleton,
            List.filter_append, List.length_append]
        by_cases hj : j ∈ flips <;> simp [hj, ih.1, ih.2]
    have hfin := hcnt (List.finRange k)
    set h := (List.finRange k).foldl (fun h j => h ++ [replyOf ∅ (ask j h) != decide (j ∈ flips)]) []
    have hlen : h.length = k := by rw [hfin.1, List.length_finRange]
    have htrue_le : h.count true ≤ e := by
      rw [hfin.2]
      have hsub : ((List.finRange k).filter (fun j => decide (j ∈ flips))).toFinset ⊆ flips := by
        intro t ht
        simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at ht
        exact ht.2
      have hnd : ((List.finRange k).filter (fun j => decide (j ∈ flips))).Nodup :=
        List.Nodup.filter _ (List.nodup_finRange k)
      rw [← List.toFinset_card_of_nodup hnd]
      exact le_trans (Finset.card_le_card hsub) hflips
    have hfalse_ge : M * (e + 1) ≤ h.count false := by
      have hsum := count_false_add_true h
      have hk' : M * (e + 1) + e ≤ k := by rw [mul_comm]; exact hk
      omega
    rcases stateOf_props M e h with ⟨hst1, hst2, _, hst4⟩
    rw [min_eq_left hfalse_ge] at hst4
    have heqM : (stateOf M e h).1 = M := by
      by_contra hne
      have hlt : (stateOf M e h).1 < M := lt_of_le_of_ne hst1 hne
      have hlt2 := hst2 hlt
      have hle_M : (stateOf M e h).1 + 1 ≤ M := by omega
      have hmul : ((stateOf M e h).1 + 1) * (e + 1) ≤ M * (e + 1) := Nat.mul_le_mul_right _ hle_M
      have hexp : ((stateOf M e h).1 + 1) * (e + 1) = (stateOf M e h).1 * (e + 1) + (e + 1) := by ring
      omega
    simp [answer, heqM]

lemma foldl_nonadaptive_getD {k : ℕ} (f : Fin k → Bool) :
    ∀ (l : List (Fin k)),
      (l.foldl (fun hist j => hist ++ [f j]) ([] : List Bool)) = l.map f := by
  intro l
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l j ih =>
    rw [List.foldl_concat, ih, List.map_append, List.map_singleton]

lemma fixed_upper (t r e k : ℕ) (ht : 0 < t)
    (hk : (2 * e + 1) * 2 ^ (r * (2 ^ t - 1 - t)) ≤ k) :
    ∃ (ask : Fin k → (Fin r → Fin (2 ^ t - 1) → Fin (2 ^ t - 1) → Bool × Bool))
      (answer : List Bool → Bool),
      ∀ (A : Finset (Fin r → Finset (Fin (2 ^ t - 1)))) (flips : Finset (Fin k)), flips.card ≤ e →
        answer ((List.finRange k).foldl (fun hist j =>
          hist ++ [replyOf A (ask j) != decide (j ∈ flips)]) ([] : List Bool)) = decide A.Nonempty := by
  classical
  let M := 2 ^ (r * (2 ^ t - 1 - t))
  have hM_pos : 0 < M := by positivity
  let centers : Finset (Fin r → Finset (Fin (2 ^ t - 1))) :=
    Fintype.piFinset (fun _ : Fin r => hammingCode t)
  have hC_card : centers.card = M := by
    rw [Fintype.card_piFinset]
    simp only [card_hammingCode t ht, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    dsimp only [M]
    rw [← pow_mul, mul_comm]
  let eC : Fin M ≃ {C // C ∈ centers} := (Fintype.equivFinOfCardEq (by simp [hC_card])).symm
  let probe : Fin M → (Fin r → Fin (2 ^ t - 1) → Fin (2 ^ t - 1) → Bool × Bool) :=
    fun i j => ballSigning ((eC i).1 j)
  have hcover : ∀ x : Fin r → Finset (Fin (2 ^ t - 1)), ∃ i : Fin M, satWord x (probe i) := by
    intro x
    let C : Fin r → Finset (Fin (2 ^ t - 1)) := fun j => Classical.choose (hammingCode_cover (x j))
    have hCmem : C ∈ centers := by
      rw [Fintype.mem_piFinset]
      intro j; exact (Classical.choose_spec (hammingCode_cover (x j))).1
    refine ⟨eC.symm ⟨C, hCmem⟩, fun j => ?_⟩
    dsimp only [probe]; simp only [Equiv.apply_symm_apply]
    exact (Classical.choose_spec (hammingCode_cover (x j))).2
  let ask : Fin k → (Fin r → Fin (2 ^ t - 1) → Fin (2 ^ t - 1) → Bool × Bool) := fun j =>
    let idx := j.val / (2 * e + 1)
    if hi : idx < M then probe ⟨idx, hi⟩ else probe ⟨0, hM_pos⟩
  let blockCount (h : List Bool) (i : Fin M) : ℕ :=
    ((Finset.univ : Finset (Fin (2 * e + 1))).filter
      (fun o => h.getD (i.val * (2 * e + 1) + o.val) false = true)).card
  let answer : List Bool → Bool := fun h =>
    decide (∃ i : Fin M, e + 1 ≤ blockCount h i)
  refine ⟨ask, answer, fun A flips hflips => ?_⟩
  rw [foldl_nonadaptive_getD]
  set f : Fin k → Bool := fun j => replyOf A (ask j) != decide (j ∈ flips)
  have hget : ∀ (j : Fin k), ((List.finRange k).map f).getD j.val false = f j := by
    intro j
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, getElem?_finRange_lt j.isLt]
    rfl
  by_cases hAne : A.Nonempty
  · rcases hAne with ⟨x, hxA⟩
    rcases hcover x with ⟨iStar, hiStar_sat⟩
    have hiStar_true : replyOf A (probe iStar) = true :=
      (replyOf_eq_true_iff A (probe iStar)).mpr ⟨x, hxA, hiStar_sat⟩
    have hpos_idx : ∀ o : Fin (2 * e + 1), iStar.val * (2 * e + 1) + o.val < k := by
      intro o
      have h1 : (iStar.val + 1) * (2 * e + 1) ≤ M * (2 * e + 1) := Nat.mul_le_mul_right _ (by omega)
      have h2 : M * (2 * e + 1) ≤ k := by rw [mul_comm]; exact hk
      have h3 : (iStar.val + 1) * (2 * e + 1) = iStar.val * (2 * e + 1) + (2 * e + 1) := by ring
      omega
    let slot (o : Fin (2 * e + 1)) : Fin k := ⟨iStar.val * (2 * e + 1) + o.val, hpos_idx o⟩
    have hslot_inj : Function.Injective slot := by
      intro o₁ o₂ h
      have hv := congrArg Fin.val h
      dsimp only [slot] at hv
      exact Fin.ext (by omega)
    have hslot_ask : ∀ o : Fin (2 * e + 1), ask (slot o) = probe iStar := by
      intro o
      dsimp only [ask, slot]
      have hdiv : (iStar.val * (2 * e + 1) + o.val) / (2 * e + 1) = iStar.val := by
        rw [mul_comm iStar.val (2 * e + 1), Nat.mul_add_div (by omega), Nat.div_eq_of_lt o.isLt, add_zero]
      simp only [hdiv, iStar.isLt, dite_true]
    have hbad_le : ((Finset.univ : Finset (Fin (2 * e + 1))).filter
        (fun o => slot o ∈ flips)).card ≤ e := by
      calc ((Finset.univ : Finset (Fin (2 * e + 1))).filter (fun o => slot o ∈ flips)).card
          = (((Finset.univ : Finset (Fin (2 * e + 1))).filter (fun o => slot o ∈ flips)).image slot).card :=
            (Finset.card_image_of_injective _ hslot_inj).symm
        _ ≤ flips.card := Finset.card_le_card (fun j hj => by
            rcases Finset.mem_image.mp hj with ⟨o, ho, rfl⟩
            exact (Finset.mem_filter.mp ho).2)
        _ ≤ e := hflips
    have hgood : e + 1 ≤ blockCount ((List.finRange k).map f) iStar := by
      have hcompl : ((Finset.univ : Finset (Fin (2 * e + 1))).filter (fun o => slot o ∉ flips)).card +
          ((Finset.univ : Finset (Fin (2 * e + 1))).filter (fun o => slot o ∈ flips)).card = 2 * e + 1 := by
        have hdisj : Disjoint
            ((Finset.univ : Finset (Fin (2 * e + 1))).filter (fun o => slot o ∉ flips))
            ((Finset.univ : Finset (Fin (2 * e + 1))).filter (fun o => slot o ∈ flips)) := by
          rw [Finset.disjoint_left]; intro o h1 h2
          exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
        have hun : (Finset.univ : Finset (Fin (2 * e + 1))).filter (fun o => slot o ∉ flips) ∪
            (Finset.univ : Finset (Fin (2 * e + 1))).filter (fun o => slot o ∈ flips) = Finset.univ := by
          ext o; by_cases ho : slot o ∈ flips <;> simp [ho]
        rw [← Finset.card_union_of_disjoint hdisj, hun]
        simp
      have hsub : (Finset.univ : Finset (Fin (2 * e + 1))).filter (fun o => slot o ∉ flips) ⊆
          (Finset.univ : Finset (Fin (2 * e + 1))).filter
            (fun o => ((List.finRange k).map f).getD (iStar.val * (2 * e + 1) + o.val) false = true) := by
        intro o ho
        have hnot : slot o ∉ flips := (Finset.mem_filter.mp ho).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ o, ?_⟩
        change ((List.finRange k).map f).getD (slot o).val false = true
        rw [hget (slot o)]
        dsimp only [f]
        rw [hslot_ask o, hiStar_true]
        simp [hnot]
      have hle := Finset.card_le_card hsub
      dsimp only [blockCount]
      omega
    have hAne' : A.Nonempty := ⟨x, hxA⟩
    dsimp only [answer]
    rw [decide_eq_true ⟨iStar, hgood⟩, decide_eq_true hAne']
  · have hA0 : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAne
    subst hA0
    have hno : ¬ ∃ i : Fin M, e + 1 ≤ blockCount ((List.finRange k).map f) i := by
      rintro ⟨i, hi⟩
      have hpos_idx : ∀ o : Fin (2 * e + 1), i.val * (2 * e + 1) + o.val < k := by
        intro o
        have h1 : (i.val + 1) * (2 * e + 1) ≤ M * (2 * e + 1) := Nat.mul_le_mul_right _ (by omega)
        have h2 : M * (2 * e + 1) ≤ k := by rw [mul_comm]; exact hk
        have h3 : (i.val + 1) * (2 * e + 1) = i.val * (2 * e + 1) + (2 * e + 1) := by ring
        omega
      let slot (o : Fin (2 * e + 1)) : Fin k := ⟨i.val * (2 * e + 1) + o.val, hpos_idx o⟩
      have hslot_inj : Function.Injective slot := by
        intro o₁ o₂ h; have hv := congrArg Fin.val h; dsimp only [slot] at hv; exact Fin.ext (by omega)
      have hsub : ((Finset.univ : Finset (Fin (2 * e + 1))).filter
          (fun o => ((List.finRange k).map f).getD (i.val * (2 * e + 1) + o.val) false = true)).image slot ⊆
          flips := by
        intro j hj
        rcases Finset.mem_image.mp hj with ⟨o, ho, rfl⟩
        have ht' : ((List.finRange k).map f).getD (slot o).val false = true := (Finset.mem_filter.mp ho).2
        rw [hget (slot o)] at ht'
        dsimp only [f] at ht'
        have hrep : replyOf ∅ (ask (slot o)) = false := by
          rw [Bool.eq_false_iff, ne_eq, replyOf_eq_true_iff]
          rintro ⟨x, hx, _⟩; exact Finset.notMem_empty x hx
        rw [hrep, Bool.false_bne] at ht'
        exact of_decide_eq_true ht'
      have hle := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ hslot_inj] at hle
      dsimp only [blockCount] at hi
      omega
    dsimp only [answer]
    rw [decide_eq_false hno, decide_eq_false Finset.not_nonempty_empty]

/-! ### Part D: Lower bounds (fixed and adaptive) -/

lemma pigeonhole_word {t r L : ℕ} (ht : 0 < t)
    (q : Fin L → (Fin r → Fin (2 ^ t - 1) → Fin (2 ^ t - 1) → Bool × Bool))
    (B : ℕ) (hL : L < B * 2 ^ (r * (2 ^ t - 1 - t))) :
    ∃ x₀ : Fin r → Finset (Fin (2 ^ t - 1)),
      ((Finset.univ : Finset (Fin L)).filter (fun j => satWord x₀ (q j))).card < B := by
  classical
  let Word := Fin r → Finset (Fin (2 ^ t - 1))
  have hcardW : (Finset.univ : Finset Word).card = 2 ^ (r * (2 ^ t - 1)) := by
    dsimp only [Word]
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_finset, Fintype.card_fin]
    rw [← pow_mul, mul_comm]
  have h2t : (2 ^ t - 1) + 1 = 2 ^ t := by
    have : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega); omega
  have ht_le : t ≤ 2 ^ t - 1 := by
    have : t < 2 ^ t := Nat.lt_two_pow_self; omega
  have hprod : 2 ^ (r * (2 ^ t - 1 - t)) * (2 ^ t) ^ r = 2 ^ (r * (2 ^ t - 1)) := by
    rw [← pow_mul, mul_comm t r, ← pow_add]
    congr 1
    have h1 : (2 ^ t - 1 - t) + t = 2 ^ t - 1 := by omega
    calc r * (2 ^ t - 1 - t) + r * t = r * ((2 ^ t - 1 - t) + t) := by ring
      _ = r * (2 ^ t - 1) := by rw [h1]
  have hsum_swap : (Finset.univ : Finset Word).sum
      (fun x => ((Finset.univ : Finset (Fin L)).filter (fun j => satWord x (q j))).card) =
      (Finset.univ : Finset (Fin L)).sum
        (fun j => ((Finset.univ : Finset Word).filter (fun x => satWord x (q j))).card) := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have hsum_le : (Finset.univ : Finset Word).sum
      (fun x => ((Finset.univ : Finset (Fin L)).filter (fun j => satWord x (q j))).card) ≤
      L * (2 ^ t) ^ r := by
    rw [hsum_swap]
    calc (Finset.univ : Finset (Fin L)).sum
          (fun j => ((Finset.univ : Finset Word).filter (fun x => satWord x (q j))).card)
        ≤ (Finset.univ : Finset (Fin L)).sum (fun _ => (2 ^ t) ^ r) :=
          Finset.sum_le_sum fun j _ => by
            dsimp only [Word]
            have h := card_satWord_le (q j)
            rwa [h2t] at h
      _ = L * (2 ^ t) ^ r := by simp
  by_contra hall
  push Not at hall
  have hsum_ge : (Finset.univ : Finset Word).card * B ≤
      (Finset.univ : Finset Word).sum
        (fun x => ((Finset.univ : Finset (Fin L)).filter (fun j => satWord x (q j))).card) := by
    calc (Finset.univ : Finset Word).card * B
        = (Finset.univ : Finset Word).sum (fun _ => B) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun x _ => hall x
  have hlt : L * (2 ^ t) ^ r < (B * 2 ^ (r * (2 ^ t - 1 - t))) * (2 ^ t) ^ r :=
    Nat.mul_lt_mul_of_pos_right hL (by positivity)
  rw [mul_assoc, hprod] at hlt
  rw [hcardW] at hsum_ge
  have hcomm : 2 ^ (r * (2 ^ t - 1)) * B = B * 2 ^ (r * (2 ^ t - 1)) := mul_comm _ _
  omega

lemma fixed_lower (t r e k : ℕ) (ht : 0 < t)
    (ask : Fin k → (Fin r → Fin (2 ^ t - 1) → Fin (2 ^ t - 1) → Bool × Bool))
    (answer : List Bool → Bool)
    (hvalid : ∀ (A : Finset (Fin r → Finset (Fin (2 ^ t - 1)))) (flips : Finset (Fin k)), flips.card ≤ e →
      answer ((List.finRange k).foldl (fun hist j =>
        hist ++ [replyOf A (ask j) != decide (j ∈ flips)]) ([] : List Bool)) = decide A.Nonempty) :
    (2 * e + 1) * 2 ^ (r * (2 ^ t - 1 - t)) ≤ k := by
  classical
  by_contra hlt
  push Not at hlt
  rcases pigeonhole_word ht ask (2 * e + 1) hlt with ⟨x₀, hx₀⟩
  let H := (Finset.univ : Finset (Fin k)).filter (fun j => satWord x₀ (ask j))
  have hH_le : H.card ≤ 2 * e := by dsimp only [H]; omega
  -- Split H into F0 of size min e H.card and F1 = H \ F0
  have hex_split : ∃ F₀ : Finset (Fin k), F₀ ⊆ H ∧ F₀.card = min e H.card :=
    Finset.exists_subset_card_eq (Nat.min_le_right e H.card)
  rcases hex_split with ⟨F₀, hF₀sub, hF₀card⟩
  let F₁ := H \ F₀
  have hF₀_le : F₀.card ≤ e := by omega
  have hF₁_le : F₁.card ≤ e := by
    have hsum := Finset.card_sdiff_add_card_eq_card hF₀sub
    dsimp only [F₁]; omega
  have h0 := hvalid ∅ F₀ hF₀_le
  have h1 := hvalid {x₀} F₁ hF₁_le
  have hfold_eq : (List.finRange k).foldl (fun hist j =>
        hist ++ [replyOf ∅ (ask j) != decide (j ∈ F₀)]) [] =
      (List.finRange k).foldl (fun hist j =>
        hist ++ [replyOf {x₀} (ask j) != decide (j ∈ F₁)]) [] := by
    rw [foldl_nonadaptive_getD, foldl_nonadaptive_getD]
    congr 1; funext j
    have hrep0 : replyOf ∅ (ask j) = false := by
      rw [Bool.eq_false_iff, ne_eq, replyOf_eq_true_iff]
      rintro ⟨x, hx, _⟩; exact Finset.notMem_empty x hx
    have hrep1 : replyOf {x₀} (ask j) = decide (j ∈ H) := by
      apply Bool.eq_iff_iff.mpr
      rw [replyOf_eq_true_iff]
      simp [H]
    rw [hrep0, hrep1, Bool.false_bne]
    by_cases hjH : j ∈ H
    · by_cases hj0 : j ∈ F₀
      · have hj1 : j ∉ F₁ := fun h => (Finset.mem_sdiff.mp h).2 hj0
        simp [hjH, hj0, hj1]
      · have hj1 : j ∈ F₁ := Finset.mem_sdiff.mpr ⟨hjH, hj0⟩
        simp [hjH, hj0, hj1]
    · have hj0 : j ∉ F₀ := fun h => hjH (hF₀sub h)
      have hj1 : j ∉ F₁ := fun h => hjH (Finset.mem_sdiff.mp h).1
      simp [hjH, hj0, hj1]
  rw [hfold_eq] at h0
  simp at h0 h1
  rw [h0] at h1
  exact Bool.false_ne_true h1

lemma adaptive_lower (t r e k : ℕ) (ht : 0 < t)
    (ask : Fin k → List Bool → (Fin r → Fin (2 ^ t - 1) → Fin (2 ^ t - 1) → Bool × Bool))
    (answer : List Bool → Bool)
    (hvalid : ∀ (A : Finset (Fin r → Finset (Fin (2 ^ t - 1)))) (flips : Finset (Fin k)), flips.card ≤ e →
      answer ((List.finRange k).foldl (fun hist j =>
        hist ++ [replyOf A (ask j hist) != decide (j ∈ flips)]) ([] : List Bool)) = decide A.Nonempty) :
    (e + 1) * 2 ^ (r * (2 ^ t - 1 - t)) + e ≤ k := by
  classical
  by_contra hlt
  push Not at hlt
  let L := k - e
  have hpos_M : 0 < (e + 1) * 2 ^ (r * (2 ^ t - 1 - t)) := by positivity
  have hL_lt : L < (e + 1) * 2 ^ (r * (2 ^ t - 1 - t)) := by dsimp only [L]; omega
  have hL_le : L ≤ k := Nat.sub_le k e
  let qPref : Fin L → (Fin r → Fin (2 ^ t - 1) → Fin (2 ^ t - 1) → Bool × Bool) :=
    fun j => ask ⟨j.val, lt_of_lt_of_le j.isLt hL_le⟩ (List.replicate j.val false)
  rcases pigeonhole_word ht qPref (e + 1) hL_lt with ⟨x₀, hx₀⟩
  let H_L : Finset (Fin L) := Finset.univ.filter (fun j => satWord x₀ (qPref j))
  have hHL_le : H_L.card ≤ e := Nat.lt_succ_iff.mp hx₀
  let emb : Fin L → Fin k := fun j => ⟨j.val, lt_of_lt_of_le j.isLt hL_le⟩
  have hemb_inj : Function.Injective emb := fun a b h => Fin.ext (by have := congrArg Fin.val h; exact this)
  let F₁ : Finset (Fin k) := H_L.image emb
  have hF₁_le : F₁.card ≤ e := by
    rw [Finset.card_image_of_injective _ hemb_inj]; exact hHL_le
  -- Run ({x0}, F1) and inspect its full transcript histStar
  let run := fun (A : Finset (Fin r → Finset (Fin (2 ^ t - 1)))) (flips : Finset (Fin k)) (m : ℕ) =>
    ((List.finRange k).take m).foldl (fun hist j =>
      hist ++ [replyOf A (ask j hist) != decide (j ∈ flips)]) ([] : List Bool)
  have hrun_len : ∀ A flips m, m ≤ k → (run A flips m).length = m := by
    intro A flips m
    induction m with
    | zero => intro _; simp [run]
    | succ m ih =>
      intro hmk
      have htake : (List.finRange k).take (m + 1) = (List.finRange k).take m ++ [⟨m, hmk⟩] := by
        rw [List.take_succ, getElem?_finRange_lt hmk, Option.toList_some]
      dsimp only [run]
      rw [htake, List.foldl_concat, List.length_append, List.length_singleton]
      exact congrArg (· + 1) (ih (by omega))
  -- For m <= L, run {x0} F1 m = List.replicate m false
  have hpref_false : ∀ m : ℕ, m ≤ L → run {x₀} F₁ m = List.replicate m false := by
    intro m
    induction m with
    | zero => intro _; simp [run]
    | succ m ih =>
      intro hmL
      have hmk : m < k := lt_of_lt_of_le hmL hL_le
      have htake : (List.finRange k).take (m + 1) = (List.finRange k).take m ++ [⟨m, hmk⟩] := by
        rw [List.take_succ, getElem?_finRange_lt hmk, Option.toList_some]
      dsimp only [run]
      rw [htake, List.foldl_concat]
      change run {x₀} F₁ m ++ [replyOf {x₀} (ask ⟨m, hmk⟩ (run {x₀} F₁ m)) != decide (⟨m, hmk⟩ ∈ F₁)] = _
      rw [ih (by omega)]
      have hmem_iff : (⟨m, hmk⟩ : Fin k) ∈ F₁ ↔ satWord x₀ (qPref ⟨m, hmL⟩) := by
        simp only [F₁, Finset.mem_image, H_L, Finset.mem_filter, Finset.mem_univ, true_and, emb]
        constructor
        · rintro ⟨j, hj, hEq⟩
          have hjm : j = ⟨m, hmL⟩ := Fin.ext (by have := congrArg Fin.val hEq; exact this)
          rwa [← hjm]
        · intro hsat
          exact ⟨⟨m, hmL⟩, hsat, rfl⟩
      have hrep : replyOf {x₀} (ask ⟨m, hmk⟩ (List.replicate m false)) =
          decide (satWord x₀ (qPref ⟨m, hmL⟩)) := by
        apply Bool.eq_iff_iff.mpr
        rw [replyOf_eq_true_iff]
        simp [qPref]
      rw [hrep, decide_eq_decide.mpr hmem_iff, bne_self_eq_false]
      rw [List.replicate_succ']
  let histStar := run {x₀} F₁ k
  let F₀ : Finset (Fin k) := Finset.univ.filter (fun j => L ≤ j.val ∧ histStar.getD j.val false = true)
  have hF₀_le : F₀.card ≤ e := by
    have hsub : F₀ ⊆ Finset.univ.filter (fun j : Fin k => L ≤ j.val) := fun j hj =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2.1⟩
    have hcard_tail : (Finset.univ.filter (fun j : Fin k => L ≤ j.val)).card = k - L := by
      have hbij : (Finset.univ.filter (fun j : Fin k => L ≤ j.val)).card =
          (Finset.univ : Finset (Fin (k - L))).card := by
        refine (Finset.card_bij (fun i _ => (⟨L + i.val, by omega⟩ : Fin k)) ?_ ?_ ?_).symm
        · intro i _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩
        · intro a _ b _ h; exact Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)
        · intro j hj
          have hLj : L ≤ j.val := (Finset.mem_filter.mp hj).2
          exact ⟨⟨j.val - L, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp; omega)⟩
      rw [hbij]; simp
    calc F₀.card ≤ (Finset.univ.filter (fun j : Fin k => L ≤ j.val)).card := Finset.card_le_card hsub
      _ = k - L := hcard_tail
      _ ≤ e := by dsimp only [L]; omega
  -- Show run ∅ F0 m = run {x0} F1 m for all m <= k
  have hrun_prefix : ∀ m : ℕ, m ≤ k → run {x₀} F₁ m = histStar.take m := by
    intro m hm
    have hlen_m := hrun_len {x₀} F₁ m hm
    -- Prove generally for m <= m' <= k: (run {x0} F1 m').take m = run {x0} F1 m
    have hgen : ∀ m' : ℕ, m ≤ m' → m' ≤ k → (run {x₀} F₁ m').take m = run {x₀} F₁ m := by
      intro m' hmm' hm'k
      induction m', hmm' using Nat.le_induction with
      | base =>
        rw [List.take_of_length_le (by rw [hlen_m])]
      | succ d hmd ih =>
        have htake : (List.finRange k).take (d + 1) = (List.finRange k).take d ++ [⟨d, hm'k⟩] := by
          rw [List.take_succ, getElem?_finRange_lt hm'k, Option.toList_some]
        have hstep : run {x₀} F₁ (d + 1) = run {x₀} F₁ d ++
            [replyOf {x₀} (ask ⟨d, hm'k⟩ (run {x₀} F₁ d)) != decide (⟨d, hm'k⟩ ∈ F₁)] := by
          dsimp only [run]; rw [htake, List.foldl_concat]
        rw [hstep, List.take_append_of_le_length (by rw [hrun_len {x₀} F₁ d (by omega)]; exact hmd)]
        exact ih (by omega)
    exact (hgen k hm le_rfl).symm
  have hsame : ∀ m : ℕ, m ≤ k → run ∅ F₀ m = run {x₀} F₁ m := by
    intro m
    induction m with
    | zero => intro _; simp [run]
    | succ m ih =>
      intro hmk
      have htake : (List.finRange k).take (m + 1) = (List.finRange k).take m ++ [⟨m, hmk⟩] := by
        rw [List.take_succ, getElem?_finRange_lt hmk, Option.toList_some]
      have hstep0 : run ∅ F₀ (m + 1) = run ∅ F₀ m ++
          [replyOf ∅ (ask ⟨m, hmk⟩ (run ∅ F₀ m)) != decide (⟨m, hmk⟩ ∈ F₀)] := by
        dsimp only [run]; rw [htake, List.foldl_concat]
      have hstep1 : run {x₀} F₁ (m + 1) = run {x₀} F₁ m ++
          [replyOf {x₀} (ask ⟨m, hmk⟩ (run {x₀} F₁ m)) != decide (⟨m, hmk⟩ ∈ F₁)] := by
        dsimp only [run]; rw [htake, List.foldl_concat]
      rw [hstep0, hstep1, ih (by omega)]
      congr 1; congr 1
      have hrep0 : replyOf ∅ (ask ⟨m, hmk⟩ (run {x₀} F₁ m)) = false := by
        rw [Bool.eq_false_iff, ne_eq, replyOf_eq_true_iff]
        rintro ⟨x, hx, _⟩; exact Finset.notMem_empty x hx
      rw [hrep0, Bool.false_bne]
      by_cases hmL : m < L
      · have hnot0 : (⟨m, hmk⟩ : Fin k) ∉ F₀ := by
          intro h; have := (Finset.mem_filter.mp h).2.1; dsimp at this; omega
        rw [decide_eq_false hnot0]
        have hpref := hpref_false (m + 1) hmL
        have hbit_eq : (run {x₀} F₁ (m + 1)).getD m false = false := by
          rw [hpref, List.getD_eq_getElem?_getD, List.getElem?_replicate]
          simp
        rw [hstep1, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hrun_len {x₀} F₁ m (by omega)])] at hbit_eq
        rw [hrun_len {x₀} F₁ m (by omega), Nat.sub_self] at hbit_eq
        simpa using hbit_eq.symm
      · push Not at hmL
        have hstar_m : histStar.getD m false =
            (replyOf {x₀} (ask ⟨m, hmk⟩ (run {x₀} F₁ m)) != decide (⟨m, hmk⟩ ∈ F₁)) := by
          have hp := hrun_prefix (m + 1) hmk
          have h1 : (histStar.take (m + 1)).getD m false = histStar.getD m false := by
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
          rw [← h1, ← hp, hstep1, List.getD_eq_getElem?_getD,
              List.getElem?_append_right (by rw [hrun_len {x₀} F₁ m (by omega)]),
              hrun_len {x₀} F₁ m (by omega), Nat.sub_self]
          rfl
        have hmem0 : (⟨m, hmk⟩ : Fin k) ∈ F₀ ↔ histStar.getD m false = true := by
          simp [F₀, hmL]
        have hdec0 : decide ((⟨m, hmk⟩ : Fin k) ∈ F₀) = histStar.getD m false := by
          by_cases hb : histStar.getD m false = true
          · rw [hb, decide_eq_true (hmem0.mpr hb)]
          · have hbf : histStar.getD m false = false := Bool.eq_false_iff.mpr hb
            rw [hbf, decide_eq_false (fun h => hb (hmem0.mp h))]
        rw [hdec0, hstar_m]
  have h0 := hvalid ∅ F₀ hF₀_le
  have h1 := hvalid {x₀} F₁ hF₁_le
  have htake_all : (List.finRange k).take k = List.finRange k := by
    rw [List.take_of_length_le (by simp)]
  have hsame_k := hsame k le_rfl
  dsimp only [run] at hsame_k
  rw [htake_all] at hsame_k
  rw [hsame_k] at h0
  simp at h0 h1
  rw [h0] at h1
  exact Bool.false_ne_true h1

theorem main :
    ∀ (t r e k : Nat), 0 < t →
      let n := 2 ^ t - 1
      let Site := Fin n
      let Word := Fin r → Finset Site
      let Signing := Fin r → Site → Site → Bool × Bool
      let sites := (Finset.univ : Finset Site).toList
      let blocks := (Finset.univ : Finset (Fin r)).toList
      let reply := fun (A : Finset Word) (s : Signing) => A.toList.any (fun x =>
        blocks.all (fun j => sites.all (fun u => sites.all (fun v =>
          !(decide (u < v)) || ((decide (u ∈ x j), decide (v ∈ x j)) != s j u v)))))
      let valid := fun (ask : Fin k → List Bool → Signing) (answer : List Bool → Bool) =>
        ∀ (A : Finset Word) (flips : Finset (Fin k)), flips.card ≤ e →
          answer ((List.finRange k).foldl (fun hist j =>
            hist ++ [reply A (ask j hist) != decide (j ∈ flips)]) ([] : List Bool)) = decide A.Nonempty
      let M := 2 ^ (r * (n - t))
      ((∃ ask : Fin k → List Bool → Signing, ∃ answer, valid ask answer) ↔ (e + 1) * M + e ≤ k) ∧
      ((∃ ask : Fin k → Signing, ∃ answer, valid (fun j _ => ask j) answer) ↔ (2 * e + 1) * M ≤ k) := by
  intro t r e k ht
  dsimp only
  constructor
  · constructor
    · rintro ⟨ask, answer, hv⟩
      exact adaptive_lower t r e k ht ask answer hv
    · intro hk
      exact adaptive_upper t r e k ht hk
  · constructor
    · rintro ⟨ask, answer, hv⟩
      exact fixed_lower t r e k ht ask answer hv
    · intro hk
      exact fixed_upper t r e k ht hk

end PEqualNP.Outside.L_lib_1173_aux

theorem PEqualNP.Outside.L_lib_1173 :
∀ (t r e k : Nat), 0 < t →
  let n := 2 ^ t - 1
  let Site := Fin n
  let Word := Fin r → Finset Site
  let Signing := Fin r → Site → Site → Bool × Bool
  let sites := (Finset.univ : Finset Site).toList
  let blocks := (Finset.univ : Finset (Fin r)).toList
  let reply := fun (A : Finset Word) (s : Signing) => A.toList.any (fun x =>
    blocks.all (fun j => sites.all (fun u => sites.all (fun v =>
      !(decide (u < v)) || ((decide (u ∈ x j), decide (v ∈ x j)) != s j u v)))))
  let valid := fun (ask : Fin k → List Bool → Signing) (answer : List Bool → Bool) =>
    ∀ (A : Finset Word) (flips : Finset (Fin k)), flips.card ≤ e →
      answer ((List.finRange k).foldl (fun hist j =>
        hist ++ [reply A (ask j hist) != decide (j ∈ flips)]) ([] : List Bool)) = decide A.Nonempty
  let M := 2 ^ (r * (n - t))
  ((∃ ask : Fin k → List Bool → Signing, ∃ answer, valid ask answer) ↔ (e + 1) * M + e ≤ k) ∧
  ((∃ ask : Fin k → Signing, ∃ answer, valid (fun j _ => ask j) answer) ↔ (2 * e + 1) * M ≤ k) :=
  PEqualNP.Outside.L_lib_1173_aux.main

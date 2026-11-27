import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PEqualNP.Defs

open scoped BigOperators
namespace PEqualNP.Outside.L_pcx_318_aux

def floorSum (M R : ℕ) : ℕ :=
  let q := M/R
  let u := M%R
  (R-u)*q^2+u*(q+1)^2

theorem integer_tangent (a q : ℕ) :
    (2*q+1)*a ≤ a^2+q*(q+1) := by
  have hh : 0≤((a:ℤ)-q)*((a:ℤ)-q-1) := by
    by_cases h : a≤q
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    · exact mul_nonneg (by omega) (by omega)
  have hi : (2*(q:ℤ)+1)*a ≤ (a:ℤ)^2+q*((q:ℤ)+1) := by nlinarith only [hh]
  exact_mod_cast hi

theorem floor_ident (M R : ℕ) (hR : 0<R) :
    floorSum M R + R*((M/R)*(M/R+1)) = (2*(M/R)+1)*M := by
  let q := M/R
  let u := M%R
  have hu : R-u+u=R := Nat.sub_add_cancel (Nat.le_of_lt (Nat.mod_lt _ hR))
  have hM : u+R*q=M := Nat.mod_add_div M R
  change (R-u)*q^2+u*(q+1)^2+R*(q*(q+1)) = (2*q+1)*M
  calc
    _ = ((R-u)+u)*q^2+u*(2*q+1)+R*(q*(q+1)) := by ring
    _ = R*q^2+u*(2*q+1)+R*(q*(q+1)) := by rw [hu]
    _ = (2*q+1)*(u+R*q) := by ring
    _ = _ := by rw [hM]


section Greedy
variable {I F : Type*} [Fintype I] [DecidableEq I] [Field F] [DecidableEq F]

def degreeOn (A : Matrix I I F) (s : Finset I) (a : I) : ℕ :=
  (s.filter (fun b => A a b ≠ 0)).card

-- Choose the smallest current row support, then remove that support.
-- Removed rows pay for the square of the support size; later pivots form a triangular minor.
theorem greedy (A : Matrix I I F) (hdiag : ∀ a, A a a = 1) (s : Finset I) :
    ∃ (p : List I) (sizes : List ℕ), p.length = sizes.length ∧
      (∀ a ∈ p, a ∈ s) ∧ p.Pairwise (fun a b => A a b = 0) ∧
      sizes.sum = s.card ∧
      (sizes.map (· ^ 2)).sum ≤ ∑ a ∈ s, degreeOn A Finset.univ a := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · let ds := s.image (degreeOn A s)
      have hn : ds.Nonempty := hs.image _
      obtain ⟨a, ha, hd⟩ := Finset.mem_image.mp (Finset.min'_mem ds hn)
      have hm (x) (hx : x ∈ s) : degreeOn A s a ≤ degreeOn A s x := by
        rw [hd]
        exact Finset.min'_le ds _ (Finset.mem_image_of_mem _ hx)
      let t := s.filter (fun b => A a b ≠ 0)
      have ht : t ⊆ s := Finset.filter_subset _ _
      have hat : a ∈ t := Finset.mem_filter.mpr ⟨ha, by simp [hdiag]⟩
      let rem := s \ t
      have hr : rem ⊂ s := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.sdiff_subset, ?_⟩
        intro he
        have hh : a ∈ rem := he ▸ ha
        exact (Finset.mem_sdiff.mp hh).2 hat
      obtain ⟨p, sizes, hlen, hp, hpw, hsum, hcost⟩ := ih rem hr
      refine ⟨a :: p, t.card :: sizes, by simp [hlen], ?_, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact (Finset.mem_sdiff.mp (hp x hx)).1
      · refine List.pairwise_cons.mpr ⟨?_, hpw⟩
        intro x hx
        by_contra h
        rcases Finset.mem_sdiff.mp (hp x hx) with ⟨hx', hnot⟩
        exact hnot (Finset.mem_filter.mpr ⟨hx', h⟩)
      · simp only [List.sum_cons, hsum]
        rw [Nat.add_comm]
        exact Finset.card_sdiff_add_card_eq_card ht
      · have htc : t.card ^ 2 ≤ ∑ x ∈ t, degreeOn A Finset.univ x := by
          calc
            _ = ∑ _x ∈ t, t.card := by simp [pow_two]
            _ ≤ _ := Finset.sum_le_sum fun x hx =>
              (hm x (ht hx)).trans
                (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _)))
        have hsplit :
            (∑ x ∈ rem, degreeOn A Finset.univ x) +
            (∑ x ∈ t, degreeOn A Finset.univ x) =
            ∑ x ∈ s, degreeOn A Finset.univ x := by
          rw [← Finset.sum_union Finset.sdiff_disjoint, Finset.sdiff_union_of_subset ht]
        simp only [List.map_cons, List.sum_cons]
        omega
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      exact ⟨[], [], by simp⟩

theorem pivots_bound (A : Matrix I I F) (hdiag : ∀ a, A a a = 1)
    (p : List I) (hp : p.Pairwise (fun a b => A a b = 0)) : p.length ≤ A.rank := by
  let B := A.submatrix p.get p.get
  have hB : B.IsLowerTriangular := by
    intro i j hij
    exact List.pairwise_iff_get.mp hp i j hij
  have hdet : B.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular B hB]
    simp [B, hdiag]
  have hk := Matrix.rank_of_det_ne_zero (show B.det ≠ 0 by simp [hdet])
  have hr := Matrix.rank_submatrix_le A p.get p.get
  change B.rank ≤ _ at hr
  rw [hk, Fintype.card_fin] at hr
  exact hr

theorem balanced_list (R : ℕ) (hR : 0 < R) (l : List ℕ) (hlen : l.length ≤ R) :
    floorSum l.sum R ≤ (l.map (· ^ 2)).sum := by
  let q := l.sum / R
  have haux (L : List ℕ) :
      (2*q+1)*L.sum ≤ (L.map (· ^ 2)).sum + L.length*(q*(q+1)) := by
    induction L with
    | nil => simp
    | cons a L ih =>
      simp only [List.sum_cons, List.map_cons, List.length_cons]
      rw [Nat.mul_add (2*q+1), Nat.add_mul L.length 1, Nat.one_mul]
      have h := integer_tangent a q
      omega
  have hmono := Nat.mul_le_mul_right (q*(q+1)) hlen
  have hid : floorSum l.sum R + R*(q*(q+1)) = (2*q+1)*l.sum := floor_ident _ _ hR
  have h := haux l
  omega

theorem floor_le_support (A : Matrix I I F) (hdiag : ∀ a, A a a = 1)
    (R : ℕ) (hR : 0 < R) (hrank : A.rank ≤ R) :
    floorSum (Fintype.card I) R ≤ ∑ a, degreeOn A Finset.univ a := by
  obtain ⟨p, sizes, hlen, _, hp, hsum, hcost⟩ := greedy A hdiag Finset.univ
  have hsz : sizes.length ≤ R := hlen ▸ (pivots_bound A hdiag p hp).trans hrank
  have h := (balanced_list R hR sizes hsz).trans hcost
  simpa [hsum] using h


end Greedy

theorem mono_card (k d : ℕ) :
    (Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ d)).card =
      ∑ j ∈ Finset.range (min k d+1), k.choose j := by
  classical
  let g (j : ℕ) := (Finset.univ : Finset (Fin k)).powersetCard j
  have h : Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ d) =
      (Finset.range (min k d+1)).biUnion g := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, g, Finset.mem_powersetCard, Finset.subset_univ]
    constructor
    · intro hd
      have hk : S.card ≤ k := by simpa using Finset.card_le_univ S
      exact ⟨S.card, by omega, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [h, Finset.card_biUnion]
  · simp [g, Finset.card_powersetCard]
  · intro a ha b hb hab
    refine Finset.disjoint_left.mpr ?_
    intro S hs ht
    exact hab ((Finset.mem_powersetCard.mp hs).2.symm.trans (Finset.mem_powersetCard.mp ht).2)

theorem tag_rank {I T J F : Type*} [Fintype I] [Fintype T] [Fintype J] [Field F]
    [DecidableEq T] (tag : I → T) (left : I → J → F) (right : J → I → F) :
    (Matrix.of (fun a b => if tag a = tag b then ∑ j, left a j * right j b else 0)).rank ≤
      Fintype.card T * Fintype.card J := by
  classical
  let L : Matrix I (T × J) F := Matrix.of (fun a tj => if tj.1 = tag a then left a tj.2 else 0)
  let Q : Matrix (T × J) I F := Matrix.of (fun tj b => if tj.1 = tag b then right tj.2 b else 0)
  have he : Matrix.of (fun a b => if tag a = tag b then ∑ j, left a j * right j b else 0) =
    L * Q := by
    ext a b
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    change (if tag a = tag b then ∑ j, left a j * right j b else 0) = ∑ t : T, ∑ j : J,
      (if t = tag a then left a j else 0) * (if t = tag b then right j b else 0)
    symm
    rw [Finset.sum_eq_single (tag a)]
    · by_cases h : tag a = tag b <;> simp [h]
    · intro t _ h
      simp [h]
    · simp
  rw [he, ← Fintype.card_prod]
  exact (Matrix.rank_mul_le_left L Q).trans L.rank_le_card_width


section Fibers
variable {X Z T : Type*} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq Z]
variable (send : X × Z → X) (tag : X × Z → T)

def fiber (x y : X) : Finset Z := Finset.univ.filter (fun z => send (x,z) = y)
def suffixRepeats (a : X × Z) : Finset Z := (fiber send a.1 (send a)).erase a.2

theorem repeat_card (a : X × Z) :
  (suffixRepeats send a).card = (fiber send a.1 (send a)).card - 1 := by
  apply Finset.card_erase_of_mem
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩

def IsError (v : Fin 3 → X × Z) : Prop :=
  (v 0).1 = (v 1).1 ∧ send (v 1) = send (v 2) ∧ tag (v 2) = tag (v 0) ∧
  ¬ (v 0 = v 1 ∧ v 1 = v 2)

def triple {Y : Type*} (a b c : Y) (i : Fin 3) : Y :=
  if i = 0 then a else if i = 1 then b else c

theorem triple_zero {Y : Type*} (a b c : Y) : triple a b c 0 = a := rfl
theorem triple_one {Y : Type*} (a b c : Y) : triple a b c 1 = b := rfl
theorem triple_two {Y : Type*} (a b c : Y) : triple a b c 2 = c := rfl

abbrev RepeatPairs := Σ a : X × Z, ↥(suffixRepeats send a)

noncomputable def repeatWitness (p : RepeatPairs send) : {v // IsError send tag v} := by
  let a := p.1
  let z := p.2.val
  have hz := Finset.mem_erase.mp p.2.property
  have hsend := (Finset.mem_filter.mp hz.2).2
  refine ⟨triple a (a.1,z) a, ?_⟩
  simp only [IsError, triple_zero, triple_one, triple_two]
  refine ⟨True.intro, hsend, True.intro, ?_⟩
  exact fun h => hz.1 (congrArg Prod.snd h.1.symm)

theorem repeatWitness_inj : Function.Injective (repeatWitness send tag) := by
  classical
  intro ⟨a,z⟩ ⟨b,w⟩ h
  have h' := congrArg Subtype.val h
  have hab := congrFun h' 0
  have hzw := congrArg Prod.snd (congrFun h' 1)
  change a = b at hab
  subst b
  exact congrArg (Sigma.mk a) (Subtype.ext hzw)

section Witnesses
variable {O : Type*} [Fintype O] [DecidableEq O] (word : O → X × Z) (hw : Function.Injective word)
variable (B : O → O → Prop) [∀ a b, Decidable (B a b)]
variable (support : ∀ a b, B a b → tag (word b) = tag (word a) ∧ (fiber send (word a).1 (send (word b))).Nonempty)

abbrev SupportPairs := Σ a : O, ↥(Finset.univ.filter (B a))

noncomputable def supportWitness (p : SupportPairs B) :
    Sum O {v // IsError send tag v} := by
  classical
  let a := p.1
  let b := p.2.val
  by_cases hab : a = b
  · exact Sum.inl a
  · obtain ⟨htags, hne⟩ := support a b (Finset.mem_filter.mp p.2.property).2
    let z := Classical.choose hne
    have hz := (Finset.mem_filter.mp (Classical.choose_spec hne)).2
    apply Sum.inr
    refine ⟨triple (word a) ((word a).1,z) (word b), ?_⟩
    simp only [IsError, triple_zero, triple_one, triple_two]
    exact ⟨True.intro, hz, htags, fun h => hab (hw (h.1.trans h.2))⟩

-- Repeats have identical endpoints. Off-diagonal matrix entries have distinct endpoints;
-- diagonal entries are charged to O rather than to false triples.
theorem count_witnesses (word : O → X × Z) (hw : Function.Injective word)
    (B : O → O → Prop) [∀ a b, Decidable (B a b)]
    (support : ∀ a b, B a b → tag (word b) = tag (word a) ∧
      (fiber send (word a).1 (send (word b))).Nonempty)
    [DecidablePred (IsError send tag)] :
    (∑ a : X × Z, ((fiber send a.1 (send a)).card - 1)) +
      (∑ a : O, (Finset.univ.filter (B a)).card) ≤
        Fintype.card O + Fintype.card {v // IsError send tag v} := by
  classical
  let f : RepeatPairs send ⊕ SupportPairs B → O ⊕ {v // IsError send tag v} :=
    Sum.elim (fun p => Sum.inr (repeatWitness send tag p)) (supportWitness send tag word hw B support)
  have hf : Function.Injective f := by
    intro u v e
    cases u with
    | inl u =>
      cases v with
      | inl v =>
        exact congrArg Sum.inl (repeatWitness_inj send tag (Sum.inr.inj e))
      | inr v =>
        rcases v with ⟨b,w⟩
        simp only [f, Sum.elim_inl, Sum.elim_inr, supportWitness] at e
        split at e
        · contradiction
        · have h := congrArg Subtype.val (Sum.inr.inj e)
          have h0 := congrFun h 0
          have h2 := congrFun h 2
          change u.1 = word b at h0
          change u.1 = word w.val at h2
          exact False.elim (‹b ≠ w.val› (hw (h0.symm.trans h2)))
    | inr u =>
      cases v with
      | inl v =>
        rcases u with ⟨a,z⟩
        simp only [f, Sum.elim_inl, Sum.elim_inr, supportWitness] at e
        split at e
        · contradiction
        · have h := congrArg Subtype.val (Sum.inr.inj e)
          have h0 := congrFun h 0
          have h2 := congrFun h 2
          change word a = v.1 at h0
          change word z.val = v.1 at h2
          exact False.elim (‹a ≠ z.val› (hw (h0.trans h2.symm)))
      | inr v =>
        rcases u with ⟨a,z⟩
        rcases v with ⟨b,w⟩
        simp only [f, Sum.elim_inr, supportWitness] at e
        split at e <;> split at e
        · have h := Sum.inl.inj e
          have hh : z.val = w.val := ‹a = z.val›.symm.trans (h.trans ‹b = w.val›)
          subst b
          exact congrArg (fun zz => Sum.inr (Sigma.mk a zz)) (Subtype.ext hh)
        · contradiction
        · contradiction
        · have h := congrArg Subtype.val (Sum.inr.inj e)
          have h0 : word a = word b := congrFun h 0
          have h2 : word z.val = word w.val := congrFun h 2
          have hab := hw h0
          have hz := hw h2
          subst b
          exact congrArg (fun zz => Sum.inr (Sigma.mk a zz)) (Subtype.ext hz)
  have h := Fintype.card_le_of_injective f hf
  simpa [RepeatPairs, SupportPairs, Fintype.card_sigma, repeat_card, Fintype.card_coe, Fintype.card_subtype] using h

end Witnesses

theorem repeat_le_error [DecidablePred (IsError send tag)] :
    (∑ a : X × Z, ((fiber send a.1 (send a)).card - 1)) ≤
        Fintype.card {v // IsError send tag v} := by
  have h := Fintype.card_le_of_injective (repeatWitness send tag) (repeatWitness_inj send tag)
  simpa [RepeatPairs, Fintype.card_sigma, repeat_card, Fintype.card_coe] using h

end Fibers
end PEqualNP.Outside.L_pcx_318_aux

open PEqualNP.Outside.L_pcx_318_aux

set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.L_pcx_318 : ∀ (k r c d : ℕ),
  let F := ZMod 2
  let X := Fin k → F
  let Z := Fin r → F
  let W := X × Z
  ∀ (send : W → X) (tag : W → Fin c → Bool) (prefixes : Finset X),
    let count := fun (u y : X) => (Finset.univ.filter (fun z : Z => send (u,z) = y)).card
    (∀ u ∈ prefixes, ∃ coeff : Finset (Fin k) → F, ∀ y : X,
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ d),
        coeff S * ∏ j ∈ S, y j) = (count u y : F)) →
    let M := (Finset.univ.filter (fun w : W =>
      w.1 ∈ prefixes ∧ count w.1 (send w) % 2 = 1)).card
    let R := 2^c * ∑ j ∈ Finset.range (min k d + 1), k.choose j
    let q := M/R
    let u := M % R
    let floorSum := (R-u)*q^2 + u*(q+1)^2
    let repeats := ∑ a : W, (count a.1 (send a) - 1)
    let errors := (Finset.univ.filter (fun v : Fin 3 → W =>
      (v 0).1 = (v 1).1 ∧ send (v 1) = send (v 2) ∧ tag (v 2) = tag (v 0) ∧
      ¬(v 0 = v 1 ∧ v 1 = v 2))).card
    repeats + (floorSum-M) ≤ errors ∧ 2^r * prefixes.card ≤ R + errors := by
  classical
  intro k r c d F X Z W send tag prefixes count hc M R q u floorS repeats errors
  let oddW := Finset.univ.filter (fun w : W => w.1 ∈ prefixes ∧ count w.1 (send w) % 2 = 1)
  let O := ↥oddW
  let mono := Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ d)
  let J := ↥mono
  let word : O → W := Subtype.val
  let coeff (a : O) := Classical.choose (hc (word a).1 (Finset.mem_filter.mp a.property).2.1)
  have hcoeff (a : O) (y : X) :
      (∑ j : J, coeff a j.val * ∏ i ∈ j.val, y i) = (count (word a).1 y : F) := by
    exact (Finset.sum_coe_sort mono (fun S => coeff a S * ∏ i ∈ S, y i)).trans
      (Classical.choose_spec (hc (word a).1 (Finset.mem_filter.mp a.property).2.1) y)
  let A : Matrix O O F := Matrix.of (fun a b =>
    if tag (word a) = tag (word b) then (count (word a).1 (send (word b)) : F) else 0)
  have hRdef : Fintype.card (Fin c → Bool) * Fintype.card J = R := by
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    rw [show Fintype.card J = mono.card from Fintype.card_coe mono]
    change 2 ^ c * (Finset.univ.filter (fun S : Finset (Fin k) => S.card ≤ d)).card = R
    rw [mono_card]
  have hrank : A.rank ≤ R := by
    rw [← hRdef]
    have hEq : A = Matrix.of (fun a b => if tag (word a) = tag (word b)
        then ∑ j : J, coeff a j.val * ∏ i ∈ j.val, (send (word b)) i else 0) := by
      apply Matrix.ext
      intro a b
      simp only [A, Matrix.of_apply]
      rw [hcoeff]
    rw [hEq]
    exact tag_rank (I := O) (J := J) (F := F) (fun a => tag (word a)) (fun a j => coeff a j.val)
      (fun j b => ∏ i ∈ j.val, (send (word b)) i)
  have hrpos : 0 < R := by
    rw [← hRdef]
    letI : Nonempty (Fin c → Bool) := ⟨fun _ => false⟩
    letI : Nonempty J := ⟨⟨∅, by simp [mono]⟩⟩
    exact Nat.mul_pos Fintype.card_pos Fintype.card_pos
  have hdiag (a : O) : A a a = 1 := by
    have ha := (Finset.mem_filter.mp a.property).2.2
    change count (word a).1 (send (word a)) % 2 = 1 at ha
    change (if tag (word a) = tag (word a) then
      (count (word a).1 (send (word a)) : ZMod 2) else 0) = 1
    rw [ite_eq_left rfl, ← ZMod.natCast_mod (count (word a).1 (send (word a))) 2, ha]
    rfl
  have hM : Fintype.card O = M := Fintype.card_coe _
  have hfloor : floorS ≤ ∑ a : O, degreeOn A Finset.univ a := by
    have h := floor_le_support A hdiag R hrpos hrank
    rw [hM] at h
    exact h
  have hsup (a b : O) (h : A a b ≠ 0) :
      tag (word b) = tag (word a) ∧
        (fiber send (word a).1 (send (word b))).Nonempty := by
    change (if tag (word a) = tag (word b) then
      (count (word a).1 (send (word b)) : F) else 0) ≠ 0 at h
    split at h
    · rename_i htag
      refine ⟨htag.symm, Finset.card_pos.mp ?_⟩
      change 0 < count (word a).1 (send (word b))
      by_contra hh
      have hz : count (word a).1 (send (word b)) = 0 := by omega
      exact h (by simp [hz])
    · exact False.elim (h rfl)
  have he : Fintype.card {v // IsError send tag v} = errors := by
    calc
      _ = (Finset.univ.filter (IsError send tag)).card := Fintype.card_subtype _
      _ = _ := by
        unfold errors
        congr 1
        ext v
        simp [IsError]
  have hrep_eq : (∑ a : W, ((fiber send a.1 (send a)).card - 1)) = repeats := by
    unfold repeats
    apply Finset.sum_congr rfl
    intro a _
    apply congrArg (fun n : ℕ => n - 1)
    apply congrArg Finset.card
    ext z
    simp [fiber]
  let B (a b : O) : Prop := A a b ≠ 0
  letI decB : ∀ a b, Decidable (B a b) :=
    fun a b => inferInstanceAs (Decidable (A a b ≠ 0))
  have hsupport_eq :
      (∑ a : O, (Finset.univ.filter (B a)).card) =
        ∑ a : O, degreeOn A Finset.univ a := by
    apply Finset.sum_congr rfl
    intro a _
    apply congrArg Finset.card
    ext b
    simp [B]
  have hraw := count_witnesses send tag word Subtype.val_injective B hsup
  rw [hM, he, hrep_eq] at hraw
  have hcount : repeats + (∑ a : O, degreeOn A Finset.univ a) ≤ M + errors := by
    calc
      _ = repeats + (∑ a : O, (Finset.univ.filter (B a)).card) :=
        congrArg (repeats + ·) hsupport_eq.symm
      _ ≤ _ := hraw
  have hrep := repeat_le_error send tag
  rw [he, hrep_eq] at hrep
  have hfirst : repeats + (floorS - M) ≤ errors := by omega
  refine ⟨hfirst, ?_⟩
  have htwice : 2*M ≤ R+floorS := by
    have hu : R-u+u=R := Nat.sub_add_cancel (Nat.le_of_lt (Nat.mod_lt _ hrpos))
    have hm : u+R*q=M := Nat.mod_add_div M R
    have hsq (a : ℕ) : 2*a ≤ a^2+1 := by
      have hp : 0 ≤ ((a:ℤ)-1)^2 := sq_nonneg _
      have hh : 2*(a:ℤ) ≤ (a:ℤ)^2+1 := by linarith only [hp]
      exact_mod_cast hh
    change 2*M ≤ R+((R-u)*q^2+u*(q+1)^2)
    calc
      2*M = (R-u)*(2*q)+u*(2*(q+1)) := by
        rw [← hm]
        calc
          _ = ((R-u)+u)*(2*q)+u*2 := by rw [hu]; ring
          _ = _ := by ring
      _ ≤ (R-u)*(q^2+1)+u*((q+1)^2+1) := by
        exact Nat.add_le_add (Nat.mul_le_mul_left _ (hsq q)) (Nat.mul_le_mul_left _ (hsq (q+1)))
      _ = R+((R-u)*q^2+u*(q+1)^2) := by
        calc
          _ = ((R-u)+u)+((R-u)*q^2+u*(q+1)^2) := by ring
          _ = _ := by rw [hu]
  have hN : 2^r * prefixes.card ≤ M + repeats := by
    have hAP : Fintype.card {w : W // w.1 ∈ prefixes} = 2^r * prefixes.card := by
      let eqv : {w : W // w.1 ∈ prefixes} ≃ (↥prefixes × Z) :=
        ⟨fun w => (⟨w.val.1,w.property⟩,w.val.2), fun w => ⟨(w.1.val,w.2),w.1.property⟩,
          fun _ => rfl, fun _ => rfl⟩
      rw [Fintype.card_congr eqv]
      have hf : Fintype.card F = 2 := ZMod.card 2
      simp [Z, hf, Nat.mul_comm]
    have ht : (∑ a : W, if a.1 ∈ prefixes then (1 : ℕ) else 0) ≤
        (∑ a : W, if a.1 ∈ prefixes ∧ count a.1 (send a) % 2 = 1 then (1 : ℕ) else 0) +
          ∑ a : W, (count a.1 (send a) - 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro a _
      by_cases h : a.1 ∈ prefixes
      · by_cases hn : count a.1 (send a) % 2 = 1
        · simp [h, hn]
        · have hp : 0 < count a.1 (send a) :=
            Finset.card_pos.mpr ⟨a.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩⟩
          simp only [h, hn, true_and, ite_true, ite_false, zero_add]
          omega
      · simp [h]
    simp only [Finset.sum_boole] at ht
    rw [← Fintype.card_subtype (fun a : W => a.1 ∈ prefixes), hAP] at ht
    exact ht
  omega

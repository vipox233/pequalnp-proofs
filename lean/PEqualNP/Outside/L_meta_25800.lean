import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25800_aux
namespace Upper

open scoped BigOperators

abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F

def first {s : ℕ} (i : Fin s) : Fin (2*s) := ⟨2*i.val, by omega⟩
def second {s : ℕ} (i : Fin s) : Fin (2*s) := ⟨2*i.val+1, by omega⟩

theorem first_injective {s : ℕ} : Function.Injective (@first s) := by
  intro i j h
  have h' := congrArg Fin.val h
  apply Fin.ext
  simp only [first] at h'
  omega

theorem second_injective {s : ℕ} : Function.Injective (@second s) := by
  intro i j h
  have h' := congrArg Fin.val h
  apply Fin.ext
  simp only [second] at h'
  omega

theorem first_ne_second {s : ℕ} (i j : Fin s) : first i ≠ second j := by
  intro h
  have h' := congrArg Fin.val h
  simp only [first, second] at h'
  omega

theorem coordinate {s : ℕ} (k : Fin (2*s)) :
    (∃ j, first j = k) ∨ (∃ j, second j = k) := by
  let j : Fin s := ⟨k.val / 2, by omega⟩
  by_cases h : k.val % 2 = 0
  · left
    refine ⟨j, Fin.ext ?_⟩
    change 2*(k.val/2) = k.val
    omega
  · right
    refine ⟨j, Fin.ext ?_⟩
    change 2*(k.val/2)+1 = k.val
    omega

def axis {n : ℕ} (i : Fin n) : Vec n := fun j => if j = i then 1 else 0

theorem first_eq_iff {s : ℕ} (i j : Fin s) : first i = first j ↔ i = j :=
  first_injective.eq_iff

theorem second_eq_iff {s : ℕ} (i j : Fin s) : second i = second j ↔ i = j :=
  second_injective.eq_iff

def part {s : ℕ} (j : Fin s) (a b : F) : Vec (2*s) :=
  fun i => if i = first j then a else if i = second j then b else 0

theorem part_first {s : ℕ} (i j : Fin s) (a b : F) :
    part j a b (first i) = if i = j then a else 0 := by
  simp [part, first_eq_iff, first_ne_second]

theorem part_second {s : ℕ} (i j : Fin s) (a b : F) :
    part j a b (second i) = if i = j then b else 0 := by
  simp [part, second_eq_iff, Ne.symm (first_ne_second j i)]

theorem part_zero {s : ℕ} (j : Fin s) : part j 0 0 = 0 := by
  funext i
  simp [part]

theorem part_one_zero {s : ℕ} (j : Fin s) : part j 1 0 = axis (first j) := by
  funext i
  simp [part, axis]

theorem part_zero_one {s : ℕ} (j : Fin s) : part j 0 1 = axis (second j) := by
  funext i
  by_cases h : i = first j
  · subst i
    simp [part, axis, first_ne_second]
  · simp [part, axis, h]

def fullPair {s : ℕ} (j : Fin s) : Vec (2*s) := part j 1 1

theorem fullPair_sum {s : ℕ} (j : Fin s) :
    fullPair j = part j 1 0 + part j 0 1 := by
  funext i
  by_cases h : i = first j <;> simp [fullPair, part, h]

def quad {s : ℕ} (x : Vec (2*s)) : F := ∑ i : Fin s, x (first i) * x (second i)

theorem quad_zero {s : ℕ} : quad (0 : Vec (2*s)) = 0 := by simp [quad]

theorem quad_part {s : ℕ} (j : Fin s) (a b : F) : quad (part j a b) = a*b := by
  classical
  simp [quad, part_first, part_second]

theorem quad_disjoint {s : ℕ} (x y : Vec (2*s))
    (h : ∀ i : Fin s, (x (first i) = 0 ∧ x (second i) = 0) ∨
        (y (first i) = 0 ∧ y (second i) = 0)) :
    quad (x+y) = quad x + quad y := by
  simp only [quad, ← Finset.sum_add_distrib, Pi.add_apply]
  apply Finset.sum_congr rfl
  intro i _
  rcases h i with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> simp [h₁,h₂]

theorem quad_part_add {s : ℕ} {i j : Fin s} (h : i ≠ j) (a b c d : F) :
    quad (part i a b + part j c d) = quad (part i a b) + quad (part j c d) := by
  apply quad_disjoint
  intro l
  by_cases e : l = i
  · subst l
    right
    simp [part_first, part_second, h]
  · left
    simp [part_first, part_second, e]

def word {k : ℕ} (x : Vec k) (a : F) : Vec (k+1) := Fin.snoc x a

theorem word_add {k : ℕ} (x y : Vec k) (a b : F) :
    word x a + word y b = word (x+y) (a+b) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [word]
  | cast i => simp [word]

theorem word_zero {k : ℕ} : word (0 : Vec k) 0 = 0 := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [word]
  | cast i => simp [word]

theorem word_axis {k : ℕ} (j : Fin k) : word (axis j) 0 = axis j.castSucc := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [word, axis, Ne.symm (Fin.castSucc_ne_last j)]
  | cast i => simp [word, axis]

theorem word_phase {k : ℕ} : word (0 : Vec k) 1 = axis (Fin.last k) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [word, axis]
  | cast i => simp [word, axis]

def lift {s : ℕ} (x : Vec (2*s)) : Vec (2*s+1) := word x (quad x)
def wrong {s : ℕ} (x : Vec (2*s)) : Vec (2*s+1) := word x (quad x + 1)

theorem lift_zero {s : ℕ} : lift (0 : Vec (2*s)) = 0 := by
  simp [lift, quad_zero, word_zero]

theorem lift_part_add {s : ℕ} {i j : Fin s} (h : i ≠ j) (a b c d : F) :
    lift (part i a b + part j c d) = lift (part i a b) + lift (part j c d) := by
  simp [lift, word_add, quad_part_add h]

theorem wrong_phase {s : ℕ} (x : Vec (2*s)) :
    wrong x = lift x + axis (Fin.last (2*s)) := by
  rw [← word_phase, lift, word_add, add_zero, wrong]

theorem bit_cases (a : F) : a = 0 ∨ a = 1 := (by decide : ∀ a : F, a = 0 ∨ a = 1) a

theorem double_bit (a : F) : a + a = 0 := (by decide : ∀ a : F, a + a = 0) a

theorem double_vec {k : ℕ} (x : Vec k) : x + x = 0 := by
  funext i
  exact double_bit (x i)

theorem wrong_fullPair {s : ℕ} (j : Fin s) :
    wrong (fullPair j) = lift (part j 1 0) + lift (part j 0 1) := by
  have h : (1 : F) + 1 = 0 := double_bit 1
  simp only [wrong, lift, fullPair, quad_part, mul_one, mul_zero, h, word_add, add_zero]
  rw [← fullPair_sum, fullPair]

theorem lift_part_first {s : ℕ} (j : Fin s) :
    lift (part j 1 0) = axis (first j).castSucc := by
  rw [lift, quad_part, mul_zero, part_one_zero, word_axis]

theorem lift_part_second {s : ℕ} (j : Fin s) :
    lift (part j 0 1) = axis (second j).castSucc := by
  rw [lift, quad_part, zero_mul, part_zero_one, word_axis]

theorem lift_fullPair_ne_wrong {s : ℕ} (j : Fin s) :
    lift (fullPair j) = wrong (fullPair j) + axis (Fin.last (2*s)) := by
  rw [wrong_phase, add_assoc, double_vec, add_zero]

inductive Reachable {W : Type} [DecidableEq W] [Add W]
    (initial : Set W) (allowed : Finset W) : W → Prop
  | base {w} : w ∈ initial → Reachable initial allowed w
  | add {x y} : x+y ∈ allowed → Reachable initial allowed x →
      Reachable initial allowed y → Reachable initial allowed (x+y)

def initial (k : ℕ) : Set (Vec (k+1)) := {0} ∪ Set.range axis

def seeds (k : ℕ) : Finset (Vec (k+1)) :=
  insert 0 (Finset.univ.image fun i : Fin k => axis i.castSucc)

def graph (s : ℕ) : Finset (Vec (2*s+1)) := Finset.univ.image (@lift s)

def extras {s : ℕ} (seed : Fin s) (errors : Finset (Vec (2*s))) :
    Finset (Vec (2*s+1)) :=
  if errors = ∅ then {wrong (fullPair seed)} else errors.image wrong

def graphAllowed {s : ℕ} (seed : Fin s) (errors : Finset (Vec (2*s))) :
    Finset (Vec (2*s+1)) := (graph s ∪ extras seed errors) \ seeds (2*s)

theorem seeds_initial {k : ℕ} {w : Vec (k+1)} (h : w ∈ seeds k) : w ∈ initial k := by
  rcases Finset.mem_insert.mp h with rfl | h
  · exact Or.inl rfl
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨i.castSucc, rfl⟩

theorem add_reachable {s : ℕ} {seed : Fin s} {errors : Finset (Vec (2*s))}
    {x y : Vec (2*s+1)} (h : x+y ∈ graph s ∪ extras seed errors)
    (hx : Reachable (initial (2*s)) (graphAllowed seed errors) x)
    (hy : Reachable (initial (2*s)) (graphAllowed seed errors) y) :
    Reachable (initial (2*s)) (graphAllowed seed errors) (x+y) := by
  by_cases hin : x+y ∈ seeds (2*s)
  · exact .base (seeds_initial hin)
  · exact .add (Finset.mem_sdiff.mpr ⟨h, hin⟩) hx hy

theorem add_lift_reachable {s : ℕ} {seed : Fin s} {errors : Finset (Vec (2*s))}
    {x y : Vec (2*s+1)} {z : Vec (2*s)} (h : lift z = x+y)
    (hx : Reachable (initial (2*s)) (graphAllowed seed errors) x)
    (hy : Reachable (initial (2*s)) (graphAllowed seed errors) y) :
    Reachable (initial (2*s)) (graphAllowed seed errors) (lift z) := by
  rw [h]
  apply add_reachable _ hx hy
  rw [← h]
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩)

theorem add_wrong_reachable {s : ℕ} {seed : Fin s} {errors : Finset (Vec (2*s))}
    {x y : Vec (2*s+1)} {z : Vec (2*s)} (h : wrong z = x+y)
    (hz : wrong z ∈ extras seed errors)
    (hx : Reachable (initial (2*s)) (graphAllowed seed errors) x)
    (hy : Reachable (initial (2*s)) (graphAllowed seed errors) y) :
    Reachable (initial (2*s)) (graphAllowed seed errors) (wrong z) := by
  rw [h]
  exact add_reachable (h ▸ Finset.mem_union_right (graph s) hz) hx hy

theorem phase_reachable {s : ℕ} (seed : Fin s) (errors : Finset (Vec (2*s))) :
    Reachable (initial (2*s)) (graphAllowed seed errors) (axis (Fin.last (2*s))) :=
  .base (Or.inr ⟨_, rfl⟩)

theorem first_reachable {s : ℕ} (seed : Fin s) (errors : Finset (Vec (2*s))) (i : Fin s) :
    Reachable (initial (2*s)) (graphAllowed seed errors) (lift (part i 1 0)) := by
  rw [lift_part_first]
  exact .base (Or.inr ⟨_, rfl⟩)

theorem second_reachable {s : ℕ} (seed : Fin s) (errors : Finset (Vec (2*s))) (i : Fin s) :
    Reachable (initial (2*s)) (graphAllowed seed errors) (lift (part i 0 1)) := by
  rw [lift_part_second]
  exact .base (Or.inr ⟨_, rfl⟩)

theorem wrong_seed_mem {s : ℕ} (seed : Fin s) (errors : Finset (Vec (2*s)))
    (hseed : errors = ∅ ∨ fullPair seed ∈ errors) :
    wrong (fullPair seed) ∈ extras seed errors := by
  classical
  by_cases h : errors = ∅
  · simp [extras, h]
  · exact by
      simp only [extras, h, ite_false]
      exact Finset.mem_image.mpr ⟨fullPair seed, hseed.resolve_left h, rfl⟩

theorem full_reachable {s : ℕ} (seed : Fin s) (errors : Finset (Vec (2*s)))
    (hseed : errors = ∅ ∨ fullPair seed ∈ errors) (i : Fin s) :
    Reachable (initial (2*s)) (graphAllowed seed errors) (lift (fullPair i)) := by
  have hwrong := add_wrong_reachable (wrong_fullPair seed) (wrong_seed_mem seed errors hseed)
    (first_reachable seed errors seed) (second_reachable seed errors seed)
  have hseed' := add_lift_reachable (lift_fullPair_ne_wrong seed) hwrong (phase_reachable seed errors)
  by_cases hi : i = seed
  · simpa [hi] using hseed'
  · have hfirst := add_lift_reachable (lift_part_add (Ne.symm hi) 1 0 1 0)
      (first_reachable seed errors seed) (first_reachable seed errors i)
    have hsecond := add_lift_reachable (lift_part_add (Ne.symm hi) 0 1 0 1)
      (second_reachable seed errors seed) (second_reachable seed errors i)
    have hcross : lift (fullPair seed + fullPair i) =
        lift (part seed 1 0 + part i 1 0) + lift (part seed 0 1 + part i 0 1) := by
      have hcoords : fullPair seed + fullPair i =
          (part seed 1 0 + part i 1 0) + (part seed 0 1 + part i 0 1) := by
        rw [fullPair_sum seed, fullPair_sum i, add_add_add_comm]
      have hq₁ : quad (fullPair seed + fullPair i) = 0 := by
        simp [fullPair, quad_part_add (Ne.symm hi), quad_part, double_bit]
      have hq₂ : quad (part seed 1 0 + part i 1 0) = 0 := by
        simp [quad_part_add (Ne.symm hi), quad_part]
      have hq₃ : quad (part seed 0 1 + part i 0 1) = 0 := by
        simp [quad_part_add (Ne.symm hi), quad_part]
      rw [lift, hq₁, lift, hq₂, lift, hq₃, word_add, add_zero, hcoords]
    have hunion := add_lift_reachable hcross hfirst hsecond
    have hsplit : lift (fullPair i) = lift (fullPair seed) + lift (fullPair seed + fullPair i) := by
      have h := lift_part_add (Ne.symm hi) (1:F) 1 1 1
      change lift (fullPair seed + fullPair i) = lift (fullPair seed) + lift (fullPair i) at h
      rw [h, ← add_assoc, double_vec, zero_add]
    exact add_lift_reachable hsplit hseed' hunion

theorem part_reachable {s : ℕ} (seed : Fin s) (errors : Finset (Vec (2*s)))
    (hseed : errors = ∅ ∨ fullPair seed ∈ errors) (i : Fin s) (a b : F) :
    Reachable (initial (2*s)) (graphAllowed seed errors) (lift (part i a b)) := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl
  · rw [part_zero, lift_zero]
    exact .base (Or.inl rfl)
  · exact second_reachable seed errors i
  · exact first_reachable seed errors i
  · exact full_reachable seed errors hseed i

def pieces {s : ℕ} (t : Finset (Fin s)) (x : Vec (2*s)) : Vec (2*s) :=
  ∑ j ∈ t, part j (x (first j)) (x (second j))

theorem pieces_first {s : ℕ} (t : Finset (Fin s)) (x : Vec (2*s)) (i : Fin s) :
    pieces t x (first i) = if i ∈ t then x (first i) else 0 := by
  classical
  simp [pieces, Finset.sum_apply, part_first, eq_comm (a:=i)]

theorem pieces_second {s : ℕ} (t : Finset (Fin s)) (x : Vec (2*s)) (i : Fin s) :
    pieces t x (second i) = if i ∈ t then x (second i) else 0 := by
  classical
  simp [pieces, Finset.sum_apply, part_second, eq_comm (a:=i)]

theorem pieces_univ {s : ℕ} (x : Vec (2*s)) : pieces Finset.univ x = x := by
  funext k
  rcases coordinate k with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [pieces_first]
  · simp [pieces_second]

theorem pieces_reachable {s : ℕ} (seed : Fin s) (errors : Finset (Vec (2*s)))
    (hseed : errors = ∅ ∨ fullPair seed ∈ errors) (x : Vec (2*s)) (t : Finset (Fin s)) :
    Reachable (initial (2*s)) (graphAllowed seed errors) (lift (pieces t x)) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have hc : pieces (∅ : Finset (Fin s)) x = 0 := by simp [pieces]
    rw [hc, lift_zero]
    exact .base (Or.inl rfl)
  | @insert i t hi ih =>
    have hsum : pieces (insert i t) x = part i (x (first i)) (x (second i)) + pieces t x := by
      simp [pieces, Finset.sum_insert hi]
    have hquad : quad (pieces (insert i t) x) =
        quad (part i (x (first i)) (x (second i))) + quad (pieces t x) := by
      rw [hsum]
      apply quad_disjoint
      intro j
      by_cases h : j = i
      · subst j
        right
        simp [pieces_first, pieces_second, hi]
      · left
        simp [part_first, part_second, h]
    have hcombine : lift (pieces (insert i t) x) =
        lift (part i (x (first i)) (x (second i))) + lift (pieces t x) := by
      unfold lift
      rw [hquad, word_add, hsum]
    exact add_lift_reachable hcombine (part_reachable seed errors hseed i _ _) ih

theorem graph_reachable {s : ℕ} (seed : Fin s) (errors : Finset (Vec (2*s)))
    (hseed : errors = ∅ ∨ fullPair seed ∈ errors) (x : Vec (2*s)) :
    Reachable (initial (2*s)) (graphAllowed seed errors) (lift x) := by
  simpa only [pieces_univ] using pieces_reachable seed errors hseed x Finset.univ

theorem error_reachable {s : ℕ} (seed : Fin s) (errors : Finset (Vec (2*s)))
    (hseed : errors = ∅ ∨ fullPair seed ∈ errors) {x : Vec (2*s)} (hx : x ∈ errors) :
    Reachable (initial (2*s)) (graphAllowed seed errors) (wrong x) := by
  have hn : errors ≠ ∅ := by
    intro h
    rw [h] at hx
    exact Finset.notMem_empty x hx
  apply add_wrong_reachable (wrong_phase x) _ (graph_reachable seed errors hseed x)
    (phase_reachable seed errors)
  simp only [extras, hn, ite_false]
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem axis_injective {k : ℕ} : Function.Injective (@axis k) := by
  intro i j h
  by_contra hne
  have h' := congrFun h i
  simp [axis, hne] at h'

theorem axis_ne_zero {k : ℕ} (i : Fin k) : axis i ≠ 0 := by
  intro h
  have h' := congrFun h i
  simp [axis] at h'

theorem lift_injective {s : ℕ} : Function.Injective (@lift s) := by
  intro x y h
  funext i
  have h' := congrFun h i.castSucc
  simpa only [lift, word, Fin.snoc_castSucc] using h'

theorem seed_mem_graph {s : ℕ} (w : Vec (2*s+1)) (h : w ∈ seeds (2*s)) :
    w ∈ graph s := by
  rcases Finset.mem_insert.mp h with rfl | h
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, lift_zero⟩
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    rcases coordinate i with ⟨j,rfl⟩ | ⟨j,rfl⟩
    · exact Finset.mem_image.mpr ⟨part j 1 0, Finset.mem_univ _, lift_part_first j⟩
    · exact Finset.mem_image.mpr ⟨part j 0 1, Finset.mem_univ _, lift_part_second j⟩

theorem seeds_card (k : ℕ) : (seeds k).card = k+1 := by
  unfold seeds
  rw [Finset.card_insert_of_notMem]
  · have hinj : Function.Injective (fun i : Fin k => axis i.castSucc) :=
      axis_injective.comp (Fin.castSucc_injective k)
    rw [Finset.card_image_of_injective _ hinj]
    simp
  · intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    exact axis_ne_zero i.castSucc hi

theorem graph_card (s : ℕ) : (graph s).card = 2^(2*s) := by
  unfold graph
  rw [Finset.card_image_of_injective _ lift_injective]
  simp [Vec, F]

theorem extras_card_le {s : ℕ} (seed : Fin s) (errors : Finset (Vec (2*s))) :
    (extras seed errors).card ≤ max 1 errors.card := by
  by_cases h : errors = ∅
  · simp [extras, h]
  · simp only [extras, h, ite_false]
    exact Finset.card_image_le.trans (le_max_right _ _)

theorem graphAllowed_card {s : ℕ} (seed : Fin s) (errors : Finset (Vec (2*s))) :
    (graphAllowed seed errors).card ≤ 2^(2*s)-1-2*s+max 1 errors.card := by
  have hsub : seeds (2*s) ⊆ graph s := fun w hw => seed_mem_graph w hw
  have hroom : 2*s+1 ≤ 2^(2*s) := by
    simpa only [seeds_card, graph_card] using Finset.card_le_card hsub
  have hub := Finset.card_union_le (graph s) (extras seed errors)
  rw [graph_card] at hub
  have he := extras_card_le seed errors
  unfold graphAllowed
  rw [Finset.card_sdiff_of_subset (fun w hw => Finset.mem_union_left _ (hsub hw)), seeds_card]
  omega

def polar {s : ℕ} (x y : Vec (2*s)) : F :=
  ∑ i : Fin s, (x (first i) * y (second i) + x (second i) * y (first i))

theorem quad_translate {s : ℕ} (a b c : Vec (2*s)) :
    quad (a+b+c) + quad a + quad b = polar (a+c) (b+c) + quad c := by
  simp only [quad, polar, ← Finset.sum_add_distrib, Pi.add_apply]
  apply Finset.sum_congr rfl
  intro i _
  have identity : ∀ a₀ a₁ b₀ b₁ c₀ c₁ : F,
      (a₀+b₀+c₀)*(a₁+b₁+c₁) + a₀*a₁ + b₀*b₁ =
        ((a₀+c₀)*(b₁+c₁) + (a₁+c₁)*(b₀+c₀)) + c₀*c₁ := by decide
  exact identity (a (first i)) (a (second i)) (b (first i)) (b (second i))
    (c (first i)) (c (second i))

theorem lift_eq_zero {s : ℕ} {x : Vec (2*s)} :
    lift x = 0 ↔ x = 0 := by
  rw [← lift_zero, lift_injective.eq_iff]

theorem sum_pairs {M : Type} [AddCommMonoid M] {s : ℕ} (f : Fin (2*s) → M) :
    (∑ i, f i) = ∑ j : Fin s, (f (first j) + f (second j)) := by
  let e : Fin s ⊕ Fin s → Fin (2*s) := Sum.elim first second
  have he : Function.Bijective e := by
    constructor
    · intro i j hij
      rcases i with i | i <;> rcases j with j | j
      · exact congrArg Sum.inl (first_injective hij)
      · exact (first_ne_second i j hij).elim
      · exact (first_ne_second j i hij.symm).elim
      · exact congrArg Sum.inr (second_injective hij)
    · intro i
      rcases coordinate i with ⟨j, hj⟩ | ⟨j, hj⟩
      · exact ⟨Sum.inl j, hj⟩
      · exact ⟨Sum.inr j, hj⟩
  rw [← he.sum_comp f, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  rfl

def pairSwap {s : ℕ} (i : Fin (2*s)) : Fin (2*s) :=
  if h : i.val % 2 = 0 then ⟨i.val+1, by omega⟩ else ⟨i.val-1, by omega⟩

theorem pairSwap_first {s : ℕ} (j : Fin s) : pairSwap (first j) = second j := by
  apply Fin.ext
  simp [pairSwap, first, second]

theorem pairSwap_second {s : ℕ} (j : Fin s) : pairSwap (second j) = first j := by
  apply Fin.ext
  simp [pairSwap, first, second]

theorem pairSwap_involutive {s : ℕ} : Function.Involutive (@pairSwap s) := by
  intro i
  rcases coordinate i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;> simp [pairSwap_first, pairSwap_second]

def swap {s : ℕ} : Vec (2*s) ≃+ Vec (2*s) where
  toFun x := x ∘ pairSwap
  invFun x := x ∘ pairSwap
  left_inv x := funext fun i => congrArg x (pairSwap_involutive i)
  right_inv x := funext fun i => congrArg x (pairSwap_involutive i)
  map_add' _ _ := rfl

theorem polar_swap {s : ℕ} (a b : Vec (2*s)) :
    polar a (swap b) = ∑ i, a i * b i := by
  rw [sum_pairs]
  simp [polar, swap, pairSwap_first, pairSwap_second]

end Upper
end PEqualNP.Outside.L_meta_25800_aux

namespace PEqualNP.Outside.L_meta_25800_aux
namespace Upper

open scoped BigOperators

def dot {k : ℕ} (x y : Vec k) : F := ∑ i, x i * y i

theorem dot_comm {k : ℕ} (x y : Vec k) : dot x y = dot y x := by
  simp only [dot, mul_comm]

theorem dot_add_right {k : ℕ} (x y z : Vec k) :
    dot x (y+z) = dot x y + dot x z := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot_zero_left {k : ℕ} (x : Vec k) : dot 0 x = 0 := by simp [dot]

theorem dot_axis {k : ℕ} (x : Vec k) (i : Fin k) : dot (axis i) x = x i := by
  simp [dot, axis, ite_mul]

def shear {k : ℕ} (j : Fin k) (v : Vec k) (h : v j = 0) : Vec k ≃+ Vec k where
  toFun x i := x i + x j * v i
  invFun x i := x i + x j * v i
  left_inv x := by
    funext i
    simp only [h, mul_zero, add_zero, add_assoc, ← add_mul, double_bit, zero_mul]
  right_inv x := by
    funext i
    simp only [h, mul_zero, add_zero, add_assoc, ← add_mul, double_bit, zero_mul]
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, add_mul]
    ac_rfl

theorem axis_self {k : ℕ} (j : Fin k) : axis j j = 1 := by simp [axis]

theorem shear_to_axis {k : ℕ} (v : Vec k) (j : Fin k) (hj : v j = 1) :
    shear j (v+axis j) (by simp [hj, axis_self, double_bit]) v = axis j := by
  funext i
  change v i + v j * (v i + axis j i) = axis j i
  rw [hj, one_mul, ← add_assoc, double_bit, zero_add]

theorem shear_from_axis {k : ℕ} (v : Vec k) (j : Fin k) (hj : v j = 1) :
    shear j (v+axis j) (by simp [hj, axis_self, double_bit]) (axis j) = v := by
  funext i
  simp [shear, axis_self, Pi.add_apply, add_left_comm, double_bit]

def permute {k : ℕ} (p : Equiv.Perm (Fin k)) : Vec k ≃+ Vec k where
  toFun x := x ∘ p.symm
  invFun x := x ∘ p
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp
  map_add' _ _ := rfl

theorem permute_axis {k : ℕ} (p : Equiv.Perm (Fin k)) (i : Fin k) :
    permute p (axis i) = axis (p i) := by
  funext j
  simp only [permute, AddEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply, axis,
    Equiv.symm_apply_eq]

theorem toFullPair {s : ℕ} (seed : Fin s) {v : Vec (2*s)} (hv : v ≠ 0) :
    ∃ P : Vec (2*s) ≃+ Vec (2*s), P v = fullPair seed := by
  classical
  have h : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨j,hj⟩ := h
  have hj' : v j = 1 := (bit_cases _).resolve_left hj
  let i := first seed
  have hp : fullPair seed i = 1 := by simp [fullPair, i, part_first]
  refine ⟨(shear j (v+axis j) (by simp [hj',axis_self,double_bit])).trans
    ((permute (Equiv.swap j i)).trans
      (shear i (fullPair seed+axis i) (by simp [hp,axis_self,double_bit]))), ?_⟩
  simp only [AddEquiv.trans_apply]
  rw [shear_to_axis _ _ hj', permute_axis, Equiv.swap_apply_left, shear_from_axis _ _ hp]

theorem sum_axes {k : ℕ} (x : Vec k) : (∑ i, x i • axis i) = x := by
  classical
  funext i
  simp [Finset.sum_apply, axis, Pi.smul_apply, smul_eq_mul, mul_ite, eq_comm (a:=i)]

theorem addEquiv_smul {k : ℕ} (P : Vec k ≃+ Vec k) (a : F) (x : Vec k) :
    P (a • x) = a • P x := by
  have hzero (v : Vec k) : (0 : F) • v = 0 := by
    funext i
    simp [Pi.smul_apply, smul_eq_mul]
  have hone (v : Vec k) : (1 : F) • v = v := by
    funext i
    simp [Pi.smul_apply, smul_eq_mul]
  rcases bit_cases a with rfl | rfl
  · rw [hzero, map_zero, hzero]
  · rw [hone, hone]

theorem dot_sum_left {k m : ℕ} (x : Fin m → Vec k) (y : Vec k) :
    dot (∑ j, x j) y = ∑ j, dot (x j) y := by
  simp only [dot, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem dot_smul_left {k : ℕ} (a : F) (x y : Vec k) : dot (a • x) y = a * dot x y := by
  simp [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

def dualMap {k : ℕ} (P : Vec k ≃+ Vec k) (y : Vec k) (i : Fin k) : F :=
  dot (P.symm (axis i)) y

theorem dot_dualMap {k : ℕ} (P : Vec k ≃+ Vec k) (x y : Vec k) :
    dot x (dualMap P y) = dot (P.symm x) y := by
  conv_rhs => arg 1; arg 2; rw [← sum_axes x]
  simp only [map_sum, addEquiv_smul, dot_sum_left, dot_smul_left]
  rfl

theorem dualMap_bijective {k : ℕ} (P : Vec k ≃+ Vec k) : Function.Bijective (dualMap P) := by
  have hinj : Function.Injective (dualMap P) := by
    intro x y h
    funext i
    have h' := congrArg (dot (P (axis i))) h
    simpa only [dot_dualMap, AddEquiv.symm_apply_apply, dot_axis] using h'
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

noncomputable def dualEquiv {k : ℕ} (P : Vec k ≃+ Vec k) : Vec k ≃ Vec k :=
  Equiv.ofBijective (dualMap P) (dualMap_bijective P)

def shift {k : ℕ} (v : Vec k) : Vec k ≃ Vec k where
  toFun x := x + v
  invFun x := x + v
  left_inv x := by simp only [add_assoc, double_vec, add_zero]
  right_inv x := by simp only [add_assoc, double_vec, add_zero]

noncomputable def badAt {k : ℕ} (Q : Vec k → F) (z : Vec k × F) : Finset (Vec k) :=
  Finset.univ.filter fun x => Q x ≠ dot z.1 x + z.2

noncomputable def distance {k : ℕ} (Q : Vec k → F) : ℕ :=
  sInf (Set.range fun z : Vec k × F => (badAt Q z).card)

theorem optimal_affine {k : ℕ} (Q : Vec k → F) :
    ∃ z : Vec k × F, (badAt Q z).card = distance Q ∧ ∃ u, u ∉ badAt Q z := by
  classical
  obtain ⟨z, hz⟩ := Nat.sInf_mem (Set.range_nonempty (fun z : Vec k × F => (badAt Q z).card))
  have hlt : (badAt Q (0, Q 0)).card < (Finset.univ : Finset (Vec k)).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_univ _, ?_⟩
    intro h
    have hh : (0 : Vec k) ∈ badAt Q (0, Q 0) := h ▸ Finset.mem_univ _
    simp [badAt, dot_zero_left] at hh
  have hz' : (badAt Q z).card ≤ (badAt Q (0, Q 0)).card := hz.trans_le
    (Nat.sInf_le (Set.mem_range_self ((0, Q 0) : Vec k × F)))
  obtain ⟨u, _, hu⟩ := Finset.exists_mem_notMem_of_card_lt_card (hz'.trans_lt hlt)
  exact ⟨z, hz, u, hu⟩

theorem affine_error {k : ℕ} (Q : Vec k → F) (z : Vec k × F) (x : Vec k) :
    Q x = dot z.1 x + z.2 + (if x ∈ badAt Q z then 1 else 0) := by
  simp only [badAt, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (by decide : ∀ a b : F, a = b + (if a ≠ b then 1 else 0)) (Q x) (dot z.1 x+z.2)

theorem affine_reduction {s : ℕ} (seed : Fin s) (Q : Vec (2*s) → F) :
    ∃ (A B : Vec (2*s) ≃ Vec (2*s)) (α : Vec (2*s)) (c : F)
      (errors : Finset (Vec (2*s))), 0 ∉ errors ∧
      (errors = ∅ ∨ fullPair seed ∈ errors) ∧ errors.card = distance Q ∧
      ∀ x y, dot x y + Q x =
        quad (A x+B y+α) + quad (A x) + quad (B y) +
          (if A x ∈ errors then 1 else 0) + c := by
  classical
  obtain ⟨z, hz, u, hu⟩ := optimal_affine Q
  let bad := badAt Q z
  have hmap : ∃ P : Vec (2*s) ≃+ Vec (2*s),
      bad = ∅ ∨ ∃ w ∈ bad, P (w+u) = fullPair seed := by
    by_cases hempty : bad = ∅
    · exact ⟨AddEquiv.refl _, Or.inl hempty⟩
    · obtain ⟨w,hw⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hwu : w+u ≠ 0 := by
        intro h
        have heq : w = u := by simpa [add_assoc, double_vec] using congrArg (fun x => x+u) h
        exact hu (heq ▸ hw)
      obtain ⟨P,hP⟩ := toFullPair seed hwu
      exact ⟨P, Or.inr ⟨w, hw, hP⟩⟩
  obtain ⟨P,hP⟩ := hmap
  let α := P u
  let A := P.toEquiv.trans (shift α)
  let B := (shift z.1).trans ((dualEquiv P).trans (swap.toEquiv.trans (shift α)))
  let errors := bad.image A
  have hA (x : Vec (2*s)) : A x + α = P x := by
    change (P x+α)+α = P x
    rw [add_assoc, double_vec, add_zero]
  have hB (y : Vec (2*s)) : B y + α = swap (dualMap P (y+z.1)) := by
    change (swap (dualMap P (y+z.1))+α)+α = _
    rw [add_assoc, double_vec, add_zero]
  have hAu : A u = 0 := double_vec _
  have herr (x : Vec (2*s)) : A x ∈ errors ↔ x ∈ bad := by
    change A x ∈ bad.image A ↔ _
    simp [A.injective.eq_iff]
  refine ⟨A, B, α, z.2 + quad α, errors, ?_, ?_, ?_, ?_⟩
  · rw [← hAu, herr]
    exact hu
  · rcases hP with hP | ⟨w,hw,hPw⟩
    · left
      simp [errors, hP]
    · right
      apply Finset.mem_image.mpr
      refine ⟨w,hw,?_⟩
      change P w + P u = fullPair seed
      simpa only [map_add] using hPw
  · rw [Finset.card_image_of_injective _ A.injective]
    exact hz
  · intro x y
    rw [quad_translate, hA, hB, polar_swap]
    change dot x y + Q x = (dot (P x) (dualMap P (y+z.1)) + quad α) +
      (if A x ∈ errors then 1 else 0) + (z.2 + quad α)
    rw [dot_dualMap, AddEquiv.symm_apply_apply, dot_add_right, dot_comm x z.1]
    simp only [herr x]
    rw [affine_error Q z x]
    linear_combination -(double_bit (quad α))

end Upper
end PEqualNP.Outside.L_meta_25800_aux

namespace PEqualNP.Outside.L_meta_25800_aux

open scoped BigOperators

private inductive XorProgram : ℕ → ℕ → Type
  | ret {n m} (ports : Fin m → Option (Fin n)) : XorProgram n m
  | push {n m} (a b : Fin n) (rest : XorProgram (n+1) m) : XorProgram n m

namespace XorProgram

private def eval {W : Type} [AddMonoid W] : XorProgram n m → (Fin n → W) → Fin m → W
  | .ret p, v => fun j => (p j).elim 0 v
  | .push a b T, v => T.eval (Fin.snoc v (v a + v b))

private def count : XorProgram n m → ℕ
  | .ret _ => 0
  | .push _ _ T => T.count + 1

private def live : XorProgram n m → Fin m → Bool
  | .ret p => fun j => (p j).isSome
  | .push _ _ T => T.live

private def outputs (T : XorProgram n m) : ℕ := ∑ j, (T.live j).toNat

private theorem eval_of_dead {W : Type} [AddMonoid W] (T : XorProgram n m)
    (x : Fin n → W) (i : Fin m) (h : T.live i = false) : T.eval x i = 0 := by
  induction T with
  | ret p =>
      cases he : p i <;> simp_all [live, eval]
  | push a b T ih =>
      exact ih _ i h

private def select (T : XorProgram n m) (f : Fin M → Fin m) : XorProgram n M :=
  match T with
  | .ret p => .ret (p ∘ f)
  | .push a b U => .push a b (U.select f)

@[simp] private theorem eval_select {W : Type} [AddMonoid W] (T : XorProgram n m)
    (f : Fin M → Fin m) (v : Fin n → W) (i : Fin M) :
    (T.select f).eval v i = T.eval v (f i) := by
  induction T with
  | ret => rfl
  | push _ _ _ ih => exact ih f _

@[simp] private theorem count_select (T : XorProgram n m) (f : Fin M → Fin m) :
    (T.select f).count = T.count := by
  induction T with
  | ret => rfl
  | push _ _ _ ih => simp [select, count, ih]

@[simp] private theorem live_select (T : XorProgram n m) (f : Fin M → Fin m) (i : Fin M) :
    (T.select f).live i = T.live (f i) := by
  induction T with
  | ret => rfl
  | push _ _ _ ih => exact ih f

private def addTo (T : XorProgram n m) (u v : Fin m) : XorProgram n m :=
  match T with
  | .ret p =>
    match p u, p v with
    | some a, some b =>
      .push a b (.ret (Function.update (fun i => (p i).map Fin.castSucc) u (some (Fin.last n))))
    | none, b => .ret (Function.update p u b)
    | some _, none => .ret p
  | .push a b U => .push a b (U.addTo u v)

private theorem addTo_at {W : Type} [AddMonoid W] (T : XorProgram n m)
    (x : Fin n → W) (u v : Fin m) (i : Fin m) :
    (T.addTo u v).eval x i = if i = u then T.eval x u + T.eval x v else T.eval x i := by
  induction T with
  | ret p =>
      by_cases h : i = u
      · subst i
        cases hu : p u <;> cases hv : p v <;>
          simp [addTo, eval, hu, hv, Fin.snoc]
      · cases hu : p u <;> cases hv : p v <;>
          simp [addTo, eval, hu, hv, h, Function.update_of_ne, Fin.snoc_castSucc]
  | push a b T ih => exact ih _ u v i

private theorem live_addTo_at (T : XorProgram n m) (u v i : Fin m) :
    (T.addTo u v).live i = if i = u then T.live u || T.live v else T.live i := by
  induction T with
  | ret p =>
      by_cases h : i = u
      · subst i
        cases hu : p u <;> cases hv : p v <;> simp [addTo, live, hu, hv]
      · cases hu : p u <;> cases hv : p v <;>
          simp [addTo, live, hu, hv, h, Function.update_of_ne]
  | push a b T ih => exact ih u v i

private theorem count_addTo (T : XorProgram n m) (u v : Fin m) :
    (T.addTo u v).count = T.count + ((T.live u) && (T.live v)).toNat := by
  induction T with
  | ret p =>
      cases hu : p u <;> cases hv : p v <;> simp [addTo, count, live, hu, hv]
  | push a b T ih => simp [addTo, count, live, ih, Nat.add_right_comm]

private theorem cost_addTo (T : XorProgram n m) (u v : Fin m) :
    (T.addTo u v).count + (T.addTo u v).outputs = T.count + T.outputs + (T.live v).toNat := by
  classical
  have hu : u ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ u
  have h₁ := Finset.sum_erase_add (s := Finset.univ)
    (fun i => ((T.addTo u v).live i).toNat) hu
  have h₂ := Finset.sum_erase_add (s := Finset.univ) (fun i => (T.live i).toNat) hu
  have he : ∑ i ∈ (Finset.univ : Finset (Fin m)).erase u, ((T.addTo u v).live i).toNat =
      ∑ i ∈ (Finset.univ : Finset (Fin m)).erase u, (T.live i).toNat := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [live_addTo_at, (Finset.mem_erase.mp hi).1]
  rw [he, live_addTo_at, if_pos rfl] at h₁
  rw [outputs, outputs, count_addTo, ← h₁, ← h₂]
  cases T.live u <;> cases T.live v <;> simp <;> omega

private def extend (T : XorProgram n m) (f : Fin n → Fin N) (new : Fin N) :
    XorProgram N (m+1) :=
  match T with
  | .ret p => .ret (Fin.snoc (fun i => (p i).map f) (some new))
  | .push a b U =>
      .push (f a) (f b) (U.extend (Fin.snoc (Fin.castSucc ∘ f) (Fin.last N)) new.castSucc)

private theorem eval_extend {W : Type} [AddMonoid W] (T : XorProgram n m)
    (f : Fin n → Fin N) (w : Fin N) (x : Fin N → W) :
    (T.extend f w).eval x = Fin.snoc (T.eval (x ∘ f)) (x w) := by
  induction T generalizing N with
  | ret p =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [extend, eval]
      · simp only [extend, eval, Fin.snoc_castSucc, Function.comp_apply]
        cases p j <;> rfl
  | push a b T ih =>
      rw [extend, eval, ih, eval, Fin.snoc_castSucc]
      have he : Fin.snoc x (x (f a) + x (f b)) ∘
          Fin.snoc (Fin.castSucc ∘ f) (Fin.last N) =
          Fin.snoc (x ∘ f) ((x ∘ f) a + (x ∘ f) b) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [he]

@[simp] private theorem count_extend (T : XorProgram n m) (f : Fin n → Fin N) (w : Fin N) :
    (T.extend f w).count = T.count := by
  induction T generalizing N with
  | ret => rfl
  | push a b T ih => simp [extend, count, ih]

private theorem live_extend (T : XorProgram n m) (f : Fin n → Fin N) (w : Fin N) :
    (T.extend f w).live = Fin.snoc T.live true := by
  induction T generalizing N with
  | ret p =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [extend, live]
  | push a b T ih => exact ih _ _

private def pop (T : XorProgram n (m+1)) : XorProgram n m := T.select Fin.castSucc

private theorem outputs_pop (T : XorProgram n (m+1)) :
    T.pop.outputs + (T.live (Fin.last m)).toNat = T.outputs := by
  simp only [outputs, pop, live_select]
  rw [Fin.sum_univ_castSucc]

private theorem outputs_extend (T : XorProgram n m) (f : Fin n → Fin N) (w : Fin N) :
    (T.extend f w).outputs = T.outputs + 1 := by
  simp [outputs, live_extend, Fin.sum_univ_castSucc]

private def transposePorts {n : ℕ} : {m : ℕ} → (Fin m → Option (Fin n)) → XorProgram m n
  | 0, _ => .ret (fun _ => none)
  | m+1, p =>
      let T := (transposePorts (p ∘ Fin.castSucc)).extend Fin.castSucc (Fin.last m)
      match p (Fin.last m) with
      | none => T.pop
      | some u => (T.addTo u.castSucc (Fin.last n)).pop

private def transpose (T : XorProgram n m) : XorProgram m n :=
  match T with
  | .ret p => transposePorts p
  | .push a b U =>
      let P := U.transpose
      if a = b then P.pop else
        ((P.addTo a.castSucc (Fin.last n)).addTo b.castSucc (Fin.last n)).pop

@[simp] private theorem count_pop (T : XorProgram n (m+1)) : T.pop.count = T.count :=
  T.count_select Fin.castSucc

private theorem cost_pop (T : XorProgram n (m+1)) :
    T.pop.count + T.pop.outputs + (T.live (Fin.last m)).toNat =
      T.count + T.outputs := by
  have h := T.outputs_pop
  rw [count_pop, Nat.add_assoc, h]

private theorem cost_transposePorts {n m : ℕ} (p : Fin m → Option (Fin n)) :
    (transposePorts p).count + (transposePorts p).outputs = ∑ j, (p j).isSome.toNat := by
  induction m with
  | zero => simp [transposePorts, count, outputs, live]
  | succ m ih =>
      let U := transposePorts (p ∘ Fin.castSucc)
      let T := U.extend Fin.castSucc (Fin.last m)
      have hc : T.count + T.outputs = U.count + U.outputs + 1 := by
        simp [T, outputs_extend, Nat.add_assoc]
      have ht : T.live (Fin.last n) = true := by simp [T, live_extend]
      have h₀ : T.pop.count + T.pop.outputs = U.count + U.outputs := by
        have h := T.cost_pop
        rw [ht, hc] at h
        simpa using h
      rw [Fin.sum_univ_castSucc]
      rw [transposePorts]
      cases hp : p (Fin.last m) with
      | none => simpa [T, U, hp, ih] using h₀
      | some u =>
          let V := T.addTo u.castSucc (Fin.last n)
          have hv : V.live (Fin.last n) = true := by
            simp [V, live_addTo_at, ht]
          have h := V.cost_pop
          rw [hv, show V.count + V.outputs = T.count + T.outputs + 1 by
            simp [V, cost_addTo, ht]] at h
          have h' : V.pop.count + V.pop.outputs = T.count + T.outputs := by simpa using h
          change V.pop.count + V.pop.outputs = (∑ i : Fin m, ((p ∘ Fin.castSucc) i).isSome.toNat) + 1
          rw [h', hc, show U.count + U.outputs = _ from ih (p ∘ Fin.castSucc)]

private theorem transpose_cost (T : XorProgram n m) :
    T.transpose.count + T.transpose.outputs ≤ T.count + T.outputs := by
  induction T with
  | ret p =>
      change (transposePorts p).count + (transposePorts p).outputs ≤ 0 + ∑ j, (p j).isSome.toNat
      rw [zero_add, cost_transposePorts]
  | @push n m a b U ih =>
      let P := U.transpose
      rw [transpose]
      by_cases h : a = b
      · rw [if_pos h]
        have hp := P.cost_pop
        change P.pop.count + P.pop.outputs ≤ U.count + 1 + U.outputs
        change P.count + P.outputs ≤ U.count + U.outputs at ih
        omega
      · rw [if_neg h]
        let V := P.addTo a.castSucc (Fin.last n)
        let Z := V.addTo b.castSucc (Fin.last n)
        have hv : V.live (Fin.last n) = P.live (Fin.last n) := by
          simp [V, live_addTo_at, Ne.symm (Fin.castSucc_ne_last a)]
        have hz : Z.live (Fin.last n) = P.live (Fin.last n) := by
          simp [Z, live_addTo_at, hv, Ne.symm (Fin.castSucc_ne_last b)]
        have h₁ := P.cost_addTo a.castSucc (Fin.last n)
        have h₂ := V.cost_addTo b.castSucc (Fin.last n)
        have h₃ := Z.cost_pop
        change V.count + V.outputs = P.count + P.outputs + _ at h₁
        change Z.count + Z.outputs = V.count + V.outputs + _ at h₂
        rw [hv] at h₂
        rw [hz] at h₃
        change Z.pop.count + Z.pop.outputs ≤ U.count + 1 + U.outputs
        change P.count + P.outputs ≤ U.count + U.outputs at ih
        have hbit : (P.live (Fin.last n)).toNat ≤ 1 := by cases P.live (Fin.last n) <;> decide
        omega

private abbrev Scalar := ZMod 2

private def pairing {n : ℕ} (x y : Fin n → Scalar) : Scalar := ∑ i, x i * y i

private theorem expand_pairing {n : ℕ} (x : Fin n → Scalar) (a : Scalar)
    (y : Fin (n+1) → Scalar) :
    pairing (Fin.snoc x a) y = pairing x (y ∘ Fin.castSucc) + a * y (Fin.last n) := by
  simp [pairing, Fin.sum_univ_castSucc]

private theorem pairing_addTo (T : XorProgram n m) (x : Fin n → Scalar)
    (z : Fin m → Scalar) (u v : Fin m) :
    pairing z ((T.addTo u v).eval x) = pairing z (T.eval x) + z u * T.eval x v := by
  classical
  have hh (i : Fin m) : z i * (T.addTo u v).eval x i =
      z i * T.eval x i + (if i = u then z u * T.eval x v else 0) := by
    by_cases h : i = u
    · subst i
      simp [addTo_at, mul_add]
    · simp [addTo_at, h]
  simp [pairing, hh, Finset.sum_add_distrib]

private theorem pairing_pop (T : XorProgram n (m+1)) (x : Fin n → Scalar)
    (z : Fin m → Scalar) :
    pairing z (T.pop.eval x) = pairing (Fin.snoc z 0) (T.eval x) := by
  rw [expand_pairing]; simp only [zero_mul, add_zero]
  congr 1
  funext i
  exact eval_select T Fin.castSucc x i

private theorem dual_ports {n m : ℕ} (p : Fin m → Option (Fin n)) (x : Fin n → Scalar)
    (y : Fin m → Scalar) :
    pairing ((XorProgram.ret p).eval x) y = pairing x ((transposePorts p).eval y) := by
  induction m with
  | zero =>
      simp [pairing, transposePorts, eval]
  | succ m ih =>
      let U := transposePorts (p ∘ Fin.castSucc)
      let T := U.extend Fin.castSucc (Fin.last m)
      have h₀ := ih (p ∘ Fin.castSucc) (y ∘ Fin.castSucc)
      have h₁ : pairing (Fin.snoc x 0) (T.eval y) =
          pairing x (U.eval (y ∘ Fin.castSucc)) := by
        change pairing (Fin.snoc x 0) ((U.extend Fin.castSucc (Fin.last m)).eval y) = _
        rw [eval_extend, expand_pairing]
        simp
      have h₂ : T.eval y (Fin.last n) = y (Fin.last m) := by
        simp [T, eval_extend]
      rw [transposePorts]
      simp only [pairing, Fin.sum_univ_castSucc, eval] at ⊢
      change pairing ((XorProgram.ret (p ∘ Fin.castSucc)).eval x) (y ∘ Fin.castSucc) +
        (p (Fin.last m)).elim 0 x * y (Fin.last m) = _
      rw [h₀]
      cases hp : p (Fin.last m) with
      | none =>
          change _ = pairing x (T.pop.eval y)
          rw [pairing_pop, h₁]
          simp [U]
      | some u =>
          change _ = pairing x ((T.addTo u.castSucc (Fin.last n)).pop.eval y)
          rw [pairing_pop, pairing_addTo, h₁, h₂]
          simp [U]

private theorem dual_transpose (T : XorProgram n m) (x : Fin n → Scalar)
    (y : Fin m → Scalar) :
    pairing (T.eval x) y = pairing x (T.transpose.eval y) := by
  induction T with
  | ret p => exact dual_ports p x y
  | @push n m a b U ih =>
      let P := U.transpose
      change pairing (U.eval (Fin.snoc x (x a + x b))) y = _
      rw [ih, transpose]
      by_cases h : a = b
      · subst b
        rw [if_pos rfl, pairing_pop]
        rw [show x a + x a = 0 from (by decide : ∀ z : Scalar, z + z = 0) _]
      · rw [if_neg h]
        let V := P.addTo a.castSucc (Fin.last n)
        let Z := V.addTo b.castSucc (Fin.last n)
        change pairing (Fin.snoc x (x a + x b)) (P.eval y) =
          pairing x (Z.pop.eval y)
        dsimp only [Z,V]
        rw [pairing_pop, pairing_addTo, pairing_addTo, expand_pairing,
          addTo_at, if_neg (Ne.symm (Fin.castSucc_ne_last a)), Fin.snoc_castSucc,
          Fin.snoc_castSucc, add_mul]
        simp only [expand_pairing, zero_mul, add_zero]
        ac_rfl

end XorProgram
open scoped BigOperators

abbrev F := ZMod 2
abbrev Vec (k : ℕ) := Fin k → F

private theorem add_self_eq_zero (a : F) : a + a = 0 := by
  exact (by decide : ∀ a : F, a + a = 0) a

private def dot {k : ℕ} (a b : Vec k) : F := ∑ i, a i * b i

private def unit {k : ℕ} (i : Fin k) : Vec k :=
  fun j => if j = i then 1 else 0

private theorem dot_unit {k : ℕ} (a : Vec k) (i : Fin k) :
    dot a (unit i) = a i := by
  classical
  simp [dot, unit, mul_ite]

private theorem unit_dot {k : ℕ} (a : Vec k) (i : Fin k) :
    dot (unit i) a = a i := by
  classical
  simp [dot, unit, ite_mul]

private theorem dot_zero_left {k : ℕ} (a : Vec k) : dot 0 a = 0 := by
  simp [dot]

private theorem dot_zero_right {k : ℕ} (a : Vec k) : dot a 0 = 0 := by
  simp [dot]

private theorem row_injective {k m : ℕ} {Q L R : Vec k → F}
    {A B : Vec k → Vec m} {H : Vec m → F}
    (h : ∀ x y, dot x y + Q x = H (A x + B y) + L x + R y) :
    Function.Injective A := by
  intro x x' heq
  funext i
  have h₁ := h x (unit i)
  have h₂ := h x' (unit i)
  have h₃ := h x 0
  have h₄ := h x' 0
  simp only [dot_unit, dot_zero_right, heq] at h₁ h₂ h₃ h₄
  linear_combination h₁ - h₂ - h₃ + h₄

private theorem col_injective {k m : ℕ} {Q L R : Vec k → F}
    {A B : Vec k → Vec m} {H : Vec m → F}
    (h : ∀ x y, dot x y + Q x = H (A x + B y) + L x + R y) :
    Function.Injective B := by
  intro y y' heq
  funext i
  have h₁ := h (unit i) y
  have h₂ := h (unit i) y'
  have h₃ := h 0 y
  have h₄ := h 0 y'
  simp only [unit_dot, dot_zero_left, heq] at h₁ h₂ h₃ h₄
  linear_combination h₁ - h₂ - h₃ + h₄

private theorem card_vec (k : ℕ) : Fintype.card (Vec k) = 2 ^ k := by
  simp [Vec, F]

private theorem dim_le {k m : ℕ} {A : Vec k → Vec m} (ha : Function.Injective A) :
    k ≤ m := by
  have h := Fintype.card_le_of_injective A ha
  simp only [card_vec] at h
  exact (pow_le_pow_iff_right₀ (by decide : (1 : ℕ) < 2)).mp h

private theorem bijective_of_injective {k : ℕ} {A : Vec k → Vec k}
    (ha : Function.Injective A) : Function.Bijective A :=
  ⟨ha, Finite.surjective_of_injective ha⟩

private noncomputable def distance {k : ℕ} (Q : Vec k → F) : ℕ :=
  sInf (Set.range fun z : Vec k × F =>
    ((Finset.univ : Finset (Vec k)).filter (fun x => Q x ≠ dot z.1 x + z.2)).card)

private theorem affine_discrepancy {k : ℕ} {Q L R : Vec k → F}
    {A B : Vec k → Vec k} {H : Vec k → F}
    (h : ∀ x y, dot x y + Q x = H (A x + B y) + L x + R y)
    (σ : Vec k ≃ Vec k) (hσ : ∀ x, B (σ x) = A x) :
    distance Q ≤ (Finset.univ.filter fun x => L x ≠ R (σ x)).card := by
  classical
  let c := Q 0 + L 0 + R (σ 0)
  have key (x : Vec k) : Q x + L x + R (σ x) = dot (σ 0) x + c := by
    have h₁ := h x (σ 0)
    have h₂ := h 0 (σ x)
    rw [hσ] at h₁ h₂
    rw [add_comm (A 0) (A x)] at h₂
    have hcomm : dot (σ 0) x = dot x (σ 0) := by
      simp only [dot, mul_comm]
    rw [dot_zero_left] at h₂
    rw [hcomm]
    dsimp [c]
    linear_combination h₁ - h₂ + add_self_eq_zero (L x) - add_self_eq_zero (L 0) - add_self_eq_zero (dot x (σ 0))
  refine (Nat.sInf_le (s := _) (Set.mem_range_self (σ 0, c))).trans ?_
  apply le_of_eq
  congr 1
  ext x
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    (show Q x ≠ dot (σ 0) x + c ↔ L x ≠ R (σ x) by
      rw [← key]
      have hs : Q x = Q x + L x + R (σ x) ↔ L x = R (σ x) := by
        have hc := add_self_eq_zero (R (σ x))
        constructor <;> intro h' <;> linear_combination -h' - hc
      exact not_congr hs)

private theorem graph_has_phase {k : ℕ} (hk : 0 < k) {Q L R : Vec k → F}
    {A B : Vec k → Vec k} {H : Vec k → F}
    (h : ∀ x y, dot x y + Q x = H (A x + B y) + L x + R y)
    (hB : Function.Surjective B) (hL : ∀ x, L x = 0) :
    ¬ (∀ y, R y = 0) := by
  intro hR
  have hH (z : Vec k) : H z = Q 0 := by
    obtain ⟨y, hy⟩ := hB (z - A 0)
    have h' := h 0 y
    simp only [dot_zero_left, hL, hR, zero_add, add_zero] at h'
    rw [hy, add_comm, sub_add_cancel] at h'
    exact h'.symm
  let i : Fin k := ⟨0, hk⟩
  have h₁ := h (unit i) (unit i)
  have h₀ := h (unit i) 0
  rw [dot_unit] at h₁
  rw [dot_zero_right] at h₀
  have hbad : (1 : F) = 0 := by
    simp [unit] at h₁
    simp only [hH, hL, hR, add_zero, zero_add] at h₁ h₀
    linear_combination h₁ - h₀
  exact one_ne_zero hbad

private structure Literal (n : ℕ) where
  wire : Option (Fin n)
  phase : ZMod 2

private def Literal.eval (x : Fin n → ZMod 2) (l : Literal n) : ZMod 2 :=
  l.wire.elim 0 x + l.phase

private def Literal.weaken (l : Literal n) : Literal (n+1) :=
  ⟨l.wire.map Fin.castSucc, l.phase⟩

private inductive Mixed : ℕ → Type
  | ret {n} (a : Literal n) : Mixed n
  | xor {n} (a b : Fin n) (rest : Mixed (n+1)) : Mixed n
  | mul {n} (a b : Literal n) (rest : Mixed (n+1)) : Mixed n

namespace Mixed

private abbrev nonlinear : Mixed n → ℕ
  | .ret _ => 0
  | .xor _ _ T => T.nonlinear
  | .mul _ _ T => T.nonlinear + 1

private def linear : Mixed n → ℕ
  | .ret _ => 0
  | .xor _ _ T => T.linear + 1
  | .mul _ _ T => T.linear

private abbrev F := ZMod 2

private def eval : Mixed n → (Fin n → F) → F
  | .ret a, x => a.eval x
  | .xor a b T, x => T.eval (Fin.snoc x (x a + x b))
  | .mul a b T, x => T.eval (Fin.snoc x (a.eval x * b.eval x))

private def products (T : Mixed n) (x : Fin n → F) : Fin T.nonlinear → F :=
  match T with
  | .ret _ => Fin.elim0
  | .xor a b U => U.products (Fin.snoc x (x a + x b))
  | .mul a b U =>
      let g := a.eval x * b.eval x
      Fin.cons g (U.products (Fin.snoc x g))

private def phases (T : Mixed n) : Fin (2*T.nonlinear+1) → F :=
  match T with
  | .ret a => fun _ => a.phase
  | .xor _ _ U => U.phases
  | .mul a b U => Fin.cons a.phase (Fin.cons b.phase U.phases)

private def operands (T : Mixed n) (x : Fin n → F)
    (g : Fin T.nonlinear → F) : Fin (2*T.nonlinear+1) → F :=
  match T with
  | .ret a => fun _ => a.eval x
  | .xor a b U => U.operands (Fin.snoc x (x a + x b)) g
  | .mul a b U =>
      Fin.cons (a.eval x) (Fin.cons (b.eval x)
        (U.operands (Fin.snoc x (g ⟨0, Nat.zero_lt_succ _⟩)) (g ∘ Fin.succ)))

private def first {t : ℕ} (j : Fin t) : Fin (2*t+1) :=
  ⟨2*j.val, by omega⟩

private def second {t : ℕ} (j : Fin t) : Fin (2*t+1) :=
  ⟨2*j.val+1, by omega⟩

private theorem first_succ {t : ℕ} (j : Fin t) :
    first j.succ = (first j).succ.succ := by
  apply Fin.ext
  simp [first, Nat.mul_add, Nat.add_assoc]

private theorem second_succ {t : ℕ} (j : Fin t) :
    second j.succ = (second j).succ.succ := by
  apply Fin.ext
  simp [second, Nat.mul_add, Nat.add_assoc]

private theorem output_operands (T : Mixed n) (x : Fin n → F) :
    T.operands x (T.products x) (Fin.last (2*T.nonlinear)) = T.eval x := by
  induction T with
  | ret => rfl
  | xor a b U ih => exact ih _
  | mul a b U ih =>
      have he : Fin.last (2 * (U.nonlinear+1)) = (Fin.last (2*U.nonlinear)).succ.succ :=
        Fin.ext (by simp [Nat.mul_add, Nat.add_assoc])
      simp only [operands, eval, he, Fin.cons_succ, products, Function.comp_apply,
        Fin.cons_zero, Fin.cons_succ]
      exact ih _

private theorem product_eq (T : Mixed n) (x : Fin n → F) (j : Fin T.nonlinear) :
    T.products x j =
      T.operands x (T.products x) (first j) * T.operands x (T.products x) (second j) := by
  induction T with
  | ret => exact Fin.elim0 j
  | xor a b U ih => exact ih _ j
  | mul a b U ih =>
      refine Fin.cases ?_ (fun q => ?_) j
      · rfl
      · simp only [products, operands, first_succ, second_succ, Fin.cons_succ,
          Fin.cons_zero, Function.comp_def]
        exact ih _ q

private theorem operands_causal (T : Mixed n) (x : Fin n → F)
    (g g' : Fin T.nonlinear → F) (j : Fin T.nonlinear)
    (agree : ∀ i : Fin T.nonlinear, i < j → g i = g' i) :
    T.operands x g (first j) = T.operands x g' (first j) ∧
      T.operands x g (second j) = T.operands x g' (second j) := by
  induction T with
  | ret => exact Fin.elim0 j
  | xor a b U ih => exact ih _ g g' j agree
  | mul a b U ih =>
      change Fin (U.nonlinear+1) at j
      revert agree
      refine Fin.cases ?_ (fun q => ?_) j
      · intro _
        exact ⟨rfl,rfl⟩
      · intro agree
        have h₀ : g ⟨0, Nat.zero_lt_succ _⟩ = g' ⟨0, Nat.zero_lt_succ _⟩ := agree ⟨0, Nat.zero_lt_succ _⟩ (show 0 < q.val+1 from Nat.zero_lt_succ _)
        have h₁ (i : Fin U.nonlinear) (hi : i < q) : g i.succ = g' i.succ :=
          agree i.succ (show i.val + 1 < q.val + 1 by exact Nat.succ_lt_succ hi)
        simp only [operands, first_succ, second_succ, Fin.cons_succ]
        rw [h₀]
        exact ih (Fin.snoc x (g' ⟨0, Nat.zero_lt_succ _⟩)) (g ∘ Fin.succ) (g' ∘ Fin.succ) q h₁

end Mixed

namespace XorProgram

private def prepend (P : XorProgram n m) (u : Option (Fin n)) : XorProgram n (m+1) :=
  match P with
  | .ret p => .ret (Fin.cons u p)
  | .push a b T => .push a b (T.prepend (u.map Fin.castSucc))

private theorem eval_prepend {W : Type} [AddMonoid W] (P : XorProgram n m)
    (u : Option (Fin n)) (x : Fin n → W) :
    (P.prepend u).eval x = Fin.cons (u.elim 0 x) (P.eval x) := by
  induction P with
  | ret p =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  | push a b T ih =>
      rw [prepend, eval, ih, eval]
      cases u <;> simp

@[simp] private theorem count_prepend (P : XorProgram n m) (u : Option (Fin n)) :
    (P.prepend u).count = P.count := by
  induction P with
  | ret => rfl
  | push a b T ih => simp [prepend, count, ih]

end XorProgram

namespace Mixed

private def linearize (T : Mixed n) (h : Fin n → Fin w) (g : Fin T.nonlinear → Fin w) :
    XorProgram w (2*T.nonlinear+1) :=
  match T with
  | .ret a => .ret (fun _ => a.wire.map h)
  | .xor a b U =>
      .push (h a) (h b) (U.linearize (Fin.snoc (Fin.castSucc ∘ h) (Fin.last w)) (Fin.castSucc ∘ g))
  | .mul a b U =>
      ((U.linearize (Fin.snoc h (g ⟨0, Nat.zero_lt_succ _⟩)) (g ∘ Fin.succ)).prepend (b.wire.map h)).prepend (a.wire.map h)

private theorem count_linearize (T : Mixed n) (h : Fin n → Fin w) (g : Fin T.nonlinear → Fin w) :
    (T.linearize h g).count = T.linear := by
  induction T generalizing w with
  | ret => rfl
  | xor a b U ih =>
      simp only [linearize, XorProgram.count, linear]
      exact congrArg (·+1) (ih _ _)
  | mul a b U ih =>
      simp only [linearize, XorProgram.count_prepend, linear]
      exact ih _ _

private theorem eval_linearize (T : Mixed n)
    (h : Fin n → Fin w) (g : Fin T.nonlinear → Fin w) (x : Fin w → F) (i) :
    (T.linearize h g).eval x i + T.phases i = T.operands (x ∘ h) (x ∘ g) i := by
  induction T generalizing w with
  | ret a => cases hwire : a.wire <;> simp [linearize, XorProgram.eval, phases, operands, Literal.eval, hwire]
  | xor a b U ih =>
      simp only [linearize, XorProgram.eval, phases, operands]
      rw [ih]
      have hh : Fin.snoc x (x (h a) + x (h b)) ∘
          Fin.snoc (Fin.castSucc ∘ h) (Fin.last w) =
          Fin.snoc (x ∘ h) ((x ∘ h) a + (x ∘ h) b) := by
        funext j
        refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
      have hg : Fin.snoc x (x (h a) + x (h b)) ∘ (Fin.castSucc ∘ g) = x ∘ g := by
        funext j
        simp
      rw [hh, hg]
  | mul a b U ih =>
      simp only [linearize, XorProgram.eval_prepend, operands, phases]
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
      · simp only [Fin.cons_zero, Literal.eval]
        cases ha : a.wire <;> simp [ha]
      · simp only [Fin.cons_zero, Fin.cons_succ, Literal.eval]
        cases hb : b.wire <;> simp [hb]
      · simp only [Fin.cons_succ]
        rw [ih]
        have hh : x ∘ Fin.snoc h (g ⟨0, Nat.zero_lt_succ _⟩) = Fin.snoc (x ∘ h) ((x ∘ g) ⟨0, Nat.zero_lt_succ _⟩) := by
          funext j
          refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
        rw [hh]
        rfl

end Mixed

namespace XorProgram

private theorem eval_coordinate (T : XorProgram n m) (v : Fin n → Fin k → Scalar)
    (i : Fin m) (j : Fin k) :
    T.eval v i j = T.eval (fun a => v a j) i := by
  induction T with
  | ret p =>
      cases hp : p i <;> simp [eval, hp]
  | push a b U ih =>
      simp only [eval, ih]
      congr 1
      funext q
      refine Fin.lastCases ?_ (fun r => ?_) q <;> simp

private def e {k : ℕ} (i : Fin k) : Fin k → Scalar := fun j => if j = i then 1 else 0

private theorem pairing_e (v : Fin n → Scalar) (i : Fin n) : pairing v (e i) = v i := by
  classical
  simp [pairing, e, mul_ite]

private theorem e_symm (i j : Fin n) : e i j = e j i := by
  simp only [e, eq_comm]

private def coefficient (T : XorProgram n m) (i : Fin n) : Fin m → Scalar :=
  T.transpose.eval e i

private theorem eval_matrix (T : XorProgram n m) (x : Fin n → Scalar) (i : Fin m) :
    T.eval x i = ∑ j, x j * T.coefficient j i := by
  have h := T.dual_transpose x (e i)
  rw [pairing_e, pairing] at h
  have hc (j : Fin n) : T.coefficient j i = T.transpose.eval (e i) j := by
    rw [coefficient, eval_coordinate]
    congr 1
    funext a
    exact e_symm a i
  simp only [hc]
  exact h

private theorem dead_coefficient (T : XorProgram n m) (i : Fin n)
    (hi : T.transpose.live i = false) : T.coefficient i = 0 :=
  T.transpose.eval_of_dead e i hi

private theorem outputs_le (T : XorProgram n m) : T.outputs ≤ m := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
    (f := fun i => (T.live i).toNat) (g := fun _ => 1)
    (fun i _ => by cases T.live i <;> decide)
  simpa [outputs] using h

private def trace {W : Type} [AddMonoid W] : XorProgram n m → (Fin n → W) → List W
  | .ret _, _ => []
  | .push a b U, x => (x a + x b) :: U.trace (Fin.snoc x (x a + x b))

private theorem trace_length {W : Type} [AddMonoid W] (T : XorProgram n m) (x : Fin n → W) :
    (T.trace x).length = T.count := by
  induction T with
  | ret => rfl
  | push a b U ih => simp [trace, count, ih]

private theorem eval_mem_trace {W : Type} [AddMonoid W] (T : XorProgram n m)
    (x : Fin n → W) (i : Fin m) (hne : T.eval x i ≠ 0) :
    T.eval x i ∈ Set.range x ∨ T.eval x i ∈ T.trace x := by
  induction T with
  | ret p =>
      cases hp : p i with
      | none => exact (hne (by simp [eval,hp])).elim
      | some j =>
          left
          exact ⟨j, by simp [eval,hp]⟩
  | push a b U ih =>
      rw [eval] at hne ⊢
      rcases ih (Fin.snoc x (x a + x b)) i hne with h|h
      · obtain ⟨j, h⟩ := h
        refine Fin.lastCases ?_ (fun j => ?_) j h
        · intro hj
          exact Or.inr (List.mem_cons.mpr (Or.inl (by simpa using hj.symm)))
        · intro hj
          exact Or.inl ⟨j, by simpa using hj⟩
      · exact Or.inr (List.mem_cons_of_mem _ h)

private theorem eval_trace_invariant {W : Type} [AddMonoid W] (T : XorProgram n m)
    (x : Fin n → W) (S K : Set W)
    (hin : ∀ j, x j ∈ K)
    (hgen : ∀ w ∈ T.trace x, w ∈ S)
    (hstep : ∀ a ∈ K, ∀ b ∈ K, a+b ∈ S → a+b ∈ K)
    (i : Fin m) (hne : T.eval x i ≠ 0) :
    T.eval x i ∈ K := by
  induction T with
  | ret p =>
      cases hp : p i with
      | none => exact (hne (by simp [eval,hp])).elim
      | some j => simpa [eval,hp] using hin j
  | push a b U ih =>
      let w := x a+x b
      have hnew : w ∈ K := hstep (x a) (hin a) (x b) (hin b) (hgen w (by simp [trace,w]))
      simp only [eval]
      apply ih (Fin.snoc x w) ?_ ?_ i hne
      · intro j
        refine Fin.lastCases ?_ (fun q => ?_) j
        · simpa using hnew
        · simpa using hin q
      · intro z hz
        exact hgen z (List.mem_cons_of_mem w hz)

end XorProgram

namespace Mixed

private def portProgram (T : Mixed (N+N)) : XorProgram ((N+N)+T.nonlinear) (2*T.nonlinear+1) :=
  T.linearize (Fin.castAdd _) (Fin.natAdd _)

private def leftWord (T : Mixed (N+N)) (i : Fin N) : Vec (2*T.nonlinear+1) :=
  T.portProgram.coefficient ((i.castAdd N).castAdd T.nonlinear)

private def rightWord (T : Mixed (N+N)) (j : Fin N) : Vec (2*T.nonlinear+1) :=
  T.portProgram.coefficient ((j.natAdd N).castAdd T.nonlinear)

private def productWord (T : Mixed (N+N)) (j : Fin T.nonlinear) : Vec (2*T.nonlinear+1) :=
  T.portProgram.coefficient (j.natAdd (N+N))

private def feedback (T : Mixed (N+N)) (g : Vec T.nonlinear) : Vec (2*T.nonlinear+1) :=
  fun q => ∑ j, g j * T.productWord j q

private def onehot (i j : Fin N) : Vec (N+N) := Fin.addCases (unit i) (unit j)

private theorem operand_word (T : Mixed (N+N)) (i j : Fin N) (g : Vec T.nonlinear)
    (q : Fin (2*T.nonlinear+1)) :
    T.operands (onehot i j) g q =
      T.leftWord i q + T.rightWord j q + T.feedback g q + T.phases q := by
  classical
  have h := T.eval_linearize (Fin.castAdd T.nonlinear) (Fin.natAdd (N+N))
    (Fin.addCases (onehot i j) g) q
  change T.portProgram.eval _ q + T.phases q = _ at h
  rw [XorProgram.eval_matrix, Fin.sum_univ_add] at h
  simp only [Fin.addCases_left, Fin.addCases_right, Function.comp_apply] at h
  rw [Fin.sum_univ_add] at h
  simp only [onehot, Fin.addCases_left, Fin.addCases_right, unit, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  have hx : (Fin.addCases (onehot i j) g) ∘ (Fin.castAdd T.nonlinear) = onehot i j := by
    funext a
    change Fin.addCases (motive := fun _ => F) (onehot i j) g (a.castAdd T.nonlinear) = _
    simp only [Fin.addCases_left]
  have hg : (Fin.addCases (onehot i j) g) ∘ (Fin.natAdd (N+N)) = g := by
    funext a
    change Fin.addCases (motive := fun _ => F) (onehot i j) g (a.natAdd (N+N)) = _
    simp only [← Fin.natAdd_eq_addNat, Fin.addCases_right]
  rw [hx,hg] at h
  simpa only [leftWord, rightWord, feedback, productWord, add_assoc] using h.symm

private theorem feedback_agree (T : Mixed (N+N)) (g h : Vec T.nonlinear)
    (agree : ∀ q, T.productWord q ≠ 0 → g q = h q) :
    T.feedback g = T.feedback h := by
  funext i
  apply Finset.sum_congr rfl
  intro q _
  by_cases hz : T.productWord q = 0
  · rw [hz]; simp
  · rw [agree q hz]

private theorem compare_runs (T : Mixed (N+N)) (i j i' j' : Fin N)
    (skip : Option (Fin T.nonlinear))
    (dead : ∀ k, some k = skip → T.productWord k = 0)
    (same : ∀ k, some k ≠ skip →
      (T.leftWord i (first k) + T.rightWord j (first k) =
        T.leftWord i' (first k) + T.rightWord j' (first k)) ∧
      (T.leftWord i (second k) + T.rightWord j (second k) =
        T.leftWord i' (second k) + T.rightWord j' (second k))) :
    T.eval (onehot i j) + (T.leftWord i (Fin.last _) + T.rightWord j (Fin.last _)) =
      T.eval (onehot i' j') + (T.leftWord i' (Fin.last _) + T.rightWord j' (Fin.last _)) := by
  let x := onehot i j
  let x' := onehot i' j'
  let g := T.products x
  let g' := T.products x'
  let h := fun k => if some k = skip then g k else g' k
  have hfb : T.feedback h = T.feedback g' := by
    apply T.feedback_agree
    intro k hk
    have hn : some k ≠ skip := fun he => hk (dead k he)
    simp [h, hn]
  have hp (k : Fin T.nonlinear) : some k ≠ skip → g k = g' k := by
    induction k using (invImage (fun k : Fin T.nonlinear => k.val) Nat.lt_wfRel).wf.induction with
    | h k ih =>
      intro hk
      have hag (p : Fin T.nonlinear) (hp : p < k) : g p = h p := by
        by_cases hd : some p = skip
        · simp [h, hd]
        · simp [h, hd, ih p hp hd]
      have hc := T.operands_causal x g h k hag
      have hports : T.operands x h (first k) = T.operands x' g' (first k) ∧
          T.operands x h (second k) = T.operands x' g' (second k) := by
        obtain ⟨h₁,h₂⟩ := same k hk
        constructor
        · rw [show x = onehot i j by rfl, show x' = onehot i' j' by rfl,
            operand_word, operand_word, hfb, h₁]
        · rw [show x = onehot i j by rfl, show x' = onehot i' j' by rfl,
            operand_word, operand_word, hfb, h₂]
      change T.products x k = T.products x' k
      rw [T.product_eq x k, T.product_eq x' k]
      change T.operands x g (first k) * T.operands x g (second k) =
        T.operands x' g' (first k) * T.operands x' g' (second k)
      rw [hc.1, hc.2, hports.1, hports.2]
  have hfin : T.feedback g = T.feedback g' := by
    apply T.feedback_agree
    intro k hk
    exact hp k (fun he => hk (dead k he))
  rw [← output_operands, ← output_operands, operand_word, operand_word]
  change (T.leftWord i (Fin.last _) + T.rightWord j (Fin.last _) + T.feedback g (Fin.last _) +
      T.phases (Fin.last _)) + (T.leftWord i (Fin.last _) + T.rightWord j (Fin.last _)) =
    (T.leftWord i' (Fin.last _) + T.rightWord j' (Fin.last _) + T.feedback g' (Fin.last _) +
      T.phases (Fin.last _)) + (T.leftWord i' (Fin.last _) + T.rightWord j' (Fin.last _))
  rw [hfin]
  linear_combination add_self_eq_zero (T.leftWord i (Fin.last _) + T.rightWord j (Fin.last _)) - add_self_eq_zero (T.leftWord i' (Fin.last _) + T.rightWord j' (Fin.last _))

private def truncate {k : ℕ} (v : Vec (k+1)) : Vec k := v ∘ Fin.castSucc

private def firstBase {t : ℕ} (j : Fin t) : Fin (2*t) := ⟨2*j.val, by omega⟩

private def secondBase {t : ℕ} (j : Fin t) : Fin (2*t) := ⟨2*j.val+1, by omega⟩

private theorem normal_form (T : Mixed (N+N)) :
    ∃ H : Vec (2*T.nonlinear) → F, ∀ i j,
      T.eval (onehot i j) =
        H (truncate (T.leftWord i) + truncate (T.rightWord j)) +
          T.leftWord i (Fin.last _) + T.rightWord j (Fin.last _) := by
  classical
  let tag : Fin N × Fin N → Vec (2*T.nonlinear) :=
    fun p => truncate (T.leftWord p.1) + truncate (T.rightWord p.2)
  let residual : Fin N × Fin N → F :=
    fun p => T.eval (onehot p.1 p.2) + (T.leftWord p.1 (Fin.last _) + T.rightWord p.2 (Fin.last _))
  let H : Vec (2*T.nonlinear) → F := fun z =>
    if h : ∃ p, tag p = z then residual (Classical.choose h) else 0
  refine ⟨H,fun i j => ?_⟩
  let p : Fin N × Fin N := (i,j)
  have he : ∃ p', tag p' = tag p := ⟨p,rfl⟩
  have hc : tag (Classical.choose he) = tag p := Classical.choose_spec he
  have hres : residual (Classical.choose he) = residual p := by
    apply T.compare_runs _ _ _ _ none
    · simp
    · intro k _
      exact ⟨congrFun hc (firstBase k), congrFun hc (secondBase k)⟩
  change T.eval (onehot i j) = (if h : ∃ p', tag p' = tag p then residual (Classical.choose h) else 0) +
    T.leftWord i (Fin.last _) + T.rightWord j (Fin.last _)
  rw [dif_pos he, hres]
  simp only [residual,p]
  linear_combination -(add_self_eq_zero (T.leftWord i (Fin.last _) + T.rightWord j (Fin.last _)))

end Mixed

namespace XorProgram

private def known {W : Type} [Zero W] (x : Fin n → W) : Set W :=
  insert 0 (Set.range x)

private noncomputable def missing {W : Type} [Zero W] (allowed : Finset W) (x : Fin n → W) : Finset W :=
  open Classical in allowed.filter (fun w => w ∉ known x)

private theorem known_snoc {W : Type} [Zero W] (x : Fin n → W) (w : W) :
    known (Fin.snoc x w) = insert w (known x) := by
  ext v
  constructor
  · intro h
    rcases h with he|⟨j,hj⟩
    · exact Or.inr (Or.inl he)
    · refine Fin.lastCases ?_ (fun i => ?_) j hj
      · intro hi
        exact Or.inl (by simpa using hi.symm)
      · intro hi
        exact Or.inr (Or.inr ⟨i, by simpa using hi⟩)
  · intro h
    rcases h with he|he|⟨j,hj⟩
    · exact Or.inr ⟨Fin.last n, by simpa using he.symm⟩
    · exact Or.inl he
    · exact Or.inr ⟨j.castSucc, by simpa using hj⟩

private theorem missing_snoc {W : Type} [Zero W] (allowed : Finset W)
    (x : Fin n → W) (w : W) [DecidableEq W] :
    missing allowed (Fin.snoc x w) = (missing allowed x).erase w := by
  classical
  ext v
  simp only [missing, Finset.mem_filter, known_snoc, Set.mem_insert_iff, not_or, Finset.mem_erase]
  tauto

private theorem synthesize_of_reachable {W : Type} [AddMonoid W] [DecidableEq W] (allowed : Finset W)
    (x : Fin n → W) (target : Fin m → W)
    (h : ∀ j, Upper.Reachable (known x) allowed (target j)) :
    ∃ T : XorProgram n m, T.count ≤ (missing allowed x).card ∧
      T.eval x = target ∧ ∀ j, (T.live j = true ↔ target j ≠ 0) := by
  classical
  generalize heq : (missing allowed x).card = bound
  induction bound using Nat.strongRecOn generalizing n with
  | ind bound ih =>
    by_cases hc : ∀ a ∈ known x, ∀ b ∈ known x, a+b ∈ allowed → a+b ∈ known x
    · have reach {w : W} (hw : Upper.Reachable (known x) allowed w) : w ∈ known x := by
        induction hw with
        | base ha => exact ha
        | add ha _ _ hi hj => exact hc _ hi _ hj ha
      have present (j : Fin m) (hzero : target j ≠ 0) : ∃ i, x i = target j :=
        (Set.mem_insert_iff.mp (reach (h j))).resolve_left hzero
      let p (j : Fin m) : Option (Fin n) :=
        if hj : target j ≠ 0 then some (Classical.choose (present j hj)) else none
      refine ⟨.ret p,Nat.zero_le _,?_,?_⟩
      · funext j
        by_cases hj : target j ≠ 0
        · simpa [eval,p,hj] using Classical.choose_spec (present j hj)
        · have hz : target j = 0 := not_ne_iff.mp hj
          simp [eval,p,hj,hz]
      · intro j
        by_cases hj : target j ≠ 0 <;> simp [live,p,hj]
    · push_neg at hc
      obtain ⟨a,ha,b,hb,hab,hn⟩ := hc
      have ha' : a ∈ Set.range x := (Set.mem_insert_iff.mp ha).resolve_left (fun hzero => by
        subst a
        exact hn (by simpa using hb))
      have hb' : b ∈ Set.range x := (Set.mem_insert_iff.mp hb).resolve_left (fun hzero => by
        subst b
        exact hn (by simpa using ha))
      obtain ⟨i,rfl⟩ := ha'
      obtain ⟨j,rfl⟩ := hb'
      let w := x i + x j
      let z : Fin (n+1) → W := Fin.snoc x w
      have hw : w ∈ missing allowed x := Finset.mem_filter.mpr ⟨hab,hn⟩
      have hz : (missing allowed z).card + 1 = bound := by
        dsimp only [z]
        rw [missing_snoc, Finset.card_erase_of_mem hw]
        have hpos := Finset.card_pos.mpr ⟨w,hw⟩
        omega
      have hsub : known x ⊆ known z := by
        dsimp only [z]
        rw [known_snoc]
        exact Set.subset_insert _ _
      have hr {u : W} (hu : Upper.Reachable (known x) allowed u) :
          Upper.Reachable (known z) allowed u := by
        induction hu with
        | base hv => exact .base (hsub hv)
        | add hv _ _ ha hb => exact .add hv ha hb
      obtain ⟨T,hT,he,hl⟩ := ih (missing allowed z).card (by omega) z
        (fun j => hr (h j)) rfl
      refine ⟨.push i j T,?_,he,hl⟩
      change T.count + 1 ≤ _
      omega

private theorem synthesize {W : Type} [AddMonoid W] [DecidableEq W] (allowed : Finset W)
    (x : Fin n → W) (target : Fin m → W)
    (h : ∀ j, Upper.Reachable (known x) allowed (target j)) :
    ∃ T : XorProgram n m, T.count ≤ allowed.card ∧
      T.eval x = target ∧ ∀ j, (T.live j = true ↔ target j ≠ 0) := by
  obtain ⟨T,ht,he,hl⟩ := synthesize_of_reachable allowed x target h
  refine ⟨T,ht.trans ?_,he,hl⟩
  classical
  unfold missing
  apply Finset.card_filter_le

end XorProgram

namespace XorProgram

private theorem literal_weaken_eval (a : Literal n) (x : Vec n) (v : F) :
    a.weaken.eval (Fin.snoc x v) = a.eval x := by
  rcases a with ⟨(_|i),p⟩ <;> simp [Literal.weaken, Literal.eval]

private def accumulate : (s : ℕ) → {n : ℕ} →
    (Fin s → Literal n × Literal n) → Literal n → Mixed n
  | 0, _, _, a => .ret a
  | s+1, n, terms, a =>
      let rest (j : Fin s) := ((terms j.succ).1.weaken, (terms j.succ).2.weaken)
      .mul (terms 0).1 (terms 0).2
        (match a.wire with
         | none => accumulate s rest ⟨some (Fin.last n), a.phase⟩
         | some i => .xor i.castSucc (Fin.last n)
             (accumulate s (fun j => ((rest j).1.weaken,(rest j).2.weaken))
               ⟨some (Fin.last (n+1)), a.phase⟩))

private theorem accumulate_count (s : ℕ) (terms : Fin s → Literal n × Literal n)
    (a : Literal n) :
    (accumulate s terms a).nonlinear = s ∧ (accumulate s terms a).linear ≤ s := by
  induction s generalizing n with
  | zero => simp [accumulate, Mixed.linear]
  | succ s ih =>
      cases hw : a.wire
      · simp only [accumulate, hw, Mixed.nonlinear, Mixed.linear]
        exact ⟨congrArg (·+1) (ih _ _).1, (ih _ _).2.trans (Nat.le_succ _)⟩
      · simp only [accumulate, hw, Mixed.nonlinear, Mixed.linear]
        exact ⟨congrArg (·+1) (ih _ _).1,Nat.succ_le_succ (ih _ _).2⟩

private theorem accumulate_eval (s : ℕ) (terms : Fin s → Literal n × Literal n)
    (a : Literal n) (x : Vec n) :
    (accumulate s terms a).eval x = a.eval x +
      ∑ i, (terms i).1.eval x * (terms i).2.eval x := by
  induction s generalizing n with
  | zero => simp [accumulate, Mixed.eval]
  | succ s ih =>
      rw [Fin.sum_univ_succ]
      cases hw : a.wire
      · simp only [accumulate, Mixed.eval, hw, ih, literal_weaken_eval]
        simp only [Literal.eval, hw, Option.elim_none, Option.elim_some, Fin.snoc_last, zero_add]
        ac_rfl
      · simp only [accumulate, Mixed.eval, hw, ih, literal_weaken_eval]
        simp only [Literal.eval, hw, Option.elim_none, Option.elim_some, Fin.snoc_last, Fin.snoc_castSucc]
        ac_rfl

private def finish (P : XorProgram n m)
    (tail : ∀ {w : ℕ}, (Fin m → Option (Fin w)) → Mixed w) : Mixed n :=
  match P with
  | .ret p => tail p
  | .push a b T => .xor a b (T.finish tail)

private theorem finish_count (P : XorProgram n m)
    (tail : ∀ {w : ℕ}, (Fin m → Option (Fin w)) → Mixed w)
    (h : ∀ {w} (p : Fin m → Option (Fin w)), (tail p).nonlinear = s ∧ (tail p).linear ≤ s) :
    (P.finish tail).nonlinear = s ∧ (P.finish tail).linear ≤ P.count+s := by
  induction P with
  | ret p => simpa [finish,count] using h p
  | push a b T ih =>
      have hi := ih tail h
      simp only [finish,Mixed.nonlinear,Mixed.linear,count]
      exact ⟨hi.1, by have hh := hi.2; omega⟩

private theorem finish_eval (P : XorProgram n m)
    (tail : ∀ {w : ℕ}, (Fin m → Option (Fin w)) → Mixed w) (out : Vec m → F)
    (h : ∀ {w} (p : Fin m → Option (Fin w)) (x : Vec w), (tail p).eval x = out ((ret p).eval x))
    (x : Vec n) :
    (P.finish tail).eval x = out (P.eval x) := by
  induction P with
  | ret p => exact h p x
  | push a b T ih => exact ih tail out h _

private def quadraticTail (phase : Vec (2*s+1)) (p : Fin (2*s+1) → Option (Fin n)) : Mixed n :=
  accumulate s (fun i =>
     (⟨p (Mixed.first i), phase (Mixed.first i)⟩,
      ⟨p (Mixed.second i), phase (Mixed.second i)⟩))
    ⟨p (Fin.last (2*s)), phase (Fin.last (2*s))⟩

private def appendQuadratic (P : XorProgram n (2*s+1)) (phase : Vec (2*s+1)) : Mixed n :=
  P.finish (quadraticTail phase)

private theorem appendQuadratic_count (P : XorProgram n (2*s+1)) (phase : Vec (2*s+1)) :
    (P.appendQuadratic phase).nonlinear = s ∧
      (P.appendQuadratic phase).linear ≤ P.count+s :=
  P.finish_count (quadraticTail phase) (fun _ => accumulate_count s _ _)

private theorem appendQuadratic_eval (P : XorProgram n (2*s+1)) (phase : Vec (2*s+1))
    (x : Vec n) :
    (P.appendQuadratic phase).eval x =
      P.eval x (Fin.last (2*s)) + phase (Fin.last (2*s)) +
        ∑ i, (P.eval x (Mixed.first i) + phase (Mixed.first i)) *
          (P.eval x (Mixed.second i) + phase (Mixed.second i)) := by
  unfold appendQuadratic
  refine P.finish_eval (quadraticTail phase) (fun v =>
    v (Fin.last (2*s)) + phase (Fin.last (2*s)) +
      ∑ i, (v (Mixed.first i) + phase (Mixed.first i)) *
        (v (Mixed.second i) + phase (Mixed.second i))) ?_ x
  intro w p x
  simp [quadraticTail, accumulate_eval, eval, Literal.eval]

end XorProgram

private noncomputable def liftDisagreements {k : ℕ} (L R : Vec k → F) : ℕ :=
  (Finset.univ.filter fun v => L v ≠ R v).card

private noncomputable def liftZeros {k : ℕ} (L R : Vec k → F) : ℕ :=
  (if L 0 = 0 then 1 else 0) + (if R 0 = 0 then 1 else 0)

private noncomputable def liftTargets {k : ℕ} (L R : Vec k → F) : Finset (Vec (k+1)) := by
  classical
  exact (Finset.univ.image fun v => Fin.snoc v (L v)) ∪
    ((Finset.univ.filter fun v => L v ≠ R v).image fun v => Fin.snoc v (R v))

private theorem liftTargets_card {k : ℕ} (L R : Vec k → F) :
    (liftTargets L R).card = 2 ^ k + liftDisagreements L R := by
  classical
  unfold liftTargets
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ (fun _ _ h => (Fin.snoc_inj.mp h).1),
      Finset.card_image_of_injective _ (fun _ _ h => (Fin.snoc_inj.mp h).1),
      Finset.card_univ, card_vec]
    rfl
  · refine Finset.disjoint_left.mpr (fun w hwL hwR => ?_)
    obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hwL
    obtain ⟨u, hu, hu'⟩ := Finset.mem_image.mp hwR
    obtain ⟨rfl, h⟩ := Fin.snoc_inj.mp (hv.trans hu'.symm)
    exact (Finset.mem_filter.mp hu).2 h

private theorem mem_liftTargets {k : ℕ} {L R : Vec k → F} {w : Vec (k+1)} :
    w ∈ liftTargets L R ↔ (∃ v, w = Fin.snoc v (L v)) ∨ (∃ v, w = Fin.snoc v (R v)) := by
  classical
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨v, -, hv⟩ := Finset.mem_image.mp h
      exact Or.inl ⟨v, hv.symm⟩
    · obtain ⟨v, -, hv⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨v, hv.symm⟩
  · rintro (⟨v, rfl⟩ | ⟨v, rfl⟩)
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩)
    · by_cases h : L v = R v
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, by rw [h]⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩)

private theorem lift_count {k m : ℕ} (P : XorProgram (k+1) m) (L R : Vec k → F)
    (hL : ∀ v, ∃ i, P.eval XorProgram.e i = Fin.snoc v (L v))
    (hR : ∀ v, ∃ i, P.eval XorProgram.e i = Fin.snoc v (R v))
    (hphase : (∀ v, L v = R v) → ∃ v, L v ≠ 0) :
    2 ^ k + max 1 (liftDisagreements L R) + liftZeros L R ≤ P.count + k + 3 := by
  classical
  let T := liftTargets L R
  let U := (Finset.univ : Finset (Fin (k+1))).image XorProgram.e
  let X := (P.trace XorProgram.e).toFinset
  let A := insert (0 : Vec (k+1)) (U ∪ X)
  let c : Vec (k+1) := XorProgram.e (Fin.last k)
  have hT : T.card = 2 ^ k + liftDisagreements L R := liftTargets_card L R
  have hA : A.card ≤ P.count + k + 2 := by
    have h₀ := Finset.card_insert_le (a := (0 : Vec (k+1))) (s := U ∪ X)
    have h₁ := Finset.card_union_le U X
    have h₂ : U.card ≤ k+1 := by
      simpa [U] using Finset.card_image_le (s := (Finset.univ : Finset (Fin (k+1)))) (f := XorProgram.e)
    have h₃ : X.card ≤ P.count := by
      simpa only [X, XorProgram.trace_length] using (P.trace XorProgram.e).toFinset_card_le
    change A.card ≤ _ at h₀
    omega
  have hcA : c ∈ A :=
    Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨Fin.last k, Finset.mem_univ _, rfl⟩))
  have heval (i : Fin m) : P.eval XorProgram.e i ∈ A := by
    by_cases h : P.eval XorProgram.e i = 0
    · simp [A,h]
    · rcases P.eval_mem_trace XorProgram.e i h with ⟨j, hj⟩ | hj
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩))
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (List.mem_toFinset.mpr hj))
  have hTA : T ⊆ A := by
    intro w hw
    rcases mem_liftTargets.mp hw with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · obtain ⟨i, hi⟩ := hL v
      exact hi ▸ heval i
    · obtain ⟨i, hi⟩ := hR v
      exact hi ▸ heval i
  have hbase := (Finset.card_le_card hTA).trans hA
  have hcForm : c = Fin.snoc (0 : Vec k) 1 := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [c, XorProgram.e]
    · simp [c, XorProgram.e, Fin.castSucc_ne_last]
  have hcNotTarget (hzero : L 0 = 0 ∧ R 0 = 0) : c ∉ T := by
    intro h
    rcases mem_liftTargets.mp h with ⟨v, hv⟩ | ⟨v, hv⟩
    · rw [hcForm] at hv
      obtain ⟨rfl, hj⟩ := Fin.snoc_inj.mp hv
      simp [hzero.1] at hj
    · rw [hcForm] at hv
      obtain ⟨rfl, hj⟩ := Fin.snoc_inj.mp hv
      simp [hzero.2] at hj
  by_cases hD : liftDisagreements L R = 0
  · have heq : ∀ v, L v = R v := by
      intro v
      by_contra h
      have hm : v ∈ Finset.univ.filter (fun u => L u ≠ R u) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      have hEmpty : v ∈ (∅ : Finset (Vec k)) := Finset.card_eq_zero.mp hD ▸ hm
      exact Finset.notMem_empty _ hEmpty
    rw [hD, max_eq_left (by omega : 0 ≤ 1)]
    by_cases hzero : L 0 = 0
    · have hRzero : R 0 = 0 := (heq 0).symm.trans hzero
      have hz : liftZeros L R = 2 := by simp [liftZeros, hzero, hRzero]
      rw [hz]
      have hgraph {w : Vec (k+1)} : w ∈ T → ∃ v, w = Fin.snoc v (L v) := by
        intro hw
        rcases mem_liftTargets.mp hw with h | ⟨v, hv⟩
        · exact h
        · exact ⟨v, (heq v).symm ▸ hv⟩
      have hcT := hcNotTarget ⟨hzero, hRzero⟩
      have hextra : ∃ w ∈ A, w ∉ insert c T := by
        by_contra! hAll
        let K : Set (Vec (k+1)) := {w | (w ∈ T ∧ w (Fin.last k) = 0) ∨ w = c}
        have hInit (j : Fin (k+1)) : XorProgram.e j ∈ K := by
          by_cases hj : j = Fin.last k
          · exact Or.inr (congrArg XorProgram.e hj)
          · have hU : XorProgram.e j ∈ A := Finset.mem_insert_of_mem
              (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
            rcases Finset.mem_insert.mp (hAll _ hU) with he | he
            · exact Or.inr he
            · exact Or.inl ⟨he, by simp [XorProgram.e, Ne.symm hj]⟩
        have hAdd (a : Vec (k+1)) (ha : a ∈ T) :
            a + c ∉ T := by
          intro hb
          obtain ⟨u, hu⟩ := hgraph ha
          obtain ⟨v, hv⟩ := hgraph hb
          have huv : u = v := by
            funext i
            have hh := congrFun hv i.castSucc
            simpa [hu,hcForm] using hh
          have hlast := congrFun hv (Fin.last k)
          simp [hu,hcForm,huv] at hlast
        have hStep (a : Vec (k+1)) (ha : a ∈ K) (b : Vec (k+1)) (hb : b ∈ K)
            (hs : a+b ∈ (↑(insert c T) : Set (Vec (k+1)))) : a+b ∈ K := by
          rcases Finset.mem_insert.mp hs with hs' | hs'
          · exact Or.inr hs'
          rcases ha with ⟨ha, ha₀⟩ | rfl
          · rcases hb with ⟨hb, hb₀⟩ | rfl
            · exact Or.inl ⟨hs', by simp [Pi.add_apply, ha₀,hb₀]⟩
            · exact (hAdd a ha hs').elim
          · rcases hb with ⟨hb, hb₀⟩ | rfl
            · exact (hAdd b hb (add_comm c b ▸ hs')).elim
            · exact Or.inl ⟨hs', add_self_eq_zero _⟩
        obtain ⟨v, hv⟩ := hphase heq
        obtain ⟨i, hi⟩ := hL v
        have hne : P.eval XorProgram.e i ≠ 0 := by
          intro h
          exact hv (by simpa [hi] using congrFun h (Fin.last k))
        have hm := P.eval_trace_invariant XorProgram.e (↑(insert c T) : Set (Vec (k+1))) K hInit
          (fun w hw => hAll w (Finset.mem_insert_of_mem (Finset.mem_union_right _ (List.mem_toFinset.mpr hw)))) hStep i hne
        rw [hi] at hm
        rcases hm with ⟨_, hh⟩ | hh
        · exact hv (by simpa using hh)
        · exact hcT (hh ▸ mem_liftTargets.mpr (Or.inl ⟨v, rfl⟩))
      obtain ⟨w, hwA, hwT⟩ := hextra
      have hsub : insert w (insert c T) ⊆ A := Finset.insert_subset hwA (Finset.insert_subset hcA hTA)
      have hbig := (Finset.card_le_card hsub).trans hA
      rw [Finset.card_insert_of_notMem hwT, Finset.card_insert_of_notMem hcT, hT, hD] at hbig
      omega
    · have hRzero : R 0 ≠ 0 := fun h => hzero ((heq 0).trans h)
      have hz : liftZeros L R = 0 := by simp [liftZeros, hzero, hRzero]
      rw [hz]
      omega
  · have hDpos : 1 ≤ liftDisagreements L R := by omega
    rw [max_eq_right hDpos]
    by_cases hzero : L 0 = 0 ∧ R 0 = 0
    · have hz : liftZeros L R = 2 := by simp [liftZeros, hzero.1, hzero.2]
      have hcT := hcNotTarget hzero
      have hsub : insert c T ⊆ A := Finset.insert_subset hcA hTA
      have hbig := (Finset.card_le_card hsub).trans hA
      rw [Finset.card_insert_of_notMem hcT, hT] at hbig
      rw [hz]
      omega
    · have hz : liftZeros L R ≤ 1 := by
        by_cases hl : L 0 = 0 <;> by_cases hr : R 0 = 0 <;>
          simp_all [liftZeros]
      omega

private theorem snoc_truncate {k : ℕ} (v : Vec (k+1)) :
    Fin.snoc (Mixed.truncate v) (v (Fin.last k)) = v := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [Mixed.truncate]

private theorem sum_live_lift {k N m : ℕ} (P : XorProgram (k+1) m)
    (E : Fin N ≃ Vec k) (L : Vec k → F) (r : Fin N → Fin m)
    (h : ∀ i, P.eval XorProgram.e (r i) = Fin.snoc (E i) (L (E i))) :
    N ≤ (∑ i, (P.live (r i)).toNat) + (if L 0 = 0 then 1 else 0) := by
  classical
  let p := E.symm 0
  have hp : E p = 0 := E.apply_symm_apply 0
  have point (i : Fin N) :
      1 ≤ (P.live (r i)).toNat + (if i = p then if L 0 = 0 then 1 else 0 else 0) := by
    cases ht : P.live (r i) with
    | true => simp [ht]
    | false =>
        have hz := P.eval_of_dead XorProgram.e (r i) ht
        have hz' : Fin.snoc (fun _ : Fin k => (0 : F)) (0 : F) = (0 : Vec (k+1)) := by
          funext j
          refine Fin.lastCases ?_ (fun r => ?_) j <;> simp
        rw [h i, ← hz'] at hz
        obtain ⟨he,hl⟩ := Fin.snoc_inj.mp hz
        have hi : i = p := E.injective (he.trans hp.symm)
        rw [he] at hl
        change L 0 = 0 at hl
        simp [hi,hl]
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N))) (fun i _ => point i)
  simpa [Finset.sum_add_distrib] using hh

private theorem Mixed.lower_bound_matched (T : Mixed (N+N)) (hN : N = 2^(2*T.nonlinear))
    (ht : 0 < T.nonlinear) (label : Fin N ≃ Vec (2*T.nonlinear)) (Q : Vec (2*T.nonlinear) → F)
    (repr : ∀ i j, T.eval (Mixed.onehot i j) = dot (label i) (label j) + Q (label i)) :
    3*N + max 1 (distance Q) ≤ T.linear + T.nonlinear + 2*T.nonlinear + 4 := by
  classical
  let k := 2*T.nonlinear
  let a (x : Vec k) := Mixed.truncate (T.leftWord (label.symm x))
  let b (y : Vec k) := Mixed.truncate (T.rightWord (label.symm y))
  let l (x : Vec k) := T.leftWord (label.symm x) (Fin.last k)
  let r (y : Vec k) := T.rightWord (label.symm y) (Fin.last k)
  obtain ⟨H,hH⟩ := T.normal_form
  have form (x y : Vec k) : dot x y + Q x = H (a x + b y) + l x + r y := by
    have h := repr (label.symm x) (label.symm y)
    rw [hH, label.apply_symm_apply, label.apply_symm_apply] at h
    exact h.symm
  let A : Vec k ≃ Vec k := Equiv.ofBijective a (bijective_of_injective (row_injective form))
  let B : Vec k ≃ Vec k := Equiv.ofBijective b (bijective_of_injective (col_injective form))
  let L (v : Vec k) := l (A.symm v)
  let R (v : Vec k) := r (B.symm v)
  let σ := A.trans B.symm
  have hσ (x : Vec k) : b (σ x) = a x := B.apply_symm_apply (A x)
  have hD := affine_discrepancy form σ hσ
  have hDR : (Finset.univ.filter fun x => l x ≠ r (σ x)).card = liftDisagreements L R := by
    unfold liftDisagreements
    apply Finset.card_bij (fun x _ => A x)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      simpa [L,R,σ] using hx
    · intro x _ y _ he
      exact A.injective he
    · intro v hv
      refine ⟨A.symm v,?_,A.apply_symm_apply v⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      simpa [L,R,σ] using hv
  rw [hDR] at hD
  let P := T.portProgram.transpose
  let idxL (i : Fin N) := (i.castAdd N).castAdd T.nonlinear
  let idxR (i : Fin N) := (i.natAdd N).castAdd T.nonlinear
  let idxG (j : Fin T.nonlinear) := j.natAdd (N+N)
  have hleft (i : Fin N) :
      P.eval XorProgram.e (idxL i) = Fin.snoc ((label.trans A) i) (L ((label.trans A) i)) := by
    change T.leftWord i = _
    symm
    simp only [Equiv.trans_apply, L, Equiv.symm_apply_apply, l]
    rw [show A (label i) = Mixed.truncate (T.leftWord i) by change a (label i) = _; simp [a]]
    exact snoc_truncate _
  have hright (i : Fin N) :
      P.eval XorProgram.e (idxR i) = Fin.snoc ((label.trans B) i) (R ((label.trans B) i)) := by
    change T.rightWord i = _
    symm
    simp only [Equiv.trans_apply, R, Equiv.symm_apply_apply, r]
    rw [show B (label i) = Mixed.truncate (T.rightWord i) by change b (label i) = _; simp [b]]
    exact snoc_truncate _
  have hphase (eqLR : ∀ v, L v = R v) : ∃ v, L v ≠ 0 := by
    by_contra hz
    push_neg at hz
    have hzL (x : Vec k) : l x = 0 := by simpa [L] using hz (A x)
    have hzR (y : Vec k) : r y = 0 := by
      have h := (eqLR (B y)).symm.trans (hz (B y))
      simpa [R] using h
    exact graph_has_phase (by dsimp [k]; omega) form B.surjective hzL hzR
  have hbits := lift_count P L R
    (fun v => ⟨idxL ((label.trans A).symm v), by simp [hleft]⟩)
    (fun v => ⟨idxR ((label.trans B).symm v), by simp [hright]⟩) hphase
  have hul := sum_live_lift P (label.trans A) L idxL hleft
  have hur := sum_live_lift P (label.trans B) R idxR hright
  have hnl (j : Fin T.nonlinear) : P.live (idxG j) = true := by
    by_contra hd
    have hz : T.productWord j = 0 :=
      T.portProgram.dead_coefficient _ (Bool.eq_false_of_not_eq_true hd)
    let x₀ := A.symm 0
    let x₁ := A.symm (unit (Mixed.firstBase j))
    have h₀ : a x₀ = 0 := A.apply_symm_apply _
    have h₁ : a x₁ = unit (Mixed.firstBase j) := A.apply_symm_apply _
    have hne : x₀ ≠ x₁ := by
      intro he
      have h : (0 : Vec k) = unit (Mixed.firstBase j) := by rw [← h₀,← h₁,he]
      exact (zero_ne_one : (0 : F) ≠ 1) (by simpa [unit] using congrFun h (Mixed.firstBase j))
    have he (y : Vec k) :
        dot x₀ y + Q x₀ + (l x₀ + r y) = dot x₁ y + Q x₁ + (l x₁ + r y) := by
      have h := T.compare_runs (label.symm x₀) (label.symm y) (label.symm x₁) (label.symm y)
        (some j) (fun q h => by injection h with h'; simpa [h'] using hz) (by
          intro q hq
          have hf : Mixed.firstBase q ≠ Mixed.firstBase j := by
            intro hh
            apply hq
            congr 1
            apply Fin.ext
            have hn := congrArg Fin.val hh
            change 2*q.val = 2*j.val at hn
            omega
          have hs : Mixed.secondBase q ≠ Mixed.firstBase j := by
            intro hh
            have hn := congrArg Fin.val hh
            change 2*q.val+1 = 2*j.val at hn
            omega
          have hfirst : a x₀ (Mixed.firstBase q) = a x₁ (Mixed.firstBase q) := by
            simp [h₀,h₁,unit,hf]
          have hsecond : a x₀ (Mixed.secondBase q) = a x₁ (Mixed.secondBase q) := by
            simp [h₀,h₁,unit,hs]
          exact ⟨congrArg (· + T.rightWord (label.symm y) (Mixed.first q)) hfirst,
            congrArg (· + T.rightWord (label.symm y) (Mixed.second q)) hsecond⟩)
      rw [repr, repr] at h
      simpa only [label.apply_symm_apply] using h
    apply hne
    funext i
    have hi := he (unit i)
    have h0 := he 0
    simp only [dot_unit,dot_zero_right,zero_add] at hi h0
    linear_combination hi-h0
  have hsum : P.outputs =
      (∑ i, (P.live (idxL i)).toNat) + (∑ i, (P.live (idxR i)).toNat) + T.nonlinear := by
    unfold XorProgram.outputs
    rw [Fin.sum_univ_add,Fin.sum_univ_add]
    simp [idxL,idxR,idxG, hnl]
  have hpc := T.portProgram.transpose_cost
  have hports := T.portProgram.outputs_le
  have hc : T.portProgram.count = T.linear := T.count_linearize _ _
  change P.count + P.outputs ≤ T.portProgram.count + T.portProgram.outputs at hpc
  rw [hc,hsum] at hpc
  rw [← hN] at hbits
  unfold liftZeros at hbits
  have hm : max 1 (distance Q) ≤ max 1 (liftDisagreements L R) := max_le_max_left _ hD
  omega

private theorem Mixed.lower_bound (T : Mixed (N+N)) (hk : k = 2*s)
    (hN : N = 2^k) (hs : 0 < s) (label : Fin N ≃ Vec k) (Q : Vec k → F)
    (ht : T.nonlinear ≤ s)
    (repr : ∀ i j, T.eval (Mixed.onehot i j) = dot (label i) (label j) + Q (label i)) :
    T.nonlinear = s ∧ 3*N + max 1 (distance Q) ≤ T.linear + T.nonlinear + 2*s + 4 := by
  obtain ⟨H,hH⟩ := T.normal_form
  let a (x : Vec k) := Mixed.truncate (T.leftWord (label.symm x))
  let b (y : Vec k) := Mixed.truncate (T.rightWord (label.symm y))
  have form (x y : Vec k) :
      dot x y + Q x = H (a x + b y) + T.leftWord (label.symm x) (Fin.last _) +
        T.rightWord (label.symm y) (Fin.last _) := by
    have h := repr (label.symm x) (label.symm y)
    rw [hH, label.apply_symm_apply,label.apply_symm_apply] at h
    exact h.symm
  have hdim := dim_le (row_injective form)
  have hts : T.nonlinear = s := by omega
  have he : k = 2*T.nonlinear := by omega
  clear hk
  subst k
  refine ⟨hts,?_⟩
  simpa only [hts] using T.lower_bound_matched hN (by omega) label Q repr

open PEqualNP.CircuitLowerBounds

private abbrev Bit := ZMod 2

private def bit (b : Bool) : Bit := if b then 1 else 0

private def asBool (x : Bit) : Bool := decide (x = 1)

@[simp] private theorem bit_asBool (x : Bit) : bit (asBool x) = x :=
  (by decide : ∀ x : Bit, bit (asBool x) = x) x

@[simp] private theorem asBool_bit (b : Bool) : asBool (bit b) = b := by
  cases b <;> rfl

private theorem bit_injective : Function.Injective bit := by
  intro a b h
  simpa using congrArg asBool h

private def oddGate (op : GateOp) : Bool :=
  xor (xor (op.eval [false,false]) (op.eval [false,true]))
      (xor (op.eval [true,false]) (op.eval [true,true]))

private def binaryGate (g : Gate) : Bool := g.inputs.length == 2

private def chargedProduct (g : Gate) : Bool := binaryGate g && oddGate g.op

private def binaryCost (gs : List Gate) : ℕ := gs.countP binaryGate

private def nonlinearCost (gs : List Gate) : ℕ := gs.countP chargedProduct

private def constant (c : Bit) : Literal n := ⟨none,c⟩

@[simp] private theorem constant_eval (x : Fin n → Bit) (c : Bit) :
    (constant c).eval x = c := by
  simp [constant, Literal.eval]

private def wireLit (i : Fin n) (p : Bit) : Literal n := ⟨some i,p⟩

private def Literal.flip (l : Literal n) (p : Bit) : Literal n := ⟨l.wire, l.phase+p⟩

private theorem Literal.eval_flip (l : Literal n) (x : Fin n → Bit) (p : Bit) :
    (l.flip p).eval x = l.eval x + p := by
  simp [Literal.flip, Literal.eval, add_assoc]

private theorem Literal.eval_weaken (l : Literal n) (x : Fin n → Bit) (v : Bit) :
    l.weaken.eval (Fin.snoc x v) = l.eval x := by
  rcases l with ⟨(_|i),p⟩ <;> simp [Literal.weaken, Literal.eval]

private theorem Literal.eval_last (x : Fin n → Bit) (v p : Bit) :
    (wireLit (Fin.last n) p).eval (Fin.snoc x v) = v+p := by
  simp [wireLit, Literal.eval]

private inductive GateStep (n : ℕ)
  | copy (a : Literal n)
  | add (i j : Fin n) (phase : Bit)
  | mul (a b : Literal n) (phase : Bit)

private def GateStep.eval (s : GateStep n) (x : Fin n → Bit) : Bit :=
  match s with
  | .copy a => a.eval x
  | .add i j p => x i + x j + p
  | .mul a b p => a.eval x * b.eval x + p

private def GateStep.isMul (s : GateStep n) : Bool :=
  match s with
  | .mul .. => true
  | _ => false

private def GateStep.isBinary (s : GateStep n) : Bool :=
  match s with
  | .copy .. => false
  | _ => true

private def affineStep (c a b : Bit) (u v : Literal n) : GateStep n :=
  if a = 0 then
    .copy (if b = 0 then constant c else v.flip c)
  else if b = 0 then
    .copy (u.flip c)
  else
    let p := u.phase + v.phase + c
    match u.wire, v.wire with
    | some i, some j => .add i j p
    | none, w | w, none => .copy ⟨w,p⟩

private theorem affineStep_correct (c a b : Bit) (u v : Literal n) (x : Fin n → Bit) :
    (affineStep c a b u v).eval x = c + a*u.eval x + b*v.eval x := by
  have hf := (by decide : ∀ x : Bit, x = 0 ∨ x = 1)
  rcases hf a with ha|ha <;> rcases hf b with hb|hb
  · simp [affineStep, GateStep.eval, ha, hb, constant, Literal.eval]
  · simp [affineStep, GateStep.eval, ha, hb, Literal.eval_flip, add_comm]
  · simp [affineStep, GateStep.eval, ha, hb, Literal.eval_flip, add_comm]
  · rcases u with ⟨(_|i),p⟩ <;> rcases v with ⟨(_|j),q⟩ <;>
      simp [affineStep, GateStep.eval, ha, hb, Literal.eval] <;> ac_rfl

private theorem affineStep_noMul (c a b : Bit) (u v : Literal n) :
    (affineStep c a b u v).isMul = false := by
  unfold affineStep
  split <;> rename_i ha
  · split <;> rfl
  · split
    · rfl
    · split <;> rfl

private def binaryStep (op : GateOp) (u v : Literal n) : GateStep n :=
  let c := bit (op.eval [false,false])
  let a := c + bit (op.eval [true,false])
  let b := c + bit (op.eval [false,true])
  if oddGate op then .mul (u.flip b) (v.flip a) (c+a*b)
  else affineStep c a b u v

private theorem binaryStep_mul (op : GateOp) (u v : Literal n) :
    (binaryStep op u v).isMul = oddGate op := by
  cases he : oddGate op
  · simpa only [binaryStep, he, Bool.false_eq_true, ite_false] using
      affineStep_noMul (bit (op.eval [false,false]))
        (bit (op.eval [false,false]) + bit (op.eval [true,false]))
        (bit (op.eval [false,false]) + bit (op.eval [false,true])) u v
  · simp [binaryStep, he, GateStep.isMul]

private theorem binaryTable (op : GateOp) (x y : Bool) :
    bit (op.eval [x,y]) = bit (op.eval [false,false]) +
      (bit (op.eval [false,false]) + bit (op.eval [true,false])) * bit x +
      (bit (op.eval [false,false]) + bit (op.eval [false,true])) * bit y +
      bit (oddGate op) * bit x * bit y := by
  unfold oddGate
  cases x <;> cases y <;>
    generalize op.eval [false,false] = c <;> generalize op.eval [false,true] = b <;>
    generalize op.eval [true,false] = a <;> generalize op.eval [true,true] = d <;>
    cases c <;> cases b <;> cases a <;> cases d <;> decide

private theorem binaryStep_correct (op : GateOp) (u v : Literal n) (x : Fin n → Bit) :
    (binaryStep op u v).eval x = bit (op.eval [asBool (u.eval x), asBool (v.eval x)]) := by
  rw [binaryTable, bit_asBool, bit_asBool]
  cases he : oddGate op
  · simp [binaryStep, he, bit, affineStep_correct]
  · simp [binaryStep, he, bit, GateStep.eval, Literal.eval_flip]
    exact (by decide : ∀ c a b x y : Bit,
      (x+b)*(y+a)+(c+a*b) = c+a*x+b*y+x*y) _ _ _ _ _

private def unaryStep (op : GateOp) (u : Literal n) : GateStep n :=
  let c := bit (op.eval [false])
  .copy (if op.eval [false] = op.eval [true] then constant c else u.flip c)

private theorem unaryStep_correct (op : GateOp) (u : Literal n) (x : Fin n → Bit) :
    (unaryStep op u).eval x = bit (op.eval [asBool (u.eval x)]) := by
  have he : u.eval x = 0 ∨ u.eval x = 1 := (by decide : ∀ c : Bit, c = 0 ∨ c = 1) _
  rcases he with he|he
  · have ha : asBool (u.eval x) = false := by rw [he]; decide
    rw [ha, unaryStep]
    generalize op.eval [false] = a
    generalize op.eval [true] = b
    cases a <;> cases b <;>
      simp [GateStep.eval, bit, Literal.eval_flip, he]
  · have ha : asBool (u.eval x) = true := by rw [he]; decide
    rw [ha, unaryStep]
    generalize op.eval [false] = a
    generalize op.eval [true] = b
    cases a <;> cases b <;>
      simp [GateStep.eval, bit, Literal.eval_flip, he]
    decide

private def getLit (ls : List (Literal n)) (i : ℕ) : Literal n := ls.getD i (constant 0)

private def gateStep (g : Gate) (ls : List (Literal n)) : GateStep n :=
  match g.inputs with
  | [] => .copy (constant (bit (g.op.eval [])))
  | [a] => unaryStep g.op (getLit ls a)
  | [a,b] => binaryStep g.op (getLit ls a) (getLit ls b)
  | _ => .copy (constant 0)

private theorem getD_map_default {α β : Type} (ls : List α) (i : ℕ) (f : α → β) (a : α) :
    (ls.map f).getD i (f a) = f (ls.getD i a) := by
  induction ls generalizing i with
  | nil => simp
  | cons a ls ih => cases i <;> simp [List.getD]

private def fieldGate (g : Gate) (w : List Bit) : Bit :=
  bit (g.op.eval (g.inputs.map fun i => asBool (w.getD i 0)))

private theorem gateStep_correct (g : Gate) (ls : List (Literal n)) (x : Fin n → Bit)
    (h : g.inputs.length ≤ 2) :
    (gateStep g ls).eval x = fieldGate g (ls.map (Literal.eval x)) := by
  have hget (i : ℕ) : (ls.map (Literal.eval x)).getD i 0 = (getLit ls i).eval x := by
    exact getD_map_default ls i (Literal.eval x) (constant 0)
  rcases g with ⟨op, (_|⟨i,(_|⟨j,(_|⟨k,is⟩)⟩)⟩)⟩
  · simp [gateStep, GateStep.eval, fieldGate, constant, Literal.eval]
  · simpa only [gateStep, fieldGate, List.map_cons, List.map_nil,hget] using unaryStep_correct op (getLit ls i) x
  · simpa only [gateStep, fieldGate, List.map_cons, List.map_nil,hget] using binaryStep_correct op (getLit ls i) (getLit ls j) x
  · simp at h

private theorem gateStep_mul (g : Gate) (ls : List (Literal n)) :
    (gateStep g ls).isMul = chargedProduct g := by
  rcases g with ⟨op, (_|⟨i,(_|⟨j,(_|⟨k,is⟩)⟩)⟩)⟩
  · rfl
  · rfl
  · exact binaryStep_mul op (getLit ls i) (getLit ls j)
  · rfl

private theorem gateStep_binary (g : Gate) (ls : List (Literal n)) :
    (gateStep g ls).isBinary.toNat ≤ (binaryGate g).toNat := by
  rcases g with ⟨op, (_|⟨i,(_|⟨j,(_|⟨k,is⟩)⟩)⟩)⟩ <;>
    simp [gateStep, unaryStep, binaryGate, GateStep.isBinary, Bool.toNat_le]

private def normalize (gs : List Gate) (ls : List (Literal n)) (out : ℕ) : Mixed n :=
  match gs with
  | [] => .ret (getLit ls out)
  | g :: gs =>
    match gateStep g ls with
    | .copy a => normalize gs (ls ++ [a]) out
    | .add i j p => .xor i j (normalize gs (ls.map Literal.weaken ++ [wireLit (Fin.last n) p]) out)
    | .mul a b p => .mul a b (normalize gs (ls.map Literal.weaken ++ [wireLit (Fin.last n) p]) out)

private theorem normalize_count (gs : List Gate) (ls : List (Literal n)) (out : ℕ) :
    (normalize gs ls out).nonlinear = nonlinearCost gs ∧
    (normalize gs ls out).linear + (normalize gs ls out).nonlinear ≤ binaryCost gs := by
  induction gs generalizing n with
  | nil => simp [normalize, Mixed.nonlinear, Mixed.linear, binaryCost, nonlinearCost]
  | cons g gs ih =>
      have hmul := gateStep_mul g ls
      have hbin := gateStep_binary g ls
      cases he : gateStep g ls with
      | copy a =>
          have ht := ih (ls ++ [a])
          simp only [he, GateStep.isMul, GateStep.isBinary] at hmul hbin
          simp [normalize, he, nonlinearCost, binaryCost, List.countP_cons, ← hmul] at ⊢
          exact ⟨ht.1, by simpa [binaryCost] using ht.2.trans (Nat.le_add_right _ _)⟩
      | add i j p =>
          have ht := ih (ls.map Literal.weaken ++ [wireLit (Fin.last n) p])
          simp only [he, GateStep.isMul, GateStep.isBinary] at hmul hbin
          simp only [normalize, he, Mixed.nonlinear, Mixed.linear,
            nonlinearCost, binaryCost, List.countP_cons, ← hmul]
          constructor
          · simpa [nonlinearCost] using ht.1
          · have hb := ht.2
            unfold binaryCost at hb
            have hg : binaryGate g = true := by
              cases h : binaryGate g <;> simp [h] at hbin ⊢
            simp only [hg, ↓reduceIte]
            omega
      | mul a b p =>
          have ht := ih (ls.map Literal.weaken ++ [wireLit (Fin.last n) p])
          simp only [he, GateStep.isMul, GateStep.isBinary] at hmul hbin
          simp only [normalize, he, Mixed.nonlinear, Mixed.linear,
            nonlinearCost, binaryCost, List.countP_cons, ← hmul]
          constructor
          · simpa [nonlinearCost] using ht.1
          · have hb := ht.2
            unfold binaryCost at hb
            have hg : binaryGate g = true := by
              cases h : binaryGate g <;> simp [h] at hbin ⊢
            simp only [hg, ↓reduceIte]
            omega

private def fieldWires (gs : List Gate) (ws : List Bit) : List Bit :=
  gs.foldl (fun w g => w ++ [fieldGate g w]) ws

private theorem eval_normalize (gs : List Gate) (ls : List (Literal n)) (out : ℕ)
    (x : Fin n → Bit) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (normalize gs ls out).eval x = (fieldWires gs (ls.map (Literal.eval x))).getD out 0 := by
  induction gs generalizing n with
  | nil =>
      exact (getD_map_default ls out (Literal.eval x) (constant 0)).symm
  | cons g gs ih =>
      have hhead := gateStep_correct g ls x (h g (by simp))
      have htail (a : Gate) (ha : a ∈ gs) := h a (by simp [ha])
      have hl (v p : Bit) :
          ((ls.map Literal.weaken ++ [wireLit (Fin.last n) p]).map
            (Literal.eval (Fin.snoc x v))) = ls.map (Literal.eval x) ++ [v+p] := by
        simp [List.map_append, List.map_map, Function.comp_def, Literal.eval_weaken, Literal.eval_last]
      simp only [normalize, fieldWires, List.foldl_cons]
      cases he : gateStep g ls with
      | copy a =>
          rw [he] at hhead
          change a.eval x = _ at hhead
          rw [ih (ls ++ [a]) x htail, List.map_append, List.map_singleton, hhead]
          rfl
      | add i j p =>
          rw [he] at hhead
          change x i + x j + p = _ at hhead
          simp only [Mixed.eval]
          rw [ih _ _ htail, hl, hhead]
          rfl
      | mul a b p =>
          rw [he] at hhead
          change a.eval x * b.eval x + p = _ at hhead
          simp only [Mixed.eval]
          rw [ih _ _ htail, hl, hhead]
          rfl

private theorem fieldWires_eq (gs : List Gate) (ws : List Bool) :
    fieldWires gs (ws.map bit) =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) ws).map bit := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
      simp only [fieldWires, List.foldl_cons]
      have hm (i : ℕ) : (ws.map bit).getD i 0 = bit (ws.getD i false) :=
        getD_map_default ws i bit false
      have hhead :
          fieldGate g (ws.map bit) = bit (g.op.eval (g.inputs.map fun i => ws.getD i false)) := by
        simp only [fieldGate, hm, asBool_bit]
      rw [hhead]
      simpa only [fieldWires, List.map_append, List.map_singleton] using
        ih (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)])

private theorem normalize_circuit (C : Circuit) (n : ℕ)
    (h : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ T : Mixed n, T.nonlinear = nonlinearCost C.gates ∧
      T.linear + T.nonlinear ≤ binaryCost C.gates ∧
      ∀ x : Fin n → Bool, T.eval (bit ∘ x) = bit (C.eval (List.ofFn x)) := by
  let ls := List.ofFn fun i : Fin n => wireLit i 0
  let T := normalize C.gates ls C.output
  obtain ⟨h1,h2⟩ := normalize_count C.gates ls C.output
  refine ⟨T,h1,h2,fun x => ?_⟩
  have hls : ls.map (Literal.eval (bit ∘ x)) = (List.ofFn x).map bit := by
    simp [ls, List.map_ofFn, wireLit, Literal.eval, Function.comp_def]
  change (normalize C.gates ls C.output).eval (bit ∘ x) = _
  rw [eval_normalize _ _ _ _ h, hls, fieldWires_eq]
  exact getD_map_default _ _ bit false

open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

private abbrev Back (m : ℕ) (gs : List Gate) : Prop := ReadsBack m ⟨gs, 0⟩

private theorem back_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (h : ∀ i ∈ g.inputs, i < m) (ht : Back (m+1) gs) : Back m (g :: gs) := by
  intro j hj i hi
  cases j with
  | zero => exact h i (by simpa [gateAt, List.getD] using hi)
  | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have hi' : i ∈ (gateAt ⟨gs, 0⟩ j).inputs := by
        simpa [gateAt, List.getD] using hi
      have h' := ht j hj' i hi'
      omega

private theorem read_old {α : Type} (ws ys : List α) (i : ℕ) (d : α)
    (h : i < ws.length) : (ws ++ ys).getD i d = ws.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem read_last {α : Type} (ws : List α) (v d : α) :
    (ws ++ [v]).getD ws.length d = v := by
  simp [List.getD_eq_getElem?_getD]

private def emitLit (ρ : Fin n → ℕ) (l : Literal n) : Gate :=
  match l.wire with
  | none => if asBool l.phase then ⟨.and, []⟩ else ⟨.or, []⟩
  | some i => if asBool l.phase then ⟨.not, [ρ i]⟩ else ⟨.and, [ρ i]⟩

private theorem emitLit_bound (ρ : Fin n → ℕ) (l : Literal n) (h : ∀ i, ρ i < m) :
    ∀ i ∈ (emitLit ρ l).inputs, i < m := by
  rcases l with ⟨(_|i),p⟩ <;> cases hp : asBool p <;> simp [emitLit, hp, h]

@[simp] private theorem emitLit_binary (ρ : Fin n → ℕ) (l : Literal n) :
    binaryGate (emitLit ρ l) = false := by
  rcases l with ⟨(_|i),p⟩ <;> cases hp : asBool p <;> simp [emitLit, hp, binaryGate]

@[simp] private theorem emitLit_charged (ρ : Fin n → ℕ) (l : Literal n) :
    chargedProduct (emitLit ρ l) = false := by
  simp [chargedProduct]

private theorem emitLit_arity (ρ : Fin n → ℕ) (l : Literal n) :
    (emitLit ρ l).inputs.length ≤ 2 := by
  rcases l with ⟨(_|i),p⟩ <;> cases hp : asBool p <;> simp [emitLit, hp]

private theorem field_and (ws : List Bit) (i j : ℕ) :
    fieldGate ⟨.and, [i,j]⟩ ws = ws.getD i 0 * ws.getD j 0 := by
  have h : ∀ a b : Bool, bit (GateOp.and.eval [a,b]) = bit a * bit b := by decide
  simpa only [fieldGate, List.map_cons, List.map_nil, bit_asBool] using
    h (asBool (ws.getD i 0)) (asBool (ws.getD j 0))

private theorem field_not (ws : List Bit) (i : ℕ) :
    fieldGate ⟨.not, [i]⟩ ws = ws.getD i 0 + 1 := by
  have h : ∀ a : Bool, bit (GateOp.not.eval [a]) = bit a + 1 := by decide
  simpa only [fieldGate, List.map_cons, List.map_nil, bit_asBool] using
    h (asBool (ws.getD i 0))

private theorem field_xnor (ws : List Bit) (i j : ℕ) :
    fieldGate ⟨.mod 2, [i,j]⟩ ws = ws.getD i 0 + ws.getD j 0 + 1 := by
  have h : ∀ a b : Bool, bit ((GateOp.mod 2).eval [a,b]) = bit a + bit b + 1 := by decide
  simpa only [fieldGate, List.map_cons, List.map_nil, bit_asBool] using
    h (asBool (ws.getD i 0)) (asBool (ws.getD j 0))

private theorem field_emitLit (ρ : Fin n → ℕ) (l : Literal n)
    (ws : List Bit) (x : Fin n → Bit) (h : ∀ i, ws.getD (ρ i) 0 = x i) :
    fieldGate (emitLit ρ l) ws = l.eval x := by
  have hcopy (i : ℕ) : fieldGate ⟨.and, [i]⟩ ws = ws.getD i 0 := by
    simp [fieldGate, GateOp.eval]
  rcases l with ⟨(_|i),p⟩ <;>
    rcases (by decide : ∀ p : Bit, p = 0 ∨ p = 1) p with hp|hp <;>
    subst p
  · rfl
  · rfl
  · simpa only [emitLit, show asBool (0 : Bit) = false by decide, Bool.false_eq_true,
      ↓reduceIte, Literal.eval, Option.elim_some, add_zero] using (hcopy (ρ i)).trans (h i)
  · simp only [emitLit, show asBool (1 : Bit) = true by decide, ↓reduceIte, field_not,
      Literal.eval, Option.elim_some, h]

private theorem extend_wires (ρ : Fin n → ℕ) (ws ys : List Bit) (v : Bit)
    (x : Fin n → Bit) (hm : ws.length = m) (hρ : ∀ i, ρ i < m)
    (h : ∀ i, ws.getD (ρ i) 0 = x i) :
    ∀ i, ((ws ++ ys) ++ [v]).getD (Fin.snoc (α := fun _ => ℕ) ρ (m+ys.length) i) 0 = Fin.snoc (α := fun _ => Bit) x v i := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last, Fin.snoc_last, ← hm, ← List.length_append, read_last]
  · simp only [Fin.snoc_castSucc, List.append_assoc]
    rw [read_old _ _ _ _ (by rw [hm]; exact hρ j), h]

private def projectCompile (T : Mixed n) (m : ℕ) (ρ : Fin n → ℕ) : Circuit :=
  match T with
  | .ret a => ⟨[emitLit ρ a], m⟩
  | .xor a b R =>
    let C := projectCompile R (m+2) (Fin.snoc ρ (m+1))
    ⟨⟨.mod 2, [ρ a, ρ b]⟩ :: ⟨.not, [m]⟩ :: C.gates, C.output⟩
  | .mul a b R =>
    let C := projectCompile R (m+3) (Fin.snoc ρ (m+2))
    ⟨emitLit ρ a :: emitLit ρ b :: ⟨.and, [m,m+1]⟩ :: C.gates, C.output⟩

private theorem snoc_bound (ρ : Fin n → ℕ) (hρ : ∀ i, ρ i < m)
    (k : ℕ) (h : m ≤ k) : ∀ i, Fin.snoc (α := fun _ => ℕ) ρ k i < k+1 := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simpa only [Fin.snoc_castSucc] using (hρ j).trans_le (by omega : m ≤ k+1)

private theorem projectCompile_shape (T : Mixed n) (m : ℕ) (ρ : Fin n → ℕ)
    (hρ : ∀ i, ρ i < m) :
    let C := projectCompile T m ρ
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ ReadsBack m C ∧
      binaryCost C.gates = T.linear + T.nonlinear ∧ nonlinearCost C.gates = T.nonlinear := by
  induction T generalizing m with
  | ret a =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [projectCompile] using emitLit_arity ρ a
      · exact back_cons m (emitLit ρ a) [] (emitLit_bound ρ a hρ) (by simp [Back, ReadsBack])
      · simp [projectCompile, binaryCost, Mixed.linear, Mixed.nonlinear]
      · simp [projectCompile, nonlinearCost, Mixed.nonlinear]
  | xor a b R ih =>
      let C := projectCompile R (m+2) (Fin.snoc ρ (m+1))
      obtain ⟨hfi,hback,hlin,hnon⟩ := ih (m+2) (Fin.snoc ρ (m+1)) (snoc_bound ρ hρ (m+1) (by omega))
      let g : Gate := ⟨.mod 2, [ρ a, ρ b]⟩
      let h : Gate := ⟨.not, [m]⟩
      change (∀ j ∈ g :: h :: C.gates, j.inputs.length ≤ 2) ∧ Back m (g :: h :: C.gates) ∧
        binaryCost (g :: h :: C.gates) = (Mixed.xor a b R).linear + (Mixed.xor a b R).nonlinear ∧
        nonlinearCost (g :: h :: C.gates) = (Mixed.xor a b R).nonlinear
      refine ⟨?_, back_cons m g _ ?_ (back_cons (m+1) h _ ?_ hback), ?_, ?_⟩
      · simpa [g, h] using hfi
      · simp [g, hρ]
      · simp [h]
      · have he : binaryCost (g :: h :: C.gates) = binaryCost C.gates + 1 := by
          have hg : binaryGate g = true := rfl
          have hh : binaryGate h = false := rfl
          simp [binaryCost, hg, hh]
        change binaryCost C.gates = _ at hlin
        rw [he, hlin]
        simp only [Mixed.linear, Mixed.nonlinear]
        omega
      · have hg : chargedProduct g = false := rfl
        have hh : chargedProduct h = false := rfl
        simpa [nonlinearCost, List.countP_cons, hg, hh, Mixed.nonlinear] using hnon
  | mul a b R ih =>
      let C := projectCompile R (m+3) (Fin.snoc ρ (m+2))
      obtain ⟨hfi,hback,hlin,hnon⟩ := ih (m+3) (Fin.snoc ρ (m+2)) (snoc_bound ρ hρ (m+2) (by omega))
      let g : Gate := ⟨.and, [m,m+1]⟩
      change (∀ j ∈ emitLit ρ a :: emitLit ρ b :: g :: C.gates, j.inputs.length ≤ 2) ∧
        Back m (emitLit ρ a :: emitLit ρ b :: g :: C.gates) ∧
        binaryCost (emitLit ρ a :: emitLit ρ b :: g :: C.gates) =
          (Mixed.mul a b R).linear + (Mixed.mul a b R).nonlinear ∧
        nonlinearCost (emitLit ρ a :: emitLit ρ b :: g :: C.gates) = (Mixed.mul a b R).nonlinear
      refine ⟨?_, back_cons m _ _ (emitLit_bound ρ a hρ)
        (back_cons (m+1) _ _ (emitLit_bound ρ b (fun i => (hρ i).trans (Nat.lt_succ_self _)))
          (back_cons (m+2) g _ ?_ hback)), ?_, ?_⟩
      · simpa [g, emitLit_arity] using hfi
      · simp [g]
      · have hg : binaryGate g = true := rfl
        change binaryCost C.gates = _ at hlin
        have he : binaryCost (emitLit ρ a :: emitLit ρ b :: g :: C.gates) =
            binaryCost C.gates + 1 := by simp [binaryCost, hg]
        rw [he, hlin, Mixed.nonlinear, Mixed.linear, Nat.add_assoc]
      · have hg : chargedProduct g = true := rfl
        change nonlinearCost C.gates = _ at hnon
        have he : nonlinearCost (emitLit ρ a :: emitLit ρ b :: g :: C.gates) =
            nonlinearCost C.gates + 1 := by simp [nonlinearCost, hg]
        rw [he, hnon, Mixed.nonlinear]

private theorem projectCompile_eval (T : Mixed n) (m : ℕ) (ρ : Fin n → ℕ)
    (hρ : ∀ i, ρ i < m) (ws : List Bit) (x : Fin n → Bit) (hm : ws.length = m)
    (hx : ∀ i, ws.getD (ρ i) 0 = x i) :
    let C := projectCompile T m ρ
    (fieldWires C.gates ws).getD C.output 0 = T.eval x := by
  induction T generalizing m ws with
  | ret a =>
      change (ws ++ [fieldGate (emitLit ρ a) ws]).getD m 0 = a.eval x
      rw [← hm, read_last, field_emitLit _ _ _ _ hx]
  | xor a b R ih =>
      let C := projectCompile R (m+2) (Fin.snoc ρ (m+1))
      let u := fieldGate ⟨.mod 2, [ρ a, ρ b]⟩ ws
      let v := fieldGate ⟨.not, [m]⟩ (ws ++ [u])
      have hv : v = x a + x b := by
        dsimp only [v]
        rw [field_not, ← hm, read_last]
        dsimp only [u]
        rw [field_xnor, hx, hx, add_assoc]
        rw [show (1 : Bit) + 1 = 0 by decide, add_zero]
      change (fieldWires C.gates ((ws ++ [u]) ++ [v])).getD C.output 0 = _
      rw [hv]
      refine ih (m+2) (Fin.snoc ρ (m+1)) (snoc_bound ρ hρ (m+1) (by omega)) _ _ ?_ ?_
      · simp [hm]
      · exact extend_wires ρ ws [u] _ x hm hρ hx
  | mul a b R ih =>
      let C := projectCompile R (m+3) (Fin.snoc ρ (m+2))
      let u := fieldGate (emitLit ρ a) ws
      let v := fieldGate (emitLit ρ b) (ws ++ [u])
      let w := fieldGate ⟨.and, [m, m+1]⟩ ((ws ++ [u]) ++ [v])
      have hu : u = a.eval x := field_emitLit _ _ _ _ hx
      have hv : v = b.eval x := by
        refine field_emitLit _ _ _ _ (fun i => ?_)
        rw [read_old _ _ _ _ (by rw [hm]; exact hρ i), hx]
      have hw : w = a.eval x * b.eval x := by
        have hm' : (ws ++ [u]).length = m+1 := by simp [hm]
        dsimp only [w]
        rw [field_and, ← hm', read_last, read_old _ _ _ _ (by omega), ← hm, read_last, hu, hv]
      change (fieldWires C.gates (((ws ++ [u]) ++ [v]) ++ [w])).getD C.output 0 = _
      rw [hw, List.append_assoc ws [u] [v]]
      refine ih (m+3) (Fin.snoc ρ (m+2)) (snoc_bound ρ hρ (m+2) (by omega)) _ _ ?_ ?_
      · simp [hm]
      · exact extend_wires ρ ws [u,v] _ x hm hρ hx

private theorem compile_circuit (T : Mixed n) :
    ∃ C : Circuit, (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ ReadsBack n C ∧
      binaryCost C.gates = T.linear + T.nonlinear ∧ nonlinearCost C.gates = T.nonlinear ∧
      ∀ x : Fin n → Bool, bit (C.eval (List.ofFn x)) = T.eval (bit ∘ x) := by
  let C := projectCompile T n Fin.val
  obtain ⟨hf, hr, hb, hn⟩ := projectCompile_shape T n Fin.val Fin.isLt
  refine ⟨C, hf, hr, hb, hn, fun x => ?_⟩
  let ws := (List.ofFn x).map bit
  have hm : ws.length = n := by simp [ws]
  have hx (i : Fin n) : ws.getD i.val 0 = (bit ∘ x) i := by
    rw [List.getD_eq_getElem _ _ (by rw [hm]; exact i.isLt)]
    simp [ws, Function.comp_def]
  have he := projectCompile_eval T n Fin.val Fin.isLt ws (bit ∘ x) hm hx
  change (fieldWires C.gates ws).getD C.output 0 = _ at he
  rw [fieldWires_eq] at he
  exact (getD_map_default (C.wires (List.ofFn x)) C.output bit false).symm.trans he

namespace XorProgram

private theorem dual_as_matrix (T : XorProgram n m) (x : Vec m) (i : Fin n) :
    T.transpose.eval x i = ∑ j, x j * T.eval e j i := by
  have h := T.dual_transpose (e i) x
  have hp : pairing (e i) (T.transpose.eval x) = T.transpose.eval x i := by
    unfold pairing e
    simp [ite_mul]
  rw [hp] at h
  rw [← h]
  unfold pairing
  apply Finset.sum_congr rfl
  intro j _
  rw [eval_coordinate, mul_comm]
  congr 2
  funext k
  exact e_symm i k

private theorem outputs_two_dead (T : XorProgram n m) {a b : Fin m} (hab : a ≠ b)
    (ha : T.live a = false) (hb : T.live b = false) : T.outputs+2 ≤ m := by
  classical
  have hl (i : Fin m) :
      (T.live i).toNat + ((if i = a then 1 else 0) + (if i = b then 1 else 0)) ≤ 1 := by
    by_cases h₁ : i = a
    · subst i
      simp [ha,hab]
    · by_cases h₂ : i = b
      · subst i
        simp [hb,hab,Ne.symm hab]
      · cases hi : T.live i <;> simp [h₁,h₂,hi]
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => hl i)
  simpa [outputs, Finset.sum_add_distrib] using h

end XorProgram

private theorem Mixed.upper_of_affine {s N : ℕ} (hN : N = 2^(2*s))
    (label : Fin N ≃ Vec (2*s)) (Q : Vec (2*s) → F) (seed : Fin s)
    (A B : Vec (2*s) ≃ Vec (2*s)) (α : Vec (2*s)) (c : F)
    (errors : Finset (Vec (2*s))) (hzero : 0 ∉ errors)
    (hseed : errors = ∅ ∨ Upper.fullPair seed ∈ errors)
    (hd : errors.card = distance Q)
    (spec : ∀ x y, dot x y + Q x =
      Upper.quad (A x+B y+α) + Upper.quad (A x) + Upper.quad (B y) +
        (if A x∈errors then 1 else 0) + c) :
    ∃ T : Mixed (N+N), T.nonlinear=s ∧
      T.linear + T.nonlinear + 2*s+4 ≤ 3*N+max 1 (distance Q) ∧
      ∀ i j, T.eval (Mixed.onehot i j) = dot (label i) (label j) + Q (label i) := by
  classical
  let L (i : Fin N) : Vec ((2*s)+1) :=
    if A (label i) ∈ errors then Upper.wrong (A (label i)) else Upper.lift (A (label i))
  let R (j : Fin N) : Vec ((2*s)+1) := Upper.lift (B (label j))
  let target : Fin (N+N) → Vec ((2*s)+1) := Fin.addCases L R
  let allowed := Upper.graphAllowed seed errors
  have hknown : XorProgram.known (XorProgram.e : Fin ((2*s)+1) → Vec ((2*s)+1)) = Upper.initial (2*s) := by
    ext v
    rfl
  have hr (j : Fin (N+N)) : Upper.Reachable
      (XorProgram.known (XorProgram.e : Fin ((2*s)+1) → Vec ((2*s)+1))) allowed (target j) := by
    rw [hknown]
    refine Fin.addCases (motive := fun j => Upper.Reachable (Upper.initial (2*s)) allowed (target j)) ?_ ?_ j
    · intro i
      have hi : target (i.castAdd N) = L i := by simp [target]
      rw [hi]
      by_cases he : A (label i) ∈ errors
      · simpa only [L,he,if_true] using Upper.error_reachable seed errors hseed he
      · simpa only [L,he,if_false] using Upper.graph_reachable seed errors hseed (A (label i))
    · intro j
      have hj : target (j.natAdd N) = R j := by
        change Fin.addCases (motive := fun _ => Vec ((2*s)+1)) L R (j.natAdd N) = _
        simp only [Fin.addCases_right]
      rw [hj]
      exact Upper.graph_reachable seed errors hseed (B (label j))
  obtain ⟨P,hp,hval,hlive⟩ := XorProgram.synthesize allowed XorProgram.e target hr
  let QP := P.transpose
  have hvalL (i : Fin N) : P.eval XorProgram.e (i.castAdd N) = L i := by
    rw [hval]; change Fin.addCases (motive := fun _ => Vec ((2*s)+1)) L R (i.castAdd N) = _
    simp only [Fin.addCases_left]
  have hvalR (j : Fin N) : P.eval XorProgram.e (j.natAdd N) = R j := by
    rw [hval]; change Fin.addCases (motive := fun _ => Vec ((2*s)+1)) L R (j.natAdd N) = _
    simp only [Fin.addCases_right]
  have hQP (i j : Fin N) : QP.eval (Mixed.onehot i j) = L i + R j := by
    funext q
    change P.transpose.eval (Mixed.onehot i j) q = (L i+R j) q
    rw [P.dual_as_matrix,Fin.sum_univ_add]
    simp only [Mixed.onehot,Fin.addCases_left,Fin.addCases_right,hvalL,hvalR,unit,
      ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true,Pi.add_apply]
  have hQcol (j : Fin N) (q : Fin ((2*s)+1)) :
      QP.eval (unit (j.natAdd N)) q = R j q := by
    change P.transpose.eval (unit (j.natAdd N)) q = R j q
    rw [P.dual_as_matrix]
    simp [unit,ite_mul, ← Fin.natAdd_eq_addNat, hvalR]
  have hAll (q : Fin ((2*s)+1)) : QP.live q = true := by
    have hw : ∃ j, R j q ≠ 0 := by
      refine Fin.lastCases ?_ (fun p => ?_) q
      · let j := (label.trans B).symm (Upper.fullPair seed)
        refine ⟨j,?_⟩
        have hj : B (label j) = Upper.fullPair seed := (label.trans B).apply_symm_apply _
        simp only [R,hj,Upper.lift,Upper.word,Fin.snoc_last,Upper.fullPair,Upper.quad_part,one_mul]
        exact (one_ne_zero : (1 : F) ≠ 0)
      · let j := (label.trans B).symm (Upper.axis p)
        refine ⟨j,?_⟩
        have hj : B (label j) = Upper.axis p := (label.trans B).apply_symm_apply _
        simp only [R,hj,Upper.lift,Upper.word,Fin.snoc_castSucc,Upper.axis,ite_eq_left rfl]
        exact (one_ne_zero : (1 : F) ≠ 0)
    obtain ⟨j,hj⟩ := hw
    by_contra he
    exact hj ((hQcol j q).symm.trans
      (QP.eval_of_dead (unit (j.natAdd N)) q (Bool.eq_false_of_not_eq_true he)))
  have hAllCount : QP.outputs = (2*s)+1 := by
    unfold XorProgram.outputs
    calc
      (∑ q, (QP.live q).toNat) = ∑ _ : Fin ((2*s)+1), 1 := by
        apply Finset.sum_congr rfl
        intro q _
        rw [hAll]
        rfl
      _ = (2*s)+1 := by simp
  let il := (label.trans A).symm 0
  let ir := (label.trans B).symm 0
  have hiL : A (label il) = 0 := (label.trans A).apply_symm_apply 0
  have hiR : B (label ir) = 0 := (label.trans B).apply_symm_apply 0
  have hcL : P.live (il.castAdd N) = false := by
    have h := hvalL il
    have h' : target (il.castAdd N) = 0 := by
      rw [← hval,h]
      simp [L,hiL,hzero,Upper.lift_eq_zero]
    have hl := hlive (il.castAdd N)
    cases hq : P.live (il.castAdd N) <;> simp_all
  have hcR : P.live (ir.natAdd N) = false := by
    have h := hvalR ir
    have h' : target (ir.natAdd N) = 0 := by
      rw [← hval,h]
      simp [R,hiR,Upper.lift_eq_zero]
    have hl := hlive (ir.natAdd N)
    cases hq : P.live (ir.natAdd N) <;> simp_all
  have h2 := P.outputs_two_dead (a := il.castAdd N) (b := ir.natAdd N)
    (by intro hh; have h := congrArg Fin.val hh; simp at h; omega) hcL hcR
  have ht := P.transpose_cost
  change QP.count+QP.outputs ≤ P.count+P.outputs at ht
  rw [hAllCount] at ht
  have hg := Upper.graphAllowed_card seed errors
  rw [hd,← hN] at hg
  let phase : Vec ((2*s)+1) := Fin.snoc α c
  let T := QP.appendQuadratic phase
  obtain ⟨hn,hb⟩ := QP.appendQuadratic_count phase
  refine ⟨T,hn,?_,?_⟩
  · have hNk : (2*s) < N := by
      rw [hN]
      exact Nat.lt_two_pow_self
    change T.linear ≤ QP.count+s at hb
    change T.nonlinear = s at hn
    rw [hn]
    change (P.count ≤ allowed.card) at hp
    change allowed.card ≤ _ at hg
    omega
  · intro i j
    change (QP.appendQuadratic phase).eval (Mixed.onehot i j) = _
    rw [XorProgram.appendQuadratic_eval,hQP,spec]
    have hva (p : Fin (2*s)) : L i p.castSucc = A (label i) p := by
      by_cases he : A (label i) ∈ errors <;>
        simp [L,he,Upper.lift,Upper.wrong,Upper.word]
    have hvb (p : Fin (2*s)) : R j p.castSucc = B (label j) p := by
      simp [R,Upper.lift,Upper.word]
    have hvphase (p : Fin (2*s)) : phase p.castSucc = α p := by simp [phase]
    have hl : L i (Fin.last (2*s)) = Upper.quad (A (label i)) + (if A (label i)∈errors then 1 else 0) := by
      by_cases he : A (label i) ∈ errors <;> simp [L,he,Upper.lift,Upper.wrong,Upper.word]
    have hR : R j (Fin.last (2*s)) = Upper.quad (B (label j)) := by
      simp [R,Upper.lift,Upper.word]
    have hsum :
        (∑ q : Fin s, ((L i + R j) (Mixed.first q) + phase (Mixed.first q)) *
          ((L i + R j) (Mixed.second q) + phase (Mixed.second q))) =
        Upper.quad (A (label i)+B (label j)+α) := by
      unfold Upper.quad
      apply Finset.sum_congr rfl
      intro q _
      change ((L i (Upper.first q).castSucc + R j (Upper.first q).castSucc) +
          phase (Upper.first q).castSucc) *
        ((L i (Upper.second q).castSucc + R j (Upper.second q).castSucc) +
          phase (Upper.second q).castSucc) = _
      rw [hva,hva,hvb,hvb,hvphase,hvphase]
      rfl
    rw [hsum]
    simp only [Pi.add_apply,hl,hR,phase,Fin.snoc_last]
    ac_rfl

private def boolHot (i j : Fin N) : Fin (N+N) → Bool :=
  Fin.addCases (fun x => decide (x=i)) (fun y => decide (y=j))

private theorem boolHot_bits (i j : Fin N) : bit ∘ boolHot i j = Mixed.onehot i j := by
  funext x
  refine Fin.addCases (motive := fun x => (bit ∘ boolHot i j) x = Mixed.onehot i j x) ?_ ?_ x
  · intro x
    simp only [Function.comp_apply,boolHot,Mixed.onehot,Fin.addCases_left,unit]
    by_cases h : x=i <;> simp [h,bit]
  · intro y
    simp only [Function.comp_apply,boolHot,Mixed.onehot,Fin.addCases_right,unit]
    by_cases h : y=j <;> simp [h,bit]

private theorem boolHot_list (i j : Fin N) :
    List.ofFn (boolHot i j) = PEqualNP.Represents.oneEach i j := by
  have hc (x : Fin N) : x.castLE (Nat.le_add_right N N) = x.castAdd N := Fin.ext rfl
  rw [List.ofFn_add]
  simp only [hc,boolHot,Fin.addCases_left,Fin.addCases_right,PEqualNP.Represents.oneEach]

end PEqualNP.Outside.L_meta_25800_aux

open PEqualNP.Outside.L_meta_25800_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25800 : (∀ s : ℕ, 1 ≤ s →
  let k := 2*s
  let N := 2^k
  let V := Fin k → ZMod 2
  let dot := fun (x y : V) => ∑ j : Fin k, x j * y j
  ∀ (label : Fin N ≃ V) (Q : V → ZMod 2),
    let d := sInf (Set.range (fun z : V × ZMod 2 =>
      ((Finset.univ : Finset V).filter (fun x => Q x ≠ dot z.1 x + z.2)).card))
    let b := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      C.gates.countP (fun g => g.inputs.length == 2)
    let t := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      C.gates.countP (fun g => (g.inputs.length == 2) &&
        xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
            (xor (g.op.eval [true,false]) (g.op.eval [true,true])))
    let accepts := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧
      PEqualNP.Represents.Represents (fun i j =>
        decide (dot (label i) (label j) + Q (label i) = 1)) C ∧ t C ≤ s
    (∀ C, accepts C → t C = s ∧ 3*N + max 1 d ≤ b C + 2*s + 4) ∧
      ∃ C, accepts C ∧ t C = s ∧ b C + 2*s + 4 = 3*N + max 1 d) := by

  classical
  intro s hs
  dsimp only
  intro label Q
  let N := 2^(2*s)
  let target (i j : Fin N) := asBool (dot (label i) (label j) + Q (label i))
  let admits (C : Circuit) := (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧
    PEqualNP.Represents.Represents target C ∧ nonlinearCost C.gates ≤ s
  change (∀ C, admits C → nonlinearCost C.gates = s ∧
      3*N + max 1 (distance Q) ≤ binaryCost C.gates + 2*s + 4) ∧
    ∃ C, admits C ∧ nonlinearCost C.gates = s ∧
      binaryCost C.gates + 2*s+4 = 3*N + max 1 (distance Q)
  have lower (C : Circuit) (h : admits C) :
      nonlinearCost C.gates = s ∧
        3*N + max 1 (distance Q) ≤ binaryCost C.gates + 2*s + 4 := by
    obtain ⟨T,hn,hb,he⟩ := normalize_circuit C (N+N) h.1
    have hr (i j : Fin N) :
        T.eval (Mixed.onehot i j) = dot (label i) (label j) + Q (label i) := by
      have hx := he (boolHot i j)
      rw [boolHot_bits, boolHot_list, h.2.2.1 i j] at hx
      simpa only [target, bit_asBool] using hx
    obtain ⟨ht,hb'⟩ := T.lower_bound rfl rfl (by omega) label Q (hn.trans_le h.2.2.2) hr
    exact ⟨hn.symm.trans ht, by omega⟩
  refine ⟨lower,?_⟩
  let seed : Fin s := ⟨0, by omega⟩
  obtain ⟨A,B,α,c,errors,hzero,hseed,hd,hf⟩ := Upper.affine_reduction seed Q
  obtain ⟨T,ht,hcost,hr⟩ := Mixed.upper_of_affine (N := N) rfl label Q
    seed A B α c errors hzero hseed hd hf
  obtain ⟨C,hfan,hread,hbin,hnl,heval⟩ := compile_circuit T
  have ok : admits C := by
    refine ⟨hfan,hread,?_,by omega⟩
    intro i j
    apply bit_injective
    have hx := heval (boolHot i j)
    rw [boolHot_bits,boolHot_list,hr] at hx
    simpa only [target,bit_asBool] using hx
  have hlow := (lower C ok).2
  exact ⟨C,ok,hnl.trans ht,by omega⟩

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20595

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def matrix (u v : Fin 5) := (6489088 : ℕ).testBit (5 * u.val + v.val)

def witness : Circuit :=
  ⟨[⟨.and, [2,5]⟩, ⟨.or, [3,4]⟩, ⟨.or, [6,7]⟩, ⟨.and, [11,12]⟩, ⟨.or, [10,13]⟩], 14⟩

theorem upper : RepSizeAtMost matrix 5 := by
  refine ⟨witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

def step (x : List Bool) (g : Gate) : List Bool :=
  x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]

def rises (x y : List Bool) (i : ℕ) := x.getD i false = true → y.getD i false = true

theorem rises_step_other {x y : List Bool} {n i : ℕ} (hx : x.length = n) (hy : y.length = n)
    (g : Gate) (hne : i ≠ n) (h : rises x y i) : rises (step x g) (step y g) i := by
  by_cases hi : i < n
  · simpa only [rises, step, List.getD_append _ _ _ _ (show i < x.length by omega),
      List.getD_append _ _ _ _ (show i < y.length by omega)] using h
  · have past : (step x g).length ≤ i := by simp [step]; omega
    unfold rises
    rw [List.getD_eq_default _ _ past]
    simp

theorem rises_step_new {x y : List Bool} {n : ℕ} (hx : x.length = n) (hy : y.length = n)
    (g : Gate) (op : g.op = .and ∨ g.op = .or) (h : ∀ i ∈ g.inputs, rises x y i) :
    rises (step x g) (step y g) n := by
  unfold rises step
  rw [List.getD_append_right _ _ _ _ hx.le, List.getD_append_right _ _ _ _ hy.le, hx, hy]
  simp only [Nat.sub_self, List.getD_cons_zero]
  rcases op with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun a i hi => h i hi (a i hi)
  · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, yes⟩
    exact ⟨i, hi, h i hi yes⟩

theorem smallSupport (gs : List Gate)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) (n w : ℕ) :
    ∃ S : Finset ℕ, S.card ≤ gs.length + 1 ∧
      ∀ x y : List Bool, x.length = n → y.length = n → (∀ i ∈ S, rises x y i) →
        rises (gs.foldl step x) (gs.foldl step y) w := by
  induction gs generalizing n with
  | nil => exact ⟨{w}, by simp, fun _ _ _ _ h => h w (by simp)⟩
  | cons g gs ih =>
    obtain ⟨T, hT, follows⟩ := ih (fun a ha => hm a (by simp [ha])) (n+1)
    obtain ⟨op, fan⟩ := hm g List.mem_cons_self
    by_cases used : n ∈ T
    · let S := T.erase n ∪ g.inputs.toFinset
      refine ⟨S, ?_, ?_⟩
      · have hU := Finset.card_union_le (T.erase n) g.inputs.toFinset
        have hE := Finset.card_erase_add_one used
        have hG := (List.toFinset_card_le g.inputs).trans fan
        simp only [S, List.length_cons]
        omega
      · intro x y hx hy h
        apply follows _ _ (by simp [step, hx]) (by simp [step, hy])
        intro i hi
        by_cases eq : i = n
        · subst i
          exact rises_step_new hx hy g op (fun j hj => h j (Finset.mem_union_right _ (by simpa using hj)))
        · exact rises_step_other hx hy g eq (h i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hi⟩)))
    · refine ⟨T, by simp only [List.length_cons]; omega, ?_⟩
      intro x y hx hy h
      apply follows _ _ (by simp [step, hx]) (by simp [step, hy])
      intro i hi
      exact rises_step_other hx hy g (fun e => used (e ▸ hi)) (h i hi)

def required : Finset ℕ := {2,3,4,5,6,7}

theorem distinguish : ∀ i ∈ required, ∃ u v u' v' : Fin 5,
    matrix u v = true ∧ matrix u' v' = false ∧
    ∀ j : Fin 10, j.val ≠ i → rises (oneEach u v) (oneEach u' v') j.val := by
  intro i hi
  simp only [required, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2,0,0,0,by decide,by decide,by unfold rises; decide⟩
  · exact ⟨3,1,0,1,by decide,by decide,by unfold rises; decide⟩
  · exact ⟨4,1,0,1,by decide,by decide,by unfold rises; decide⟩
  · exact ⟨2,0,2,3,by decide,by decide,by unfold rises; decide⟩
  · exact ⟨3,1,3,3,by decide,by decide,by unfold rises; decide⟩
  · exact ⟨3,2,3,3,by decide,by decide,by unfold rises; decide⟩

theorem lower : ¬ RepSizeAtMost matrix 4 := by
  rintro ⟨C, hm, hs, rep⟩
  obtain ⟨S, bound, follows⟩ := smallSupport C.gates (fun g hg => hm g hg) 10 C.output
  have sub : required ⊆ S := by
    intro i hi
    by_contra absent
    obtain ⟨u,v,u',v',hp,hn,hmove⟩ := distinguish i hi
    have out := follows (oneEach u v) (oneEach u' v') (by simp [oneEach]) (by simp [oneEach]) (by
      intro j hj
      by_cases valid : j < 10
      · exact hmove ⟨j, valid⟩ (fun eq => absent (eq ▸ hj))
      · have past : (oneEach u v).length ≤ j := by simp [oneEach]; omega
        unfold rises
        rw [List.getD_eq_default _ _ past]
        simp)
    change C.eval (oneEach u v) = true → C.eval (oneEach u' v') = true at out
    rw [rep u v, rep u' v', hp, hn] at out
    exact Bool.noConfusion (out rfl)
  have count := Finset.card_le_card sub
  have six : required.card = 6 := by decide
  change C.gates.length ≤ 4 at hs
  omega

end PEqualNP.Outside.L_meta_20595

theorem PEqualNP.Outside.L_meta_20595 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (6489088 : ℕ).testBit (5 * u.val + v.val)) 5 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (6489088 : ℕ).testBit (5 * u.val + v.val)) 4) := by
  exact ⟨PEqualNP.Outside.L_meta_20595.upper, PEqualNP.Outside.L_meta_20595.lower⟩

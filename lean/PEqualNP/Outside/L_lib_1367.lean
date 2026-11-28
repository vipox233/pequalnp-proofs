import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1367_aux

section WireFacts
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
variable {n m : ℕ}
abbrev Col (m : ℕ) := Fin m → Bool
noncomputable def raw (x : Fin m → Finset (Fin n)) (i : Fin m) :=
  List.ofFn (fun a : Fin n => decide (a ∈ x i)) ++ [false, true]
noncomputable def val (x : Fin m → Finset (Fin n)) (gs : List Gate) (p : ℕ) : Col m :=
  fun i => ((Circuit.mk gs 0).wires (raw x i)).getD p false
noncomputable def ix (gs : List Gate) := (List.range gs.length).filter fun j =>
  decide ((gs.getD j ⟨.or, []⟩).op = GateOp.not)
noncomputable def trace (x : Fin m → Finset (Fin n)) (gs : List Gate) :=
  (ix gs).map fun j => val x gs (n + 2 + j)
noncomputable def sing (x : Fin m → Finset (Fin n)) (a : Fin n) : Col m := fun i => decide (a ∈ x i)
noncomputable def baseCol (x : Fin m → Finset (Fin n)) : Set (Col m) :=
  {f | f = (fun _ => false) ∨ f = (fun _ => true) ∨ ∃ a, f = sing x a}
noncomputable def inv (f : Col m) : Col m := fun i => !(f i)
noncomputable def conj (f g : Col m) : Col m := fun i => f i && g i
noncomputable def disj (f g : Col m) : Col m := fun i => f i || g i

theorem wirelen (gs : List Gate) (u : List Bool) :
    ((Circuit.mk gs 0).wires u).length = u.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simpa [Circuit.wires, List.foldl_append, Nat.add_assoc] using congrArg Nat.succ ih

theorem old (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) {p} (hp : p < n + 2 + gs.length) :
    val x (gs ++ [g]) p = val x gs p := by
  funext i
  have len := wirelen gs (raw x i)
  rw [show (raw x i).length = n + 2 by simp [raw]] at len
  simp only [val, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (((Circuit.mk gs 0).wires (raw x i)) ++ [_]).getD p false = _
  exact List.getD_append _ _ _ _ (by omega)

theorem fresh (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) (i : Fin m) :
    val x (gs ++ [g]) (n + 2 + gs.length) i = g.op.eval (g.inputs.map fun p => val x gs p i) := by
  have len := wirelen gs (raw x i)
  rw [show (raw x i).length = n + 2 by simp [raw]] at len
  simp only [val, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (((Circuit.mk gs 0).wires (raw x i)) ++ [_]).getD _ false = _
  rw [← len, List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem ixAdd (gs : List Gate) (g : Gate) :
    ix (gs ++ [g]) = ix gs ++ (if g.op = .not then [gs.length] else []) := by
  unfold ix
  simp only [List.length_append, List.length_singleton, List.range_succ, List.filter_append]
  congr 1
  · apply List.filter_congr
    intro i hi
    rw [List.getD_append _ _ _ _ (List.mem_range.mp hi)]
  · by_cases h : g.op = .not <;> simp [h]

theorem ixRange {gs : List Gate} {j} (h : j ∈ ix gs) : j < gs.length :=
  List.mem_range.mp (List.mem_filter.mp h).1

theorem traceAdd (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) :
    trace x (gs ++ [g]) =
      trace x gs ++ (if g.op = .not then [val x (gs ++ [g]) (n + 2 + gs.length)] else []) := by
  unfold trace
  rw [ixAdd, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro j hj
    exact old _ _ _ (by have := ixRange hj; omega)
  · split <;> rfl

theorem countIx (gs : List Gate) : PEqualNP.NotBracket.notCount ⟨gs, 0⟩ = (ix gs).length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [ixAdd]
    unfold PEqualNP.NotBracket.notCount at *
    by_cases h : g.op = .not <;> simp [List.filter_append, h, ih]

theorem extendBack (gs : List Gate) (g : Gate) (h : ReadsBack (n + 2) ⟨gs, 0⟩)
    (ok : ∀ p ∈ g.inputs, p < n + 2 + gs.length) : ReadsBack (n + 2) ⟨gs ++ [g], 0⟩ := by
  intro j hj p hp
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hj' : j < gs.length
  · apply h j hj' p
    simpa only [gateAt, List.getD_append _ _ _ _ hj'] using hp
  · obtain rfl : j = gs.length := by omega
    apply ok
    simpa [gateAt, List.getD_append_right _ _ _ _ (le_refl _)] using hp

noncomputable def Built (x : Fin m → Finset (Fin n)) (tr : List (Col m)) (k : ℕ) (S : Set (Col m)) :=
  ∃ gs : List Gate, FanInTwo ⟨gs, 0⟩ ∧ ReadsBack (n + 2) ⟨gs, 0⟩ ∧ gs.length ≤ k ∧ trace x gs = tr ∧
    ∀ f ∈ S, ∃ p < n + 2 + gs.length, val x gs p = f
end WireFacts

section Compiler
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
variable {n m : ℕ} {x : Fin m → Finset (Fin n)} {tr : List (Col m)} {k : ℕ} {S : Set (Col m)}

theorem Built.start : Built x [] 0 (baseCol x) := by
  refine ⟨[], by simp [FanInTwo], by simp [ReadsBack], by simp, rfl, ?_⟩
  intro f hf
  rcases hf with rfl | rfl | ⟨a, rfl⟩
  · refine ⟨n, by simp, ?_⟩
    funext i
    simp [val, Circuit.wires, raw]
  · refine ⟨n + 1, by simp, ?_⟩
    funext i
    simp [val, Circuit.wires, raw]
  · refine ⟨a.val, by have := a.isLt; simp; omega, ?_⟩
    funext i
    change ((List.ofFn fun u : Fin n => decide (u ∈ x i)) ++ _).getD a.val false = _
    rw [List.getD_append _ _ _ _ (by simp)]
    simp [sing]

theorem Built.relax {K : ℕ} {T : Set (Col m)} (ih : Built x tr k S) (sz : k ≤ K) (sub : T ⊆ S) :
    Built x tr K T := by
  obtain ⟨gs, fan, back, le, trace, signal⟩ := ih
  exact ⟨gs, fan, back, le.trans sz, trace, fun f hf => signal f (sub hf)⟩

theorem Built.andGate {f z : Col m} (ih : Built x tr k S) (hf : f ∈ S) (hg : z ∈ S) :
    Built x tr (k + 1) (insert (conj f z) S) := by
  obtain ⟨gs, fan, back, sz, ht, sig⟩ := ih
  obtain ⟨a, ha, ea⟩ := sig _ hf
  obtain ⟨b, hb, eb⟩ := sig _ hg
  let g : Gate := ⟨.and, [a, b]⟩
  refine ⟨gs ++ [g], ?_, ?_, by simpa using sz, ?_, ?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with oj | nj
    · exact fan j oj
    · obtain rfl : j = g := List.mem_singleton.mp nj
      simp [g]
  · apply extendBack _ _ back
    simp_all [g]
  · rw [traceAdd]; simpa [g] using ht
  · intro f mem
    rcases mem with rfl | mem
    · refine ⟨n + 2 + gs.length, by simp, ?_⟩
      funext i; rw [fresh]; simp [g, GateOp.eval, ea, eb, conj]
    · obtain ⟨p, hp, eq⟩ := sig _ mem
      exact ⟨p, by simp; omega, (old _ _ _ hp).trans eq⟩

theorem Built.orGate {f z : Col m} (ih : Built x tr k S) (hf : f ∈ S) (hg : z ∈ S) :
    Built x tr (k + 1) (insert (disj f z) S) := by
  obtain ⟨gs, fan, back, sz, ht, sig⟩ := ih
  obtain ⟨a, ha, ea⟩ := sig _ hf
  obtain ⟨b, hb, eb⟩ := sig _ hg
  let g : Gate := ⟨.or, [a, b]⟩
  refine ⟨gs ++ [g], ?_, ?_, by simpa using sz, ?_, ?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with oj | nj
    · exact fan j oj
    · obtain rfl : j = g := List.mem_singleton.mp nj
      simp [g]
  · apply extendBack _ _ back
    simp_all [g]
  · rw [traceAdd]; simpa [g] using ht
  · intro f mem
    rcases mem with rfl | mem
    · refine ⟨n + 2 + gs.length, by simp, ?_⟩
      funext i; rw [fresh]; simp [g, GateOp.eval, ea, eb, disj]
    · obtain ⟨p, hp, eq⟩ := sig _ mem
      exact ⟨p, by simp; omega, (old _ _ _ hp).trans eq⟩

theorem Built.notGate {f : Col m} (ih : Built x tr k S) (hf : f ∈ S) :
    Built x (tr ++ [inv f]) (k + 1) (insert (inv f) S) := by
  obtain ⟨gs, fan, back, sz, ht, sig⟩ := ih
  obtain ⟨a, ha, ea⟩ := sig _ hf
  let g : Gate := ⟨.not, [a]⟩
  have ev : val x (gs ++ [g]) (n + 2 + gs.length) = inv f := by
    funext i; rw [fresh]; simp [g, GateOp.eval, ea, inv]
  refine ⟨gs ++ [g], ?_, ?_, by simpa using sz, by simp [traceAdd, g, ht, ev], ?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with oldg | newg
    · exact fan j oldg
    · obtain rfl : j = g := List.mem_singleton.mp newg
      simp [g]
  · apply extendBack _ _ back; simpa [g] using ha
  · intro f mem
    rcases mem with rfl | mem
    · exact ⟨_, by simp, ev⟩
    · obtain ⟨p, hp, eq⟩ := sig _ mem
      exact ⟨p, by simp; omega, (old _ _ _ hp).trans eq⟩

end Compiler

section Construction
open scoped Classical
variable {n m : ℕ} {x : Fin m → Finset (Fin n)} {tr : List (Col m)} {k : ℕ} {S : Set (Col m)}

noncomputable def Grow (x : Fin m → Finset (Fin n)) (tr : List (Col m)) (k : ℕ) (S : Set (Col m))
    (b : ℕ) (f : Col m) := ∃ T, Built x tr (k + b) T ∧ S ⊆ T ∧ f ∈ T

theorem batch {ι : Type} (s : Finset ι) (F : ι → Col m) (b : ℕ) (H : Built x tr k S)
    (make : ∀ {K T}, Built x tr K T → S ⊆ T → ∀ a ∈ s, Grow x tr K T b (F a)) :
    ∃ T, Built x tr (k + s.card * b) T ∧ S ⊆ T ∧ ∀ a ∈ s, F a ∈ T := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨S, by simpa using H, Set.Subset.rfl, by simp⟩
  | @insert a s fresh ih =>
    obtain ⟨U, hU, sub, allU⟩ := ih (fun h st i hi => make h st i (Finset.mem_insert_of_mem hi))
    obtain ⟨T, hT, ut, hit⟩ := make hU sub a (Finset.mem_insert_self _ _)
    refine ⟨T, by simpa [Finset.card_insert_of_notMem fresh, Nat.add_mul, Nat.add_assoc] using hT,
      sub.trans ut, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hh
    · exact hit
    · exact ut (allU _ hh)

theorem allFold {ι : Type} (s : Finset ι) (F : ι → Col m) (H : Built x tr k S)
    (unit : (fun _ => true) ∈ S) (get : ∀ a ∈ s, F a ∈ S) :
    Grow x tr k S s.card (fun j => decide (∀ a ∈ s, F a j = true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨S, by simpa using H, Set.Subset.rfl, by simpa using unit⟩
  | @insert a s fr ih =>
    obtain ⟨T, h, st, ft⟩ := ih (fun a ha => get a (Finset.mem_insert_of_mem ha))
    have g := Built.andGate h (st (get a (Finset.mem_insert_self _ _))) ft
    refine ⟨_, by simpa [Finset.card_insert_of_notMem fr, Nat.add_assoc] using g,
      st.trans (Set.subset_insert _ _), ?_⟩
    apply Set.mem_insert_iff.mpr; left
    funext j
    simp [conj, Bool.decide_and]

theorem anyFold {ι : Type} (s : Finset ι) (F : ι → Col m) (H : Built x tr k S)
    (unit : (fun _ => false) ∈ S) (get : ∀ a ∈ s, F a ∈ S) :
    Grow x tr k S s.card (fun j => decide (∃ a ∈ s, F a j = true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨S, by simpa using H, Set.Subset.rfl, by simpa using unit⟩
  | @insert a s fr ih =>
    obtain ⟨T, h, st, ft⟩ := ih (fun a ha => get a (Finset.mem_insert_of_mem ha))
    have g := Built.orGate h (st (get a (Finset.mem_insert_self _ _))) ft
    refine ⟨_, by simpa [Finset.card_insert_of_notMem fr, Nat.add_assoc] using g,
      st.trans (Set.subset_insert _ _), ?_⟩
    apply Set.mem_insert_iff.mpr; left
    funext j
    simp [disj, Bool.decide_or]

noncomputable def indicator (x : Fin m → Finset (Fin n)) (v : Fin m → ℕ) (i : Fin m) : Col m :=
  fun j => decide (x i ⊆ x j ∧ v i = v j)
noncomputable def hist (r : ℕ) (v : Fin m → ℕ) : List (Col m) :=
  List.ofFn fun b : Fin r => fun i => !(v i).testBit (r - 1 - b.val)

theorem hist_succ (r : ℕ) (v : Fin m → ℕ) :
    hist (r + 1) v = hist r (fun i => v i / 2) ++ [fun i => !(v i).testBit 0] := by
  rw [hist, List.ofFn_succ', List.concat_eq_append]
  congr 1
  · unfold hist
    congr 1
    funext b i
    simp [Nat.testBit_div_two, show r - 1 - (b : ℕ) + 1 = r + 1 - 1 - b by have := b.isLt; omega]
  · simp

theorem stages (x : Fin m → Finset (Fin n)) (r : ℕ) (v : Fin m → ℕ)
    (cap : ∀ i, v i < 2 ^ r) (mono : ∀ i j, x i ⊆ x j → v i ≤ v j) :
    ∃ S, Built x (hist r v) (m * (n + 2 * r) + r) S ∧ baseCol x ⊆ S ∧ ∀ i, indicator x v i ∈ S := by
  induction r generalizing v with
  | zero =>
    have z : ∀ i, v i = 0 := fun i => by have := cap i; simp at this; omega
    obtain ⟨T, bt, st, allT⟩ := batch (Finset.univ : Finset (Fin m)) (indicator x v) n (Built.start (x := x)) (by
      intro K U h bu i _
      obtain ⟨V, hh, sub, fi⟩ := allFold (x i) (sing x) h (bu (Or.inr (Or.inl rfl)))
        (fun a _ => bu (Or.inr (Or.inr ⟨a, rfl⟩)))
      have lim := Finset.card_le_univ (x i)
      refine ⟨V, hh.relax (by simpa using Nat.add_le_add_left lim K) Set.Subset.rfl, sub, ?_⟩
      have eq : indicator x v i = (fun j => decide (∀ a ∈ x i, sing x a j = true)) := by
        funext j; simp [indicator, sing, z, Finset.subset_iff]
      rw [eq]; convert fi using 1; funext j; apply Bool.eq_iff_iff.mpr; simp)
    exact ⟨T, by simpa [hist] using bt, st, fun i => allT i (Finset.mem_univ _)⟩
  | succ r ih =>
    let u := fun i => v i / 2
    have ucap : ∀ i, u i < 2 ^ r := fun i => by have := cap i; simp [pow_succ] at this; dsimp [u]; omega
    obtain ⟨S, h, bs, hInd⟩ := ih u ucap (fun i j h => Nat.div_le_div_right (mono i j h))
    let bit : Col m := fun i => (v i).testBit 0
    let sel := Finset.univ.filter fun i => bit i = true
    obtain ⟨T, hT, st, hit⟩ := anyFold sel (indicator x u) h (bs (Or.inl rfl)) (fun i _ => hInd i)
    have eqn : (fun j => decide (∃ a ∈ sel, indicator x u a j = true)) = bit := by
      funext j
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, indicator, sel, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, ba, sub, eq⟩
        have ord := mono a j sub
        simp [u] at eq
        simp [bit] at ba ⊢
        omega
      · intro b; exact ⟨j, b, Finset.Subset.rfl, rfl⟩
    have hit2 : bit ∈ T := by
      rw [← eqn]; convert hit using 1; funext j; apply Bool.eq_iff_iff.mpr; simp
    have hn := Built.notGate hT hit2
    let U := insert (inv bit) T
    have su : S ⊆ U := st.trans (Set.subset_insert _ _)
    obtain ⟨V, hV, uv, allV⟩ := batch (Finset.univ : Finset (Fin m)) (indicator x v) 1 hn (by
      intro K W hw uw i _
      have iw := uw (su (hInd i))
      by_cases bi : bit i = true
      · have same : indicator x v i = indicator x u i := by
          funext j; simp only [indicator, decide_eq_decide]
          constructor
          · rintro ⟨a, b⟩; exact ⟨a, congrArg (· / 2) b⟩
          · rintro ⟨a, b⟩; have ord := mono i j a
            simp [bit] at bi; dsimp [u] at b; exact ⟨a, by omega⟩
        exact ⟨W, hw.relax (by omega) Set.Subset.rfl, Set.Subset.rfl, same ▸ iw⟩
      · have bw : inv bit ∈ W := uw (Set.mem_insert _ _)
        have made := Built.andGate hw iw bw
        refine ⟨_, made, Set.subset_insert _ _, Set.mem_insert_iff.mpr (Or.inl ?_)⟩
        funext j
        apply Bool.eq_iff_iff.mpr
        simp only [indicator, conj, inv, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true']
        simp [bit] at bi
        simp [bit, u]
        grind)
    have lim : sel.card ≤ m := by simpa using Finset.card_le_univ sel
    rw [hist_succ]
    refine ⟨V, hV.relax ?_ Set.Subset.rfl, (bs.trans su).trans uv, fun i => allV i (Finset.mem_univ _)⟩
    simp only [Finset.card_univ, Fintype.card_fin, mul_one]
    simp only [Nat.mul_add, Nat.mul_succ] at *
    omega
end Construction

section TraceOrder
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {n m : ℕ} {x : Fin m → Finset (Fin n)}
noncomputable def decode (i : Fin m) : List (Col m) → ℕ
  | [] => 0
  | a :: as => 2 * decode i as + if a i then 0 else 1
noncomputable def score (i : Fin m) (word : List (Col m)) := decode i word.reverse
theorem snocScore (i : Fin m) (l : List (Col m)) (f : Col m) :
    score i (l ++ [f]) = 2 * score i l + if f i then 0 else 1 := by simp [score, decode]

theorem score_lt (i : Fin m) (l : List (Col m)) : score i l < 2 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [score, decode]
  | append_singleton l f ih =>
    rw [snocScore, List.length_append, List.length_singleton, pow_succ]
    split_ifs <;> omega

theorem other (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) {p}
    (hp : p ≠ n + 2 + gs.length) : val x (gs ++ [g]) p = val x gs p := by
  by_cases low : p < n + 2 + gs.length
  · exact old x gs g low
  funext i
  have oz := wirelen gs (raw x i)
  have nz := wirelen (gs ++ [g]) (raw x i)
  rw [show (raw x i).length = n + 2 by simp [raw]] at oz nz
  simp only [List.length_append, List.length_singleton] at nz
  unfold val
  rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

theorem rawMono {i j : Fin m} (sub : x i ⊆ x j) (p : ℕ) :
    val x [] p i = true → val x [] p j = true := by
  by_cases hp : p < n
  · simp only [val, Circuit.wires, List.foldl_nil, raw]
    rw [List.getD_append _ _ _ _ (by simpa using hp), List.getD_append _ _ _ _ (by simpa using hp)]
    simpa [List.getD_eq_getElem?_getD, hp] using @sub ⟨p, hp⟩
  · simp only [val, Circuit.wires, List.foldl_nil, raw]
    rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hp),
      List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hp)]
    simp

theorem ordinary {i j : Fin m} {gs : List Gate} (prior : ∀ p, val x gs p i = true → val x gs p j = true)
    (g : Gate) (op : g.op = .and ∨ g.op = .or) :
    val x (gs ++ [g]) (n + 2 + gs.length) i = true → val x (gs ++ [g]) (n + 2 + gs.length) j = true := by
  rw [fresh, fresh]
  rcases op with op | op
  · simp only [op, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun h p hp => prior _ (h p hp)
  · simp only [op, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨p, hp, v⟩; exact ⟨p, hp, prior _ v⟩

theorem inverseGate {i j : Fin m} {gs : List Gate} (prior : ∀ p, val x gs p i = true → val x gs p j = true)
    (g : Gate) (op : g.op = .not) :
    val x (gs ++ [g]) (n + 2 + gs.length) j = true → val x (gs ++ [g]) (n + 2 + gs.length) i = true := by
  rw [fresh, fresh]
  cases args : g.inputs with
  | nil => simp [op, GateOp.eval]
  | cons a l =>
    have h := prior a
    simp [op, GateOp.eval]
    cases e : val x gs a i <;> cases d : val x gs a j <;> simp_all

theorem stepOrder (x : Fin m → Finset (Fin n)) (gs : List Gate) (fan : FanInTwo ⟨gs, 0⟩)
    (i j : Fin m) (sub : x i ⊆ x j) :
    score i (trace x gs) ≤ score j (trace x gs) ∧
    (score i (trace x gs) = score j (trace x gs) → ∀ p, val x gs p i = true → val x gs p j = true) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨le_refl _, fun _ => rawMono sub⟩
  | append_singleton gs g ih =>
    obtain ⟨le, transfer⟩ := ih (fun u hu => fan u (List.mem_append_left _ hu))
    have ops := (fan g (List.mem_append_right _ (List.mem_singleton_self _))).1
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at ops
    by_cases nt : g.op = .not
    · simp only [traceAdd, ite_eq_left nt, snocScore]
      let p := n + 2 + gs.length
      by_cases eq : score i (trace x gs) = score j (trace x gs)
      · have ant := inverseGate (transfer eq) g nt
        constructor
        · rw [eq]
          change _ + (if val x (gs ++ [g]) p i then 0 else 1) ≤ _ + (if val x (gs ++ [g]) p j then 0 else 1)
          cases ai : val x (gs ++ [g]) p i <;> cases aj : val x (gs ++ [g]) p j <;> simp_all [p]
        · intro same a
          by_cases aeq : a = p
          · subst a
            dsimp [p] at *
            split at same <;> split at same <;> simp_all
          · rw [other x gs g aeq]; exact transfer eq _
      · have strict := lt_of_le_of_ne le eq
        split <;> split <;> constructor <;> omega
    · have ao : g.op = .and ∨ g.op = .or := ops.elim Or.inl (fun h => Or.inr (h.resolve_right nt))
      simp only [traceAdd, ite_eq_right nt, List.append_nil]
      refine ⟨le, fun eq a => ?_⟩
      by_cases he : a = n + 2 + gs.length
      · subst a; exact ordinary (transfer eq) g ao
      · rw [other x gs g he]; exact transfer eq _
end TraceOrder

section Synthesis
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

noncomputable def OK {n m a : ℕ} (mask : Fin m → Finset (Fin n)) (v : Fin m → ℕ)
    (w : Fin m → Fin a → Bool) : Prop :=
  ∀ t u, mask t ⊆ mask u → v t ≤ v u ∧ (v t = v u → ∀ i, w t i = true → w u i = true)

theorem sufficient_main {n m a r : ℕ} (mask : Fin m → Finset (Fin n)) (v : Fin m → ℕ)
    (w : Fin m → Fin a → Bool) (cap : ∀ t, v t < 2 ^ r) (ok : OK mask v w) :
    ∃ (C : Circuit) (tap : Fin a → ℕ),
      FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
      PEqualNP.NotBracket.notCount C = r ∧ (∀ i, tap i < n + 2 + C.size) ∧
      (∀ t i, val mask C.gates (tap i) t = w t i) ∧
      C.size ≤ m * (n + 2 * r + a) + r := by
  obtain ⟨S, b, baseSub, ind⟩ := stages mask r v cap (fun i j h => (ok i j h).1)
  let f := fun i : Fin a => fun t => w t i
  obtain ⟨T, hT, _, haveTap⟩ := batch (Finset.univ : Finset (Fin a)) f m b (by
    intro K U hu su i _
    let sel := Finset.univ.filter fun t => w t i = true
    obtain ⟨V, hV, uv, got⟩ := anyFold sel (indicator mask v) hu (su (baseSub (Or.inl rfl))) (fun t _ => su (ind t))
    have lim : sel.card ≤ m := by simpa using Finset.card_le_univ sel
    refine ⟨V, hV.relax (by omega) Set.Subset.rfl, uv, ?_⟩
    convert got using 1
    funext u
    apply Bool.eq_iff_iff.mpr
    simp only [sel, Finset.mem_filter, Finset.mem_univ, true_and, indicator, decide_eq_true_eq, f]
    constructor
    · intro h; exact ⟨u, h, Finset.Subset.rfl, rfl⟩
    · rintro ⟨t, hit, sub, same⟩; exact (ok t u sub).2 same i hit)
  obtain ⟨gs, fan, back, sz, ht, wire⟩ := hT
  choose tap valid data using fun i => wire _ (haveTap i (Finset.mem_univ _))
  have len := congrArg List.length ht
  simp [trace, hist] at len
  refine ⟨⟨gs, 0⟩, tap, fan, back, by simp [Circuit.size], (countIx gs).trans len, valid,
    fun t i => congrFun (data i) t, ?_⟩
  change gs.length ≤ _
  simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm] using sz

end Synthesis

section Combinatorics
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma log2_bounds (k : ℕ) (hk : 1 ≤ k) : 2 ^ Nat.log2 k ≤ k ∧ k < 2 ^ (Nat.log2 k + 1) :=
  ⟨Nat.log2_self_le (by omega), Nat.lt_log2_self⟩

lemma limit_and_q_props (n m b : ℕ) :
    let limit := max 1 (min m (n + 1))
    let h := min b (Nat.log2 (2 * limit - 1))
    let q := min (2 ^ h) limit
    1 ≤ limit ∧ 1 ≤ q ∧ q ≤ limit ∧ q ≤ 2 ^ h ∧ h ≤ b ∧
    (b < Nat.log2 (2 * limit - 1) → q = 2 ^ b) ∧
    (Nat.log2 (2 * limit - 1) ≤ b → q = limit) := by
  intro limit h q
  have hlim : 1 ≤ limit := le_max_left 1 _
  obtain ⟨hl1, hl2⟩ := log2_bounds (2 * limit - 1) (by omega)
  have hpow_lim : limit ≤ 2 ^ Nat.log2 (2 * limit - 1) := by
    rw [pow_succ] at hl2
    omega
  refine ⟨hlim, ?_, min_le_right _ _, min_le_left _ _, min_le_left _ _, ?_, ?_⟩
  · exact le_min Nat.one_le_two_pow hlim
  · intro hlt
    have hh : h = b := min_eq_left (Nat.le_of_lt hlt)
    have hpow_lt : 2 ^ b < limit := by
      have h1 : b + 1 ≤ Nat.log2 (2 * limit - 1) := hlt
      have h2 : 2 ^ (b + 1) ≤ 2 ^ Nat.log2 (2 * limit - 1) :=
        Nat.pow_le_pow_right (by omega) h1
      rw [pow_succ] at h2
      omega
    dsimp only [q]
    rw [hh]
    exact min_eq_left (Nat.le_of_lt hpow_lt)
  · intro hle
    have hh : h = Nat.log2 (2 * limit - 1) := min_eq_right hle
    dsimp only [q]
    rw [hh]
    exact min_eq_right hpow_lim

noncomputable def arcFn (x y : Bool) (k : ℕ) : ℕ := if x = true ∧ y = false then k else 0

noncomputable def baseFn {m a : ℕ} (unary : Fin m → Fin a → Bool → ℕ) (t : Fin m) (v : Bool) : ℕ :=
  Finset.univ.sum (fun i => unary t i v)

noncomputable def priceFn {m a : ℕ} (unary : Fin m → Fin a → Bool → ℕ)
    (pair : Fin m → Fin a → Fin a → ℕ) (t : Fin m) (w : Fin a → Bool) : ℕ :=
  Finset.univ.sum (fun i => unary t i (w i)) +
  Finset.univ.sum (fun i => Finset.univ.sum (fun j => arcFn (w i) (w j) (pair t i j)))

noncomputable def offsetFn {m a : ℕ} (q : ℕ) (unary : Fin m → Fin a → Bool → ℕ) : ℕ :=
  (q - 1) * Finset.univ.sum (fun t => baseFn unary t false + baseFn unary t true)

noncomputable def bigFn {m a : ℕ} (q : ℕ) (unary : Fin m → Fin a → Bool → ℕ) : ℕ :=
  1 + offsetFn q unary + Finset.univ.sum (fun t => baseFn unary t false)

noncomputable def cutFn {n m a : ℕ} (q : ℕ) (mask : Fin m → Finset (Fin n))
    (unary : Fin m → Fin a → Bool → ℕ) (pair : Fin m → Fin a → Fin a → ℕ)
    (X : Fin m → ℕ → Fin a → Bool) (Y : Fin m → ℕ → Bool) : ℕ :=
  Finset.univ.sum (fun t =>
    (Finset.range q).sum (fun r => priceFn unary pair t (X t r)) +
    (Finset.range (q - 1)).sum (fun r =>
      (if Y t r = true then baseFn unary t false else baseFn unary t true) +
      Finset.univ.sum (fun i =>
        arcFn (Y t r) (X t r i) (bigFn q unary) + arcFn (X t (r + 1) i) (Y t r) (bigFn q unary))) +
    Finset.univ.sum (fun u => if mask t ⊆ mask u then
      (Finset.range q).sum (fun r => Finset.univ.sum (fun i => arcFn (X t r i) (X u r i) (bigFn q unary))) +
      (Finset.range (q - 1)).sum (fun r => arcFn (Y t r) (Y u r) (bigFn q unary))
    else 0))

lemma price_const_true {m a : ℕ} (unary : Fin m → Fin a → Bool → ℕ)
    (pair : Fin m → Fin a → Fin a → ℕ) (t : Fin m) :
    priceFn unary pair t (fun _ => true) = baseFn unary t true := by
  simp [priceFn, baseFn, arcFn]

lemma price_const_false {m a : ℕ} (unary : Fin m → Fin a → Bool → ℕ)
    (pair : Fin m → Fin a → Fin a → ℕ) (t : Fin m) :
    priceFn unary pair t (fun _ => false) = baseFn unary t false := by
  simp [priceFn, baseFn, arcFn]

lemma sum_cubes (q L bt bf pw : ℕ) (hL : L < q) :
    (Finset.range q).sum (fun r => if r < L then bt else if r = L then pw else bf) =
      L * bt + (q - 1 - L) * bf + pw := by
  induction q with
  | zero => omega
  | succ q ih =>
    rw [Finset.sum_range_succ]
    by_cases hLq : L = q
    · subst hLq
      have h1 : (Finset.range L).sum (fun r => if r < L then bt else if r = L then pw else bf) =
          (Finset.range L).sum (fun _ => bt) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_range] at hr
        simp [hr]
      rw [h1, Finset.sum_const, Finset.card_range, smul_eq_mul]
      simp
    · have hLt : L < q := by omega
      rw [ih hLt]
      have hnq : ¬ (q < L) := by omega
      have hne : q ≠ L := Ne.symm hLq
      simp only [hnq, hne, ite_false]
      have hq_sub : q + 1 - 1 - L = (q - 1 - L) + 1 := by omega
      rw [hq_sub, Nat.add_mul, Nat.one_mul]
      omega

lemma sum_links (q L bf bt : ℕ) (hq : 1 ≤ q) (hL : L ≤ q - 1) :
    (Finset.range (q - 1)).sum (fun r => if r < L then bf else bt) =
      L * bf + (q - 1 - L) * bt := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hq
  clear hq
  simp only [Nat.add_sub_cancel] at hL ⊢
  induction k with
  | zero =>
    have hL0 : L = 0 := by omega
    subst hL0; simp
  | succ k ih =>
    by_cases hLk : L = k + 1
    · subst hLk
      have h1 : (Finset.range (k + 1)).sum (fun r => if r < k + 1 then bf else bt) =
          (Finset.range (k + 1)).sum (fun _ => bf) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_range] at hr
        simp [hr]
      rw [h1, Finset.sum_const, Finset.card_range, smul_eq_mul]
      simp
    · rw [Finset.sum_range_succ, ih (by omega)]
      have hnl : ¬ (k < L) := by omega
      simp only [hnl, ite_false]
      have hk_sub : k + 1 - L = (k - L) + 1 := by omega
      rw [hk_sub, Nat.add_mul, Nat.one_mul]
      omega

lemma row_cost_exact {n m a : ℕ} (q : ℕ) (hq : 1 ≤ q) (mask : Fin m → Finset (Fin n))
    (unary : Fin m → Fin a → Bool → ℕ) (pair : Fin m → Fin a → Fin a → ℕ)
    (lvl : Fin m → ℕ) (w : Fin m → Fin a → Bool)
    (hlvl : ∀ t, lvl t < q) (ok : OK mask lvl w) :
    let X : Fin m → ℕ → Fin a → Bool := fun t r i =>
      if r < lvl t then true else if r = lvl t then w t i else false
    let Y : Fin m → ℕ → Bool := fun t r => decide (r < lvl t)
    cutFn q mask unary pair X Y = offsetFn q unary + Finset.univ.sum (fun t => priceFn unary pair t (w t)) := by
  intro X Y
  have harc_yx : ∀ t, ∀ r ∈ Finset.range (q - 1), ∀ i, arcFn (Y t r) (X t r i) (bigFn q unary) = 0 := by
    intro t r _ i
    dsimp only [arcFn, Y, X]
    by_cases h : r < lvl t
    · simp [h]
    · simp [h]
  have harc_xy : ∀ t, ∀ r ∈ Finset.range (q - 1), ∀ i, arcFn (X t (r + 1) i) (Y t r) (bigFn q unary) = 0 := by
    intro t r _ i
    dsimp only [arcFn, Y, X]
    by_cases h : r < lvl t
    · simp [h]
    · have h1 : ¬ (r + 1 < lvl t) := by omega
      have h2 : r + 1 ≠ lvl t := by omega
      simp [h, h1, h2]
  have harc_iso_y : ∀ t u, mask t ⊆ mask u → ∀ r ∈ Finset.range (q - 1),
      arcFn (Y t r) (Y u r) (bigFn q unary) = 0 := by
    intro t u hsub r _
    have hle := (ok t u hsub).1
    dsimp only [arcFn, Y]
    by_cases h : r < lvl t
    · have hu : r < lvl u := by omega
      simp [h, hu]
    · simp [h]
  have harc_iso_x : ∀ t u, mask t ⊆ mask u → ∀ r ∈ Finset.range q, ∀ i,
      arcFn (X t r i) (X u r i) (bigFn q unary) = 0 := by
    intro t u hsub r _ i
    have hok := ok t u hsub
    dsimp only [arcFn, X]
    by_cases h1 : r < lvl t
    · have hu : r < lvl u := by omega
      simp [h1, hu]
    · by_cases h2 : r = lvl t
      · subst h2
        rcases Nat.eq_or_lt_of_le hok.1 with heq | hlt
        · rw [← heq]
          simp only [lt_self_iff_false, ite_false, ite_true]
          by_cases hw : w t i = true
          · simp [hw, hok.2 heq i hw]
          · simp [hw]
        · simp [hlt]
      · simp [h1, h2]
  have hrow : ∀ t : Fin m,
      (Finset.range q).sum (fun r => priceFn unary pair t (X t r)) +
      (Finset.range (q - 1)).sum (fun r =>
        (if Y t r = true then baseFn unary t false else baseFn unary t true) +
        Finset.univ.sum (fun i =>
          arcFn (Y t r) (X t r i) (bigFn q unary) + arcFn (X t (r + 1) i) (Y t r) (bigFn q unary))) +
      Finset.univ.sum (fun u => if mask t ⊆ mask u then
        (Finset.range q).sum (fun r => Finset.univ.sum (fun i => arcFn (X t r i) (X u r i) (bigFn q unary))) +
        (Finset.range (q - 1)).sum (fun r => arcFn (Y t r) (Y u r) (bigFn q unary))
      else 0) =
      (q - 1) * (baseFn unary t false + baseFn unary t true) + priceFn unary pair t (w t) := by
    intro t
    have hzero1 : (Finset.range (q - 1)).sum (fun r =>
        (if Y t r = true then baseFn unary t false else baseFn unary t true) +
        Finset.univ.sum (fun i =>
          arcFn (Y t r) (X t r i) (bigFn q unary) + arcFn (X t (r + 1) i) (Y t r) (bigFn q unary))) =
        (Finset.range (q - 1)).sum (fun r =>
          if r < lvl t then baseFn unary t false else baseFn unary t true) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hs : Finset.univ.sum (fun i =>
          arcFn (Y t r) (X t r i) (bigFn q unary) + arcFn (X t (r + 1) i) (Y t r) (bigFn q unary)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [harc_yx t r hr i, harc_xy t r hr i]
        simp
      rw [hs, Nat.add_zero]
      dsimp only [Y]
      by_cases h : r < lvl t <;> simp [h]
    have hzero2 : Finset.univ.sum (fun u => if mask t ⊆ mask u then
        (Finset.range q).sum (fun r => Finset.univ.sum (fun i => arcFn (X t r i) (X u r i) (bigFn q unary))) +
        (Finset.range (q - 1)).sum (fun r => arcFn (Y t r) (Y u r) (bigFn q unary)) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro u _
      split_ifs with hsub
      · have hs1 : (Finset.range q).sum (fun r => Finset.univ.sum (fun i =>
            arcFn (X t r i) (X u r i) (bigFn q unary))) = 0 := by
          apply Finset.sum_eq_zero; intro r hr
          apply Finset.sum_eq_zero; intro i _
          exact harc_iso_x t u hsub r hr i
        have hs2 : (Finset.range (q - 1)).sum (fun r =>
            arcFn (Y t r) (Y u r) (bigFn q unary)) = 0 := by
          apply Finset.sum_eq_zero; intro r hr
          exact harc_iso_y t u hsub r hr
        omega
      · rfl
    have hcubes : (Finset.range q).sum (fun r => priceFn unary pair t (X t r)) =
        lvl t * baseFn unary t true + (q - 1 - lvl t) * baseFn unary t false + priceFn unary pair t (w t) := by
      have hcongr : (Finset.range q).sum (fun r => priceFn unary pair t (X t r)) =
          (Finset.range q).sum (fun r =>
            if r < lvl t then baseFn unary t true else if r = lvl t then priceFn unary pair t (w t) else baseFn unary t false) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        dsimp only [X]
        by_cases h1 : r < lvl t
        · simp only [h1, ite_true]
          exact price_const_true unary pair t
        · by_cases h2 : r = lvl t
          · simp only [h2, lt_self_iff_false, ite_false, ite_true]
          · simp only [h1, h2, ite_false]
            exact price_const_false unary pair t
      rw [hcongr]
      exact sum_cubes q (lvl t) (baseFn unary t true) (baseFn unary t false) (priceFn unary pair t (w t)) (hlvl t)
    have hlinks : (Finset.range (q - 1)).sum (fun r =>
        if r < lvl t then baseFn unary t false else baseFn unary t true) =
        lvl t * baseFn unary t false + (q - 1 - lvl t) * baseFn unary t true :=
      sum_links q (lvl t) (baseFn unary t false) (baseFn unary t true) hq (by have := hlvl t; omega)
    rw [hzero1, hzero2, Nat.add_zero, hcubes, hlinks]
    have hle : lvl t ≤ q - 1 := by have := hlvl t; omega
    have hsplit : lvl t + (q - 1 - lvl t) = q - 1 := Nat.add_sub_of_le hle
    calc lvl t * baseFn unary t true + (q - 1 - lvl t) * baseFn unary t false + priceFn unary pair t (w t) +
          (lvl t * baseFn unary t false + (q - 1 - lvl t) * baseFn unary t true)
      _ = (lvl t + (q - 1 - lvl t)) * baseFn unary t false +
            (lvl t + (q - 1 - lvl t)) * baseFn unary t true + priceFn unary pair t (w t) := by ring
      _ = (q - 1) * (baseFn unary t false + baseFn unary t true) + priceFn unary pair t (w t) := by
          rw [hsplit]; ring
  unfold cutFn offsetFn
  rw [Finset.sum_congr rfl fun t _ => hrow t, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma sum_lt_bound_all {ι : Type*} (s : Finset ι) (f : ι → ℕ) (B : ℕ) (h : s.sum f < B) :
    ∀ x ∈ s, f x < B := by
  intro x hx
  exact lt_of_le_of_lt (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx) h

lemma arc_lt_imp {x y : Bool} {B : ℕ} (h : arcFn x y B < B) : x = true → y = true := by
  intro hx
  by_contra hy
  have hyf : y = false := Bool.eq_false_iff.mpr hy
  simp [arcFn, hx, hyf] at h

lemma main_equiv (n m a b k : ℕ) (mask : Fin m → Finset (Fin n))
    (unary : Fin m → Fin a → Bool → ℕ) (pair : Fin m → Fin a → Fin a → ℕ) :
    let limit := max 1 (min m (n + 1))
    let h := min b (Nat.log2 (2 * limit - 1))
    let q := min (2 ^ h) limit
    ((∃ (C : Circuit) (tap : Fin a → ℕ),
        FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
        (∀ i, tap i < n + 2 + C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
        Finset.univ.sum (fun t => priceFn unary pair t (fun i =>
          ((C.wires (raw mask t)).getD (tap i) false))) ≤ k) ↔
      ∃ (X : Fin m → ℕ → Fin a → Bool) (Y : Fin m → ℕ → Bool), cutFn q mask unary pair X Y ≤ offsetFn q unary + k) ∧
    ((∃ (X : Fin m → ℕ → Fin a → Bool) (Y : Fin m → ℕ → Bool), cutFn q mask unary pair X Y ≤ offsetFn q unary + k) →
      ∃ (C : Circuit) (tap : Fin a → ℕ),
        (FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
         (∀ i, tap i < n + 2 + C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
         Finset.univ.sum (fun t => priceFn unary pair t (fun i =>
           ((C.wires (raw mask t)).getD (tap i) false))) ≤ k) ∧
        PEqualNP.NotBracket.notCount C ≤ h ∧ C.size ≤ m * (n + 2 * h + a) + h) := by
  intro limit h q
  obtain ⟨hlim, hq1, hq_lim, hq_pow, hhb, hlt_log, hge_log⟩ := limit_and_q_props n m b
  have dir2 : (∃ X Y, cutFn q mask unary pair X Y ≤ offsetFn q unary + k) →
      ∃ (C : Circuit) (tap : Fin a → ℕ),
        (FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
         (∀ i, tap i < n + 2 + C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
         Finset.univ.sum (fun t => priceFn unary pair t (fun i =>
           ((C.wires (raw mask t)).getD (tap i) false))) ≤ k) ∧
        PEqualNP.NotBracket.notCount C ≤ h ∧ C.size ≤ m * (n + 2 * h + a) + h := by
    rintro ⟨X, Y, hcut⟩
    by_cases hk_triv : Finset.univ.sum (fun t => baseFn unary t false) ≤ k
    · refine ⟨⟨[], 0⟩, fun _ => n, ?_, ?_, ?_⟩
      · refine ⟨by simp [FanInTwo], by simp [ReadsBack], by simp [Circuit.size],
          fun _ => by simp [Circuit.size], by simp [PEqualNP.NotBracket.notCount], ?_⟩
        have hwire : ∀ t, (({ gates := [], output := 0 } : Circuit).wires (raw mask t)).getD n false = false := by
          intro t
          simp only [Circuit.wires, List.foldl_nil, raw]
          rw [List.getD_append_right _ _ _ _ (by simp)]
          simp
        refine le_trans (le_of_eq ?_) hk_triv
        refine Finset.sum_congr rfl fun t _ => ?_
        have hfn : (fun _ : Fin a => (({ gates := [], output := 0 } : Circuit).wires (raw mask t)).getD n false) =
            fun _ => false := funext (fun _ => hwire t)
        rw [hfn, price_const_false]
      · simp [PEqualNP.NotBracket.notCount]
      · simp [Circuit.size]
    · have hk_lt : k < Finset.univ.sum (fun t => baseFn unary t false) := Nat.lt_of_not_ge hk_triv
      have ha_pos : 0 < a := by
        by_contra ha0
        have ha_eq : a = 0 := by omega
        subst ha_eq
        have hz : Finset.univ.sum (fun t : Fin m => baseFn unary t false) = 0 := by
          apply Finset.sum_eq_zero; intro t _
          simp [baseFn]
        omega
      let i0 : Fin a := ⟨0, ha_pos⟩
      have hcut_lt : cutFn q mask unary pair X Y < bigFn q unary := by
        dsimp only [bigFn]
        omega
      have harc_yx : ∀ t : Fin m, ∀ r ∈ Finset.range (q - 1), ∀ i : Fin a,
          Y t r = true → X t r i = true := by
        intro t r hr i hYt
        have ht := sum_lt_bound_all Finset.univ _ _ hcut_lt t (Finset.mem_univ t)
        have h2 : (Finset.range (q - 1)).sum (fun r =>
            (if Y t r = true then baseFn unary t false else baseFn unary t true) +
            Finset.univ.sum (fun i =>
              arcFn (Y t r) (X t r i) (bigFn q unary) + arcFn (X t (r + 1) i) (Y t r) (bigFn q unary))) <
            bigFn q unary := by omega
        have hr_lt := sum_lt_bound_all (Finset.range (q - 1)) _ _ h2 r hr
        have hs_lt : Finset.univ.sum (fun i =>
            arcFn (Y t r) (X t r i) (bigFn q unary) + arcFn (X t (r + 1) i) (Y t r) (bigFn q unary)) <
            bigFn q unary := by omega
        have hi_lt := sum_lt_bound_all Finset.univ _ _ hs_lt i (Finset.mem_univ i)
        exact arc_lt_imp (lt_of_le_of_lt (Nat.le_add_right _ _) hi_lt) hYt
      have harc_xy : ∀ t : Fin m, ∀ r ∈ Finset.range (q - 1), ∀ i : Fin a,
          X t (r + 1) i = true → Y t r = true := by
        intro t r hr i hXt
        have ht := sum_lt_bound_all Finset.univ _ _ hcut_lt t (Finset.mem_univ t)
        have h2 : (Finset.range (q - 1)).sum (fun r =>
            (if Y t r = true then baseFn unary t false else baseFn unary t true) +
            Finset.univ.sum (fun i =>
              arcFn (Y t r) (X t r i) (bigFn q unary) + arcFn (X t (r + 1) i) (Y t r) (bigFn q unary))) <
            bigFn q unary := by omega
        have hr_lt := sum_lt_bound_all (Finset.range (q - 1)) _ _ h2 r hr
        have hs_lt : Finset.univ.sum (fun i =>
            arcFn (Y t r) (X t r i) (bigFn q unary) + arcFn (X t (r + 1) i) (Y t r) (bigFn q unary)) <
            bigFn q unary := by omega
        have hi_lt := sum_lt_bound_all Finset.univ _ _ hs_lt i (Finset.mem_univ i)
        exact arc_lt_imp (lt_of_le_of_lt (Nat.le_add_left _ _) hi_lt) hXt
      have harc_iso_y : ∀ t u : Fin m, mask t ⊆ mask u → ∀ r ∈ Finset.range (q - 1),
          Y t r = true → Y u r = true := by
        intro t u hsub r hr hYt
        have ht := sum_lt_bound_all Finset.univ _ _ hcut_lt t (Finset.mem_univ t)
        have h3 : Finset.univ.sum (fun u => if mask t ⊆ mask u then
            (Finset.range q).sum (fun r => Finset.univ.sum (fun i => arcFn (X t r i) (X u r i) (bigFn q unary))) +
            (Finset.range (q - 1)).sum (fun r => arcFn (Y t r) (Y u r) (bigFn q unary)) else 0) <
            bigFn q unary := by omega
        have hu_lt := sum_lt_bound_all Finset.univ _ _ h3 u (Finset.mem_univ u)
        simp only [hsub, ite_true] at hu_lt
        have hr_sum : (Finset.range (q - 1)).sum (fun r => arcFn (Y t r) (Y u r) (bigFn q unary)) < bigFn q unary := by omega
        have hr_lt := sum_lt_bound_all (Finset.range (q - 1)) _ _ hr_sum r hr
        exact arc_lt_imp hr_lt hYt
      have harc_iso_x : ∀ t u : Fin m, mask t ⊆ mask u → ∀ r ∈ Finset.range q, ∀ i : Fin a,
          X t r i = true → X u r i = true := by
        intro t u hsub r hr i hXt
        have ht := sum_lt_bound_all Finset.univ _ _ hcut_lt t (Finset.mem_univ t)
        have h3 : Finset.univ.sum (fun u => if mask t ⊆ mask u then
            (Finset.range q).sum (fun r => Finset.univ.sum (fun i => arcFn (X t r i) (X u r i) (bigFn q unary))) +
            (Finset.range (q - 1)).sum (fun r => arcFn (Y t r) (Y u r) (bigFn q unary)) else 0) <
            bigFn q unary := by omega
        have hu_lt := sum_lt_bound_all Finset.univ _ _ h3 u (Finset.mem_univ u)
        simp only [hsub, ite_true] at hu_lt
        have hr_sum : (Finset.range q).sum (fun r => Finset.univ.sum (fun i =>
            arcFn (X t r i) (X u r i) (bigFn q unary))) < bigFn q unary := by omega
        have hr_lt := sum_lt_bound_all (Finset.range q) _ _ hr_sum r hr
        have hi_lt := sum_lt_bound_all Finset.univ _ _ hr_lt i (Finset.mem_univ i)
        exact arc_lt_imp hi_lt hXt
      have hY_anti : ∀ t : Fin m, ∀ r1 r2, r1 ≤ r2 → r2 < q - 1 → Y t r2 = true → Y t r1 = true := by
        intro t r1 r2 h12 hr2 hY2
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h12
        induction d with
        | zero => simpa using hY2
        | succ d ih =>
          apply ih (by omega) (by omega)
          have hX : X t (r1 + d + 1) i0 = true :=
            harc_yx t (r1 + d + 1) (Finset.mem_range.mpr (by omega)) i0 hY2
          exact harc_xy t (r1 + d) (Finset.mem_range.mpr (by omega)) i0 hX
      let S : Fin m → Finset ℕ := fun t => (Finset.range (q - 1)).filter (fun r => Y t r = true)
      let lvl : Fin m → ℕ := fun t => (S t).card
      have hlvl_le : ∀ t, lvl t ≤ q - 1 := fun t => by
        calc lvl t = (S t).card := rfl
          _ ≤ (Finset.range (q - 1)).card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = q - 1 := Finset.card_range _
      have hlvl_lt : ∀ t, lvl t < q := fun t =>
        Nat.lt_of_le_of_lt (hlvl_le t) (Nat.sub_lt hq1 zero_lt_one)
      have hY_iff : ∀ t, ∀ r < q - 1, Y t r = true ↔ r < lvl t := by
        intro t r hr
        constructor
        · intro hYt
          have hsub : Finset.range (r + 1) ⊆ S t := by
            intro r' hr'
            rw [Finset.mem_range] at hr'
            rw [Finset.mem_filter, Finset.mem_range]
            exact ⟨by omega, hY_anti t r' r (by omega) hr hYt⟩
          have hcard := Finset.card_le_card hsub
          rw [Finset.card_range] at hcard
          exact hcard
        · intro hr_lt
          by_contra hnf
          have hsub : S t ⊆ Finset.range r := by
            intro r' hr'
            rw [Finset.mem_filter, Finset.mem_range] at hr'
            rw [Finset.mem_range]
            by_contra hge
            exact hnf (hY_anti t r r' (by omega) hr'.1 hr'.2)
          have hcard := Finset.card_le_card hsub
          rw [Finset.card_range] at hcard
          change lvl t ≤ r at hcard
          omega
      let w : Fin m → Fin a → Bool := fun t i => X t (lvl t) i
      have hX_true : ∀ t, ∀ r < lvl t, ∀ i, X t r i = true := by
        intro t r hr i
        have hrq : r < q - 1 := lt_of_lt_of_le hr (hlvl_le t)
        exact harc_yx t r (Finset.mem_range.mpr hrq) i ((hY_iff t r hrq).2 hr)
      have hX_false : ∀ t, ∀ r, lvl t < r → r < q → ∀ i, X t r i = false := by
        intro t r h1 h2 i
        by_contra hnt
        have htrue : X t r i = true := by cases hX : X t r i <;> simp_all
        obtain ⟨r', rfl⟩ := Nat.exists_eq_add_of_le (by omega : 1 ≤ r)
        have hYtrue : Y t (r' + 1 - 1) = true :=
          harc_xy t r' (Finset.mem_range.mpr (by omega)) i (by simpa [Nat.add_comm] using htrue)
        have hr'lt := (hY_iff t r' (by omega)).1 (by simpa using hYtrue)
        omega
      have hcost_row : ∀ t : Fin m,
          (q - 1) * (baseFn unary t false + baseFn unary t true) + priceFn unary pair t (w t) ≤
            (Finset.range q).sum (fun r => priceFn unary pair t (X t r)) +
            (Finset.range (q - 1)).sum (fun r =>
              (if Y t r = true then baseFn unary t false else baseFn unary t true) +
              Finset.univ.sum (fun i =>
                arcFn (Y t r) (X t r i) (bigFn q unary) + arcFn (X t (r + 1) i) (Y t r) (bigFn q unary))) +
            Finset.univ.sum (fun u => if mask t ⊆ mask u then
              (Finset.range q).sum (fun r => Finset.univ.sum (fun i => arcFn (X t r i) (X u r i) (bigFn q unary))) +
              (Finset.range (q - 1)).sum (fun r => arcFn (Y t r) (Y u r) (bigFn q unary))
            else 0) := by
        intro t
        have hcubes : (Finset.range q).sum (fun r => priceFn unary pair t (X t r)) =
            lvl t * baseFn unary t true + (q - 1 - lvl t) * baseFn unary t false + priceFn unary pair t (w t) := by
          have hcongr : (Finset.range q).sum (fun r => priceFn unary pair t (X t r)) =
              (Finset.range q).sum (fun r =>
                if r < lvl t then baseFn unary t true else if r = lvl t then priceFn unary pair t (w t) else baseFn unary t false) := by
            refine Finset.sum_congr rfl fun r hr => ?_
            rw [Finset.mem_range] at hr
            by_cases h1 : r < lvl t
            · simp only [h1, ite_true]
              have hXt : X t r = fun _ => true := funext (hX_true t r h1)
              rw [hXt, price_const_true]
            · by_cases h2 : r = lvl t
              · simp only [h2, lt_self_iff_false, ite_false]
                rfl
              · simp only [h1, h2, ite_false]
                have hXf : X t r = fun _ => false := funext (hX_false t r (by omega) hr)
                rw [hXf, price_const_false]
          rw [hcongr]
          exact sum_cubes q (lvl t) (baseFn unary t true) (baseFn unary t false) (priceFn unary pair t (w t)) (hlvl_lt t)
        have hlinks_le : lvl t * baseFn unary t false + (q - 1 - lvl t) * baseFn unary t true ≤
            (Finset.range (q - 1)).sum (fun r =>
              (if Y t r = true then baseFn unary t false else baseFn unary t true) +
              Finset.univ.sum (fun i =>
                arcFn (Y t r) (X t r i) (bigFn q unary) + arcFn (X t (r + 1) i) (Y t r) (bigFn q unary))) := by
          have hcongr : (Finset.range (q - 1)).sum (fun r =>
              if Y t r = true then baseFn unary t false else baseFn unary t true) =
              (Finset.range (q - 1)).sum (fun r =>
                if r < lvl t then baseFn unary t false else baseFn unary t true) := by
            refine Finset.sum_congr rfl fun r hr => ?_
            rw [Finset.mem_range] at hr
            by_cases h1 : r < lvl t
            · have hy : Y t r = true := (hY_iff t r hr).2 h1
              simp [h1, hy]
            · have hy : Y t r ≠ true := fun h => h1 ((hY_iff t r hr).1 h)
              simp [h1, hy]
          rw [← sum_links q (lvl t) (baseFn unary t false) (baseFn unary t true) hq1 (hlvl_le t), ← hcongr]
          exact Finset.sum_le_sum fun _ _ => Nat.le_add_right _ _
        have hle_sum : lvl t + (q - 1 - lvl t) = q - 1 := Nat.add_sub_of_le (hlvl_le t)
        have hcalc : (q - 1) * (baseFn unary t false + baseFn unary t true) + priceFn unary pair t (w t) =
            (lvl t * baseFn unary t true + (q - 1 - lvl t) * baseFn unary t false + priceFn unary pair t (w t)) +
            (lvl t * baseFn unary t false + (q - 1 - lvl t) * baseFn unary t true) := by
          calc (q - 1) * (baseFn unary t false + baseFn unary t true) + priceFn unary pair t (w t)
            _ = (lvl t + (q - 1 - lvl t)) * baseFn unary t false +
                  (lvl t + (q - 1 - lvl t)) * baseFn unary t true + priceFn unary pair t (w t) := by
                rw [hle_sum]; ring
            _ = _ := by ring
        rw [hcalc, ← hcubes]
        exact le_trans (Nat.add_le_add_left hlinks_le _) (Nat.le_add_right _ _)
      have hsum_cost : offsetFn q unary + Finset.univ.sum (fun t => priceFn unary pair t (w t)) ≤
          cutFn q mask unary pair X Y := by
        have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) fun t _ => hcost_row t
        rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
        exact hs
      have hloss : Finset.univ.sum (fun t => priceFn unary pair t (w t)) ≤ k := by
        dsimp only [offsetFn] at hsum_cost hcut
        omega
      have hOK : OK mask lvl w := by
        intro t u hsub
        constructor
        · refine Finset.card_le_card ?_
          intro r hr
          rw [Finset.mem_filter, Finset.mem_range] at hr ⊢
          exact ⟨hr.1, harc_iso_y t u hsub r (Finset.mem_range.mpr hr.1) hr.2⟩
        · intro heq i hw
          have hr : lvl t ∈ Finset.range q := Finset.mem_range.mpr (hlvl_lt t)
          have hu := harc_iso_x t u hsub (lvl t) hr i hw
          dsimp only [w]
          rwa [← heq]
      have hcap : ∀ t, lvl t < 2 ^ h := fun t => lt_of_lt_of_le (hlvl_lt t) hq_pow
      obtain ⟨C, tap, hfan, hrb, hout, hnc, htap, hval, hsz⟩ := sufficient_main mask lvl w hcap hOK
      refine ⟨C, tap, ?_, le_of_eq hnc, hsz⟩
      refine ⟨hfan, hrb, hout, htap, hnc ▸ hhb, ?_⟩
      refine le_trans (le_of_eq ?_) hloss
      refine Finset.sum_congr rfl fun t _ => ?_
      congr 1; funext i
      exact hval t i
  have dir1 : (∃ (C : Circuit) (tap : Fin a → ℕ),
        FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧
        (∀ i, tap i < n + 2 + C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
        Finset.univ.sum (fun t => priceFn unary pair t (fun i =>
          ((C.wires (raw mask t)).getD (tap i) false))) ≤ k) →
      ∃ X Y, cutFn q mask unary pair X Y ≤ offsetFn q unary + k := by
    rintro ⟨C, tap, hfan, _, _, _, hnc, hloss⟩
    let w : Fin m → Fin a → Bool := fun t i => (C.wires (raw mask t)).getD (tap i) false
    let sc : Fin m → ℕ := fun t => score t (trace mask C.gates)
    have hsc_lt : ∀ t, sc t < 2 ^ b := by
      intro t
      have h1 : sc t < 2 ^ (trace mask C.gates).length := score_lt t _
      have hlen : (trace mask C.gates).length = PEqualNP.NotBracket.notCount C := by
        have hix := countIx C.gates
        simp only [trace, List.length_map]
        rw [← hix]
        rfl
      have hpow : 2 ^ PEqualNP.NotBracket.notCount C ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hnc
      rw [hlen] at h1
      exact lt_of_lt_of_le h1 hpow
    have hsc_ok : OK mask sc w := by
      intro t u hsub
      have hst := stepOrder mask C.gates hfan t u hsub
      refine ⟨hst.1, fun heq i hwi => ?_⟩
      exact hst.2 heq (tap i) hwi
    have hbuild_lvl : ∃ lvl : Fin m → ℕ, (∀ t, lvl t < q) ∧ OK mask lvl w := by
      by_cases hlog : b < Nat.log2 (2 * limit - 1)
      · have hqb : q = 2 ^ b := hlt_log hlog
        exact ⟨sc, fun t => hqb ▸ hsc_lt t, hsc_ok⟩
      · have hql : q = limit := hge_log (Nat.le_of_not_gt hlog)
        by_cases hm0 : m = 0
        · exact ⟨fun t => absurd t.isLt (by omega), fun t => absurd t.isLt (by omega), fun t => absurd t.isLt (by omega)⟩
        · by_cases hmn : m ≤ n + 1
          · have hqm : q = m := by rw [hql]; dsimp only [limit]; omega
            let vals := (Finset.univ.image sc).sort (· ≤ ·)
            have hpair : vals.Pairwise (· < ·) :=
              (((Finset.univ.image sc).pairwise_sort (· ≤ ·)).and
                ((Finset.univ.image sc).sort_nodup (· ≤ ·))).imp fun h => Nat.lt_of_le_of_ne h.1 h.2
            have hmem : ∀ t, sc t ∈ vals := fun t =>
              (Finset.mem_sort _).2 (Finset.mem_image_of_mem _ (Finset.mem_univ t))
            let lvl : Fin m → ℕ := fun t => vals.idxOf (sc t)
            have hlvl_idx : ∀ t, lvl t < vals.length := fun t => List.idxOf_lt_length_iff.mpr (hmem t)
            have hval_len : vals.length ≤ m := by
              rw [Finset.length_sort]
              simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := sc)
            have hval_get : ∀ t, vals[lvl t]'(hlvl_idx t) = sc t := fun t =>
              List.getElem_idxOf (hlvl_idx t)
            refine ⟨lvl, fun t => by rw [hqm]; exact lt_of_lt_of_le (hlvl_idx t) hval_len, ?_⟩
            intro t u hsub
            have hok := hsc_ok t u hsub
            constructor
            · by_contra hgt
              have hrel := List.pairwise_iff_getElem.1 hpair (lvl u) (lvl t) (hlvl_idx u) (hlvl_idx t) (by omega)
              rw [hval_get u, hval_get t] at hrel
              omega
            · intro heq i hwi
              have hseq : sc t = sc u := by
                have h1 := hval_get t
                have h2 := hval_get u
                rw [← h1, ← h2]
                simp only [heq]
              exact hok.2 hseq i hwi
          · have hqn : q = n + 1 := by rw [hql]; dsimp only [limit]; omega
            let lvl : Fin m → ℕ := fun t => (mask t).card
            refine ⟨lvl, fun t => ?_, ?_⟩
            · rw [hqn]
              have hc : (mask t).card ≤ n := by simpa using Finset.card_le_univ (mask t)
              exact Nat.lt_succ_of_le hc
            · intro t u hsub
              refine ⟨Finset.card_le_card hsub, fun heq i hwi => ?_⟩
              have hmeq : mask t = mask u := Finset.eq_of_subset_of_card_le hsub (by dsimp only [lvl] at heq; omega)
              have hraw_eq : raw mask t = raw mask u := by
                unfold raw
                congr 2; funext j
                simp [hmeq]
              dsimp only [w] at hwi ⊢
              rwa [← hraw_eq]
    obtain ⟨lvl, hlvl_lt, hOK⟩ := hbuild_lvl
    let X : Fin m → ℕ → Fin a → Bool := fun t r i =>
      if r < lvl t then true else if r = lvl t then w t i else false
    let Y : Fin m → ℕ → Bool := fun t r => decide (r < lvl t)
    refine ⟨X, Y, ?_⟩
    rw [row_cost_exact q hq1 mask unary pair lvl w hlvl_lt hOK]
    exact Nat.add_le_add_left hloss _
  refine ⟨⟨dir1, fun h => ?_⟩, dir2⟩
  obtain ⟨C, tap, hfit, _⟩ := dir2 h
  exact ⟨C, tap, hfit⟩

end Combinatorics

end PEqualNP.Outside.L_lib_1367_aux

theorem PEqualNP.Outside.L_lib_1367 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n m a b : Nat) (mask : Fin m → Finset (Fin n))
    (unary : Fin m → Fin a → Bool → Nat) (pair : Fin m → Fin a → Fin a → Nat),
  let rows : Finset (Fin m) := Finset.univ
  let taps : Finset (Fin a) := Finset.univ
  let limit := max 1 (min m (n+1))
  let h := min b (Nat.log2 (2*limit-1))
  let q := min (2^h) limit
  let levels := Finset.range q
  let links := Finset.range (q-1)
  let arc := fun (x y : Bool) (k : Nat) => if x = true ∧ y = false then k else 0
  let base := fun (t : Fin m) (v : Bool) => taps.sum (fun i => unary t i v)
  let price := fun (t : Fin m) (w : Fin a → Bool) =>
    taps.sum (fun i => unary t i (w i)) +
    taps.sum (fun i => taps.sum (fun j => arc (w i) (w j) (pair t i j)))
  let offset := (q-1) * rows.sum (fun t => base t false + base t true)
  let big := 1 + offset + rows.sum (fun t => base t false)
  let cut := fun (X : Fin m → Nat → Fin a → Bool) (Y : Fin m → Nat → Bool) =>
    rows.sum (fun t =>
      levels.sum (fun r => price t (X t r)) +
      links.sum (fun r =>
        (if Y t r = true then base t false else base t true) +
        taps.sum (fun i => arc (Y t r) (X t r i) big + arc (X t (r+1) i) (Y t r) big)) +
      rows.sum (fun u => if mask t ⊆ mask u then
        levels.sum (fun r => taps.sum (fun i => arc (X t r i) (X u r i) big)) +
        links.sum (fun r => arc (Y t r) (Y u r) big) else 0))
  let fit := fun (k : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ (∀ i, tap i < n+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
    rows.sum (fun t => price t (fun i => (C.wires
      (List.ofFn (fun j : Fin n => decide (j ∈ mask t)) ++ [false,true])).getD (tap i) false)) ≤ k
  ∀ k : Nat,
    ((∃ C tap, fit k C tap) ↔ ∃ X Y, cut X Y ≤ offset+k) ∧
    ((∃ X Y, cut X Y ≤ offset+k) →
      ∃ C tap, fit k C tap ∧ PEqualNP.NotBracket.notCount C ≤ h ∧ C.size ≤ m*(n+2*h+a)+h)) := by
  classical
  intro n m a b mask unary pair rows taps limit h q levels links arc base price offset big cut fit k
  open PEqualNP.Outside.L_lib_1367_aux in
  have harc : ∀ x y v, arc x y v = arcFn x y v := fun x y v => by
    dsimp only [arc, arcFn]
    cases x <;> cases y <;> simp
  have hbase : ∀ t v, base t v = baseFn unary t v := fun _ _ => rfl
  have hprice : ∀ t w, price t w = priceFn unary pair t w := fun t w => by
    dsimp only [price]
    unfold priceFn
    simp only [taps, harc]
  have hoffset : offset = offsetFn q unary := by
    dsimp only [offset]
    unfold offsetFn
    simp only [rows, hbase]
  have hbig : big = bigFn q unary := by
    dsimp only [big]
    unfold bigFn
    simp only [hoffset, rows, hbase]
  have hcut : ∀ X Y, cut X Y = cutFn q mask unary pair X Y := fun X Y => by
    dsimp only [cut]
    unfold cutFn
    refine Finset.sum_congr rfl fun t _ => ?_
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
    · refine Finset.sum_congr rfl fun r _ => ?_
      exact hprice t (X t r)
    · refine Finset.sum_congr rfl fun r _ => ?_
      refine congrArg₂ (· + ·) ?_ ?_
      · by_cases hY : Y t r = true
        · simp only [hY, ite_true]; exact hbase t false
        · simp only [hY]; exact hbase t true
      · simp only [taps, harc, hbig]
    · refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hsub : mask t ⊆ mask u
      · simp only [hsub, ite_true, levels, links, taps, harc, hbig]
      · simp only [hsub, ite_false]
  have hraw : ∀ t, (List.ofFn (fun j : Fin n => @decide (j ∈ mask t) (Classical.propDecidable _)) ++ [false, true]) =
      raw mask t := by
    intro t
    unfold raw
    congr 2; funext j
    apply Bool.eq_iff_iff.mpr; simp
  have hfit : ∀ C tap, fit k C tap ↔
      (PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧
       C.output < n + 2 + C.size ∧ (∀ i, tap i < n + 2 + C.size) ∧
       PEqualNP.NotBracket.notCount C ≤ b ∧
       Finset.univ.sum (fun t => priceFn unary pair t (fun i =>
         ((C.wires (raw mask t)).getD (tap i) false))) ≤ k) := by
    intro C tap
    dsimp only [fit]
    simp only [rows, hprice, hraw]
  have hm := main_equiv n m a b k mask unary pair
  simp only [hfit, hcut, hoffset] at hm ⊢
  exact hm

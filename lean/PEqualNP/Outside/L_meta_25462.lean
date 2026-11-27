import Mathlib.Data.Fintype.Fin
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25462_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def run (gs : List Gate) (x : List Bool) := (Circuit.mk gs 0).wires x
def readGate (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [readGate (run gs x) g] := by
  simp [run, Circuit.wires, List.foldl_append, readGate]

theorem run_len (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run, Circuit.wires]
  | append_singleton gs g ih => simp [run_snoc, ih, Nat.add_assoc]

variable {α : Type} {N : ℕ} {inp : α → List Bool}
def Has (inp : α → List Bool) (N : ℕ) (gs : List Gate) (f : α → Bool) : Prop :=
  ∃ i, i < N + gs.length ∧ ∀ v, (run gs (inp v)).getD i false = f v

def Ext (inp : α → List Bool) (N : ℕ) (gs hs : List Gate) (k : ℕ) : Prop :=
  hs.length ≤ gs.length + k ∧ (FanInTwo ⟨gs,0⟩ → FanInTwo ⟨hs,0⟩) ∧
  ∀ f, Has inp N gs f → Has inp N hs f

theorem Ext.refl (gs : List Gate) : Ext inp N gs gs 0 := ⟨by omega, id, fun _ h => h⟩

theorem Ext.trans {a b c : List Gate} {j k l : ℕ}
    (h : Ext inp N a b j) (h' : Ext inp N b c k) (hl : j + k ≤ l) : Ext inp N a c l :=
  ⟨by have := h.1; have := h'.1; omega, fun hg => h'.2.1 (h.2.1 hg),
    fun f hf => h'.2.2 f (h.2.2 f hf)⟩

theorem addGate (len : ∀ v, (inp v).length = N) (gs : List Gate) (g : Gate)
    (ok : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    Ext inp N gs (gs ++ [g]) 1 ∧
    Has inp N (gs ++ [g]) (fun v => readGate (run gs (inp v)) g) := by
  constructor
  · refine ⟨by simp, ?_, ?_⟩
    · intro good h mem
      change h ∈ gs ++ [g] at mem
      rcases List.mem_append.mp mem with h1|h2
      · exact good h h1
      · simpa using (List.mem_singleton.mp h2 ▸ ok : h.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ h.inputs.length ≤ 2)
    · intro f hf
      obtain ⟨i, hi, hv⟩ := hf
      refine ⟨i, by simp; omega, fun v => ?_⟩
      rw [run_snoc, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [run_len,len]; exact hi)]
      exact hv v
  · refine ⟨N+gs.length, by simp, fun v => ?_⟩
    rw [run_snoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [run_len,len])]
    simp [run_len,len]

theorem combine (len : ∀ v, (inp v).length = N) {gs : List Gate} {f h : α → Bool}
    (hf : Has inp N gs f) (hh : Has inp N gs h) (o : Bool) :
    ∃ hs, Ext inp N gs hs 1 ∧ Has inp N hs (fun v => if o then f v || h v else f v && h v) := by
  obtain ⟨a,_,A⟩ := hf
  obtain ⟨b,_,B⟩ := hh
  simp only [List.getD_eq_getElem?_getD] at A B
  cases o <;> first
    | obtain ⟨E,H⟩ := addGate len gs ⟨.and,[a,b]⟩ (by simp)
      exact ⟨_,E,by simpa [readGate, GateOp.eval,A,B] using H⟩
    | obtain ⟨E,H⟩ := addGate len gs ⟨.or,[a,b]⟩ (by simp)
      exact ⟨_,E,by simpa [readGate, GateOp.eval,A,B] using H⟩

def bit (x : Bool) : ℕ := if x then 1 else 0

def total (l : List (α → Bool)) (v : α) : ℕ := ((l.map (fun f => f v)).count true)

theorem total_cons (f : α → Bool) (l : List (α → Bool)) (v : α) :
    total (f::l) v = total l v + bit (f v) := by
  cases h : f v <;> simp [total,bit,h]

def SumW (inp : α → List Bool) (N : ℕ) (gs : List Gate) (s : α → ℕ) : Prop :=
  Has inp N gs (fun v => decide (1 ≤ s v)) ∧ Has inp N gs (fun v => decide (2 ≤ s v)) ∧
  Has inp N gs (fun v => decide (3 ≤ s v))

theorem sumStep (len : ∀ v, (inp v).length = N) {gs : List Gate} {s : α → ℕ} {x : α → Bool}
    (h : SumW inp N gs s) (hx : Has inp N gs x) :
    ∃ hs, Ext inp N gs hs 5 ∧ SumW inp N hs (fun v => s v + bit (x v)) := by
  obtain ⟨p,A,P⟩ := combine len h.2.1 hx false
  obtain ⟨q,B,Q⟩ := combine len (A.2.2 _ h.2.2) P true
  have AB := A.trans B (by decide : 1+1 ≤ 2)
  obtain ⟨r,C,R⟩ := combine len (AB.2.2 _ h.1) (AB.2.2 _ hx) false
  have ABC := AB.trans C (by decide : 2+1 ≤ 3)
  obtain ⟨u,D,U⟩ := combine len (ABC.2.2 _ h.2.1) R true
  have ABCD := ABC.trans D (by decide : 3+1 ≤ 4)
  obtain ⟨w,E,W⟩ := combine len (ABCD.2.2 _ h.1) (ABCD.2.2 _ hx) true
  refine ⟨w, ABCD.trans E (by decide), ?_⟩
  have V := E.2.2 _ U
  have Z := E.2.2 _ (D.2.2 _ (C.2.2 _ Q))
  refine ⟨?_,?_,?_⟩
  · convert W using 2 with v
    apply Bool.eq_iff_iff.mpr
    cases z : x v <;> simp [bit,z]
  · convert V using 2 with v
    apply Bool.eq_iff_iff.mpr
    cases z : x v <;> simp [bit,z]; omega
  · convert Z using 2 with v
    apply Bool.eq_iff_iff.mpr
    cases z : x v <;> simp [bit,z]; omega

theorem counter (len : ∀ v, (inp v).length = N) {gs : List Gate} {z : α → Bool}
    (hz : Has inp N gs z) (hf : Has inp N gs (fun _ => false)) (l : List (α → Bool))
    (hl : ∀ x ∈ l, Has inp N gs x) :
    ∃ hs, Ext inp N gs hs (5*l.length) ∧ SumW inp N hs (fun v => total l v + bit (z v)) := by
  induction l with
  | nil =>
    refine ⟨gs,Ext.refl _, ?_,?_,?_⟩
    · convert hz using 2 with v
      cases hv : z v <;> simp [total,bit,hv]
    · convert hf using 2 with v
      cases hv : z v <;> simp [total,bit,hv]
    · convert hf using 2 with v
      cases hv : z v <;> simp [total,bit,hv]
  | cons x xs ih =>
    obtain ⟨hs,E,H⟩ := ih (fun y hy => hl y (by simp [hy]))
    obtain ⟨rs,D,R⟩ := sumStep len H (E.2.2 _ (hl x (by simp)))
    refine ⟨rs,E.trans D (by simp; omega), ?_⟩
    simpa only [total_cons,Nat.add_right_comm] using R

theorem sideOr (len : ∀ v, (inp v).length = N) {gs : List Gate}
    (hf : Has inp N gs (fun _ => false)) (l : List (α → Bool)) (hl : ∀ x ∈ l, Has inp N gs x) :
    ∃ hs, Ext inp N gs hs l.length ∧ Has inp N hs (fun v => decide (0 < total l v)) := by
  induction l with
  | nil => exact ⟨gs,Ext.refl _,by simpa [total] using hf⟩
  | cons x xs ih =>
    obtain ⟨hs,E,H⟩ := ih (fun y hy => hl y (by simp [hy]))
    obtain ⟨rs,D,R⟩ := combine len H (E.2.2 _ (hl x (by simp))) true
    refine ⟨rs,E.trans D (by simp), ?_⟩
    convert R using 2 with v
    apply Bool.eq_iff_iff.mpr
    cases z : x v <;> simp [total_cons,bit,z]

theorem inputs_keep (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [run_snoc, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [run_len]; omega)]
    exact ih

theorem assemble (len : ∀ v, (inp v).length = N) (L R : List (α → Bool))
    (nLR : (L ++ R).length = N) (hN : 3 ≤ N) (C : Circuit)
    (raw : ∀ f ∈ L ++ R, Has inp N C.gates f) (good : FanInTwo C) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size + 6*N ∧
      ∀ v, D.eval (inp v) =
        (decide (2 < total L v + total R v) ||
          ((C.eval (inp v) && decide (0 < total L v)) && decide (0 < total R v))) := by
  obtain ⟨A,H⟩ := addGate len C.gates ⟨.or,[C.output]⟩ (by simp)
  let p := C.gates ++ [⟨.or,[C.output]⟩]
  have cv : Has inp N p (fun v => C.eval (inp v)) := by
    simpa [p,readGate,GateOp.eval,Circuit.eval,run,Circuit.wires] using H
  obtain ⟨B,F⟩ := addGate len p ⟨.or,[]⟩ (by simp)
  let q := p ++ [⟨.or,[]⟩]
  have ff : Has inp N q (fun _ => false) := F
  have AB : Ext inp N C.gates q 2 := A.trans B (by decide)
  have Lw : ∀ x ∈ L, Has inp N q x := fun x hx => AB.2.2 _ (raw x (List.mem_append_left R hx))
  have Rw : ∀ x ∈ R, Has inp N q x := fun x hx => AB.2.2 _ (raw x (List.mem_append_right L hx))
  obtain ⟨z,rest,hs⟩ : ∃ z rest, L ++ R = z :: rest := by
    cases e : L ++ R with
    | nil => rw [e] at nLR; simp at nLR; omega
    | cons z rest => exact ⟨z,rest,rfl⟩
  have haveInputs : ∀ x ∈ z::rest, Has inp N q x := by
    intro x hx
    exact AB.2.2 _ (raw x (hs ▸ hx))
  obtain ⟨r,E,S⟩ := counter len (haveInputs z (by simp)) ff rest (fun x hx => haveInputs x (by simp [hx]))
  have T : Has inp N r (fun v => decide (2 < total L v + total R v)) := by
    convert S.2.2 using 2 with v
    have eqs := congrArg (fun l => total l v) hs
    rw [total_cons] at eqs
    simp only [total, List.map_append, List.count_append] at eqs
    change decide (2 < total L v + total R v) = _
    congr 1
    apply propext
    change 2 < total L v + total R v ↔ 3 ≤ total rest v + bit (z v)
    simpa [total] using (by omega : 2 < ((L.map (fun f => f v)).count true + (R.map (fun f => f v)).count true) ↔ 3 ≤ (rest.map (fun f => f v)).count true + bit (z v))
  obtain ⟨u,I,U⟩ := sideOr len (E.2.2 _ ff) L (fun x hx => E.2.2 _ (Lw x hx))
  obtain ⟨t,J,V⟩ := sideOr len (I.2.2 _ (E.2.2 _ ff)) R (fun x hx => I.2.2 _ (E.2.2 _ (Rw x hx)))
  obtain ⟨y,K,Y⟩ := combine len (J.2.2 _ (I.2.2 _ (E.2.2 _ (B.2.2 _ cv)))) (J.2.2 _ U) false
  obtain ⟨w,M,W⟩ := combine len Y (K.2.2 _ V) false
  obtain ⟨b,P,out⟩ := combine len (M.2.2 _ (K.2.2 _ (J.2.2 _ (I.2.2 _ T)))) W true
  obtain ⟨idx,_,ev⟩ := out
  refine ⟨⟨b,idx⟩,P.2.1 (M.2.1 (K.2.1 (J.2.1 (I.2.1 (E.2.1 (AB.2.1 good)))))), ?_,ev⟩
  change b.length ≤ C.gates.length + 6*N
  have ar := congrArg List.length hs
  simp only [List.length_append,List.length_cons] at ar nLR
  have := AB.1; have := E.1; have := I.1; have := J.1; have := K.1; have := M.1; have := P.1
  omega

theorem singletonInput {n : ℕ} (a : Fin n → Bool) (h : (List.ofFn a).count true = 1) :
    ∃ u : Fin n, a = fun i => decide (i=u) := by
  rw [List.count_ofFn, Finset.card_eq_one] at h
  obtain ⟨u,hu⟩ := h
  refine ⟨u,funext fun i => Bool.eq_iff_iff.mpr ?_⟩
  have eq := Finset.ext_iff.mp hu i
  simpa using eq

theorem slice_correct {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (rep : Represents A C) (a : Fin n → Bool) (b : Fin m → Bool) :
    (decide (2 < (List.ofFn a).count true + (List.ofFn b).count true) ||
        ((C.eval (List.ofFn a ++ List.ofFn b) && decide (0 < (List.ofFn a).count true)) &&
          decide (0 < (List.ofFn b).count true))) =
      (decide (2 < (List.ofFn a).count true + (List.ofFn b).count true) ||
        (decide ((List.ofFn a).count true + (List.ofFn b).count true = 2) &&
          decide (∃ u v, a u = true ∧ b v = true ∧ A u v = true))) := by
  by_cases big : 2 < (List.ofFn a).count true + (List.ofFn b).count true
  · simp only [big,decide_true,Bool.true_or]
  by_cases both : 0 < (List.ofFn a).count true ∧ 0 < (List.ofFn b).count true
  · obtain ⟨u,hu⟩ := singletonInput a (by omega)
    obtain ⟨v,hv⟩ := singletonInput b (by omega)
    have e : C.eval (List.ofFn a ++ List.ofFn b) = A u v := by simpa [oneEach,hu,hv] using rep u v
    have two : (List.ofFn a).count true + (List.ofFn b).count true = 2 := by omega
    simp only [both.1,both.2,e,two,decide_true,Bool.and_true,Bool.true_and]
    simp [hu,hv]
  · have no : ¬ ∃ u v, a u = true ∧ b v = true ∧ A u v = true := by
      rintro ⟨u,v,hu,hv,_⟩
      apply both
      exact ⟨List.count_pos_iff.mpr (List.mem_ofFn.mpr ⟨u,hu⟩),
        List.count_pos_iff.mpr (List.mem_ofFn.mpr ⟨v,hv⟩)⟩
    rcases not_and_or.mp both with ha|hb
    · simp only [no,ha,big,decide_false,Bool.false_or,Bool.and_false,Bool.false_and]
    · simp only [no,hb,big,decide_false,Bool.false_or,Bool.and_false]

end PEqualNP.Outside.L_meta_25462_aux

open PEqualNP.Outside.L_meta_25462_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_25462 : (∀ (n m s : ℕ) (A : Fin n → Fin m → Bool), 3 ≤ n + m → (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents A C) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' ∧ C'.size ≤ s + 6 * (n + m) ∧ ∀ (a : Fin n → Bool) (b : Fin m → Bool), C'.eval (List.ofFn a ++ List.ofFn b) = (decide (2 < (List.ofFn a).count true + (List.ofFn b).count true) || (decide ((List.ofFn a).count true + (List.ofFn b).count true = 2) && decide (∃ (u : Fin n) (v : Fin m), a u = true ∧ b v = true ∧ A u v = true)))) := by
  intro n m s A hN h
  obtain ⟨C,hg,hsize,rep⟩ := h
  let Inputs := (Fin n → Bool) × (Fin m → Bool)
  let inp : Inputs → List Bool := fun v => List.ofFn v.1 ++ List.ofFn v.2
  let L : List (Inputs → Bool) := List.ofFn (fun i : Fin n => fun v : Inputs => v.1 i)
  let R : List (Inputs → Bool) := List.ofFn (fun j : Fin m => fun v : Inputs => v.2 j)
  have len : ∀ v, (inp v).length = n+m := by intro v; simp [inp]
  have nLR : (L++R).length = n+m := by simp [L,R]
  have raw : ∀ f ∈ L++R, Has inp (n+m) C.gates f := by
    intro f hf
    rcases List.mem_append.mp hf with hL|hR
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hL
      refine ⟨i.val, by omega, fun v => ?_⟩
      rw [inputs_keep _ _ _ (by rw [len]; omega)]
      simp [inp,List.getD_eq_getElem?_getD,List.getElem?_append_left, i.isLt]
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hR
      refine ⟨n+j.val, by omega, fun v => ?_⟩
      rw [inputs_keep _ _ _ (by rw [len]; omega)]
      simp [inp,List.getD_eq_getElem?_getD, j.isLt]
  obtain ⟨D,gd,sd,ev⟩ := assemble len L R nLR hN C raw hg
  refine ⟨D,gd,by omega,fun a b => ?_⟩
  calc
    _ = _ := ev (a,b)
    _ = _ := by
      simpa only [total,L,R,inp,List.map_ofFn,Function.comp_def] using slice_correct rep a b

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.GetD
import PEqualNP.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi

namespace PEqualNP.Outside.L_meta_53167_aux
namespace Dervish53156Donor
namespace Donor1196
namespace DervishBuild1196

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

abbrev Legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

structure Build (w : Nat) where
  gates : List Gate
  back : ReadsBack w ⟨gates,0⟩
  fan : ∀ g ∈ gates, Legal g

namespace Build

variable {w : Nat} {X : Type}

def circ (s : Build w) : Circuit := ⟨s.gates,0⟩
def empty (w : Nat) : Build w := ⟨[], by simp [ReadsBack], by simp⟩
def size (s : Build w) : Nat := w+s.gates.length
def cost (s : Build w) : Nat := s.gates.length
def nots (s : Build w) : Nat := PEqualNP.NotBracket.notCount s.circ
def Ext (s s' : Build w) : Prop := s.gates <+: s'.gates

def Read (input : X → List Bool) (s : Build w) (r : Nat) (f : X → Bool) : Prop :=
  r < s.size ∧ ∀ x, (s.circ.wires (input x)).getD r false = f x

theorem getD_append_left {α : Type*} {xs ys : List α} {i : Nat} (h : i < xs.length) (d : α) :
    (xs++ys).getD i d = xs.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc {α : Type*} (xs : List α) (v d : α) : (xs++[v]).getD xs.length d = v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]

theorem Ext.getD {α : Type*} {xs ys : List α} (h : xs <+: ys) {i : Nat} (hi : i < xs.length) (d : α) :
    ys.getD i d = xs.getD i d := by
  obtain ⟨zs,rfl⟩ := h
  exact getD_append_left hi d

private theorem foldlen {α β : Type*} (step : List α → β → List α) (gates : List β) (x : List α)
    (hlen : ∀ l g, (step l g).length = l.length+1) :
    (gates.foldl step x).length = x.length+gates.length := by
  induction gates generalizing x with
  | nil => simp
  | cons g gs ih => simp only [List.length_cons, List.foldl_cons, ih, hlen]; omega

theorem wires_len (s : Build w) (x : List Bool) : (s.circ.wires x).length = x.length+s.gates.length :=
  foldlen _ _ _ (by simp)

private theorem foldPrefix {α β : Type*} (step : List α → β → List α) (gates : List β) (x : List α)
    (hp : ∀ l g, l <+: step l g) : x <+: gates.foldl step x := by
  induction gates generalizing x with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih => exact (hp x g).trans (ih (step x g))

theorem wires_prefix {s s' : Build w} (h : Ext s s') (x : List Bool) :
    s.circ.wires x <+: s'.circ.wires x := by
  obtain ⟨gs,hgs⟩ := h
  unfold Circuit.wires circ
  dsimp
  rw [← hgs, List.foldl_append]
  exact foldPrefix _ _ _ (fun _ _ => List.prefix_append ..)

theorem read_persist {input : X → List Bool} (hinput : ∀ x, (input x).length = w)
    {s s' : Build w} {r f} (E : Ext s s') (V : Read input s r f) : Read input s' r f := by
  refine ⟨V.1.trans_le (Nat.add_le_add_left E.length_le _), ?_⟩
  intro x
  rw [Ext.getD (wires_prefix E _) (by rw [wires_len, hinput]; exact V.1)]
  exact V.2 x

theorem read_input {input : X → List Bool} (hinput : ∀ x, (input x).length = w)
    (s : Build w) (i : Nat) (hi : i < w) : Read input s i (fun x => (input x).getD i false) := by
  have E : Ext (empty w) s := List.nil_prefix
  apply read_persist hinput E
  exact ⟨by simpa [size,empty] using hi, fun _ => rfl⟩

def push (s : Build w) (g : Gate) (fan : Legal g)
    (back : ∀ i ∈ g.inputs, i < s.size) : Build w := by
  refine ⟨s.gates++[g],?_,?_⟩
  · intro j hj i hi
    change j < (s.gates++[g]).length at hj
    change i ∈ ((s.gates++[g]).getD j _).inputs at hi
    by_cases h : j < s.gates.length
    · rw [getD_append_left h] at hi
      exact s.back j h i hi
    · have h' : j = s.gates.length := by simp at hj; omega
      subst j
      rw [getD_snoc] at hi
      exact back i hi
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact s.fan _ h
    · obtain rfl : g' = g := by simpa using h
      exact fan

theorem emit (input : X → List Bool) (hinput : ∀ x, (input x).length = w)
    (s : Build w) (g : Gate) (ok : Legal g) (back : ∀ i ∈ g.inputs, i < s.size)
    (f : X → Bool)
    (sem : ∀ x, g.op.eval (g.inputs.map (fun i => (s.circ.wires (input x)).getD i false)) = f x) :
    ∃ s' t, Ext s s' ∧ Read input s' t f ∧ s'.cost = s.cost+1 ∧
      s'.nots = s.nots + PEqualNP.NotBracket.notCount ⟨[g],0⟩ := by
  refine ⟨s.push g ok back,s.size,List.prefix_append ..,⟨by simp [size,push],?_⟩,?_ ,?_⟩
  · intro x
    have hl : (s.circ.wires (input x)).length = s.size := by rw [wires_len,hinput]; rfl
    unfold Circuit.wires circ push
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change ((s.circ.wires (input x)) ++ [_]).getD s.size false = _
    rw [← hl, getD_snoc]
    exact sem x
  · simp [cost,push]
  · simp [nots,circ,push,PEqualNP.NotBracket.notCount]

section
variable {input : X → List Bool} (hinput : ∀ x, (input x).length = w)
include hinput

theorem emitAnd {s : Build w} {a b f g} (ha : Read input s a f) (hb : Read input s b g) :
    ∃ t c, Ext s t ∧ Read input t c (fun x => f x && g x) ∧ t.cost ≤ s.cost+1 ∧ t.nots = s.nots := by
  obtain ⟨t,c,E,V,eq,n⟩ := emit input hinput s ⟨.and,[a,b]⟩ (by simp [Legal])
    (by intro j hj; simp at hj; rcases hj with rfl | rfl; exact ha.1; exact hb.1)
    (fun x => f x && g x) (by intro x; simp only [List.map_cons,List.map_nil,ha.2 x,hb.2 x] <;> cases f x <;> cases g x <;> rfl)
  exact ⟨t,c,E,V,eq.le,by simpa [PEqualNP.NotBracket.notCount] using n⟩

theorem emitOr {s : Build w} {a b f g} (ha : Read input s a f) (hb : Read input s b g) :
    ∃ t c, Ext s t ∧ Read input t c (fun x => f x || g x) ∧ t.cost ≤ s.cost+1 ∧ t.nots = s.nots := by
  obtain ⟨t,c,E,V,eq,n⟩ := emit input hinput s ⟨.or,[a,b]⟩ (by simp [Legal])
    (by intro j hj; simp at hj; rcases hj with rfl | rfl; exact ha.1; exact hb.1)
    (fun x => f x || g x) (by intro x; simp only [List.map_cons,List.map_nil,ha.2 x,hb.2 x] <;> cases f x <;> cases g x <;> rfl)
  exact ⟨t,c,E,V,eq.le,by simpa [PEqualNP.NotBracket.notCount] using n⟩

theorem emitNot {s : Build w} {a f} (ha : Read input s a f) :
    ∃ t c, Ext s t ∧ Read input t c (fun x => !(f x)) ∧ t.cost ≤ s.cost+1 ∧ t.nots = s.nots+1 := by
  obtain ⟨t,c,E,V,eq,n⟩ := emit input hinput s ⟨.not,[a]⟩ (by simp [Legal])
    (by intro j hj; simp at hj; subst j; exact ha.1)
    (fun x => !(f x)) (by intro x; simp only [List.map_cons,List.map_nil,ha.2 x] <;> cases f x <;> rfl)
  exact ⟨t,c,E,V,eq.le,by simpa [PEqualNP.NotBracket.notCount] using n⟩

end

end Build
end DervishBuild1196
namespace Upper1196Unary

private def T (m j : Nat) : Bool := decide (j ≤ m)
private def H (m d : Nat) : Bool := !(T m d)
private def U (m d j : Nat) : Bool := (H m d && T m j) || T m (d+j)

theorem comparator_reverse (a b : Bool) :
    (!(a || b) || (!(a && b) && b)) = !a ∧
    (!(a || b) || (!(a && b) && a)) = !b := by
  cases a <;> cases b <;> decide

theorem comparator_gate_law (a b : Bool) :
    PEqualNP.CircuitLowerBounds.GateOp.eval .and [a,b] = (a && b) ∧
    PEqualNP.CircuitLowerBounds.GateOp.eval .or [a,b] = (a || b) ∧
    PEqualNP.CircuitLowerBounds.GateOp.eval .not [a] = (!a) := by
  cases a <;> cases b <;> decide

theorem unary_forward (m d j : Nat) :
    U m d j = T (if m < d then m else m-d) j := by
  by_cases hm : m < d
  · have hnot : ¬ d ≤ m := by omega
    have hnot' : ¬ d+j ≤ m := by omega
    simp [U, H, T, hm, hnot, hnot']
  · have hle : d ≤ m := by omega
    have hiff : d+j ≤ m ↔ j ≤ m-d := by omega
    simp [U, H, T, hm, hle, hiff]

theorem unary_decode_low (m d j : Nat) (hj : j < d) :
    (!(T m j)) = (H m d && (!(U m d j))) := by
  by_cases hm : m < d
  · have hnot : ¬ d ≤ m := by omega
    have hnot' : ¬ d+j ≤ m := by omega
    simp [U, H, T, hm, hnot, hnot']
  · have hle : d ≤ m := by omega
    have hjle : j ≤ m := by omega
    simp [U, H, T, hle, hjle]

theorem unary_decode_mid (m d : Nat) : (!(T m d)) = H m d := rfl

theorem unary_decode_high (m d j : Nat) :
    (!(T m (d+j))) = (H m d || (!(U m d j))) := by
  by_cases hm : m < d
  · have hnot : ¬ d ≤ m := by omega
    have hnot' : ¬ d+j ≤ m := by omega
    simp [U, H, T, hnot, hnot']
  · have hle : d ≤ m := by omega
    simp [U, H, T, hle]

theorem unary_range (k m : Nat) (hm : m ≤ k) :
    (if m < k/2+1 then m else m-(k/2+1)) ≤ k/2 := by
  split_ifs <;> omega

theorem recursion_not_budget (k r : Nat) (h : k < 2^(r+1)) : k/2 < 2^r := by
  rw [pow_succ] at h
  omega

theorem unary_fold_budget (F : Nat → Nat) (h0 : F 0 = 0)
    (hs : ∀ k : Nat, 0 < k → F k ≤ k + 2*(k/2) + F (k/2)) :
    ∀ k : Nat, F k ≤ 4*k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
      by_cases hk : k = 0
      · simp [hk, h0]
      · have hsmall : k/2 < k := by omega
        have hrec := hs k (by omega)
        have hi := ih (k/2) hsmall
        omega

theorem sorting_unsorting_budget (k : Nat) :
    3*k*(k-1) + 4*k = 3*k^2 + k := by
  cases k with
  | zero => norm_num
  | succ k =>
      simp only [Nat.succ_sub_one]
      ring

theorem total_upper_budget (k m : Nat) (hm : m ≤ 3*k^2+k) :
    m+4*k ≤ 3*k^2+13*k := by omega

end Upper1196Unary
namespace Unary1196Fold
open DervishBuild1196
open DervishBuild1196.Build
open Upper1196Unary

def thresh (m : Nat) (j : Nat) : Bool := decide (j+1 ≤ m)
def reduced (m d : Nat) : Nat := if m < d then m else m-d

private theorem forward_sem (m d j : Nat) (hd : 0 < d) :
    ((!thresh m (d-1) && thresh m j) || thresh m (d+j)) =
      thresh (reduced m d) j := by
  have h := unary_forward m d (j+1)
  have hd' : d-1+1=d := by omega
  simpa [thresh, reduced, Upper1196Unary.U, Upper1196Unary.H, Upper1196Unary.T,
    hd', Nat.add_assoc] using h

private theorem low_sem (m d j : Nat) (h : j+1 < d) :
    (!thresh m j) = (!thresh m (d-1) && !thresh (reduced m d) j) := by
  have hh := unary_decode_low m d (j+1) h
  rw [unary_forward] at hh
  have hd' : d-1+1=d := by omega
  simpa [thresh, reduced, Upper1196Unary.H, Upper1196Unary.T, hd'] using hh

private theorem high_sem (m d j : Nat) (hd : 0<d) :
    (!thresh m (d+j)) = (!thresh m (d-1) || !thresh (reduced m d) j) := by
  have hh := unary_decode_high m d (j+1)
  rw [unary_forward] at hh
  have hd' : d-1+1=d := by omega
  simpa [thresh, reduced, Upper1196Unary.H, Upper1196Unary.T, hd', Nat.add_assoc] using hh

variable {w : Nat} {X : Type} {input : X → List Bool} (hlen : ∀ x, (input x).length = w)
include hlen

private theorem forward_loop (m : X → Nat) (k d q : Nat) (hm : ∀ x, m x ≤ k)
    (hd : d=q+1) (hindex : d ≤ k) (s : Build w) (z h : Nat)
    (vz : Read input s z (fun _ => false))
    (vh : Read input s h (fun x => !thresh (m x) (d-1)))
    (tap : Nat → Nat) (vt : ∀ j, j < k → Read input s (tap j) (fun x => thresh (m x) j)) :
    ∀ n, n ≤ q → ∃ t : Build w, ∃ u : Nat → Nat,
      Ext s t ∧ t.cost ≤ s.cost+2*n ∧ t.nots = s.nots ∧
      (∀ j, j < n → Read input t (u j) (fun x => thresh (reduced (m x) d) j)) := by
  intro n
  induction n with
  | zero =>
      intro _
      exact ⟨s,fun _ => z,List.prefix_rfl,by omega,rfl,by intro j hj; omega⟩
  | succ n ih =>
      intro hn
      obtain ⟨t,u,E,cb,nb,vu⟩ := ih (by omega)
      have vH := read_persist hlen E vh
      have vlow := read_persist hlen E (vt n (by omega))
      obtain ⟨a,ra,Ea,va,ca,na⟩ := emitAnd hlen vH vlow
      have hhi : d+n+1 ≤ k ∨ k < d+n+1 := by omega
      have vhi : Read input a (if d+n < k then tap (d+n) else z)
           (fun x => thresh (m x) (d+n)) := by
        by_cases hv : d+n < k
        · simpa [hv] using read_persist hlen (E.trans Ea) (vt (d+n) hv)
        · have zero : ∀ x, thresh (m x) (d+n) = false := by
            intro x
            simp [thresh, decide_eq_false_iff_not, show ¬ d+n+1 ≤ m x by have := hm x; omega]
          simpa only [if_neg hv, zero] using read_persist hlen (E.trans Ea) vz
      obtain ⟨b,rb,Eb,vb,cb',nb'⟩ := emitOr hlen va vhi
      refine ⟨b,fun j => if j=n then rb else u j,(E.trans Ea).trans Eb,?_,?_,?_⟩
      · omega
      · omega
      · intro j hj
        by_cases he : j=n
        · subst j
          have vr : Read input b rb (fun x => thresh (reduced (m x) d) n) := by
            convert vb using 1
            funext x
            exact (forward_sem (m x) d n (by omega)).symm
          simpa using vr
        · simpa only [if_neg he] using read_persist hlen (Ea.trans Eb) (vu j (by omega))

private theorem low_loop (m : X → Nat) (d q : Nat) (hd : d=q+1)
    (s : Build w) (h : Nat) (vh : Read input s h (fun x => !thresh (m x) (d-1)))
    (u : Nat → Nat)
    (vu : ∀ j, j<q → Read input s (u j) (fun x => !thresh (reduced (m x) d) j)) :
    ∀ n, n ≤ q → ∃ t : Build w, ∃ v : Nat → Nat,
      Ext s t ∧ t.cost ≤ s.cost+n ∧ t.nots = s.nots ∧
      (∀ j, j<n → Read input t (v j) (fun x => !thresh (m x) j)) := by
  intro n
  induction n with
  | zero =>
      intro _
      exact ⟨s,fun _ => h,List.prefix_rfl,by omega,rfl,by intro j hj; omega⟩
  | succ n ih =>
      intro hn
      obtain ⟨t,v,E,cb,nb,vv⟩ := ih (by omega)
      obtain ⟨a,ra,Ea,va,ca,na⟩ := emitAnd hlen (read_persist hlen E vh)
        (read_persist hlen E (vu n (by omega)))
      refine ⟨a,fun j => if j=n then ra else v j,E.trans Ea,?_,?_,?_⟩
      · omega
      · omega
      · intro j hj
        by_cases he : j=n
        · subst j
          have vr : Read input a ra (fun x => !thresh (m x) n) := by
            convert va using 1
            funext x
            exact low_sem (m x) d n (by omega)
          simpa using vr
        · simpa only [if_neg he] using read_persist hlen Ea (vv j (by omega))

private theorem high_loop (m : X → Nat) (d q : Nat) (hd : d=q+1)
    (s : Build w) (h : Nat) (vh : Read input s h (fun x => !thresh (m x) (d-1)))
    (u : Nat → Nat)
    (vu : ∀ j, j<q → Read input s (u j) (fun x => !thresh (reduced (m x) d) j)) :
    ∀ n, n ≤ q → ∃ t : Build w, ∃ v : Nat → Nat,
      Ext s t ∧ t.cost ≤ s.cost+n ∧ t.nots = s.nots ∧
      (∀ j, j<n → Read input t (v j) (fun x => !thresh (m x) (d+j))) := by
  intro n
  induction n with
  | zero =>
      intro _
      exact ⟨s,fun _ => h,List.prefix_rfl,by omega,rfl,by intro j hj; omega⟩
  | succ n ih =>
      intro hn
      obtain ⟨t,v,E,cb,nb,vv⟩ := ih (by omega)
      obtain ⟨a,ra,Ea,va,ca,na⟩ := emitOr hlen (read_persist hlen E vh)
        (read_persist hlen E (vu n (by omega)))
      refine ⟨a,fun j => if j=n then ra else v j,E.trans Ea,?_,?_,?_⟩
      · omega
      · omega
      · intro j hj
        by_cases he : j=n
        · subst j
          have vr : Read input a ra (fun x => !thresh (m x) (d+n)) := by
            convert va using 1
            funext x
            exact high_sem (m x) d n (by omega)
          simpa using vr
        · simpa only [if_neg he] using read_persist hlen Ea (vv j (by omega))

theorem invert (r : Nat) : ∀ (k : Nat) (hk : k < 2^r)
    (m : X → Nat) (hm : ∀ x, m x ≤ k)
    (s : Build w) (zero : Nat)
    (vzero : Read input s zero (fun _ => false))
    (tap : Nat → Nat)
    (vt : ∀ j, j<k → Read input s (tap j) (fun x => thresh (m x) j)),
    ∃ t : Build w, ∃ inv : Nat → Nat,
      Ext s t ∧ t.cost ≤ s.cost+4*k ∧ t.nots ≤ s.nots+r ∧
      (∀ j, j<k → Read input t (inv j) (fun x => !thresh (m x) j)) := by
  induction r with
  | zero =>
      intro k hk m hm s zero vzero tap vt
      have kz : k=0 := by simpa using hk
      subst k
      exact ⟨s,fun _ => zero,List.prefix_rfl,by omega,by omega,by intro j hj; omega⟩
  | succ r ih =>
      intro k hk m hm s zero vzero tap vt
      by_cases kz : k=0
      · subst k
        exact ⟨s,fun _ => zero,List.prefix_rfl,by omega,by omega,by intro j hj; omega⟩
      · let q := k/2
        let d := q+1
        have hq : q<k := by dsimp [q]; omega
        have hd : d≤k := by dsimp [d,q]; omega
        have hrec : q < 2^r := by
          dsimp [q]
          exact recursion_not_budget k r (by simpa using hk)
        obtain ⟨sH,H,EH,VH,cH,nH⟩ := emitNot hlen (vt q hq)
        have VHz : Read input sH zero (fun _ => false) := read_persist hlen EH vzero
        have VHT : Read input sH H (fun x => !thresh (m x) (d-1)) := by
          simpa [d,q] using VH
        have vtH : ∀ j, j<k → Read input sH (tap j) (fun x => thresh (m x) j) :=
          fun j hj => read_persist hlen EH (vt j hj)
        obtain ⟨sF,u,EF,cF,nF,vu⟩ :=
          forward_loop hlen m k d q hm (by dsimp [d]) hd sH zero H VHz VHT tap vtH q (by omega)
        have mred : ∀ x, reduced (m x) d ≤ q := by
          intro x
          simpa [reduced,d,q] using unary_range k (m x) (hm x)
        obtain ⟨sR,v,ER,cR,nR,vR⟩ :=
          ih q hrec (fun x => reduced (m x) d) mred sF zero
            (read_persist hlen EF VHz) u vu
        have VRH : Read input sR H (fun x => !thresh (m x) (d-1)) :=
          read_persist hlen (EF.trans ER) VHT
        obtain ⟨sL,l,EL,cL,nL,vl⟩ :=
          low_loop hlen m d q (by dsimp [d]) sR H VRH v vR q (by omega)
        have vHR : Read input sL H (fun x => !thresh (m x) (d-1)) :=
          read_persist hlen EL VRH
        have vrL : ∀ j, j<q → Read input sL (v j) (fun x => !thresh (reduced (m x) d) j) :=
          fun j hj => read_persist hlen EL (vR j hj)
        have hkD : k-d ≤ q := by dsimp [d,q]; omega
        obtain ⟨sT,uH,ET,cT,nT,vuH⟩ :=
          high_loop hlen m d q (by dsimp [d]) sL H vHR v vrL (k-d) hkD
        refine ⟨sT,fun j => if j<q then l j else if j=q then H else uH (j-d),
          (((EH.trans EF).trans ER).trans EL).trans ET,?_,?_,?_⟩
        · dsimp [d,q] at *
          omega
        · dsimp [d,q] at *
          omega
        · intro j hj
          by_cases jl : j<q
          · simpa [jl] using read_persist hlen ET (vl j jl)
          · by_cases je : j=q
            · subst j
              have hmid : d-1=q := by dsimp [d]
              have vr := read_persist hlen (EL.trans ET) VRH
              rw [hmid] at vr
              simpa [jl] using vr
            · have jhigh : d ≤ j := by dsimp [d]; omega
              have jbound : j-d < k-d := by omega
              have jeq : d+(j-d)=j := by omega
              simpa only [if_neg jl, if_neg je, jeq] using vuH (j-d) jbound

end Unary1196Fold

end Donor1196
namespace Wiring1270
open Dervish53156Donor.Donor1196
open DervishBuild1196 DervishBuild1196.Build

variable {n : Nat}
def input (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true]
theorem input_len (x : Finset (Fin n)) : (input x).length = n+2 := by simp [input]
theorem bit (x : Finset (Fin n)) (j : Fin n) :
    (input x).getD j.val false = decide (j ∈ x) := by
  rw [input, getD_append_left (by simp)]
  simp
theorem zero (x : Finset (Fin n)) : (input x).getD n false = false := by
  rw [input, List.getD_append_right _ _ _ _ (by simp)]
  simp

def good (s : Build (n+2)) (f : Finset (Fin n) → Bool) : Prop :=
  ∃ a, Read input s a f

theorem good_persist {s t : Build (n+2)} {f} (E : Ext s t)
    (h : good s f) : good t f := by
  obtain ⟨a,ha⟩ := h
  exact ⟨a, read_persist input_len E ha⟩

theorem good_bit (s : Build (n+2)) (j : Fin n) :
    good s (fun x => decide (j ∈ x)) := by
  refine ⟨j.val,?_⟩
  have h := read_input (input := input (n:=n)) input_len s j.val (by omega : j.val<n+2)
  convert h using 1
  funext x
  exact (bit x j).symm

theorem good_zero (s : Build (n+2)) : good s (fun _ => false) := by
  refine ⟨n,?_⟩
  have h := read_input (input := input (n:=n)) input_len s n (by omega : n<n+2)
  convert h using 1
  funext x
  exact (zero x).symm

theorem good_one (s : Build (n+2)) : good s (fun _ => true) := by
  refine ⟨n+1,?_⟩
  have h := read_input (input := input (n:=n)) input_len s (n+1) (by omega : n+1<n+2)
  convert h using 1
  funext x
  rw [input, List.getD_append_right _ _ _ _ (by simp)]
  simp

def conj (y x : Finset (Fin n)) : Bool := decide (y ⊆ x)

def any_bools {I : Type} (idx : Finset I)
    (fs : I → Finset (Fin n) → Bool) (x : Finset (Fin n)) : Bool :=
  decide (∃ i ∈ idx, fs i x = true)

end Wiring1270
end Dervish53156Donor

namespace DervishSampleBasis53156
variable {n m : ℕ}
abbrev X (n : ℕ) := Finset (Fin n)

noncomputable def sampleRank (S : Finset (X n)) (h : X n → ℕ) (x : X n) : ℕ := by
  classical
  exact (S.filter (fun y => y ⊆ x)).sup h

theorem sampleRank_le (S : Finset (X n)) (h : X n → ℕ) (L : ℕ)
    (hh : ∀ y ∈ S, h y ≤ L) (x : X n) : sampleRank S h x ≤ L := by
  classical
  exact Finset.sup_le_iff.mpr (fun y hy => hh y (Finset.mem_filter.mp hy).1)

theorem sampleRank_mono (S : Finset (X n)) (h : X n → ℕ) : Monotone (sampleRank S h) := by
  classical
  intro x z hx
  apply Finset.sup_mono
  intro y hy
  obtain ⟨hyS, hxy⟩ := Finset.mem_filter.mp hy
  exact Finset.mem_filter.mpr ⟨hyS,hxy.trans hx⟩

theorem sampleRank_on (S : Finset (X n)) (h : X n → ℕ) (hh : ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → h x ≤ h y)
    (x : X n) (hx : x ∈ S) : sampleRank S h x = h x := by
  classical
  apply Nat.le_antisymm
  · exact Finset.sup_le_iff.mpr (fun y hy => hh y (Finset.mem_filter.mp hy).1 x hx (Finset.mem_filter.mp hy).2)
  · exact Finset.le_sup (Finset.mem_filter.mpr ⟨hx,Finset.Subset.rfl⟩)

theorem threshold_on (S : Finset (X n)) (h : X n → ℕ) (x : X n) (u : ℕ) :
    u+1 ≤ sampleRank S h x ↔ ∃ y ∈ S, y ⊆ x ∧ u+1 ≤ h y := by
  classical
  constructor
  · intro hz
    by_contra hn
    have hub : sampleRank S h x ≤ u := by
      apply Finset.sup_le_iff.mpr
      intro y hy
      obtain ⟨hyS,hyx⟩ := Finset.mem_filter.mp hy
      by_contra hbad
      exact hn ⟨y,hyS,hyx,by omega⟩
    omega
  · rintro ⟨y,hy,hyx,hu⟩
    exact hu.trans (Finset.le_sup (Finset.mem_filter.mpr ⟨hy,hyx⟩))

noncomputable def basis (S : Finset (X n)) (h : X n → ℕ) (y x : X n) : Bool := by
  classical
  exact decide (y ⊆ x ∧ sampleRank S h x ≤ h y)

noncomputable def report (S : Finset (X n)) (h : X n → ℕ) (v : X n → Fin m → Bool)
    (j : Fin m) (x : X n) : Bool := by
  classical
  exact decide (∃ y ∈ S, v y j = true ∧ basis S h y x = true)

theorem report_exact (S : Finset (X n)) (h : X n → ℕ) (v : X n → Fin m → Bool)
    (hh : ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → h x ≤ h y)
    (hv : ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → h x = h y → ∀ j, v x j = true → v y j = true)
    (x : X n) (hx : x ∈ S) (j : Fin m) : report S h v j x = v x j := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [report, basis, decide_eq_true_eq, sampleRank_on S h hh x hx]
  constructor
  · rintro ⟨y,hy,hyj,hyx,hhxy⟩
    exact hv y hy x hx hyx (Nat.le_antisymm (hh y hy x hx hyx) hhxy) j hyj
  · intro hxj
    exact ⟨x,hx,hxj,Finset.Subset.rfl,Nat.le_refl _⟩

end DervishSampleBasis53156

namespace DervishBudget53156
open Dervish53156Donor
open Donor1196 DervishBuild1196 DervishBuild1196.Build Wiring1270
variable {n : ℕ}
abbrev X (n : ℕ) := Finset (Fin n)

theorem goodAnd {s : Build (n+2)} {f g : X n → Bool} (hf : good s f) (hg : good s g) :
    ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+1 ∧ good t (fun x => f x && g x) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  obtain ⟨u,w,he,hr,hc,hn⟩ := emitAnd input_len ha hb
  exact ⟨u,he,hn,hc,w,hr⟩

theorem goodOr {s : Build (n+2)} {f g : X n → Bool} (hf : good s f) (hg : good s g) :
    ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+1 ∧ good t (fun x => f x || g x) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  obtain ⟨u,w,he,hr,hc,hn⟩ := emitOr input_len ha hb
  exact ⟨u,he,hn,hc,w,hr⟩

theorem conjBudget (s : Build (n+2)) (y : X n) :
    ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+y.card ∧ good t (conj y) := by
  classical
  induction y using Finset.induction_on generalizing s with
  | empty =>
    refine ⟨s,List.prefix_rfl,rfl,by simp,?_⟩
    convert good_one s using 1
    funext x
    simp [conj]
  | @insert j y hj ih =>
    obtain ⟨u,E,N,C,V⟩ := ih s
    obtain ⟨t,Et,Nt,Ct,Vt⟩ := goodAnd (good_bit u j) V
    refine ⟨t,E.trans Et,Nt.trans N,?_,?_⟩
    · rw [Finset.card_insert_of_notMem hj]
      omega
    · convert Vt using 1
      funext x
      simp [conj, Finset.insert_subset_iff]

theorem orBudget {I : Type} [DecidableEq I] (idx : Finset I) (fs : I → X n → Bool)
    (s : Build (n+2)) (hf : ∀ j ∈ idx, good s (fs j)) :
    ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+idx.card ∧ good t (any_bools idx fs) := by
  classical
  induction idx using Finset.induction_on generalizing s with
  | empty =>
    refine ⟨s,List.prefix_rfl,rfl,by simp,?_⟩
    convert good_zero s using 1
    funext x
    simp [any_bools]
  | @insert j idx hj ih =>
    obtain ⟨u,E,N,C,V⟩ := ih s (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    obtain ⟨t,Et,Nt,Ct,Vt⟩ := goodOr (good_persist E (hf j (Finset.mem_insert_self ..))) V
    refine ⟨t,E.trans Et,Nt.trans N,?_,?_⟩
    · rw [Finset.card_insert_of_notMem hj]
      omega
    · convert Vt using 1
      funext x
      simp [any_bools,Finset.mem_insert]

theorem buildMany {I : Type} [DecidableEq I] (idx : Finset I) (fs : I → X n → Bool)
    (C : ℕ) (s₀ s : Build (n+2)) (E₀ : Ext s₀ s)
    (make : ∀ i ∈ idx, ∀ u : Build (n+2), Ext s₀ u →
      ∃ t, Ext u t ∧ t.nots = u.nots ∧ t.cost ≤ u.cost+C ∧ good t (fs i)) :
    ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+idx.card*C ∧ ∀ i ∈ idx, good t (fs i) := by
  classical
  induction idx using Finset.induction_on generalizing s with
  | empty => exact ⟨s,List.prefix_rfl,rfl,by simp,by simp⟩
  | @insert j idx hj ih =>
    obtain ⟨u,E,N,H,V⟩ := make j (Finset.mem_insert_self ..) s E₀
    obtain ⟨t,Et,Nt,Ht,Vt⟩ := ih u (E₀.trans E)
      (fun i hi => make i (Finset.mem_insert_of_mem hi))
    refine ⟨t,E.trans Et,Nt.trans N,?_,?_⟩
    · rw [Finset.card_insert_of_notMem hj, Nat.add_mul, Nat.one_mul]
      omega
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact good_persist Et V
      · exact Vt i hi

end DervishBudget53156

namespace DervishCeil53156
open Dervish53156Donor
open Donor1196 DervishBuild1196 DervishBuild1196.Build Wiring1270
open DervishSampleBasis53156 DervishBudget53156
variable {n : ℕ}

theorem sampleContainments (S : Finset (Finset (Fin n))) (s : Build (n+2)) :
    ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+S.card*n ∧ ∀ y ∈ S, good t (conj y) := by
  apply buildMany S conj n s s List.prefix_rfl
  intro y hy u _
  obtain ⟨t,E,N,C,V⟩ := conjBudget u y
  have hy' : y.card ≤ n := by
    simpa using (Finset.card_le_univ y)
  exact ⟨t,E,N,by omega,V⟩

theorem positiveThresholds (S : Finset (Finset (Fin n))) (h : Finset (Fin n) → ℕ)
    (L : ℕ) (s : Build (n+2)) (hs : ∀ y ∈ S, good s (conj y)) :
    ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+L*S.card ∧
      ∀ l : Fin L, good t (fun x => decide (l.val+1 ≤ sampleRank S h x)) := by
  classical
  let idx : Finset (Fin L) := Finset.univ
  let fs (j : Fin L) (x : Finset (Fin n)) : Bool := decide (j.val+1 ≤ sampleRank S h x)
  have make (i : Fin L) (_ : i ∈ idx) (u : Build (n+2)) (E : Ext s u) :
      ∃ t, Ext u t ∧ t.nots = u.nots ∧ t.cost ≤ u.cost+S.card ∧ good t (fs i) := by
    let ys := S.filter (fun y => i.val+1 ≤ h y)
    have hs' : ∀ y ∈ ys, good u (conj y) := fun y hy =>
      good_persist E (hs y (Finset.mem_filter.mp hy).1)
    obtain ⟨t,Et,Nt,Ct,Vt⟩ := orBudget ys conj u hs'
    have hsz : ys.card ≤ S.card := Finset.card_filter_le _ _
    have eq : any_bools ys conj = fs i := by
      funext x
      apply Bool.eq_iff_iff.mpr
      simp only [any_bools,ys,fs,conj,decide_eq_true_eq,Finset.mem_filter,threshold_on]
      constructor
      · rintro ⟨y,⟨hy,hr⟩,hx⟩
        exact ⟨y,hy,hx,hr⟩
      · rintro ⟨y,hy,hx,hr⟩
        exact ⟨y,⟨hy,hr⟩,hx⟩
    rw [eq] at Vt
    exact ⟨t,Et,Nt,by omega,Vt⟩
  obtain ⟨t,E,N,C,H⟩ := buildMany idx fs S.card s s List.prefix_rfl make
  exact ⟨t,E,N,by simpa [idx] using C,fun i => H i (Finset.mem_univ _)⟩

theorem ceilThresholds (S : Finset (Finset (Fin n))) (h : Finset (Fin n) → ℕ)
    (L b : ℕ) (hPow : L < 2^b) (hBound : ∀ y ∈ S, h y ≤ L)
    (s : Build (n+2))
    (hs : ∀ l : Fin L, good s (fun x => decide (l.val+1 ≤ sampleRank S h x))) :
    ∃ t, Ext s t ∧ t.nots ≤ s.nots+b ∧ t.cost ≤ s.cost+4*L ∧
      ∀ y ∈ S, good t (fun x => decide (sampleRank S h x ≤ h y)) := by
  classical
  let R := sampleRank S h
  have hm : ∀ x, R x ≤ L := sampleRank_le S h L hBound
  choose addr hr using hs
  obtain ⟨z,hz⟩ := good_zero s
  let tap (j : ℕ) : ℕ := if hj : j < L then addr ⟨j,hj⟩ else z
  have vow : ∀ j, j<L → Read input s (tap j) (fun x => Unary1196Fold.thresh (R x) j) := by
    intro j hj
    simpa only [tap,dif_pos hj,R,Unary1196Fold.thresh] using (hr ⟨j,hj⟩)
  obtain ⟨t,it,E,C,N,vi⟩ := Unary1196Fold.invert
    (input := input (n:=n)) input_len b L hPow R hm s z hz tap vow
  refine ⟨t,E,N,C,?_⟩
  intro y hy
  by_cases hlt : h y < L
  · refine ⟨it (h y),?_⟩
    convert vi (h y) hlt using 1
    funext x
    change decide (R x ≤ h y) = !(decide (h y+1 ≤ R x))
    by_cases he : R x ≤ h y
    · have hn : ¬ h y+1 ≤ R x := by omega
      simp [he,hn]
    · have hp : h y+1 ≤ R x := by omega
      simp [he,hp]
  · convert good_one t using 1
    funext x
    exact decide_eq_true ((hm x).trans (Nat.le_of_not_gt hlt))

end DervishCeil53156

namespace DervishGrouped53167
open Dervish53156Donor
open Donor1196 DervishBuild1196 DervishBuild1196.Build Wiring1270
open DervishSampleBasis53156 DervishBudget53156
variable {n : ℕ}

theorem groupedThresholds (S : Finset (Finset (Fin n))) (h : Finset (Fin n) → ℕ)
    (L : ℕ) (hb : ∀ y ∈ S, h y ≤ L) (s : Build (n+2))
    (hs : ∀ y ∈ S, good s (conj y)) :
    ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+S.card+L ∧
      ∀ l : Fin L, good t (fun x => decide (l.val+1 ≤ sampleRank S h x)) := by
  classical
  let cut (a : ℕ) := S.filter (fun y => a ≤ h y)
  let P (a : ℕ) (x : Finset (Fin n)) : Bool := decide (a ≤ sampleRank S h x)
  have loop : ∀ d : ℕ, d ≤ L → ∃ t, Ext s t ∧ t.nots = s.nots ∧
      t.cost ≤ s.cost+(cut (L+1-d)).card+d ∧
      ∀ k : ℕ, L+1-d ≤ k → good t (P k) := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨s,List.prefix_rfl,rfl,by omega,?_⟩
      intro k hk
      have eq : P k = fun _ => false := by
        funext x
        change decide (k ≤ sampleRank S h x) = false
        have le := sampleRank_le S h L hb x
        exact decide_eq_false (by omega)
      rw [eq]
      exact good_zero s
    | succ d ih =>
      intro hd
      let a := L-d
      have hstep : L+1-(d+1) = a := by dsimp [a]; omega
      have hprev : L+1-d = a+1 := by dsimp [a]; omega
      change ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+(cut (L+1-(d+1))).card+(d+1) ∧
        ∀ k : ℕ, L+1-(d+1) ≤ k → good t (P k)
      rw [hstep]
      obtain ⟨u,Eu,Nu,Cu,Hu⟩ := ih (by omega)
      rw [hprev] at Cu Hu
      let A := S.filter (fun y => h y = a)
      have hA : ∀ y ∈ A, good u (conj y) := fun y hy => good_persist Eu (hs y (Finset.mem_filter.mp hy).1)
      obtain ⟨v,Ev,Nv,Cv,Hv⟩ := orBudget A conj u hA
      obtain ⟨t,Et,Nt,Ct,Ht⟩ := goodOr Hv (good_persist Ev (Hu (a+1) le_rfl))
      have hdis : Disjoint A (cut (a+1)) := by
        apply Finset.disjoint_left.mpr
        intro y hy hz
        have he : h y = a := (Finset.mem_filter.mp hy).2
        have hle : a+1 ≤ h y := (Finset.mem_filter.mp hz).2
        omega
      have hUnion : A ∪ cut (a+1) = cut a := by
        ext y
        simp only [A,cut,Finset.mem_union,Finset.mem_filter]
        constructor
        · rintro (⟨hy,he⟩ | ⟨hy,he⟩) <;> exact ⟨hy, by omega⟩
        · rintro ⟨hy,hle⟩
          by_cases he : h y = a
          · exact Or.inl ⟨hy,he⟩
          · exact Or.inr ⟨hy,by omega⟩
      have hCard : A.card+(cut (a+1)).card = (cut a).card := by
        rw [← Finset.card_union_of_disjoint hdis, hUnion]
      have hFun : (fun x => any_bools A conj x || P (a+1) x) = P a := by
        funext x
        apply Bool.eq_iff_iff.mpr
        have ha : 0 < a := by dsimp [a]; omega
        have hra : a-1+1 = a := by omega
        have th0 := threshold_on S h x (a-1)
        rw [hra] at th0
        simp only [any_bools,conj,A,P,Bool.or_eq_true,decide_eq_true_eq,Finset.mem_filter]
        rw [threshold_on S h x a, th0]
        constructor
        · rintro (⟨y,⟨hy,he⟩,hyx⟩ | ⟨y,hy,hyx,hk⟩)
          · exact ⟨y,hy,hyx,by omega⟩
          · exact ⟨y,hy,hyx,by omega⟩
        · rintro ⟨y,hy,hyx,hk⟩
          by_cases he : h y = a
          · exact Or.inl ⟨y,⟨hy,he⟩,hyx⟩
          · exact Or.inr ⟨y,hy,hyx,by omega⟩
      rw [hFun] at Ht
      refine ⟨t,Eu.trans (Ev.trans Et),Nt.trans (Nv.trans Nu),by omega,?_⟩
      intro k hk
      by_cases he : k = a
      · subst k; exact Ht
      · exact good_persist (Ev.trans Et) (Hu k (by omega))
  obtain ⟨t,E,N,C,F⟩ := loop L le_rfl
  have he : L+1-L = 1 := by omega
  rw [he] at C F
  have hCard : (cut 1).card ≤ S.card := Finset.card_filter_le _ _
  exact ⟨t,E,N,by omega,fun l => F (l.val+1) (by omega)⟩

end DervishGrouped53167

namespace DervishTight53167
open PEqualNP PEqualNP.CircuitLowerBounds
open Dervish53156Donor
open Donor1196 DervishBuild1196 DervishBuild1196.Build Wiring1270
open DervishSampleBasis53156 DervishBudget53156 DervishCeil53156 DervishGrouped53167
variable {n m : ℕ}

theorem basisBank (S : Finset (Finset (Fin n))) (h : Finset (Fin n) → ℕ) (s : Build (n+2))
    (hc : ∀ y ∈ S, good s (conj y))
    (hr : ∀ y ∈ S, good s (fun x => decide (sampleRank S h x ≤ h y))) :
    ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+S.card ∧
      ∀ y ∈ S, good t (basis S h y) := by
  classical
  have hMany := buildMany S (basis S h) 1 s s List.prefix_rfl
  obtain ⟨t,E,N,C,H⟩ := hMany (by
    intro y hy u e
    obtain ⟨v,Ev,Nv,Cv,Vv⟩ := goodAnd (good_persist e (hc y hy)) (good_persist e (hr y hy))
    refine ⟨v,Ev,Nv,Cv,?_⟩
    convert Vv using 1
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [basis,conj,Bool.and_eq_true,decide_eq_true_eq])
  exact ⟨t,E,N,by simpa using C,H⟩

theorem reportBank (S : Finset (Finset (Fin n))) (h : Finset (Fin n) → ℕ)
    (v : Finset (Fin n) → Fin m → Bool) (s : Build (n+2))
    (hs : ∀ y ∈ S, good s (basis S h y)) :
    ∃ t, Ext s t ∧ t.nots = s.nots ∧ t.cost ≤ s.cost+m*S.card ∧
      ∀ j, good t (report S h v j) := by
  classical
  let idx : Finset (Fin m) := Finset.univ
  have make (j : Fin m) (_ : j ∈ idx) (u : Build (n+2)) (E : Ext s u) :
      ∃ t, Ext u t ∧ t.nots = u.nots ∧ t.cost ≤ u.cost+S.card ∧ good t (report S h v j) := by
    let ys := S.filter (fun y => v y j = true)
    obtain ⟨t,E',N,C,H⟩ := orBudget ys (basis S h) u
      (fun y hy => good_persist E (hs y (Finset.mem_filter.mp hy).1))
    have hCard : ys.card ≤ S.card := Finset.card_filter_le _ _
    refine ⟨t,E',N,by omega,?_⟩
    convert H using 1
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [report,any_bools,ys,Finset.mem_filter,decide_eq_true_eq,and_assoc]
  obtain ⟨t,E,N,C,H⟩ := buildMany idx (report S h v) S.card s s List.prefix_rfl make
  exact ⟨t,E,N,by simpa [idx] using C,fun j => H j (Finset.mem_univ _)⟩

theorem compile_tight (S : Finset (Finset (Fin n))) (h : Finset (Fin n) → ℕ)
    (v : Finset (Fin n) → Fin m → Bool) (L b : ℕ) (hPow : L < 2^b)
    (hBound : ∀ y ∈ S, h y ≤ L)
    (hh : ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → h x ≤ h y)
    (hv : ∀ x ∈ S, ∀ y ∈ S, x ⊆ y → h x = h y → ∀ j, v x j = true → v y j = true) :
    ∃ (C : Circuit) (tap : Fin m → Fin (n+2+C.size)),
      MetaComplexity.FanInTwo C ∧ MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ NotBracket.notCount C ≤ b ∧
      C.size ≤ (n+2)*S.card + m*S.card + 5*L ∧
      ∀ x ∈ S, ∀ j, (C.wires (input x)).getD (tap j).val false = v x j := by
  classical
  let s : Build (n+2) := Build.empty _
  obtain ⟨u,_,N₁,C₁,V₁⟩ := sampleContainments S s
  obtain ⟨p,E₂,N₂,C₂,V₂⟩ := groupedThresholds S h L hBound u V₁
  obtain ⟨a,E₃,N₃,C₃,V₃⟩ := ceilThresholds S h L b hPow hBound p V₂
  obtain ⟨d,_,N₄,C₄,V₄⟩ := basisBank S h a
    (fun y hy => good_persist (E₂.trans E₃) (V₁ y hy)) V₃
  obtain ⟨e,_,N₅,C₅,V₅⟩ := reportBank S h v d V₄
  have hzero : s.cost = 0 ∧ s.nots = 0 := by
    simp [s,Build.empty,Build.cost,Build.nots,Build.circ,NotBracket.notCount]
  have hCost : e.cost ≤ (n+2)*S.card + m*S.card + 5*L := by
    rw [Nat.add_mul, Nat.mul_comm n S.card]
    omega
  have hNots : e.nots ≤ b := by omega
  choose addr hadd using V₅
  let C : Circuit := ⟨e.gates,0⟩
  let tap : Fin m → Fin (n+2+C.size) := fun j =>
    ⟨addr j, by
      have h := (hadd j).1
      simpa only [C,Circuit.size,Build.size,Build.cost] using h⟩
  refine ⟨C,tap,e.fan,e.back,by simp [C],hNots,hCost,?_⟩
  intro x hx j
  exact ((hadd j).2 x).trans (report_exact S h v hh hv x hx j)

end DervishTight53167

namespace DervishRank53167
variable {X : Type*} [Preorder X] {m : Nat}

abbrev Labels (X : Type*) (m : Nat) := X → Fin m → Option Bool

def reach (lab : Labels X m) : Nat → X → Prop :=
  Nat.rec (motive := fun _ => X → Prop) (fun _ => True)
    (fun _ prev z => ∃ x y j, prev x ∧ x ≤ y ∧ y ≤ z ∧
      lab x j = some true ∧ lab y j = some false)

theorem reach_mono (lab : Labels X m) (k : Nat) : Monotone (reach lab k) := by
  cases k with
  | zero => intro x y h hx; exact True.intro
  | succ k =>
    intro x y h hx
    rcases hx with ⟨u,v,j,hu,huv,hvx,ht,hf⟩
    exact ⟨u,v,j,hu,huv,hvx.trans h,ht,hf⟩

theorem reach_pred (lab : Labels X m) (k : Nat) (z : X) :
    reach lab (k+1) z → reach lab k z := by
  induction k generalizing z with
  | zero => intro; exact True.intro
  | succ k ih =>
    rintro ⟨x,y,j,hx,hxy,hyz,ht,hf⟩
    exact ⟨x,y,j,ih x hx,hxy,hyz,ht,hf⟩

theorem reach_le (lab : Labels X m) {a b : Nat} (hab : a ≤ b) (z : X) :
    reach lab b z → reach lab a z := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hab
  induction r with
  | zero => simp
  | succ r ih =>
    intro h
    exact ih (by omega) (reach_pred lab (a+r) z h)

noncomputable def rank (lab : Labels X m) (z : X) : Nat :=
  sSup {k | reach lab k z}

theorem rank_set_bound (lab : Labels X m) (L : Nat)
    (cap : ∀ z, ¬ reach lab (L+1) z) (z : X) :
    BddAbove {k : Nat | reach lab k z} := by
  refine ⟨L, ?_⟩
  intro k hk
  change reach lab k z at hk
  by_contra h
  exact cap z (reach_le lab (by omega) z hk)

theorem rank_reached (lab : Labels X m) (L : Nat)
    (cap : ∀ z, ¬ reach lab (L+1) z) (z : X) : reach lab (rank lab z) z := by
  change sSup {k : Nat | reach lab k z} ∈ {k : Nat | reach lab k z}
  exact Nat.sSup_mem ⟨0, True.intro⟩ (rank_set_bound lab L cap z)

theorem rank_le (lab : Labels X m) (L : Nat)
    (cap : ∀ z, ¬ reach lab (L+1) z) (z : X) : rank lab z ≤ L := by
  by_contra h
  exact cap z (reach_le lab (by omega) z (rank_reached lab L cap z))

theorem rank_mono (lab : Labels X m) (L : Nat)
    (cap : ∀ z, ¬ reach lab (L+1) z) : Monotone (rank lab) := by
  intro x y h
  apply le_csSup (rank_set_bound lab L cap y)
  exact reach_mono lab _ h (rank_reached lab L cap x)

theorem rank_fall (lab : Labels X m) (L : Nat)
    (cap : ∀ z, ¬ reach lab (L+1) z) {x y : X} (hxy : x ≤ y) (j : Fin m)
    (ht : lab x j = some true) (hf : lab y j = some false) : rank lab x < rank lab y := by
  apply Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
  apply le_csSup (rank_set_bound lab L cap y)
  exact ⟨x,y,j,rank_reached lab L cap x,hxy,le_rfl,ht,hf⟩

noncomputable def fill (S : Finset X) (lab : Labels X m) (z : X) (j : Fin m) : Bool := by
  classical
  exact decide (∃ x ∈ S, x ≤ z ∧ rank lab x = rank lab z ∧ lab x j = some true)

theorem fill_mono (S : Finset X) (lab : Labels X m) {x y : X} (hxy : x ≤ y)
    (hr : rank lab x = rank lab y) (j : Fin m) : fill S lab x j ≤ fill S lab y j := by
  apply Bool.le_iff_imp.mpr
  simp only [fill, decide_eq_true_eq]
  rintro ⟨z,hz,hzx,hrz,ht⟩
  exact ⟨z,hz,hzx.trans hxy,hrz.trans hr,ht⟩

theorem fill_extends (S : Finset X) (lab : Labels X m) (L : Nat)
    (cap : ∀ z, ¬ reach lab (L+1) z) {z : X} (hz : z ∈ S) (j : Fin m)
    (v : Bool) (hv : lab z j = some v) : fill S lab z j = v := by
  classical
  cases v with
  | true =>
    simp only [fill, decide_eq_true_eq]
    exact ⟨z,hz,le_rfl,rfl,hv⟩
  | false =>
    simp only [fill, decide_eq_false_iff_not]
    rintro ⟨x,_,hx,hr,ht⟩
    exact (ne_of_lt (rank_fall lab L cap hx j ht hv)) hr

end DervishRank53167

namespace DervishLabels53167
open PEqualNP PEqualNP.CircuitLowerBounds DervishRank53167

variable {n m b : ℕ}
abbrev X (n : ℕ) := Fin n → Bool
abbrev Tap (n m : ℕ) (C : Circuit) := Fin m → Fin (n+2+C.size)

def bits (x : X n) : Finset (Fin n) := Finset.univ.filter (fun i => x i = true)
def unbits (A : Finset (Fin n)) : X n := fun i => decide (i ∈ A)

theorem unbits_bits (x : X n) : unbits (bits x) = x := by
  funext i
  cases hx : x i <;> simp [unbits,bits,hx]

theorem unbits_mono : Monotone (unbits (n:=n)) := by
  intro a c hac i
  apply Bool.le_iff_imp.mpr
  simp only [unbits, decide_eq_true_eq]
  exact fun hi => hac hi

theorem compile_labels (S : Finset (X n)) (lab : Labels (X n) m)
    (cap : ∀ z, ¬ reach lab (2^b) z) :
    ∃ (C : Circuit) (tap : Tap n m C),
      MetaComplexity.FanInTwo C ∧ MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ NotBracket.notCount C ≤ b ∧
      C.size ≤ b+(n+2)*S.card + m*S.card + 5*(2^b-1) ∧
      ∀ x ∈ S, ∀ j v, lab x j = some v →
        (C.wires (List.ofFn x ++ [false,true])).getD (tap j).val false = v := by
  classical
  let U := S.image bits
  let L := 2^b-1
  have hp : 0 < 2^b := Nat.two_pow_pos b
  have he : L+1=2^b := by dsimp [L]; omega
  have cap' : ∀ z, ¬ reach lab (L+1) z := by simpa only [he] using cap
  have hL : L < 2^b := by omega
  let h (A : Finset (Fin n)) := rank lab (unbits A)
  let v (A : Finset (Fin n)) (j : Fin m) := fill S lab (unbits A) j
  have hb : ∀ y ∈ U, h y ≤ L := fun y _ => rank_le lab L cap' (unbits y)
  have hm : ∀ x ∈ U, ∀ y ∈ U, x ⊆ y → h x ≤ h y := by
    intro x _ y _ hxy
    exact rank_mono lab L cap' (unbits_mono hxy)
  have hv : ∀ x ∈ U, ∀ y ∈ U, x ⊆ y → h x = h y → ∀ j, v x j = true → v y j = true := by
    intro x _ y _ hxy heq j hx
    exact Bool.le_iff_imp.mp (fill_mono S lab (unbits_mono hxy) heq j) hx
  obtain ⟨C,tap,fan,back,out,nots,size,fit⟩ := DervishTight53167.compile_tight U h v L b hL hb hm hv
  have hc : U.card ≤ S.card := Finset.card_image_le
  have hc1 := Nat.mul_le_mul_left (n+2) hc
  have hc2 := Nat.mul_le_mul_left m hc
  refine ⟨C,tap,fan,back,out,nots,by dsimp [L] at size; omega,?_⟩
  intro x hx j q hq
  have hi : bits x ∈ U := Finset.mem_image_of_mem bits hx
  have hf := fit (bits x) hi j
  change (C.wires (List.ofFn (unbits (bits x)) ++ [false,true])).getD (tap j).val false =
     fill S lab (unbits (bits x)) j at hf
  rw [unbits_bits] at hf
  exact hf.trans (fill_extends S lab L cap' hx j q hq)

theorem realizability (S Z : Finset (X n)) (want lab : Labels (X n) m)
    (need : ∀ x ∈ S, x ∈ Z → ∀ j q, want x j = some q → lab x j = some q)
    (miss : ∀ x ∈ S, x ∉ Z → ∃ (j : Fin m) (q : Bool),
       want x j = some q ∧ lab x j = some (!q))
    (cap : ∀ z, ¬ reach lab (2^b) z) :
    ∃ (C : Circuit) (tap : Tap n m C),
      MetaComplexity.FanInTwo C ∧ MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ NotBracket.notCount C ≤ b ∧
      C.size ≤ b+(n+2)*S.card + m*S.card + 5*(2^b-1) ∧
      ∀ x ∈ S, (∀ j q, want x j = some q →
        (C.wires (List.ofFn x ++ [false,true])).getD (tap j).val false = q) ↔ x ∈ Z := by
  obtain ⟨C,tap,fan,back,out,nots,size,fit⟩ := compile_labels S lab cap
  refine ⟨C,tap,fan,back,out,nots,size,?_⟩
  intro x hx
  constructor
  · intro hit
    by_contra notZ
    obtain ⟨j,q,hq,hl⟩ := miss x hx notZ
    have he := (hit j q hq).symm.trans (fit x hx j (!q) hl)
    cases q <;> simp at he
  · intro hZ j q hq
    exact fit x hx j q (need x hx hZ j q hq)

end DervishLabels53167

namespace DervishLabelData53167
noncomputable def label {n m : ℕ} (S Z : Finset (Fin n → Bool))
    (want : (Fin n → Bool) → Fin m → Option Bool)
    (w : (Fin n → Bool) → Option (Fin m)) (x : Fin n → Bool) (j : Fin m) : Option Bool :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  if x ∈ S then if x ∈ Z then want x j else
    if w x = some j then (want x j).map Bool.not else none
  else none
end DervishLabelData53167

open PEqualNP.CircuitLowerBounds
local instance : DecidableEq PEqualNP.CircuitLowerBounds.GateOp :=
  PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
namespace Falls53167

def below (x y : List Bool) : Prop := ∀ i, x.getD i false ≤ y.getD i false

private theorem below_append (a b : List Bool) (u v : Bool)
    (h : below a b) (hu : u ≤ v) (hl : a.length = b.length) :
    below (a ++ [u]) (b ++ [v]) := by
  intro i
  by_cases hi : i < a.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hl ▸ hi)]
    exact h i
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_lt hi),
        List.getD_append_right _ _ _ _ (by omega : b.length ≤ i)]
    by_cases hiz : i - a.length = 0
    · have hbz : i - b.length = 0 := by omega
      simp only [hiz, hbz]
      exact hu
    · have hg : 1 ≤ i - a.length := by omega
      have hg2 : 1 ≤ i - b.length := by omega
      rw [List.getD_eq_default _ _ hg, List.getD_eq_default _ _ hg2]
private theorem all_mono (a b : List Bool) (h : below a b) (is : List ℕ) :
    (is.map fun i => a.getD i false).all id ≤
    (is.map fun i => b.getD i false).all id := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons, List.all_cons, id_eq]
    have hi := h i
    cases ha : a.getD i false <;> cases hb : b.getD i false
    · simp
    · simp
    · have hcontra : False := (by decide : ¬ (true : Bool) ≤ false) (by simpa only [ha, hb] using hi)
      exact hcontra.elim
    · simpa [ha, hb] using ih

private theorem any_mono (a b : List Bool) (h : below a b) (is : List ℕ) :
    (is.map fun i => a.getD i false).any id ≤
    (is.map fun i => b.getD i false).any id := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons, List.any_cons, id_eq]
    have hi := h i
    cases ha : a.getD i false <;> cases hb : b.getD i false
    · simpa [ha, hb] using ih
    · simp
    · have hcontra : False := (by decide : ¬ (true : Bool) ≤ false) (by simpa only [ha, hb] using hi)
      exact hcontra.elim
    · simpa [ha, hb] using ih

private theorem gate_mono (a b : List Bool) (h : below a b) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hn : g.op = GateOp.not →
      g.op.eval (g.inputs.map fun i => a.getD i false) =
      g.op.eval (g.inputs.map fun i => b.getD i false)) :
    g.op.eval (g.inputs.map fun i => a.getD i false) ≤
    g.op.eval (g.inputs.map fun i => b.getD i false) := by
  rcases hop with ha | ho | hnop
  · simpa [ha, GateOp.eval] using all_mono a b h g.inputs
  · simpa [ho, GateOp.eval] using any_mono a b h g.inputs
  · exact le_of_eq (hn hnop)

private def physicalNot (C : Circuit) := {j : Fin C.size // (C.gates[j.val]).op = GateOp.not}

private noncomputable instance (C : Circuit) : Fintype (physicalNot C) := by
  classical
  unfold physicalNot
  infer_instance

private theorem physical_not_count (C : Circuit) :
    Fintype.card (physicalNot C) = PEqualNP.NotBracket.notCount C := by
  classical
  simp only [physicalNot, Fintype.card_subtype, PEqualNP.NotBracket.notCount]
  change (Finset.univ.filter (fun j : Fin C.gates.length => C.gates[j.val].op = GateOp.not)).card =
    (C.gates.filter fun g => decide (g.op = GateOp.not)).length
  rw [← List.countP_eq_length_filter]
  conv_rhs => rw [← List.ofFn_get C.gates]
  rw [List.countP_ofFn]
  simp

def value (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
def step (w : List Bool) (g : Gate) := w ++ [value g w]
def resultFrom (gs : List Gate) (w : List Bool) := gs.foldl step w

def signatureFrom : List Gate → List Bool → List Bool
  | [], _ => []
  | g :: gs, w =>
      (if g.op = GateOp.not then [value g w] else []) ++ signatureFrom gs (step w g)

private theorem signatureFrom_length (gs : List Gate) (w : List Bool) :
    (signatureFrom gs w).length =
      (gs.filter fun g => decide (g.op = GateOp.not)).length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : g.op = GateOp.not <;> simp [signatureFrom, ih, h]

private theorem resultFrom_length (gs : List Gate) (w : List Bool) :
    (resultFrom gs w).length = w.length + gs.length := by
  simp only [resultFrom]
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

private theorem not_between (a b c : List Bool) (hab : below a b) (hbc : below b c)
    (is : List ℕ)
    (hac : GateOp.not.eval (is.map fun i => a.getD i false) =
      GateOp.not.eval (is.map fun i => c.getD i false)) :
    GateOp.not.eval (is.map fun i => a.getD i false) =
      GateOp.not.eval (is.map fun i => b.getD i false) ∧
    GateOp.not.eval (is.map fun i => b.getD i false) =
      GateOp.not.eval (is.map fun i => c.getD i false) := by
  cases is with
  | nil => simp [GateOp.eval]
  | cons i is =>
    have hi := hab i
    have hi' := hbc i
    simp only [List.map_cons, GateOp.eval, List.headD_cons] at hac ⊢
    cases ha : a.getD i false <;> cases hb : b.getD i false <;>
      cases hc : c.getD i false <;> simp_all
    all_goals exact False.elim ((by decide : ¬ (true : Bool) ≤ false) (by assumption))

private theorem signature_convex (gs : List Gate) (a b c : List Bool)
    (hab : below a b) (hbc : below b c)
    (hablen : a.length = b.length) (hbclen : b.length = c.length)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hends : signatureFrom gs a = signatureFrom gs c) :
    signatureFrom gs a = signatureFrom gs b ∧
    below (resultFrom gs a) (resultFrom gs b) ∧
    below (resultFrom gs b) (resultFrom gs c) := by
  induction gs generalizing a b c with
  | nil => exact ⟨rfl, hab, hbc⟩
  | cons g gs ih =>
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
      hops g (by simp)
    have htOps : ∀ q ∈ gs, q.op = GateOp.and ∨ q.op = GateOp.or ∨ q.op = GateOp.not := by
      intro q hq
      exact hops q (by simp [hq])
    by_cases hn : g.op = GateOp.not
    · have hv : value g a = value g c := by
        have h := hends
        simp only [signatureFrom, if_pos hn, List.singleton_append, List.cons.injEq] at h
        exact h.1
      have htail : signatureFrom gs (step a g) = signatureFrom gs (step c g) := by
        have h := hends
        simp only [signatureFrom, if_pos hn, List.singleton_append, List.cons.injEq] at h
        exact h.2
      have hvals : value g a = value g b ∧ value g b = value g c := by
        simpa only [value, hn] using
          (not_between a b c hab hbc g.inputs (by simpa only [value, hn] using hv))
      have hab' : below (step a g) (step b g) :=
        below_append a b (value g a) (value g b) hab hvals.1.le hablen
      have hbc' : below (step b g) (step c g) :=
        below_append b c (value g b) (value g c) hbc hvals.2.le hbclen
      have hres := ih (step a g) (step b g) (step c g) hab' hbc'
        (by simp [step, hablen]) (by simp [step, hbclen]) htOps htail
      refine ⟨?_, hres.2.1, hres.2.2⟩
      simp [signatureFrom, hn, hvals.1, hres.1]
    · have htail : signatureFrom gs (step a g) = signatureFrom gs (step c g) := by
        simpa only [signatureFrom, if_neg hn, List.nil_append] using hends
      have hab' : below (step a g) (step b g) :=
        below_append a b (value g a) (value g b) hab
          (gate_mono a b hab g hop (by intro h; exact (hn h).elim)) hablen
      have hbc' : below (step b g) (step c g) :=
        below_append b c (value g b) (value g c) hbc
          (gate_mono b c hbc g hop (by intro h; exact (hn h).elim)) hbclen
      have hres := ih (step a g) (step b g) (step c g) hab' hbc'
        (by simp [step, hablen]) (by simp [step, hbclen]) htOps htail
      refine ⟨?_, hres.2.1, hres.2.2⟩
      simpa [signatureFrom, hn] using hres.1

def circuitSignature (C : Circuit) (x : List Bool) :
    Fin (PEqualNP.NotBracket.notCount C) → Bool :=
  fun j => (signatureFrom C.gates x).getD j.val false

private theorem sig_injective (C : Circuit) (x y : List Bool)
    (h : circuitSignature C x = circuitSignature C y) :
    signatureFrom C.gates x = signatureFrom C.gates y := by
  have hlen (w : List Bool) :
      (signatureFrom C.gates w).length = PEqualNP.NotBracket.notCount C := by
    exact signatureFrom_length C.gates w
  apply List.ext_getElem
  · exact (hlen x).trans (hlen y).symm
  · intro i hix hiy
    let j : Fin (PEqualNP.NotBracket.notCount C) := ⟨i, by simpa only [hlen] using hix⟩
    have hj := congrFun h j
    change (signatureFrom C.gates x).getD i false =
      (signatureFrom C.gates y).getD i false at hj
    rwa [List.getD_eq_getElem _ _ hix, List.getD_eq_getElem _ _ hiy] at hj

theorem circuit_signature_convex (C : Circuit) (a b c : List Bool)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hab : below a b) (hbc : below b c)
    (hlenAB : a.length = b.length) (hlenBC : b.length = c.length)
    (heq : circuitSignature C a = circuitSignature C c) :
    circuitSignature C a = circuitSignature C b ∧
      below (C.wires a) (C.wires b) ∧ below (C.wires b) (C.wires c) := by
  have hops : ∀ g ∈ C.gates,
      g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    intro g hg
    have h := (hfan g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have h := signature_convex C.gates a b c hab hbc hlenAB hlenBC hops
    (sig_injective C a c heq)
  refine ⟨?_, ?_, ?_⟩
  · funext j
    exact congrArg (fun w : List Bool => w.getD j.val false) h.1
  · exact h.2.1
  · exact h.2.2

theorem signature_bound (k r : ℕ) (σ : Fin (k+1) → Fin r → Bool)
    (hconvex : ∀ a b c : Fin (k+1), a ≤ b → b ≤ c → σ a = σ c → σ a = σ b)
    (hfall : ∀ i : Fin k, σ (Fin.castSucc i) ≠ σ (Fin.succ i)) : k < 2^r := by
  have hinj : Function.Injective σ := by
    intro a c heq
    rcases le_total a c with hac | hca
    · by_contra hne
      have hlt : a.val < c.val := Nat.lt_of_le_of_ne hac (by
        intro h; exact hne (Fin.ext h))
      have hsmall : a.val < k := by omega
      let i : Fin k := ⟨a.val, hsmall⟩
      have hboundary := hfall i
      have hstep := hconvex a (Fin.succ i) c (by change a.val ≤ i.val + 1; dsimp [i]; omega) (by change i.val + 1 ≤ c.val; dsimp [i]; omega) heq
      have ha : Fin.castSucc i = a := by ext; rfl
      exact hboundary (by simpa [ha] using hstep)
    · by_contra hne
      have hlt : c.val < a.val := Nat.lt_of_le_of_ne hca (by
        intro h; exact hne (Fin.ext h.symm))
      have hsmall : c.val < k := by omega
      let i : Fin k := ⟨c.val, hsmall⟩
      have hboundary := hfall i
      have hstep := hconvex c (Fin.succ i) a (by change c.val ≤ i.val + 1; dsimp [i]; omega) (by change i.val + 1 ≤ a.val; dsimp [i]; omega) heq.symm
      have hc : Fin.castSucc i = c := by ext; rfl
      exact hboundary (by simpa [hc] using hstep)
  have hcard : Fintype.card (Fin (k+1)) ≤ Fintype.card (Fin r → Bool) :=
    Fintype.card_le_of_injective σ hinj
  simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool] at hcard
  omega
theorem odd_fall_bound (k r : ℕ) (σ : Fin (2*k+1) → Fin r → Bool)
    (hconvex : ∀ a b c : Fin (2*k+1), a ≤ b → b ≤ c → σ a = σ c → σ a = σ b)
    (hfall : ∀ i : Fin k,
      σ ⟨2*i.val+1, by omega⟩ ≠ σ ⟨2*i.val+2, by omega⟩) : k < 2^r := by
  let τ : Fin (k+1) → Fin r → Bool := fun i => σ ⟨2*i.val, by omega⟩
  apply signature_bound k r τ
  · intro a b c hab hbc heq
    exact hconvex ⟨2*a.val, by omega⟩ ⟨2*b.val, by omega⟩
      ⟨2*c.val, by omega⟩ (by change 2*a.val ≤ 2*b.val; omega)
      (by change 2*b.val ≤ 2*c.val; omega) heq
  · intro i heq
    have hbase := hfall i
    have hend : σ ⟨2*i.val, by omega⟩ = σ ⟨2*i.val+2, by omega⟩ := by
      simpa [τ, Fin.succ, Fin.castSucc, mul_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using heq
    have hfirst : σ ⟨2*i.val, by omega⟩ = σ ⟨2*i.val+1, by omega⟩ :=
      hconvex ⟨2*i.val, by omega⟩ ⟨2*i.val+1, by omega⟩
        ⟨2*i.val+2, by omega⟩
        (by change 2*i.val ≤ 2*i.val+1; omega)
        (by change 2*i.val+1 ≤ 2*i.val+2; omega) hend
    exact hbase (hfirst.symm.trans hend)

theorem circuit_multioutput_markov (k n : Nat) (C : Circuit)
    (x : Fin (2*k+1) → List Bool)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hlen : ∀ t, (x t).length = n)
    (hmono : ∀ a b, a ≤ b → below (x a) (x b))
    (hfall : ∀ i : Fin k, ∃ w : ℕ,
      (C.wires (x ⟨2*i.val+1, by omega⟩)).getD w false = true ∧
      (C.wires (x ⟨2*i.val+2, by omega⟩)).getD w false = false) :
    k < 2 ^ PEqualNP.NotBracket.notCount C := by
  apply odd_fall_bound k (PEqualNP.NotBracket.notCount C)
    (fun t => circuitSignature C (x t))
  · intro a b c hab hbc heq
    exact (circuit_signature_convex C (x a) (x b) (x c) hfan
      (hmono a b hab) (hmono b c hbc)
      (by rw [hlen a, hlen b]) (by rw [hlen b, hlen c]) heq).1
  · intro i heq
    rcases hfall i with ⟨w, hw1, hw0⟩
    let a : Fin (2*k+1) := ⟨2*i.val+1, by omega⟩
    let b : Fin (2*k+1) := ⟨2*i.val+2, by omega⟩
    have hab : a ≤ b := by change 2*i.val+1 ≤ 2*i.val+2; omega
    have hbelow := (circuit_signature_convex C (x a) (x b) (x b) hfan
      (hmono a b hab) (by intro j; exact le_refl _)
      (by rw [hlen a, hlen b]) rfl heq).2.1
    have hf := hbelow w
    rw [show x a = x ⟨2*i.val+1, by omega⟩ from rfl,
      show x b = x ⟨2*i.val+2, by omega⟩ from rfl, hw1, hw0] at hf
    exact (by decide : ¬ (true : Bool) ≤ false) hf

end Falls53167

namespace Falls53167

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

private def input {n : Nat} (x : Fin n → Bool) : List Bool := List.ofFn x ++ [false, true]

private theorem input_length {n : Nat} (x : Fin n → Bool) : (input x).length = n+2 := by
  simp [input]

private theorem input_below {n : Nat} {x y : Fin n → Bool} (hxy : x ≤ y) :
    below (input x) (input y) := by
  intro i
  by_cases hi : i < n
  · have hx : i < (List.ofFn x).length := by simpa using hi
    have hy : i < (List.ofFn y).length := by simpa using hi
    rw [input, input, List.getD_append _ _ _ _ hx, List.getD_append _ _ _ _ hy]
    rw [List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hy]
    simpa only [List.getElem_ofFn] using hxy ⟨i, hi⟩
  · rw [input, input, List.getD_append_right _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by simp; omega)]
    simp

private def reach {n m : Nat} (label : (Fin n → Bool) → Fin m → Option Bool) :
    Nat → (Fin n → Bool) → Prop :=
  Nat.rec (motive := fun _ => (Fin n → Bool) → Prop) (fun _ => True)
    (fun _ prev z => ∃ x y j, prev x ∧ x ≤ y ∧ y ≤ z ∧
      label x j = some true ∧ label y j = some false)

private theorem reach_signature_bound {n m : Nat} (C : Circuit)
    (a : Fin m → Fin (n+2+C.size))
    (label : (Fin n → Bool) → Fin m → Option Bool)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hlabel : ∀ (x : Fin n → Bool) (j : Fin m) (v : Bool),
      label x j = some v → (C.wires (input x)).getD (a j).val false = v) :
    ∀ k z, reach label k z → k < 2 ^ PEqualNP.NotBracket.notCount C := by
  let sig : (Fin n → Bool) → (Fin (PEqualNP.NotBracket.notCount C) → Bool) :=
    fun x => circuitSignature C (input x)
  have hconv (x y z : Fin n → Bool) (hxy : x ≤ y) (hyz : y ≤ z)
      (heq : sig x = sig z) : sig x = sig y ∧
        below (C.wires (input x)) (C.wires (input y)) := by
    have h := circuit_signature_convex C (input x) (input y) (input z)
      hfan (input_below hxy) (input_below hyz)
      (by rw [input_length, input_length]) (by rw [input_length, input_length]) heq
    exact ⟨h.1, h.2.1⟩
  have hfall (x y z : Fin n → Bool) (j : Fin m)
      (hxy : x ≤ y) (hyz : y ≤ z)
      (htrue : label x j = some true) (hfalse : label y j = some false) :
      sig x ≠ sig z := by
    intro heq
    have hh := (hconv x y z hxy hyz heq).2 (a j).val
    rw [hlabel x j true htrue, hlabel y j false hfalse] at hh
    exact (by decide : ¬ (true : Bool) ≤ false) hh
  have hstrong : ∀ k z, reach label k z →
      ∃ E : Finset (Fin (PEqualNP.NotBracket.notCount C) → Bool),
        E.card = k ∧ ∀ t, z ≤ t → sig t ∉ E := by
    intro k
    induction k with
    | zero =>
      intro z _
      exact ⟨∅, rfl, by simp⟩
    | succ k ih =>
      intro z hz
      obtain ⟨x,y,j,hprev,hxy,hyz,htrue,hfalse⟩ := hz
      obtain ⟨E,hcard,havoid⟩ := ih x hprev
      refine ⟨insert (sig x) E, ?_, ?_⟩
      · simp [havoid x le_rfl, hcard]
      · intro t hzt
        rw [Finset.mem_insert]
        push_neg
        constructor
        · exact (hfall x y t j hxy (le_trans hyz hzt) htrue hfalse).symm
        · exact havoid t (le_trans hxy (le_trans hyz hzt))
  intro k z hz
  obtain ⟨E,hcard,havoid⟩ := hstrong k z hz
  have hsubset : E ⊆ (Finset.univ : Finset (Fin (PEqualNP.NotBracket.notCount C) → Bool)).erase (sig z) := by
    intro v hv
    exact Finset.mem_erase.mpr ⟨by intro heq; subst v; exact havoid z le_rfl hv,
      Finset.mem_univ _⟩
  have hsize := Finset.card_le_card hsubset
  have herase := Finset.card_erase_of_mem (Finset.mem_univ (sig z))
  have hfinite : (Finset.univ : Finset (Fin (PEqualNP.NotBracket.notCount C) → Bool)).card =
      2 ^ PEqualNP.NotBracket.notCount C := by simp
  rw [hfinite] at herase
  rw [hcard, herase] at hsize
  have hpos : 0 < 2 ^ PEqualNP.NotBracket.notCount C := pow_pos (by norm_num) _
  omega

private theorem pattern_of_valid_hit {n m b : Nat} (S Z : Finset (Fin n → Bool))
    (want : (Fin n → Bool) → Fin m → Option Bool)
    (C : Circuit) (a : Fin m → Fin (n+2+C.size))
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hbudget : PEqualNP.NotBracket.notCount C ≤ b)
    (hZ : Z ⊆ S)
    (hpattern : ∀ x ∈ S, (∀ (j : Fin m) (v : Bool), want x j = some v →
        (C.wires (List.ofFn x ++ [false,true])).getD (a j).val false = v) ↔ x ∈ Z) :
    Z ⊆ S ∧ ∃ w : (Fin n → Bool) → Option (Fin m),
      (∀ x ∈ S, x ∉ Z → ∃ (j : Fin m) (v : Bool),
        w x = some j ∧ want x j = some v) ∧
      let label := DervishLabelData53167.label S Z want w
      ∀ z, ¬ reach label (2^b) z := by
  classical
  have hbad (x : Fin n → Bool) (hx : x ∈ S) (hnot : x ∉ Z) :
      ∃ (j : Fin m) (v : Bool), want x j = some v ∧
        (C.wires (input x)).getD (a j).val false ≠ v := by
    have hno : ¬ ∀ (j : Fin m) (v : Bool), want x j = some v →
        (C.wires (input x)).getD (a j).val false = v := by
      intro hh
      exact hnot ((hpattern x hx).mp hh)
    push_neg at hno
    exact hno
  let chosen (x : Fin n → Bool) (hx : x ∈ S) (hnot : x ∉ Z) : Fin m :=
    (hbad x hx hnot).choose
  let w : (Fin n → Bool) → Option (Fin m) := fun x =>
    if h : x ∈ S ∧ x ∉ Z then some (chosen x h.1 h.2) else none
  have hw (x : Fin n → Bool) (hx : x ∈ S) (hnot : x ∉ Z) :
      w x = some (chosen x hx hnot) := by
    simp only [w, dif_pos (show x ∈ S ∧ x ∉ Z from ⟨hx, hnot⟩)]
  have hlabel : ∀ (x : Fin n → Bool) (j : Fin m) (v : Bool),
      DervishLabelData53167.label S Z want w x j = some v →
      (C.wires (input x)).getD (a j).val false = v := by
    intro x j v hv
    by_cases hx : x ∈ S
    · by_cases hz : x ∈ Z
      · have hh := (hpattern x hx).mpr hz
        exact hh j v (by simpa [DervishLabelData53167.label,hx, hz] using hv)
      · have hj : w x = some j := by
          by_contra hj
          simp [DervishLabelData53167.label,hx, hz, hj] at hv
        have hj' : chosen x hx hz = j := by
          have hh := hw x hx hz
          rw [hj] at hh
          exact (Option.some.inj hh).symm
        obtain ⟨v0, hval, hwrong⟩ := (hbad x hx hz).choose_spec
        have hgiven : (want x j).map Bool.not = some v := by
          simpa [DervishLabelData53167.label,hx, hz, hj] using hv
        change want x (chosen x hx hz) = some v0 at hval
        change (C.wires (input x)).getD (a (chosen x hx hz)).val false ≠ v0 at hwrong
        rw [hj'] at hval hwrong
        rw [hval] at hgiven
        cases v0 <;> cases v <;> simp_all
    · simp [DervishLabelData53167.label,hx] at hv
  refine ⟨hZ, w, ?_, ?_⟩
  · intro x hx hz
    obtain ⟨v0, hval, _⟩ := (hbad x hx hz).choose_spec
    change want x (chosen x hx hz) = some v0 at hval
    exact ⟨chosen x hx hz, v0, hw x hx hz, hval⟩
  · dsimp only
    intro z hz
    have hb := reach_signature_bound C a _ hfan hlabel (2^b) z hz
    have hp : 2 ^ PEqualNP.NotBracket.notCount C ≤ 2^b :=
      Nat.pow_le_pow_right (by omega : 0 < 2) hbudget
    omega

end
end Falls53167

namespace DervishPattern53167
open PEqualNP PEqualNP.CircuitLowerBounds
abbrev X (n : ℕ) := Fin n → Bool
abbrev Tap (n m : ℕ) (C : Circuit) := Fin m → Fin (n+2+C.size)
abbrev Want (n m : ℕ) := X n → Fin m → Option Bool

def valid (n b : ℕ) (C : Circuit) : Prop :=
  MetaComplexity.FanInTwo C ∧ MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ NotBracket.notCount C ≤ b

def hit {n m : ℕ} (want : Want n m) (C : Circuit) (a : Tap n m C) (x : X n) : Prop :=
  ∀ j v, want x j = some v → (C.wires (List.ofFn x ++ [false,true])).getD (a j).val false = v

open DervishLabelData53167

def pat {n m : ℕ} (S : Finset (X n)) (b : ℕ) (want : Want n m) (Z : Finset (X n)) : Prop :=
  Z ⊆ S ∧ ∃ w : X n → Option (Fin m),
    (∀ x ∈ S, x ∉ Z → ∃ (j : Fin m) (v : Bool), w x = some j ∧ want x j = some v) ∧
    ∀ z, ¬ DervishRank53167.reach (label S Z want w) (2^b) z

theorem exact_pattern {n m b : ℕ} (S Z : Finset (X n)) (want : Want n m) :
    pat S b want Z ↔ Z ⊆ S ∧ ∃ (C : Circuit) (a : Tap n m C),
      valid n b C ∧ C.size ≤ b+(n+2)*S.card + m*S.card + 5*(2^b-1) ∧
      ∀ x ∈ S, hit want C a x ↔ x ∈ Z := by
  classical
  constructor
  · rintro ⟨hZ,w,hw,hcap⟩
    have need : ∀ x ∈ S, x ∈ Z → ∀ j q, want x j = some q → label S Z want w x j = some q := by
      intro x hx hz j q he
      simpa [label,hx,hz] using he
    have miss : ∀ x ∈ S, x ∉ Z → ∃ (j : Fin m) (q : Bool),
        want x j = some q ∧ label S Z want w x j = some (!q) := by
      intro x hx hz
      obtain ⟨j,q,hj,hq⟩ := hw x hx hz
      exact ⟨j,q,hq,by simp [label,hx,hz,hj,hq]⟩
    obtain ⟨C,a,fan,back,out,nots,size,fit⟩ :=
      DervishLabels53167.realizability S Z want (label S Z want w) need miss hcap
    exact ⟨hZ,C,a,⟨fan,back,out,nots⟩,size,fit⟩
  · rintro ⟨hZ,C,a,hvalid,_,hfit⟩
    obtain ⟨hz,w,hw,hc⟩ := Falls53167.pattern_of_valid_hit S Z want C a hvalid.1 hvalid.2.2.2 hZ hfit
    exact ⟨hz,w,hw,hc⟩

end DervishPattern53167

namespace Sparse53167

variable {X : Type*} [Fintype X] [DecidableEq X]

private def signature (S : Finset X) (F : Finset (Finset X))
    (A : {A : Finset (Finset X) // A ⊆ F}) (r : Option S) : Fin (F.card + 1) :=
  ⟨match r with
   | none => A.val.card
   | some x => (A.val.filter (fun Z => x.val ∈ Z)).card,
   by
     cases r with
     | none => exact Nat.lt_succ_of_le (Finset.card_le_card A.property)
     | some x =>
       exact Nat.lt_succ_of_le ((Finset.card_le_card (Finset.filter_subset _ _)).trans
         (Finset.card_le_card A.property))⟩

private theorem signature_none (S : Finset X) (F : Finset (Finset X))
    (A : {A : Finset (Finset X) // A ⊆ F}) :
    (signature S F A none).val = A.val.card := rfl

private theorem signature_some (S : Finset X) (F : Finset (Finset X))
    (A : {A : Finset (Finset X) // A ⊆ F}) (x : S) :
    (signature S F A (some x)).val = (A.val.filter (fun Z => x.val ∈ Z)).card := rfl

theorem support_bound_of_signature_inj (S : Finset X) (F : Finset (Finset X))
    (hinj : Function.Injective (fun (A : {A : Finset (Finset X) // A ⊆ F}) =>
      signature S F A)) :
    2 ^ F.card ≤ (F.card+1) ^ (S.card+1) := by
  have hc : Fintype.card {A : Finset (Finset X) // A ⊆ F} ≤
      Fintype.card (Option S → Fin (F.card+1)) :=
    Fintype.card_le_of_injective _ hinj
  have hsub : Fintype.card {A : Finset (Finset X) // A ⊆ F} = 2 ^ F.card := by
    rw [Fintype.subtype_card]
    convert Finset.card_powerset F using 1
    congr 1
    ext A
    simp
  simpa [hsub, Fintype.card_fun] using hc

private theorem sum_indicator (F P : Finset X) (hP : P ⊆ F) (g : X → Nat) :
    F.sum (fun z => if z ∈ P then g z else 0) = P.sum g := by
  rw [← Finset.sum_filter]
  congr 1
  ext z
  simp only [Finset.mem_filter]
  constructor
  · exact And.right
  · intro hz
    exact ⟨hP hz, hz⟩

private theorem shift_sum (F P Q : Finset X) (hP : P ⊆ F) (hQ : Q ⊆ F)
    (hPQ : Disjoint P Q) (mult g : X → Nat) (d : Nat)
    (hmin : ∀ z ∈ P, d ≤ mult z) (hcount : P.sum g = Q.sum g) :
    F.sum (fun z => g z * (if z ∈ P then mult z - d else if z ∈ Q then mult z + d else mult z)) =
      F.sum (fun z => g z * mult z) := by
  let shifted : X → Nat := fun z =>
    if z ∈ P then mult z - d else if z ∈ Q then mult z + d else mult z
  have hpoint (z : X) : shifted z + (if z ∈ P then d else 0) =
      mult z + (if z ∈ Q then d else 0) := by
    dsimp [shifted]
    by_cases hp : z ∈ P
    · have hq : z ∉ Q := (Finset.disjoint_left.mp hPQ) hp
      simp [hp, hq, Nat.sub_add_cancel (hmin z hp)]
    · by_cases hq : z ∈ Q <;> simp [hp, hq]
  have hcorr (R : Finset X) (hR : R ⊆ F) :
      F.sum (fun z => g z * (if z ∈ R then d else 0)) = d * R.sum g := by
    calc
      F.sum (fun z => g z * (if z ∈ R then d else 0)) =
          F.sum (fun z => if z ∈ R then d * g z else 0) := by
        apply Finset.sum_congr rfl
        intro z hz
        split_ifs <;> simp [Nat.mul_comm]
      _ = R.sum (fun z => d * g z) := sum_indicator F R hR _
      _ = d * R.sum g := by rw [Finset.mul_sum]
  have hs : F.sum (fun z => g z * shifted z) +
      F.sum (fun z => g z * (if z ∈ P then d else 0)) =
      F.sum (fun z => g z * mult z) +
      F.sum (fun z => g z * (if z ∈ Q then d else 0)) := by
    simp_rw [← Finset.sum_add_distrib, ← mul_add]
    apply Finset.sum_congr rfl
    intro z hz
    rw [hpoint]
  change F.sum (fun z => g z * shifted z) = F.sum (fun z => g z * mult z)
  rw [hcorr P hP, hcorr Q hQ, hcount] at hs
  exact Nat.add_right_cancel hs

private theorem sum_sdiff_eq_of_sum_eq (A B : Finset X) (g : X → Nat)
    (heq : A.sum g = B.sum g) : (A \ B).sum g = (B \ A).sum g := by
  have hA : A = (A \ B) ∪ (A ∩ B) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hB : B = (B \ A) ∪ (A ∩ B) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hdA : Disjoint (A \ B) (A ∩ B) := by
    apply Finset.disjoint_left.mpr
    intro z hz hzz
    exact (Finset.mem_sdiff.mp hz).2 (Finset.mem_inter.mp hzz).2
  have hdB : Disjoint (B \ A) (A ∩ B) := by
    apply Finset.disjoint_left.mpr
    intro z hz hzz
    exact (Finset.mem_sdiff.mp hz).2 (Finset.mem_inter.mp hzz).1
  have heq' : (A \ B).sum g + (A ∩ B).sum g =
      (B \ A).sum g + (A ∩ B).sum g := by
    calc
      _ = ((A \ B) ∪ (A ∩ B)).sum g := (Finset.sum_union hdA).symm
      _ = A.sum g := by rw [← hA]
      _ = B.sum g := heq
      _ = ((B \ A) ∪ (A ∩ B)).sum g := by rw [← hB]
      _ = _ := Finset.sum_union hdB
  exact Nat.add_right_cancel heq'

theorem shift_reduces_support (F P Q : Finset X) (mult : X → Nat)
    (hP : P ⊆ F) (hQ : Q ⊆ F) (hPQ : Disjoint P Q)
    (hne : P.Nonempty) (hpos : ∀ z ∈ F, 0 < mult z) :
    ∃ (F' : Finset X) (mult' : X → Nat), F'.card < F.card ∧ F' ⊆ F ∧
      (∀ z ∈ F', 0 < mult' z) ∧
      (∀ (g : X → Nat), P.sum g = Q.sum g →
        F'.sum (fun z => g z * mult' z) = F.sum (fun z => g z * mult z)) := by
  obtain ⟨z0, hz0, hzmin⟩ := P.exists_min_image mult hne
  let d := mult z0
  let mult' : X → Nat := fun z =>
    if z ∈ P then mult z - d else if z ∈ Q then mult z + d else mult z
  let F' := F.filter (fun z => 0 < mult' z)
  refine ⟨F', mult', ?_, Finset.filter_subset _ _, ?_, ?_⟩
  · apply Finset.card_lt_card
    apply Finset.ssubset_iff_of_subset (Finset.filter_subset _ _ ) |>.mpr
    refine ⟨z0, hP hz0, ?_⟩
    simp [mult', hz0, d]
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · intro g hcount
    have hsum : F'.sum (fun z => g z * mult' z) =
        F.sum (fun z => g z * mult' z) := by
      dsimp [F']
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hp : 0 < mult' z
      · simp [hp]
      · have hz : mult' z = 0 := Nat.eq_zero_of_not_pos hp
        simp [hp, hz]
    rw [hsum]
    exact shift_sum F P Q hP hQ hPQ mult g d
      (fun z hz => hzmin z hz) hcount

private theorem card_filter_eq_sum_indicator (A : Finset (Finset X)) (x : X) :
    (A.filter (fun z => x ∈ z)).card =
      A.sum (fun z => if x ∈ z then 1 else 0) := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

private theorem sum_row_eq (F : Finset (Finset X)) (mult : Finset X → Nat) (x : X) :
    (F.filter (fun z => x ∈ z)).sum mult =
      F.sum (fun z => (if x ∈ z then 1 else 0) * mult z) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : x ∈ z <;> simp [h]

private def Exact (S : Finset X) (T : Nat) (k : X → Nat)
    (F : Finset (Finset X)) (mult : Finset X → Nat) : Prop :=
  (∀ z ∈ F, 0 < mult z) ∧ F.sum mult = T ∧
    (∀ x ∈ S, (F.filter (fun z => x ∈ z)).sum mult = k x)

theorem no_collision_of_minimal (S : Finset X) (T : Nat) (k : X → Nat)
    (U F : Finset (Finset X)) (mult : Finset X → Nat)
    (hexact : Exact S T k F mult) (hFU : F ⊆ U)
    (hminimal : ∀ (G : Finset (Finset X)) (w : Finset X → Nat),
      Exact S T k G w → G ⊆ U → F.card ≤ G.card)
    (A B : Finset (Finset X)) (hA : A ⊆ F) (hB : B ⊆ F)
    (hcard : A.card = B.card)
    (hrows : ∀ x ∈ S, (A.filter (fun z => x ∈ z)).card =
      (B.filter (fun z => x ∈ z)).card) : A = B := by
  by_contra hne
  let P := A \ B
  let Q := B \ A
  have hp : P ⊆ F := (Finset.sdiff_subset).trans hA
  have hq : Q ⊆ F := (Finset.sdiff_subset).trans hB
  have hpq : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro z hzP hzQ
    exact (Finset.mem_sdiff.mp hzP).2 (Finset.mem_sdiff.mp hzQ).1
  have hpne : P.Nonempty := by
    by_contra hn
    have hAB : A ⊆ B := by
      intro z hzA
      by_contra hzB
      exact hn ⟨z, Finset.mem_sdiff.mpr ⟨hzA, hzB⟩⟩
    exact hne (Finset.eq_of_subset_of_card_le hAB (le_of_eq hcard.symm))
  obtain ⟨G, w, hsmall, hGsub, hpos, hpres⟩ :=
    shift_reduces_support F P Q mult hp hq hpq hpne hexact.1
  have htotal : G.sum w = F.sum mult := by
    have hPQ : P.sum (fun _ => (1 : Nat)) = Q.sum (fun _ => (1 : Nat)) :=
      sum_sdiff_eq_of_sum_eq A B _ (by simpa using hcard)
    simpa only [one_mul] using hpres (fun _ => 1) hPQ
  have hrow : ∀ x ∈ S, (G.filter (fun z => x ∈ z)).sum w =
      (F.filter (fun z => x ∈ z)).sum mult := by
    intro x hx
    have hAB : A.sum (fun z => if x ∈ z then 1 else 0) =
        B.sum (fun z => if x ∈ z then 1 else 0) := by
      simpa only [← card_filter_eq_sum_indicator] using hrows x hx
    have hPQ := sum_sdiff_eq_of_sum_eq A B _ hAB
    simpa only [sum_row_eq] using hpres (fun z => if x ∈ z then 1 else 0) hPQ
  have hnew : Exact S T k G w :=
    ⟨hpos, htotal.trans hexact.2.1,
      fun x hx => (hrow x hx).trans (hexact.2.2 x hx)⟩
  exact (not_le_of_gt hsmall) (hminimal G w hnew (hGsub.trans hFU))

theorem bounds_of_minimal (S : Finset X) (T : Nat) (k : X → Nat)
    (U F : Finset (Finset X)) (mult : Finset X → Nat)
    (hexact : Exact S T k F mult) (hFU : F ⊆ U)
    (hminimal : ∀ (G : Finset (Finset X)) (w : Finset X → Nat),
      Exact S T k G w → G ⊆ U → F.card ≤ G.card) :
    ∀ h : Nat, h ≤ F.card → 2 ^ h ≤ (h+1) ^ (S.card+1) := by
  intro h hh
  obtain ⟨H, hH, hHcard⟩ := Finset.exists_subset_card_eq hh
  have hinj : Function.Injective (signature S H) := by
    intro A B heq
    apply Subtype.ext
    apply no_collision_of_minimal S T k U F mult hexact hFU hminimal A.val B.val
      (A.property.trans hH) (B.property.trans hH)
    · have hc := congrArg Fin.val (congrFun heq none)
      simpa [signature] using hc
    · intro x hx
      have hc := congrArg Fin.val (congrFun heq (some ⟨x, hx⟩))
      simpa [signature] using hc
  simpa only [hHcard] using support_bound_of_signature_inj S H hinj

theorem compress_exact (S : Finset X) (T : Nat) (k : X → Nat)
    (U : Finset (Finset X))
    (hin : ∃ (F : Finset (Finset X)) (mult : Finset X → Nat),
      F ⊆ U ∧ Exact S T k F mult) :
    ∃ (F : Finset (Finset X)) (mult : Finset X → Nat),
      F ⊆ U ∧ Exact S T k F mult ∧
      ∀ h : Nat, h ≤ F.card → 2 ^ h ≤ (h+1) ^ (S.card+1) := by
  classical
  let P : Nat → Prop := fun h => ∃ (F : Finset (Finset X)) (mult : Finset X → Nat),
    F ⊆ U ∧ Exact S T k F mult ∧ F.card = h
  have hex : ∃ h, P h := by
    obtain ⟨F, mult, hFU, hexact⟩ := hin
    exact ⟨F.card, F, mult, hFU, hexact, rfl⟩
  obtain ⟨F, mult, hFU, hexact, hcard⟩ := Nat.find_spec hex
  have hminimal : ∀ (G : Finset (Finset X)) (w : Finset X → Nat),
      Exact S T k G w → G ⊆ U → F.card ≤ G.card := by
    intro G w hG hGU
    rw [hcard]
    exact Nat.find_min' hex ⟨G, w, hGU, hG, rfl⟩
  exact ⟨F, mult, hFU, hexact,
    bounds_of_minimal S T k U F mult hexact hFU hminimal⟩

theorem compress_intervals (S : Finset X) (T : Nat) (lo hi : X → Nat)
    (F₀ : Finset (Finset X)) (mult₀ : Finset X → Nat)
    (hpos : ∀ z ∈ F₀, 0 < mult₀ z) (htotal : F₀.sum mult₀ = T)
    (hrow : ∀ x ∈ S, lo x ≤ (F₀.filter (fun z => x ∈ z)).sum mult₀ ∧
      (F₀.filter (fun z => x ∈ z)).sum mult₀ ≤ hi x) :
    ∃ (F : Finset (Finset X)) (mult : Finset X → Nat),
      F ⊆ F₀ ∧ (∀ z ∈ F, 0 < mult z) ∧ F.sum mult = T ∧
      (∀ x ∈ S, lo x ≤ (F.filter (fun z => x ∈ z)).sum mult ∧
        (F.filter (fun z => x ∈ z)).sum mult ≤ hi x) ∧
      (∀ h : Nat, h ≤ F.card → 2 ^ h ≤ (h+1) ^ (S.card+1)) := by
  obtain ⟨G, w, hGsub, hexact, hbound⟩ := compress_exact S T
    (fun x => (F₀.filter (fun z => x ∈ z)).sum mult₀) F₀
    ⟨F₀, mult₀, Finset.Subset.refl F₀, ⟨hpos, htotal, fun x hx => rfl⟩⟩
  refine ⟨G, w, hGsub, hexact.1, hexact.2.1, ?_, hbound⟩
  intro x hx
  rw [hexact.2.2 x hx]
  exact hrow x hx

end Sparse53167

namespace Sparse53167

variable {X : Type*} [Fintype X] [DecidableEq X]

private theorem slots_count_fiber (T : Nat) (S : Finset X)
    (Zs : Fin T → Finset X) (x : X) :
    ((Finset.univ : Finset (Fin T)).filter (fun t => x ∈ Zs t)).card =
      (((Finset.univ : Finset (Fin T)).image Zs).filter (fun Z => x ∈ Z)).sum
        (fun Z => ((Finset.univ : Finset (Fin T)).filter (fun t => Zs t = Z)).card) := by
  let sf : Finset (Fin T) := (Finset.univ.filter (fun t => x ∈ Zs t))
  let ff : Finset (Finset X) := ((Finset.univ : Finset (Fin T)).image Zs).filter
    (fun Z => x ∈ Z)
  have hmaps : (sf : Set (Fin T)).MapsTo Zs ff := by
    intro t ht
    have htx : x ∈ Zs t := (Finset.mem_filter.mp ht).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩, htx⟩
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  change sf.card = ff.sum (fun Z => (sf.filter (fun t => Zs t = Z)).card) at h
  rw [h]
  apply Finset.sum_congr rfl
  intro Z hZ
  apply congrArg Finset.card
  ext t
  have hxZ : x ∈ Z := (Finset.mem_filter.mp hZ).2
  simp only [sf, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact And.right
  · intro ht
    exact ⟨ht ▸ hxZ, ht⟩

theorem slots_to_sparse (S : Finset X) (T : Nat) (lo hi : X → Nat)
    (P : Finset X → Prop) (Zs : Fin T → Finset X)
    (hP : ∀ t, P (Zs t))
    (hrow : ∀ x ∈ S,
      lo x ≤ ((Finset.univ : Finset (Fin T)).filter (fun t => x ∈ Zs t)).card ∧
      ((Finset.univ : Finset (Fin T)).filter (fun t => x ∈ Zs t)).card ≤ hi x) :
    ∃ (F : Finset (Finset X)) (mult : Finset X → Nat),
      (∀ Z ∈ F, P Z ∧ 0 < mult Z) ∧ F.sum mult = T ∧
      (∀ x ∈ S, lo x ≤ (F.filter (fun Z => x ∈ Z)).sum mult ∧
        (F.filter (fun Z => x ∈ Z)).sum mult ≤ hi x) ∧
      (∀ h : Nat, h ≤ F.card → 2 ^ h ≤ (h+1) ^ (S.card+1)) := by
  let F₀ := (Finset.univ : Finset (Fin T)).image Zs
  let mult₀ : Finset X → Nat := fun Z =>
    ((Finset.univ : Finset (Fin T)).filter (fun t => Zs t = Z)).card
  have hpos : ∀ Z ∈ F₀, 0 < mult₀ Z := by
    intro Z hZ
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hZ
    exact Finset.card_pos.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, rfl⟩⟩
  have htotal : F₀.sum mult₀ = T := by
    have h := Finset.card_eq_sum_card_image Zs (Finset.univ : Finset (Fin T))
    simpa [F₀, mult₀] using h.symm
  have hcounts : ∀ x ∈ S,
      lo x ≤ (F₀.filter (fun Z => x ∈ Z)).sum mult₀ ∧
        (F₀.filter (fun Z => x ∈ Z)).sum mult₀ ≤ hi x := by
    intro x hx
    rw [← slots_count_fiber T S Zs x]
    exact hrow x hx
  obtain ⟨F, mult, hFsub, hpos', htotal', hcounts', hbound⟩ :=
    compress_intervals S T lo hi F₀ mult₀ hpos htotal hcounts
  refine ⟨F, mult, ?_, htotal', hcounts', hbound⟩
  intro Z hZ
  have hZ₀ := hFsub hZ
  obtain ⟨t, ht, hZeq⟩ := Finset.mem_image.mp hZ₀
  exact ⟨hZeq ▸ hP t, hpos' Z hZ⟩

private def sigma_fiber_equiv (F : Finset (Finset X)) (mult : Finset X → Nat)
    (z : F) :
    {p : Σ z' : F, Fin (mult z'.val) // p.1 = z} ≃ Fin (mult z.val) where
  toFun p := p.property ▸ p.val.2
  invFun i := ⟨⟨z, i⟩, rfl⟩
  left_inv p := by
    obtain ⟨⟨z', i⟩, hz⟩ := p
    cases hz
    rfl
  right_inv i := rfl

private theorem sigma_slots_card (F : Finset (Finset X)) (mult : Finset X → Nat)
    (T : Nat) (htotal : F.sum mult = T) :
    Fintype.card (Σ z : F, Fin (mult z.val)) = T := by
  simpa [Fintype.card_sigma, Finset.sum_attach] using htotal

private theorem slots_fiber_card (F : Finset (Finset X)) (mult : Finset X → Nat)
    (T : Nat) (htotal : F.sum mult = T)
    (e : Fin T ≃ (Σ z : F, Fin (mult z.val))) (z : F) :
    ((Finset.univ : Finset (Fin T)).filter (fun t => (e t).1.val = z.val)).card =
      mult z.val := by
  let D := Σ z' : F, Fin (mult z'.val)
  let fiber : {t : Fin T // (e t).1 = z} ≃ {p : D // p.1 = z} :=
    Equiv.subtypeEquiv e (by intro t; rfl)
  calc
    _ = Fintype.card {t : Fin T // (e t).1 = z} := by
      rw [Fintype.subtype_card]
      congr 1
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subtype.ext_iff]
    _ = Fintype.card {p : D // p.1 = z} := Fintype.card_congr fiber
    _ = Fintype.card (Fin (mult z.val)) := Fintype.card_congr (sigma_fiber_equiv F mult z)
    _ = mult z.val := Fintype.card_fin _

theorem sparse_to_slots (S : Finset X) (T : Nat) (lo hi : X → Nat)
    (P : Finset X → Prop) (F : Finset (Finset X)) (mult : Finset X → Nat)
    (hvalid : ∀ Z ∈ F, P Z ∧ 0 < mult Z) (htotal : F.sum mult = T)
    (hrow : ∀ x ∈ S, lo x ≤ (F.filter (fun Z => x ∈ Z)).sum mult ∧
      (F.filter (fun Z => x ∈ Z)).sum mult ≤ hi x) :
    ∃ Zs : Fin T → Finset X, (∀ t, P (Zs t)) ∧
      ∀ x ∈ S,
        lo x ≤ ((Finset.univ : Finset (Fin T)).filter (fun t => x ∈ Zs t)).card ∧
        ((Finset.univ : Finset (Fin T)).filter (fun t => x ∈ Zs t)).card ≤ hi x := by
  classical
  let e : Fin T ≃ (Σ z : F, Fin (mult z.val)) :=
    (Fintype.equivFinOfCardEq (sigma_slots_card F mult T htotal)).symm
  let Zs : Fin T → Finset X := fun t => (e t).1.val
  have hZs : (Finset.univ : Finset (Fin T)).image Zs = F := by
    ext Z
    constructor
    · intro hZ
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hZ
      exact (e t).1.property
    · intro hZ
      let zz : F := ⟨Z, hZ⟩
      let i : Fin (mult Z) := ⟨0, (hvalid Z hZ).2⟩
      refine Finset.mem_image.mpr ⟨e.symm ⟨zz, i⟩, Finset.mem_univ _, ?_⟩
      simp [Zs, e, zz]
  refine ⟨Zs, ?_, ?_⟩
  · intro t
    exact (hvalid (Zs t) (e t).1.property).1
  · intro x hx
    have hc : ((Finset.univ : Finset (Fin T)).filter (fun t => x ∈ Zs t)).card =
        (F.filter (fun Z => x ∈ Z)).sum mult := by
      rw [slots_count_fiber T S Zs x, hZs]
      apply Finset.sum_congr rfl
      intro Z hZ
      have hz : Z ∈ F := (Finset.mem_filter.mp hZ).1
      simpa only [Zs] using slots_fiber_card F mult T htotal e ⟨Z, hz⟩
    rw [hc]
    exact hrow x hx

theorem slots_iff_sparse (S : Finset X) (T : Nat) (lo hi : X → Nat)
    (P : Finset X → Prop) :
    (∃ Zs : Fin T → Finset X, (∀ t, P (Zs t)) ∧
      ∀ x ∈ S,
        lo x ≤ ((Finset.univ : Finset (Fin T)).filter (fun t => x ∈ Zs t)).card ∧
        ((Finset.univ : Finset (Fin T)).filter (fun t => x ∈ Zs t)).card ≤ hi x) ↔
    (∃ (F : Finset (Finset X)) (mult : Finset X → Nat),
      (∀ Z ∈ F, P Z ∧ 0 < mult Z) ∧ F.sum mult = T ∧
      (∀ x ∈ S, lo x ≤ (F.filter (fun Z => x ∈ Z)).sum mult ∧
        (F.filter (fun Z => x ∈ Z)).sum mult ≤ hi x) ∧
      (∀ h : Nat, h ≤ F.card → 2 ^ h ≤ (h+1) ^ (S.card+1))) := by
  constructor
  · rintro ⟨Zs, hP, hrow⟩
    exact slots_to_sparse S T lo hi P Zs hP hrow
  · rintro ⟨F, mult, hvalid, htotal, hrow, hbound⟩
    exact sparse_to_slots S T lo hi P F mult hvalid htotal hrow

end Sparse53167

namespace DervishPattern53167
open PEqualNP PEqualNP.CircuitLowerBounds

theorem ensemble_slots {n m : ℕ} (S : Finset (X n)) (want : Want n m)
    (b T : ℕ) (lo hi : X n → ℕ) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    (∃ (cs : Fin T → Circuit) (a : ∀ t, Tap n m (cs t)),
      (∀ t, valid n b (cs t)) ∧ ∀ x ∈ S,
        let k := ((Finset.univ : Finset (Fin T)).filter (fun t => hit want (cs t) (a t) x)).card
        lo x ≤ k ∧ k ≤ hi x) ↔
    (∃ zs : Fin T → Finset (X n), (∀ t, pat S b want (zs t)) ∧ ∀ x ∈ S,
       let k := ((Finset.univ : Finset (Fin T)).filter (fun t => x ∈ zs t)).card
       lo x ≤ k ∧ k ≤ hi x) := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  dsimp only
  constructor
  · rintro ⟨cs,a,valids,quota⟩
    let zs (t : Fin T) := S.filter (fun x => hit want (cs t) (a t) x)
    have fit (t : Fin T) (x : X n) (hx : x ∈ S) :
        hit want (cs t) (a t) x ↔ x ∈ zs t := by simp [zs,hx]
    refine ⟨zs,?_,?_⟩
    · intro t
      have hsub : zs t ⊆ S := Finset.filter_subset _ _
      obtain ⟨hz,w,hw,hc⟩ := Falls53167.pattern_of_valid_hit S (zs t) want (cs t) (a t)
        (valids t).1 (valids t).2.2.2 hsub (fit t)
      exact ⟨hz,w,hw,hc⟩
    · intro x hx
      have he : ((Finset.univ : Finset (Fin T)).filter (fun t => hit want (cs t) (a t) x)) =
          ((Finset.univ : Finset (Fin T)).filter (fun t => x ∈ zs t)) := by
        ext t
        simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using fit t x hx
      rw [← he]
      exact quota x hx
  · rintro ⟨zs,ps,quota⟩
    have H (t : Fin T) := ((exact_pattern S (zs t) want).mp (ps t)).2
    choose cs a val size fit using H
    refine ⟨cs,a,val,?_⟩
    intro x hx
    have he : ((Finset.univ : Finset (Fin T)).filter (fun t => hit want (cs t) (a t) x)) =
        ((Finset.univ : Finset (Fin T)).filter (fun t => x ∈ zs t)) := by
      ext t
      simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using fit t x hx
    rw [he]
    exact quota x hx
end DervishPattern53167

end PEqualNP.Outside.L_meta_53167_aux

open PEqualNP.Outside.L_meta_53167_aux PEqualNP.Outside.L_meta_53167_aux.DervishPattern53167 in
theorem PEqualNP.Outside.L_meta_53167 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n m T b : Nat) (S : Finset (Fin n → Bool))
  (want : (Fin n → Bool) → Fin m → Option Bool) (lo hi : (Fin n → Bool) → Nat),
  let X := Fin n → Bool
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let taps := fun (C : Circ) => Fin m → Fin (n+2+C.size)
  let valid := fun (C : Circ) => PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
    PEqualNP.NotBracket.notCount C ≤ b
  let hit := fun (C : Circ) (a : taps C) (x : X) => ∀ (j : Fin m) (v : Bool),
    want x j = some v → (C.wires (List.ofFn x ++ [false,true])).getD (a j).val false = v
  let label := fun (Z : Finset X) (w : X → Option (Fin m)) (x : X) (j : Fin m) =>
    if x ∈ S then if x ∈ Z then want x j else
      if w x = some j then (want x j).map Bool.not else none
    else none
  let pattern := fun (Z : Finset X) => Z ⊆ S ∧ ∃ w : X → Option (Fin m),
    (∀ x ∈ S, x ∉ Z → ∃ (j : Fin m) (v : Bool), w x = some j ∧ want x j = some v) ∧
    let reach := Nat.rec (motive := fun _ => X → Prop) (fun _ => True)
      (fun _ prev z => ∃ x y j, prev x ∧ x ≤ y ∧ y ≤ z ∧
        label Z w x j = some true ∧ label Z w y j = some false)
    ∀ z, ¬ reach (2^b) z
  let ensemble := ∃ (cs : Fin T → Circ) (a : ∀ t, taps (cs t)),
    (∀ t, valid (cs t)) ∧ ∀ x ∈ S,
      let k := ((Finset.univ : Finset (Fin T)).filter (fun t => hit (cs t) (a t) x)).card
      lo x ≤ k ∧ k ≤ hi x
  (ensemble ↔ ∃ (F : Finset (Finset X)) (mult : Finset X → Nat),
    (∀ Z ∈ F, pattern Z ∧ 0 < mult Z) ∧ F.sum mult = T ∧
    (∀ x ∈ S, let k := (F.filter (fun Z => x ∈ Z)).sum mult
              lo x ≤ k ∧ k ≤ hi x) ∧
    (∀ h : Nat, h ≤ F.card → 2^h ≤ (h+1)^(S.card+1))) ∧
  ∀ Z : Finset X, pattern Z ↔ Z ⊆ S ∧ ∃ (C : Circ) (a : taps C),
    valid C ∧ C.size ≤ b+(n+2)*S.card + m*S.card + 5*(2^b-1) ∧
    ∀ x ∈ S, (hit C a x ↔ x ∈ Z)) := by
  intro n m T b S want lo hi
  dsimp only
  refine ⟨?_,?_⟩
  · refine (ensemble_slots S want b T lo hi).trans ?_
    convert Sparse53167.slots_iff_sparse S T lo hi (pat S b want) using 1 <;>
      congr! 24 <;> first | apply Subsingleton.elim | apply Finset.filter_congr_decidable
  · intro Z
    exact exact_pattern S Z want

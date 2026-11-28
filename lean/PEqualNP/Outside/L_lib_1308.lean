import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import PEqualNP.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Chain

namespace PEqualNP.Outside.L_lib_1308.CircuitDonor

namespace Donor1196

open PEqualNP.CircuitLowerBounds
namespace AltChain1196

local instance : DecidableEq GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq

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

end AltChain1196
namespace Sort1196

structure Kit (S R X : Type) where
  Ext : S → S → Prop
  ext_refl : ∀ s, Ext s s
  ext_trans : ∀ {s t u}, Ext s t → Ext t u → Ext s u
  Read : S → R → (X → Bool) → Prop
  persist : ∀ {s t r f}, Ext s t → Read s r f → Read t r f
  cost : S → Nat
  nots : S → Nat
  emitAnd : ∀ (s : S) (a b : R) (fa fb : X → Bool),
    Read s a fa → Read s b fb →
    ∃ t c, Ext s t ∧ Read t c (fun x => fa x && fb x) ∧
      cost t ≤ cost s + 1 ∧ nots t = nots s
  emitOr : ∀ (s : S) (a b : R) (fa fb : X → Bool),
    Read s a fa → Read s b fb →
    ∃ t c, Ext s t ∧ Read t c (fun x => fa x || fb x) ∧
      cost t ≤ cost s + 1 ∧ nots t = nots s

structure Tap {S R X : Type} (K : Kit S R X) (s : S) where
  wire : R
  val : X → Bool
  read : K.Read s wire val

variable {S R X : Type} (K : Kit S R X)

def Tap.lift {s t : S} (h : K.Ext s t) (a : Tap K s) : Tap K t :=
  ⟨a.wire, a.val, K.persist h a.read⟩

theorem comparator_reverse (a b : Bool) :
    (!(a || b) || (!(a && b) && b)) = !a ∧
    (!(a || b) || (!(a && b) && a)) = !b := by
  cases a <;> cases b <;> decide

theorem reverse_first (a b : Bool) :
    (!(a || b) || (!(a && b) && b)) = !a :=
  (comparator_reverse a b).1

theorem reverse_second (a b : Bool) :
    (!(a || b) || (!(a && b) && a)) = !b :=
  (comparator_reverse a b).2

theorem compare (s : S) (a b : Tap K s) :
    ∃ t, ∃ lo : Tap K t, ∃ hi : Tap K t, K.Ext s t ∧
      lo.val = (fun x => a.val x && b.val x) ∧
      hi.val = (fun x => a.val x || b.val x) ∧
      K.cost t ≤ K.cost s + 2 ∧ K.nots t = K.nots s := by
  obtain ⟨u, wlo, hsu, hlo, hcu, hnu⟩ :=
    K.emitAnd s a.wire b.wire a.val b.val a.read b.read
  obtain ⟨t, whi, hut, hhi, hct, hnt⟩ :=
    K.emitOr u a.wire b.wire a.val b.val
      (K.persist hsu a.read) (K.persist hsu b.read)
  exact ⟨t, ⟨wlo, _, K.persist hut hlo⟩, ⟨whi, _, hhi⟩,
    K.ext_trans hsu hut, rfl, rfl, by omega, by rw [hnt, hnu]⟩

theorem inverse_compare (s : S) (a b lo' hi' : Tap K s)
    (hlo : lo'.val = fun x => !(a.val x && b.val x))
    (hhi : hi'.val = fun x => !(a.val x || b.val x)) :
    ∃ t, ∃ na : Tap K t, ∃ nb : Tap K t, K.Ext s t ∧
      na.val = (fun x => !(a.val x)) ∧
      nb.val = (fun x => !(b.val x)) ∧
      K.cost t ≤ K.cost s + 4 ∧ K.nots t = K.nots s := by
  obtain ⟨u, wab, hsu, hab, hcu, hnu⟩ :=
    K.emitAnd s lo'.wire b.wire lo'.val b.val lo'.read b.read
  obtain ⟨v, wa, huv, ha, hcv, hnv⟩ :=
    K.emitOr u hi'.wire wab hi'.val (fun x => lo'.val x && b.val x)
      (K.persist hsu hi'.read) hab
  obtain ⟨w, wba, hvw, hba, hcw, hnw⟩ :=
    K.emitAnd v lo'.wire a.wire lo'.val a.val
      (K.persist (K.ext_trans hsu huv) lo'.read)
      (K.persist (K.ext_trans hsu huv) a.read)
  obtain ⟨t, wb, hwt, hb, hct, hnt⟩ :=
    K.emitOr w hi'.wire wba hi'.val (fun x => lo'.val x && a.val x)
      (K.persist (K.ext_trans (K.ext_trans hsu huv) hvw) hi'.read) hba
  have ha' : (fun x => hi'.val x || (lo'.val x && b.val x)) =
      (fun x => !(a.val x)) := by
    funext x
    simpa only [hlo, hhi] using reverse_first (a.val x) (b.val x)
  have hb' : (fun x => hi'.val x || (lo'.val x && a.val x)) =
      (fun x => !(b.val x)) := by
    funext x
    simpa only [hlo, hhi] using reverse_second (a.val x) (b.val x)
  exact ⟨t, ⟨wa, _, K.persist (K.ext_trans hvw hwt) ha⟩, ⟨wb, _, hb⟩,
    K.ext_trans (K.ext_trans (K.ext_trans hsu huv) hvw) hwt,
    ha', hb', by omega, by rw [hnt, hnw, hnv, hnu]⟩

def neg (a : X → Bool) : X → Bool := fun x => !(a x)
def negs (fs : List (X → Bool)) : List (X → Bool) := fs.map neg

def insF (a : X → Bool) : List (X → Bool) → List (X → Bool)
  | [] => [a]
  | b :: bs => (fun x => a x || b x) :: insF (fun x => a x && b x) bs

inductive Taps (K : Kit S R X) (s : S) : List (X → Bool) → Prop where
  | nil : Taps K s []
  | cons (f : X → Bool) {fs : List (X → Bool)} (a : Tap K s)
      (ha : a.val = f) (tail : Taps K s fs) : Taps K s (f :: fs)

theorem Taps.lift {s t : S} (h : K.Ext s t) :
    {fs : List (X → Bool)} → Taps K s fs → Taps K t fs
  | [], .nil => .nil
  | _, .cons f a ha tail => .cons f (a.lift K h) ha (Taps.lift h tail)

theorem Taps.at {s : S} {fs : List (X → Bool)} (ts : Taps K s fs)
    (j : Nat) (hj : j < fs.length) :
    ∃ r : R, K.Read s r (fs.getD j (fun _ => false)) := by
  induction ts generalizing j with
  | nil => cases hj
  | cons f a ha tail ih =>
      cases j with
      | zero =>
          exact ⟨a.wire, by simpa [ha] using a.read⟩
      | succ j =>
          exact ih j (by simpa using hj)

theorem build_insert (s : S) (a : Tap K s)
    (fs : List (X → Bool)) (input : Taps K s fs) :
    ∃ t, K.Ext s t ∧ Taps K t (insF a.val fs) ∧
      K.cost t ≤ K.cost s + 2 * fs.length ∧ K.nots t = K.nots s ∧
      (∀ u, K.Ext t u → Taps K u (negs (insF a.val fs)) →
        ∃ v, K.Ext u v ∧ Taps K v (neg a.val :: negs fs) ∧
          K.cost v ≤ K.cost u + 4 * fs.length ∧ K.nots v = K.nots u) := by
  induction fs generalizing s a with
  | nil =>
      refine ⟨s, K.ext_refl s, Taps.cons a.val a rfl Taps.nil, ?_, rfl, ?_⟩
      · simp
      · intro u hsu flipped
        exact ⟨u, K.ext_refl u, flipped, by simp, rfl⟩
  | cons f fs ih =>
      cases input with
      | cons _ b hb tail =>
          obtain ⟨t, lo, hi, hst, hlo, hhi, hct, hnt⟩ := compare K s a b
          obtain ⟨v, htv, out, hcv, hnv, undo⟩ :=
            ih t lo (tail.lift K hst)
          refine ⟨v, K.ext_trans hst htv, ?_, ?_, ?_, ?_⟩
          · simpa only [insF, ← hb, ← hlo, ← hhi] using
              (Taps.cons hi.val (hi.lift K htv) rfl out)
          · simp only [List.length_cons]
            omega
          · rw [hnv, hnt]
          · intro u hvu flipped
            have flipped' : Taps K u (neg hi.val :: negs (insF lo.val fs)) := by
              simpa only [insF, negs, List.map_cons, ← hb, ← hlo, ← hhi] using flipped
            cases flipped' with
            | cons _ nhi hni flippedTail =>
                obtain ⟨w, huw, flippedBack, hcw, hnw⟩ :=
                  undo u hvu flippedTail
                cases flippedBack with
                | cons _ nlo hnlo nrest =>
                    let hsw : K.Ext s w := K.ext_trans hst
                      (K.ext_trans htv (K.ext_trans hvu huw))
                    have hlow : nlo.val = fun x => !(a.val x && b.val x) := by
                      calc
                        nlo.val = neg lo.val := hnlo
                        _ = neg (fun x => a.val x && b.val x) := congrArg neg hlo
                        _ = (fun x => !(a.val x && b.val x)) := rfl
                    have hhigh : (nhi.lift K huw).val =
                        (fun x => !(a.val x || b.val x)) := by
                      calc
                        (nhi.lift K huw).val = nhi.val := rfl
                        _ = neg hi.val := hni
                        _ = neg (fun x => a.val x || b.val x) := congrArg neg hhi
                        _ = (fun x => !(a.val x || b.val x)) := rfl
                    obtain ⟨z, na, nb, hwz, hna, hnb, hcz, hnz⟩ :=
                      inverse_compare K w (a.lift K hsw) (b.lift K hsw)
                        nlo (nhi.lift K huw) hlow hhigh
                    refine ⟨z, K.ext_trans huw hwz, ?_, ?_, ?_⟩
                    · have ha' : na.val = neg a.val := hna
                      have hb' : nb.val = neg b.val := hnb
                      simpa only [negs, List.map_cons, ← hb] using
                        (Taps.cons (neg a.val) na ha'
                          (Taps.cons (neg b.val) nb hb' (nrest.lift K hwz)))
                    · simp only [List.length_cons]
                      omega
                    · rw [hnz, hnw]

def sortF : List (X → Bool) → List (X → Bool)
  | [] => []
  | a :: fs => insF a (sortF fs)

private theorem insF_length (a : X → Bool) (fs : List (X → Bool)) :
    (insF a fs).length = fs.length + 1 := by
  induction fs generalizing a with
  | nil => rfl
  | cons f fs ih => simp [insF, ih, Nat.add_comm]

private theorem sortF_length (fs : List (X → Bool)) :
    (sortF fs).length = fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [sortF, insF_length, ih]

private theorem forward_budget (k : Nat) :
    k * (k-1) + 2*k ≤ (k+1)*k := by
  cases k with
  | zero => simp
  | succ k => simp only [Nat.succ_sub_one]; nlinarith

private theorem reverse_budget (k : Nat) :
    4*k + 2*(k*(k-1)) ≤ 2*((k+1)*k) := by
  cases k with
  | zero => simp
  | succ k => simp only [Nat.succ_sub_one]; nlinarith

theorem build_sort (s : S) (fs : List (X → Bool))
    (input : Taps K s fs) :
    ∃ t, K.Ext s t ∧ Taps K t (sortF fs) ∧
      K.cost t ≤ K.cost s + fs.length * (fs.length-1) ∧ K.nots t = K.nots s ∧
      (∀ u, K.Ext t u → Taps K u (negs (sortF fs)) →
        ∃ v, K.Ext u v ∧ Taps K v (negs fs) ∧
          K.cost v ≤ K.cost u + 2*(fs.length * (fs.length-1)) ∧
          K.nots v = K.nots u) := by
  induction fs generalizing s with
  | nil =>
      refine ⟨s, K.ext_refl s, Taps.nil, ?_, rfl, ?_⟩
      · simp
      · intro u _ inv
        exact ⟨u, K.ext_refl u, inv, by simp, rfl⟩
  | cons f fs ih =>
      cases input with
      | cons _ a ha tail =>
          obtain ⟨t, hst, sorted, hct, hnt, undoTail⟩ := ih s tail
          obtain ⟨v, htv, output, hcv, hnv, undoInsert⟩ :=
            build_insert K t (a.lift K hst) (sortF fs) sorted
          refine ⟨v, K.ext_trans hst htv, ?_, ?_, ?_, ?_⟩
          · change Taps K v (insF a.val (sortF fs)) at output
            simpa only [sortF, ← ha] using output
          · have hlen := sortF_length fs
            simp only [List.length_cons, Nat.succ_sub_one, hlen] at *
            have hbudget := forward_budget fs.length
            omega
          · rw [hnv, hnt]
          · intro u hvu flipped
            have flipped' : Taps K u (negs (insF a.val (sortF fs))) := by
              simpa only [sortF, ← ha] using flipped
            obtain ⟨w, huw, recovered, hcw, hnw⟩ := undoInsert u hvu flipped'
            cases recovered with
            | cons _ na hna nrest =>
                obtain ⟨z, hwz, original, hcz, hnz⟩ :=
                  undoTail w (K.ext_trans htv (K.ext_trans hvu huw)) nrest
                refine ⟨z, K.ext_trans huw hwz, ?_, ?_, ?_⟩
                · simpa only [negs, List.map_cons, ← ha] using
                    (Taps.cons (neg a.val) (na.lift K hwz) hna original)
                · simp only [List.length_cons] at *
                  simp only [Nat.succ_sub_one, sortF_length] at *
                  have hbudget := reverse_budget fs.length
                  omega
                · rw [hnz, hnw]

def ins (a : Bool) : List Bool → List Bool
  | [] => [a]
  | b :: bs => (a || b) :: ins (a && b) bs

def sort : List Bool → List Bool
  | [] => []
  | b :: bs => ins b (sort bs)

def unary (m k : Nat) : List Bool := List.replicate m true ++ List.replicate (k-m) false

private theorem ins_false (xs : List Bool) : ins false xs = xs ++ [false] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ins, ih]

private theorem ins_true_falses (k : Nat) :
    ins true (List.replicate k false) = true :: List.replicate k false := by
  cases k with
  | zero => rfl
  | succ k =>
      simp only [List.replicate_succ, ins, Bool.true_or, Bool.true_and]
      rw [ins_false]
      change true :: (List.replicate k false ++ List.replicate 1 false) =
        true :: List.replicate (k+1) false
      rw [List.replicate_add]

private theorem ins_true_unary (m k : Nat) (hm : m ≤ k) :
    ins true (unary m k) = unary (m+1) (k+1) := by
  induction m generalizing k with
  | zero =>
      simpa [unary] using ins_true_falses k
  | succ m ih =>
      cases k with
      | zero => omega
      | succ k =>
          have hmk : m ≤ k := by omega
          simpa [unary, ins, List.replicate_succ, Nat.succ_sub_succ_eq_sub] using
            congrArg (List.cons true) (ih k hmk)

private theorem unary_length (m k : Nat) (hm : m ≤ k) :
    (unary m k).length = k := by simp [unary]; omega

private theorem ins_length (a : Bool) (xs : List Bool) :
    (ins a xs).length = xs.length + 1 := by
  induction xs generalizing a with
  | nil => rfl
  | cons b xs ih => simp [ins, ih, Nat.add_comm, Nat.add_left_comm]

private theorem sort_length (xs : List Bool) : (sort xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [sort, ins_length, ih]

theorem sort_unary (xs : List Bool) :
    sort xs = unary (xs.count true) xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      have hm : xs.count true ≤ xs.length := List.count_le_length
      cases b with
      | false =>
          have hsub : xs.length + 1 - xs.count true =
            (xs.length - xs.count true) + 1 := by omega
          simp [sort, ih, unary, ins_false, hsub,
            List.replicate_add, List.append_assoc]
      | true =>
          simpa [sort, ih, List.count_cons, Nat.add_comm] using
            (ins_true_unary (xs.count true) xs.length hm)

theorem sort_threshold (xs : List Bool) (j : Nat) (hj : j < xs.length) :
    (sort xs).getD j false = decide (j < xs.count true) := by
  rw [sort_unary]
  have hm : xs.count true ≤ xs.length := List.count_le_length
  by_cases h : j < xs.count true
  · simp [unary, List.getElem?_append, h]
  · have hj' : j - xs.count true < xs.length - xs.count true := by omega
    simp [unary, List.getElem?_append, h, hj']

private theorem insF_semantics (a : X → Bool) (fs : List (X → Bool)) (x : X) :
    (insF a fs).map (fun f => f x) = ins (a x) (fs.map (fun f => f x)) := by
  induction fs generalizing a with
  | nil => rfl
  | cons b bs ih => simp [insF, ins, ih]

private theorem sortF_semantics (fs : List (X → Bool)) (x : X) :
    (sortF fs).map (fun f => f x) = sort (fs.map (fun f => f x)) := by
  induction fs with
  | nil => rfl
  | cons a fs ih => simp [sortF, sort, insF_semantics, ih]

theorem network_threshold (fs : List (X → Bool)) (x : X) (j : Nat)
    (hj : j < fs.length) :
    ((sortF fs).map (fun f => f x)).getD j false =
      decide (j < (fs.map (fun f => f x)).count true) := by
  rw [sortF_semantics]
  exact sort_threshold _ j (by simpa using hj)

end Sort1196

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

noncomputable def sortKit : Sort1196.Kit (Build w) Nat X where
  Ext := Ext
  ext_refl s := List.prefix_rfl
  ext_trans a b := a.trans b
  Read := Read input
  persist := read_persist hinput
  cost := cost
  nots := nots
  emitAnd _ _ _ _ _ := emitAnd hinput
  emitOr _ _ _ _ _ := emitOr hinput

end

end Build
end DervishBuild1196

namespace DervishWire1196

open DervishBuild1196.Build
open DervishBuild1196 (Build)

abbrev Z (k : Nat) := Fin k → Fin 3 → Bool

def raw {k : Nat} (z : Z k) : List Bool := (List.ofFn (fun i => List.ofFn (z i))).flatten

def input {k : Nat} (z : Z k) : List Bool := raw z ++ [false,true]

theorem raw_length {k : Nat} (z : Z k) : (raw z).length = 3*k := by
  simp [raw, List.length_flatten, List.map_ofFn, Function.comp_def, Nat.mul_comm]

theorem input_length {k : Nat} (z : Z k) : (input z).length = 3*k+2 := by
  simp [input,raw_length]

private theorem flat_getD {α : Type*} {n m : Nat} (f : Fin n → List α)
    (hlen : ∀ j, (f j).length = m) (j i : Nat) (hj : j < n) (hi : i < m)
    (d : α) : (List.ofFn f).flatten.getD (m*j+i) d = (f ⟨j,hj⟩).getD i d := by
  have hl : ∀ row ∈ List.ofFn f, row.length = m :=
    List.forall_mem_ofFn_iff.mpr hlen
  have hu : ∀ (rows : List (List α)) (hrows : ∀ row ∈ rows, row.length = m)
      (j i : Nat), i < m → rows.flatten.getD (m*j+i) d = (rows.getD j []).getD i d := by
    intro rows hrows j i hi
    induction rows generalizing j with
    | nil => simp
    | cons row rows ih =>
      obtain ⟨hr, hrs⟩ := List.forall_mem_cons.mp hrows
      cases j with
      | zero =>
        simpa only [List.flatten_cons, Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] using
          getD_append_left (by omega : i < row.length) d
      | succ j =>
        simp only [List.flatten_cons, Nat.mul_succ]
        rw [show m*j+m+i = row.length+(m*j+i) by omega,
          List.getD_append_right _ _ _ _ (by omega : row.length ≤ row.length+(m*j+i))]
        simpa only [Nat.add_sub_cancel_left, List.getD_cons_succ] using ih hrs j
  rw [hu _ hl _ _ hi]
  simp [List.getD_eq_getElem?_getD, hj]

theorem input_at {k : Nat} (z : Z k) (i : Fin k) (j : Fin 3) :
    (input z).getD (3*i.val+j.val) false = z i j := by
  have hb : 3*i.val+j.val < 3*k := by omega
  rw [input, getD_append_left (by rw [raw_length]; exact hb), raw]
  rw [flat_getD (fun t => List.ofFn (z t)) (by intro t; simp) i.val j.val i.isLt j.isLt]
  fin_cases j <;> simp [List.getD_eq_getElem?_getD]

theorem input_zero {k : Nat} (z : Z k) : (input z).getD (3*k) false = false := by
  rw [input, ← raw_length z, List.getD_append_right _ _ _ _ (Nat.le_refl _)]
  simp

theorem input_one {k : Nat} (z : Z k) : (input z).getD (3*k+1) false = true := by
  rw [input, ← raw_length z, List.getD_append_right _ _ _ _ (by omega)]
  simp

variable {S R X : Type}

theorem taps_of_indexed (K : Sort1196.Kit S R X) {s : S} (fs : List (X → Bool))
    (h : ∀ j < fs.length, ∃ r, K.Read s r (fs.getD j (fun _ => false))) :
    Sort1196.Taps K s fs := by
  induction fs with
  | nil => exact .nil
  | cons f fs ih =>
    obtain ⟨r,hr⟩ := h 0 (by simp)
    exact .cons f ⟨r,f,hr⟩ rfl (ih (fun j hj => h (j+1) (by simpa using hj)))

def bits {k : Nat} : List (Z k → Bool) := List.ofFn (fun i : Fin k => fun z => z i 1)

theorem input_taps (k : Nat) (s : Build (3*k+2)) :
    Sort1196.Taps (sortKit (X := Z k) (input := input) input_length) s (bits (k := k)) := by
  apply taps_of_indexed
  intro j hj
  have h : j < k := by simpa [bits] using hj
  let i : Fin k := ⟨j,h⟩
  refine ⟨3*j+1,?_⟩
  change Read input s (3*j+1) _
  have hr := read_input (input := input) input_length s (3*j+1) (by omega)
  have hf : (bits (k := k)).getD j (fun _ => false) = fun z => z i 1 := by
    simp [bits,List.getD_eq_getElem?_getD,h,i]
  rw [hf]
  exact ⟨hr.1, fun z => (hr.2 z).trans (input_at z i 1)⟩

end DervishWire1196

namespace Sort1196

variable {S R X : Type}

abbrev weight (fs : List (X → Bool)) (x : X) : Nat := (fs.map (fun f => f x)).count true

theorem weight_bound (fs : List (X → Bool)) (x : X) : weight fs x ≤ fs.length :=
  (List.count_le_length).trans (by simp)

theorem get_threshold (fs : List (X → Bool)) (j : Nat) (h : j < fs.length) :
    (sortF fs).getD j (fun _ => false) = fun x => decide (j < weight fs x) := by
  funext x
  have e := network_threshold fs x j h
  have hm : ((sortF fs).map (fun f => f x)).getD j
      ((fun f : X → Bool => f x) (fun _ => false)) =
          (sortF fs).getD j (fun _ => false) x := List.getD_map ..
  exact hm.symm.trans e

theorem threshold_taps (K : Kit S R X) {s : S} {fs : List (X → Bool)}
    (default : R) (ht : Taps K s (sortF fs)) : ∃ tap : Nat → R,
      ∀ j < fs.length, K.Read s (tap j) (fun x => decide (j < weight fs x)) := by
  classical
  have live : ∀ j < fs.length, ∃ r, K.Read s r (fun x => decide (j < weight fs x)) := by
    intro j h
    obtain ⟨r,hr⟩ := Taps.at K ht j (by rw [sortF_length]; exact h)
    exact ⟨r, get_threshold fs j h ▸ hr⟩
  refine ⟨fun j => if h : j < fs.length then (live j h).choose else default, ?_⟩
  intro j h
  simpa only [dif_pos h] using (live j h).choose_spec

end Sort1196

namespace Upper1196Functional

abbrev Z (k : Nat) := Fin k → Fin 3 → Bool
abbrev W (k : Nat) := Fin k → Fin 3 → Bool → Bool

def Valid {k : Nat} (z : Z k) : Prop := ∀ i,
  ¬ (z i 0 = true ∧ z i 1 = true ∧ z i 2 = true)

def Solves {k : Nat} (z : Z k) (w : W k) : Prop :=
  (∀ i j, (w i j false || w i j true) = z i j ∧
    ¬ (w i j false = true ∧ w i j true = true)) ∧
  (∀ i c, ¬ (w i 0 false = true ∧ w i 1 c = true) ∧
          ¬ (w i 0 true = true ∧ w i 2 c = true))

def recovered {k : Nat} (z : Z k) (u : Fin k → Bool) : W k := fun i j c =>
  if j = 0 then (if c then z i 0 && z i 1 else z i 0 && u i)
  else if j = 1 then (if c then z i 1 else false)
  else (if c then false else z i 2)

def conflict {k : Nat} (z : Z k) : Fin k → Bool := fun i =>
  (z i 0 && z i 1) && z i 2

private theorem flip_cover (a b : Bool) :
    ((a && (!b)) || (a && b)) = a ∧
    ¬ ((a && (!b)) = true ∧ (a && b) = true) := by
  cases a <;> cases b <;> decide

theorem recovered_solves {k : Nat} (z : Z k) (u : Fin k → Bool)
    (hu : ∀ i, u i = !z i 1) (hv : Valid z) : Solves z (recovered z u) := by
  constructor
  · intro i j
    have hj : j = (0 : Fin 3) ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
    rcases hj with rfl | rfl | rfl
    · simpa [recovered, hu i] using flip_cover (z i 0) (z i 1)
    · simp [recovered]
    · simp [recovered, show (2 : Fin 3) ≠ 0 by decide,
        show (2 : Fin 3) ≠ 1 by decide]
  · intro i c
    have h := hv i
    cases hz0 : z i 0 <;> cases hz1 : z i 1 <;> cases hz2 : z i 2 <;>
      cases c <;> simp_all [recovered, Valid, hu i]

theorem conflict_iff {k : Nat} (z : Z k) :
    (∃ i, conflict z i = true) ↔ ¬ Valid z := by
  constructor
  · rintro ⟨i, hi⟩ h
    have hh : z i 0 = true ∧ z i 1 = true ∧ z i 2 = true := by
      simpa [conflict, Bool.and_eq_true, and_assoc] using hi
    exact h i hh
  · intro h
    unfold Valid at h
    push_neg at h
    obtain ⟨i, h0, h1, h2⟩ := h
    exact ⟨i, by simp [conflict, h0, h1, h2]⟩

theorem size_account (k m : Nat) (h : m ≤ 3*k^2 + 9*k) :
    m + 4*k ≤ 3*k^2 + 13*k := by omega

theorem empty_case : (∀ z : Z 0, Valid z) ∧
    (∀ z : Z 0, Solves z (recovered z (fun i => Fin.elim0 i))) := by
  constructor
  · intro z i; exact Fin.elim0 i
  · intro z; exact recovered_solves z (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

end Upper1196Functional

namespace DervishWire1196

open DervishBuild1196 (Build)
open DervishBuild1196.Build

variable {k : Nat}

theorem read_bit (s : Build (3*k+2)) (i : Fin k) (j : Fin 3) :
    Read input s (3*i.val+j.val) (fun z => z i j) := by
  have h := read_input (input := input) input_length s (3*i.val+j.val) (by omega)
  exact ⟨h.1,fun z => (h.2 z).trans (input_at z i j)⟩

theorem read_false (s : Build (3*k+2)) : Read (X := Z k) input s (3*k) (fun _ => false) := by
  have h := read_input (input := input) input_length s (3*k) (by omega)
  exact ⟨h.1,fun z => (h.2 z).trans (input_zero z)⟩

private def badUpTo (m : Nat) (z : Z k) : Bool :=
  decide (∃ j : Fin k, j.val < m ∧ Upper1196Functional.conflict z j = true)

private theorem bad_succ {m : Nat} (h : m < k) (z : Z k) :
    (badUpTo m z || Upper1196Functional.conflict z ⟨m,h⟩) = badUpTo (m+1) z := by
  apply Bool.eq_iff_iff.mpr
  simp only [badUpTo, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (⟨j,hj,hc⟩ | ha)
    · exact ⟨j, by omega, hc⟩
    · exact ⟨⟨m,h⟩, by simp, ha⟩
  · rintro ⟨j,hj,hc⟩
    by_cases hlt : j.val < m
    · exact Or.inl ⟨j,hlt,hc⟩
    · have eq : j = ⟨m,h⟩ := Fin.ext (by change j.val = m; omega)
      exact Or.inr (by simpa only [eq] using hc)

private theorem read_congr {s : Build (3*k+2)} {i : Nat} {f g : Z k → Bool}
    (h : Read input s i f) (eq : ∀ z, f z = g z) : Read input s i g :=
  ⟨h.1, fun z => (h.2 z).trans (eq z)⟩

def invalid (z : Z k) : Bool := badUpTo k z

theorem invalid_spec (z : Z k) : invalid z = true ↔ ¬ Upper1196Functional.Valid z := by
  simpa only [invalid, badUpTo, decide_eq_true_eq, Fin.isLt, true_and] using
    Upper1196Functional.conflict_iff z

theorem recover_wires (s : Build (3*k+2)) (nb : Fin k → Nat)
    (hn : ∀ i, Read input s (nb i) (fun z => !(z i 1))) :
    ∃ (t : Build (3*k+2)) (out : Nat) (tap : Fin k → Fin 3 → Bool → Nat),
      Ext s t ∧ t.cost ≤ s.cost+4*k ∧ t.nots = s.nots ∧
      Read (input (k := k)) t out invalid ∧
      ∀ i j b, Read input t (tap i j b)
        (fun z => Upper1196Functional.recovered z (fun h => !(z h 1)) i j b) := by
  have go (m : Nat) (hm : m ≤ k) :
      ∃ (t : Build (3*k+2)) (out : Nat) (lo hi : Fin k → Nat),
        Ext s t ∧ t.cost ≤ s.cost+4*m ∧ t.nots = s.nots ∧
        Read (input (k := k)) t out (badUpTo m) ∧ ∀ i : Fin k, i.val < m →
          Read input t (lo i) (fun z => z i 0 && !(z i 1)) ∧
          Read input t (hi i) (fun z => z i 0 && z i 1) := by
    induction m with
    | zero =>
      refine ⟨s,3*k,fun _ => 0,fun _ => 0,List.prefix_rfl,by simp,rfl,?_,?_⟩
      · exact read_congr (read_false s) (by intro z; simp [badUpTo])
      · intro i h; omega
    | succ m ih =>
      obtain ⟨t,out,lo,hi,E,C,N,R,V⟩ := ih (by omega)
      let i : Fin k := ⟨m,by omega⟩
      obtain ⟨t₁,l,E₁,L,C₁,N₁⟩ := emitAnd input_length (read_bit t i 0)
        (read_persist input_length E (hn i))
      obtain ⟨t₂,h,E₂,H,C₂,N₂⟩ := emitAnd input_length (read_bit t₁ i 0) (read_bit t₁ i 1)
      obtain ⟨t₃,hit,E₃,Hit,C₃,N₃⟩ := emitAnd input_length H (read_bit t₂ i 2)
      have E₀ := E₁.trans (E₂.trans E₃)
      obtain ⟨t₄,out',E₄,OR,C₄,N₄⟩ := emitOr input_length (read_persist input_length E₀ R) Hit
      refine ⟨t₄,out',Function.update lo i l,Function.update hi i h,E.trans (E₀.trans E₄),
        by omega, by rw [N₄,N₃,N₂,N₁,N],?_,?_⟩
      · exact read_congr OR (bad_succ (by omega))
      · intro j hj
        by_cases e : j = i
        · subst j
          simpa only [Function.update_self] using And.intro
            (read_persist input_length (E₂.trans (E₃.trans E₄)) L)
            (read_persist input_length (E₃.trans E₄) H)
        · have hv : j.val < m := by
            have hne : j.val ≠ m := fun eq => e (Fin.ext eq)
            omega
          simpa only [Function.update_of_ne e] using And.intro
            (read_persist input_length (E₀.trans E₄) (V j hv).1)
            (read_persist input_length (E₀.trans E₄) (V j hv).2)
  obtain ⟨t,out,lo,hi,E,C,N,R,V⟩ := go k (le_refl k)
  let tap : Fin k → Fin 3 → Bool → Nat := fun i j b =>
    if j = 0 then (if b then hi i else lo i)
    else if j = 1 then (if b then 3*i.val+1 else 3*k)
    else (if b then 3*k else 3*i.val+2)
  refine ⟨t,out,tap,E,C,N,R,?_⟩
  intro i j b
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  fin_cases j <;> cases b <;>
    simp only [tap, Upper1196Functional.recovered, h10,h20,h21, if_true,if_false,
      Bool.false_eq_true]
  · exact (V i i.isLt).1
  · exact (V i i.isLt).2
  · exact read_false t
  · exact read_bit t i 1
  · exact read_bit t i 2
  · exact read_false t

end DervishWire1196

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

namespace Sort1196

variable {X : Type}

theorem sorted_length (fs : List (X → Bool)) : (sortF fs).length = fs.length := sortF_length fs

theorem negs_getD (fs : List (X → Bool)) (j : Nat) (hj : j < fs.length) :
    (negs fs).getD j (fun _ => false) = neg (fs.getD j (fun _ => false)) := by
  simp [negs,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]

end Sort1196

namespace DervishWire1196

open DervishBuild1196 (Build)
open DervishBuild1196.Build

theorem inverted_bits (k r : Nat) (hk : k < 2^r) :
    ∃ (t : Build (3*k+2)) (nb : Fin k → Nat),
      t.cost ≤ 3*k^2+k ∧ t.nots ≤ r ∧
      ∀ i, Read input t (nb i) (fun z => !(z i 1)) := by
  classical
  let s := Build.empty (3*k+2)
  let K := sortKit (input := input (k:=k)) input_length
  let fs : List (Z k → Bool) := bits
  have fl : fs.length = k := List.length_ofFn
  obtain ⟨t,_,ts,tc,tn,res⟩ := Sort1196.build_sort K s fs (input_taps k s)
  obtain ⟨rt,hrt⟩ := Sort1196.threshold_taps K 0 ts
  have bm : ∀ z, Sort1196.weight fs z ≤ k := fun z => (Sort1196.weight_bound fs z).trans_eq fl
  have hrt' : ∀ j < k, Read input t (rt j) (fun z => Unary1196Fold.thresh (Sort1196.weight fs z) j) := by
    intro j h
    exact hrt j (by simpa only [fl] using h)
  obtain ⟨u,it,E,uc,un,inv⟩ := Unary1196Fold.invert input_length r k hk
    (Sort1196.weight fs) bm t (3*k) (read_false t) rt hrt'
  have uit : Sort1196.Taps K u (Sort1196.negs (Sort1196.sortF fs)) := by
    apply taps_of_indexed
    intro j hj
    have hs : j < fs.length := by
      simpa [Sort1196.negs,Sort1196.sorted_length] using hj
    have hss : j < (Sort1196.sortF fs).length := by rw [Sort1196.sorted_length]; exact hs
    refine ⟨it j,?_⟩
    rw [Sort1196.negs_getD _ _ hss, Sort1196.get_threshold fs j hs]
    exact inv j (by simpa only [fl] using hs)
  obtain ⟨v,_,vs,vc,vn⟩ := res u E uit
  have each : ∀ i : Fin k, ∃ a : Nat, Read input v a (fun z => !(z i 1)) := by
    intro i
    have hi : i.val < fs.length := by rw [fl]; exact i.isLt
    obtain ⟨a,ha⟩ := Sort1196.Taps.at K vs i.val (by simpa [Sort1196.negs] using hi)
    change Read input v a _ at ha
    rw [Sort1196.negs_getD _ _ hi] at ha
    have sel : fs.getD i.val (fun _ => false) = fun z => z i 1 := by
      simp [fs,bits,List.getD_eq_getElem?_getD,i.isLt]
    rw [sel] at ha
    exact ⟨a,ha⟩
  choose nb hn using each
  change t.cost ≤ s.cost + fs.length*(fs.length-1) at tc
  change t.nots = s.nots at tn
  change v.cost ≤ u.cost + 2*(fs.length*(fs.length-1)) at vc
  change v.nots = u.nots at vn
  rw [fl] at tc vc
  have sc : s.cost=0 := rfl
  have sn : s.nots=0 := rfl
  have costs := Upper1196Unary.sorting_unsorting_budget k
  have eq : 3*k*(k-1) = 3*(k*(k-1)) := by rw [Nat.mul_assoc]
  rw [eq] at costs
  exact ⟨v,nb, by omega, by omega, hn⟩

end DervishWire1196

end Donor1196
namespace Inverter1270
open PEqualNP.Outside.L_lib_1308.CircuitDonor.Donor1196
open DervishBuild1196 DervishBuild1196.Build Sort1196

variable {X : Type} {w k b : Nat}
variable (input : X → List Bool) (hlen : ∀ x, (input x).length = w)

theorem invert_reads (hk : k < 2^b) (s : Build w)
    (fs : List (X → Bool)) (fl : fs.length = k)
    (vfs : Sort1196.Taps (sortKit (input := input) hlen) s fs)
    (zero : Nat) (vz : Read input s zero (fun _ => false)) :
    ∃ t : Build w, ∃ negtap : Nat → Nat,
      Ext s t ∧ t.cost ≤ s.cost + 3*(k*(k-1))+4*k ∧ t.nots ≤ s.nots+b ∧
      ∀ j, j<k → Read input t (negtap j) (Sort1196.neg (fs.getD j (fun _ => false))) := by
  classical
  let K := sortKit (input := input) hlen
  obtain ⟨t,Et,ts,tc,tn,res⟩ := Sort1196.build_sort K s fs vfs
  obtain ⟨rt,hrt⟩ := Sort1196.threshold_taps K 0 ts
  have bm : ∀ x, Sort1196.weight fs x ≤ k := fun x => (Sort1196.weight_bound fs x).trans_eq fl
  have hrt' : ∀ j < k, Read input t (rt j)
      (fun x => Unary1196Fold.thresh (Sort1196.weight fs x) j) := by
    intro j hj
    exact hrt j (by simpa only [fl] using hj)
  obtain ⟨u,it,Eu,uc,un,vi⟩ := Unary1196Fold.invert hlen b k hk
    (Sort1196.weight fs) bm t zero (read_persist hlen Et vz) rt hrt'
  have uit : Sort1196.Taps K u (Sort1196.negs (Sort1196.sortF fs)) := by
    apply DervishWire1196.taps_of_indexed
    intro j hj
    have hs : j < fs.length := by
      simpa [Sort1196.negs,Sort1196.sorted_length] using hj
    have hss : j < (Sort1196.sortF fs).length := by rw [Sort1196.sorted_length]; exact hs
    refine ⟨it j,?_⟩
    rw [Sort1196.negs_getD _ _ hss, Sort1196.get_threshold fs j hs]
    exact vi j (by simpa only [fl] using hs)
  obtain ⟨v,Ev,vs,vc,vn⟩ := res u Eu uit
  have each : ∀ j < k, ∃ a : Nat,
      Read input v a (Sort1196.neg (fs.getD j (fun _ => false))) := by
    intro j hj
    obtain ⟨a,ha⟩ := Sort1196.Taps.at K vs j (by simpa [Sort1196.negs,fl] using hj)
    rw [Sort1196.negs_getD fs j (fl ▸ hj)] at ha
    exact ⟨a,ha⟩
  let negtap : Nat → Nat := fun j => if hj : j<k then Classical.choose (each j hj) else zero
  have hv : ∀ j, j<k → Read input v (negtap j)
      (Sort1196.neg (fs.getD j (fun _ => false))) := by
    intro j hj
    simpa [negtap,hj] using (Classical.choose_spec (each j hj))
  refine ⟨v,negtap,Et.trans (Eu.trans Ev),?_,?_,hv⟩
  · change t.cost ≤ s.cost + fs.length*(fs.length-1) at tc
    change v.cost ≤ u.cost + 2*(fs.length*(fs.length-1)) at vc
    rw [fl] at tc vc
    omega
  · change t.nots = s.nots at tn
    change v.nots = u.nots at vn
    omega

end Inverter1270
namespace Wiring1270
open PEqualNP.Outside.L_lib_1308.CircuitDonor.Donor1196
open DervishBuild1196 DervishBuild1196.Build Sort1196

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

theorem good_and {s : Build (n+2)} {f g}
    (hf : good s f) (hg : good s g) :
    ∃ t : Build (n+2), Ext s t ∧ t.nots = s.nots ∧
      good t (fun x => f x && g x) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  obtain ⟨t,c,E,V,_,N⟩ := emitAnd input_len ha hb
  exact ⟨t,E,N,⟨c,V⟩⟩

theorem good_or {s : Build (n+2)} {f g}
    (hf : good s f) (hg : good s g) :
    ∃ t : Build (n+2), Ext s t ∧ t.nots = s.nots ∧
      good t (fun x => f x || g x) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  obtain ⟨t,c,E,V,_,N⟩ := emitOr input_len ha hb
  exact ⟨t,E,N,⟨c,V⟩⟩

def conj (y x : Finset (Fin n)) : Bool := decide (y ⊆ x)
def disj (ys : Finset (Finset (Fin n))) (x : Finset (Fin n)) : Bool :=
  decide (∃ y ∈ ys, y ⊆ x)

theorem build_conj (s : Build (n+2)) (y : Finset (Fin n)) :
    ∃ t : Build (n+2), Ext s t ∧ t.nots = s.nots ∧ good t (conj y) := by
  classical
  induction y using Finset.induction_on generalizing s with
  | empty =>
      refine ⟨s,List.prefix_rfl,rfl,?_⟩
      convert good_one s using 1
      funext x
      simp [conj]
  | @insert j y hj ih =>
      obtain ⟨u,E,N,V⟩ := ih s
      obtain ⟨t,Et,Nt,Vt⟩ := good_and (good_bit u j) V
      refine ⟨t,E.trans Et,by omega,?_⟩
      convert Vt using 1
      funext x
      simp [conj, Finset.insert_subset_iff]

theorem build_disj (s : Build (n+2)) (ys : Finset (Finset (Fin n))) :
    ∃ t : Build (n+2), Ext s t ∧ t.nots = s.nots ∧ good t (disj ys) := by
  classical
  induction ys using Finset.induction_on generalizing s with
  | empty =>
      refine ⟨s,List.prefix_rfl,rfl,?_⟩
      convert good_zero s using 1
      funext x
      simp [disj]
  | @insert y ys hy ih =>
      obtain ⟨u,E,N,V⟩ := build_conj s y
      obtain ⟨v,Ev,Nv,Vv⟩ := ih u
      obtain ⟨t,Et,Nt,Vt⟩ := good_or (good_persist Ev V) Vv
      refine ⟨t,E.trans (Ev.trans Et),by omega,?_⟩
      convert Vt using 1
      funext x
      simp [disj, conj, Finset.mem_insert]

theorem build_monotone (s : Build (n+2)) (f : Finset (Fin n) → Bool)
    (hf : ∀ x y, x ⊆ y → f x = true → f y = true) :
    ∃ t : Build (n+2), Ext s t ∧ t.nots = s.nots ∧ good t f := by
  classical
  let ys := Finset.univ.filter (fun y : Finset (Fin n) => f y = true)
  obtain ⟨t,E,N,V⟩ := build_disj s ys
  refine ⟨t,E,N,?_⟩
  convert V using 1
  funext x
  apply Bool.eq_iff_iff.mpr
  change f x = true ↔ decide (∃ y ∈ ys, y ⊆ x) = true
  simp only [decide_eq_true_eq]
  constructor
  · intro hx
    exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,Finset.Subset.rfl⟩
  · rintro ⟨y,hy,hxy⟩
    exact hf y x hxy (Finset.mem_filter.mp hy).2

theorem build_bank {I : Type} [DecidableEq I] (idx : Finset I)
    (fs : I → Finset (Fin n) → Bool)
    (hf : ∀ i ∈ idx, ∀ x y, x ⊆ y → fs i x = true → fs i y = true)
    (s : Build (n+2)) :
    ∃ t : Build (n+2), Ext s t ∧ t.nots = s.nots ∧
      ∀ i ∈ idx, good t (fs i) := by
  classical
  induction idx using Finset.induction_on generalizing s with
  | empty =>
      exact ⟨s,List.prefix_rfl,rfl,by simp⟩
  | @insert i idx hi ih =>
      obtain ⟨u,E,N,V⟩ := build_monotone s (fs i)
        (hf i (Finset.mem_insert_self ..))
      obtain ⟨t,Et,Nt,H⟩ := ih (by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)) u
      refine ⟨t,E.trans Et,by omega,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact good_persist Et V
      · exact H j hj

theorem build_threshold_bank (r : Nat) (R : Finset (Fin n) → Nat)
    (hmono : Monotone R) (s : Build (n+2)) :
    ∃ t : Build (n+2), Ext s t ∧ t.nots = s.nots ∧
      ∀ k : Fin r, good t (fun x => decide (k.val+1 ≤ R x)) := by
  obtain ⟨t,E,N,V⟩ := build_bank (Finset.univ : Finset (Fin r))
    (fun k x => decide (k.val+1 ≤ R x)) (by
      intro k _ x y hxy hx
      exact decide_eq_true ((decide_eq_true_eq.mp hx).trans (hmono hxy))) s
  exact ⟨t,E,N,fun k => V k (Finset.mem_univ _)⟩

theorem build_and_bank {I : Type} [DecidableEq I] (idx : Finset I)
    (fs gs : I → Finset (Fin n) → Bool) (s : Build (n+2))
    (hf : ∀ i ∈ idx, good s (fs i)) (hg : ∀ i ∈ idx, good s (gs i)) :
    ∃ t : Build (n+2), Ext s t ∧ t.nots = s.nots ∧
      ∀ i ∈ idx, good t (fun x => fs i x && gs i x) := by
  classical
  induction idx using Finset.induction_on generalizing s with
  | empty => exact ⟨s,List.prefix_rfl,rfl,by simp⟩
  | @insert i idx hi ih =>
      obtain ⟨u,E,N,V⟩ := good_and (hf i (Finset.mem_insert_self ..))
        (hg i (Finset.mem_insert_self ..))
      obtain ⟨t,Et,Nt,H⟩ := ih u
        (fun j hj => good_persist E (hf j (Finset.mem_insert_of_mem hj)))
        (fun j hj => good_persist E (hg j (Finset.mem_insert_of_mem hj)))
      refine ⟨t,E.trans Et,by omega,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact good_persist Et V
      · exact H j hj

def any_bools {I : Type} (idx : Finset I)
    (fs : I → Finset (Fin n) → Bool) (x : Finset (Fin n)) : Bool :=
  decide (∃ i ∈ idx, fs i x = true)

theorem build_or_reads {I : Type} [DecidableEq I] (idx : Finset I)
    (fs : I → Finset (Fin n) → Bool) (s : Build (n+2))
    (hf : ∀ i ∈ idx, good s (fs i)) :
    ∃ t : Build (n+2), Ext s t ∧ t.nots = s.nots ∧
      good t (any_bools idx fs) := by
  classical
  induction idx using Finset.induction_on generalizing s with
  | empty =>
      refine ⟨s,List.prefix_rfl,rfl,?_⟩
      convert good_zero s using 1
      funext x
      simp [any_bools]
  | @insert i idx hi ih =>
      obtain ⟨u,E,N,V⟩ := ih s
        (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      obtain ⟨t,Et,Nt,Vt⟩ := good_or
        (good_persist E (hf i (Finset.mem_insert_self ..))) V
      refine ⟨t,E.trans Et,by omega,?_⟩
      convert Vt using 1
      funext x
      simp [any_bools, Finset.mem_insert]

def threshold_fs (r : Nat) (R : Finset (Fin n) → Nat) :
    List (Finset (Fin n) → Bool) :=
  List.ofFn (fun k : Fin r => fun x => decide (k.val+1 ≤ R x))

theorem threshold_fs_get (r : Nat) (R : Finset (Fin n) → Nat)
    (k : Fin r) :
    (threshold_fs r R).getD k.val (fun _ => false) =
      (fun x => decide (k.val+1 ≤ R x)) := by
  simp [threshold_fs, List.getD_eq_getElem?_getD, k.isLt]

end Wiring1270
end PEqualNP.Outside.L_lib_1308.CircuitDonor

namespace PEqualNP.Outside.L_lib_1308

namespace DervishInterpolation1308
variable {I : Type} {n : ℕ}

noncomputable def active (S : Finset I) (x : I → Finset (Fin n))
    (z : Finset (Fin n)) : Finset I := by
  classical
  exact S.filter fun i => x i ⊆ z

theorem mem_active {S : Finset I} {x : I → Finset (Fin n)} {z : Finset (Fin n)} {i : I} :
    i ∈ active S x z ↔ i ∈ S ∧ x i ⊆ z := by
  classical
  simp [active]

noncomputable def rankAt (S : Finset I) (x : I → Finset (Fin n)) (level : I → ℕ)
    (z : Finset (Fin n)) : ℕ := (active S x z).sup level

theorem rankAt_mono (S : Finset I) (x : I → Finset (Fin n)) (level : I → ℕ) :
    Monotone (rankAt S x level) := by
  intro u v huv
  apply Finset.sup_mono
  intro i hi
  obtain ⟨hS,hsub⟩ := mem_active.mp hi
  exact mem_active.mpr ⟨hS,hsub.trans huv⟩

theorem rankAt_le (S : Finset I) (x : I → Finset (Fin n)) (level : I → ℕ)
    (L : ℕ) (hL : ∀ i ∈ S, level i ≤ L) (z : Finset (Fin n)) : rankAt S x level z ≤ L := by
  apply Finset.sup_le_iff.mpr
  intro i hi
  exact hL i (mem_active.mp hi).1

theorem rankAt_sample (S : Finset I) (x : I → Finset (Fin n)) (level : I → ℕ)
    (hm : ∀ i ∈ S, ∀ j ∈ S, x i ⊆ x j → level i ≤ level j)
    (i : I) (hi : i ∈ S) : rankAt S x level (x i) = level i := by
  apply Nat.le_antisymm
  · apply Finset.sup_le_iff.mpr
    intro j hj
    obtain ⟨hjS,hji⟩ := mem_active.mp hj
    exact hm j hjS i hi hji
  · exact Finset.le_sup (mem_active.mpr ⟨hi,Finset.Subset.rfl⟩)

noncomputable def reached (S : Finset I) (x : I → Finset (Fin n))
    (level : I → ℕ) (color : I → Bool) (l : ℕ) (c : Bool) (z : Finset (Fin n)) : Bool := by
  classical
  exact decide (∃ i ∈ S, level i = l ∧ color i = c ∧ x i ⊆ z)

theorem reached_mono (S : Finset I) (x : I → Finset (Fin n)) (level : I → ℕ)
    (color : I → Bool) (l : ℕ) (c : Bool) (u v : Finset (Fin n)) (huv : u ⊆ v)
    (h : reached S x level color l c u = true) : reached S x level color l c v = true := by
  classical
  simp only [reached, decide_eq_true_eq] at h ⊢
  obtain ⟨i,hi,hl,hc,hsub⟩ := h
  exact ⟨i,hi,hl,hc,hsub.trans huv⟩

noncomputable def readColor (S : Finset I) (x : I → Finset (Fin n)) (level : I → ℕ)
    (color : I → Bool) (L : ℕ) (c : Bool) (z : Finset (Fin n)) : Bool := by
  classical
  exact decide (∃ l : Fin (L+1), reached S x level color l.val c z = true ∧
      rankAt S x level z ≤ l.val)

theorem readColor_sample (S : Finset I) (x : I → Finset (Fin n)) (level : I → ℕ)
    (color : I → Bool) (L : ℕ) (hL : ∀ i ∈ S, level i ≤ L)
    (hm : ∀ i ∈ S, ∀ j ∈ S, x i ⊆ x j → level i ≤ level j)
    (hc : ∀ i ∈ S, ∀ j ∈ S, x i ⊆ x j → level i = level j → color i = color j)
    (i : I) (hi : i ∈ S) (c : Bool) :
    readColor S x level color L c (x i) = decide (color i = c) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [readColor, reached, decide_eq_true_eq, rankAt_sample S x level hm i hi]
  constructor
  · rintro ⟨l, ⟨j,hj,hl,hcol,hsub⟩, hle⟩
    have hji := Nat.le_antisymm (hm j hj i hi hsub) (hl ▸ hle)
    exact (hc j hj i hi hsub hji).symm.trans hcol
  · intro h
    exact ⟨⟨level i, Nat.lt_succ_of_le (hL i hi)⟩,
      ⟨i,hi,rfl,h,Finset.Subset.rfl⟩, Nat.le_refl _⟩

end DervishInterpolation1308

namespace DervishInterpolation1308
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_lib_1308.CircuitDonor
open PEqualNP.Outside.L_lib_1308.CircuitDonor.Donor1196
open DervishBuild1196 DervishBuild1196.Build Wiring1270

theorem build_ceil_bank (b L : ℕ) (hPow : L < 2^b)
    (R : Finset (Fin n) → ℕ) (hMono : Monotone R) (hBound : ∀ z, R z ≤ L) :
    ∃ u : Build (n+2), u.nots ≤ b ∧
      ∀ l : Fin (L+1), good u (fun z => decide (R z ≤ l.val)) := by
  classical
  let s := Build.empty (n+2)
  obtain ⟨t,_,Nt,Vt⟩ := build_threshold_bank L R hMono s
  let fs := threshold_fs L R
  have fl : fs.length = L := by simp [fs,threshold_fs]
  have taps : Sort1196.Taps (sortKit (input := input (n:=n)) input_len) t fs := by
    apply DervishWire1196.taps_of_indexed
    intro i hi
    have hi' : i < L := by simpa only [fl] using hi
    let k : Fin L := ⟨i,hi'⟩
    obtain ⟨a,ha⟩ := Vt k
    refine ⟨a,?_⟩
    change Read input t a ((threshold_fs L R).getD k.val (fun _ => false))
    rw [threshold_fs_get L R k]
    exact ha
  obtain ⟨zeroWire,hz⟩ := good_zero t
  obtain ⟨u,negTap,_,_,Nu,vu⟩ := Inverter1270.invert_reads
    (input := input (n:=n)) input_len hPow t fs fl taps zeroWire hz
  have hs : s.nots = 0 := by simp [s,Build.nots,Build.circ,Build.empty,NotBracket.notCount]
  refine ⟨u, by omega, ?_⟩
  intro l
  by_cases hl : l.val < L
  · let k : Fin L := ⟨l.val,hl⟩
    refine ⟨negTap l.val, ?_⟩
    have va := vu k.val k.isLt
    change Read input u (negTap k.val)
      (Sort1196.neg ((threshold_fs L R).getD k.val (fun _ => false))) at va
    rw [threshold_fs_get L R k] at va
    convert va using 1
    funext z
    change decide (R z ≤ l.val) = !(decide (l.val+1 ≤ R z))
    by_cases hr : R z ≤ l.val
    · have hn : ¬l.val+1 ≤ R z := by omega
      simp [hr,hn]
    · have hp : l.val+1 ≤ R z := by omega
      simp [hr,hp]
  · convert good_one u using 1
    funext z
    exact decide_eq_true ((hBound z).trans (Nat.le_of_not_gt hl))

theorem build_colors {I : Type} (S : Finset I) (x : I → Finset (Fin n))
    (lev : I → ℕ) (col : I → Bool) (b L : ℕ) (hPow : L < 2^b)
    (hLev : ∀ i ∈ S, lev i ≤ L) :
    ∃ t : Build (n+2), t.nots ≤ b ∧ ∀ c, good t (readColor S x lev col L c) := by
  classical
  let R := rankAt S x lev
  obtain ⟨u,Nu,ceil⟩ := build_ceil_bank b L hPow R (rankAt_mono S x lev)
    (rankAt_le S x lev L hLev)
  let idx : Finset (Bool × Fin (L+1)) := Finset.univ
  let reach (p : Bool × Fin (L+1)) := reached S x lev col p.2.val p.1
  let valid (p : Bool × Fin (L+1)) (z : Finset (Fin n)) := decide (R z ≤ p.2.val)
  obtain ⟨v,Ev,Nv,hReach⟩ := build_bank idx reach
    (fun p _ a z hsub h => reached_mono S x lev col p.2.val p.1 a z hsub h) u
  obtain ⟨w,_,Nw,hw⟩ := build_and_bank idx reach valid v hReach
    (fun p _ => good_persist Ev (ceil p.2))
  let term (c : Bool) (l : Fin (L+1)) (z : Finset (Fin n)) := reach (c,l) z && valid (c,l) z
  have host (c : Bool) (l : Fin (L+1)) : good w (term c l) :=
    hw (c,l) (Finset.mem_univ _)
  have codec (c : Bool) : any_bools Finset.univ (term c) = readColor S x lev col L c := by
    funext z
    apply Bool.eq_iff_iff.mpr
    simp only [any_bools, term, readColor, Bool.and_eq_true, Finset.mem_univ, true_and,
      decide_eq_true_eq, reach, valid, R]
  obtain ⟨w₀,E₀,N₀,H₀⟩ := build_or_reads Finset.univ (term false) w (fun l _ => host false l)
  obtain ⟨w₁,E₁,N₁,H₁⟩ := build_or_reads Finset.univ (term true) w₀
    (fun l _ => good_persist E₀ (host true l))
  refine ⟨w₁,by omega,?_⟩
  intro c
  cases c
  · rw [← codec]
    exact good_persist E₁ H₀
  · rw [← codec]
    exact H₁

theorem interpolation_circuit {I : Type} (S : Finset I) (x : I → Finset (Fin n))
    (lev : I → ℕ) (col : I → Bool) (b L : ℕ) (hPow : L < 2^b)
    (hLev : ∀ i ∈ S, lev i ≤ L)
    (hMono : ∀ i ∈ S, ∀ j ∈ S, x i ⊆ x j → lev i ≤ lev j)
    (hColor : ∀ i ∈ S, ∀ j ∈ S, x i ⊆ x j → lev i = lev j → col i = col j) :
    ∃ (C : Circuit) (tap : Fin 2 → ℕ),
      MetaComplexity.FanInTwo C ∧ MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ (∀ a, tap a < n+2+C.size) ∧ NotBracket.notCount C ≤ b ∧
      ∀ i ∈ S,
        let v := fun (a : Fin 2) => (C.wires (input (x i))).getD (tap a) false
        v 1 = !(v 0) ∧ v 0 = col i := by
  obtain ⟨t,Nt,Vt⟩ := build_colors S x lev col b L hPow hLev
  obtain ⟨p,hp⟩ := Vt true
  obtain ⟨q,hq⟩ := Vt false
  let C : Circuit := ⟨t.gates,0⟩
  let tap : Fin 2 → ℕ := fun a => if a.val = 0 then p else q
  refine ⟨C,tap,t.fan,t.back,by simp [C],?_,Nt,?_⟩
  · intro a
    change (if a.val = 0 then p else q) < t.size
    split
    · exact hp.1
    · exact hq.1
  · intro i hi
    have ht := (hp.2 (x i)).trans (readColor_sample S x lev col L hLev hMono hColor i hi true)
    have hf := (hq.2 (x i)).trans (readColor_sample S x lev col L hLev hMono hColor i hi false)
    change (C.wires (input (x i))).getD q false = !(C.wires (input (x i))).getD p false ∧
      (C.wires (input (x i))).getD p false = col i
    change (t.circ.wires (input (x i))).getD q false = !(t.circ.wires (input (x i))).getD p false ∧
      (t.circ.wires (input (x i))).getD p false = col i
    rw [ht,hf]
    cases col i <;> decide

end DervishInterpolation1308

namespace DervishSpineColors1308

variable {I : Type} {n : ℕ}

structure Layout (x : I → Finset (Fin n)) (pin : I → Option Bool) (L : ℕ) where
  height : I → ℕ
  pos : I → ℕ
  edge : I → Bool
  armColor : I → Bool
  first : I
  last : I
  bound : ∀ i, height i ≤ L
  mono : ∀ i j, x i ⊆ x j → height i ≤ height j
  uniqueArm : ∀ i j, x i ⊆ x j → height i = height j → height i < L → i = j
  distinctPos : ∀ i j, height i = L → height j = L → pos i = pos j → i = j
  adjoining : ∀ i j, x i ⊆ x j → height i = L → height j = L → i ≠ j →
    (pos i ≤ pos j + 1 ∧ pos j ≤ pos i + 1) ∧ edge i = false ∧ edge j = true
  edgesTop : ∀ i j, edge i = true → x i ⊆ x j → i ≠ j → False
  firstPos : pos first = 0
  lastHeight : height last = L
  lastPos : ∀ i, height i = L → pos i ≤ pos last
  different : first ≠ last
  pins : ∀ i c, pin i = some c →
    if height i < L then armColor i = c else (i = first ∧ c = false) ∨ (i = last ∧ c = true)

variable {x : I → Finset (Fin n)} {pin : I → Option Bool} {L : ℕ}

def Layout.Model (A : Layout x pin L) (S : Finset I) (B : ℕ)
    (lev : I → ℕ) (col : I → Bool) : Prop :=
  (∀ i ∈ S, lev i ≤ B) ∧
  (∀ i ∈ S, ∀ j ∈ S, x i ⊆ x j → lev i ≤ lev j) ∧
  (∀ i ∈ S, ∀ j ∈ S, x i ⊆ x j → lev i = lev j → col i = col j) ∧
  (∀ i ∈ S, ∀ c, pin i = some c → col i = c)

theorem Layout.erase_model [Fintype I] [DecidableEq I] (A : Layout x pin L)
    (d : I) (hd : A.height d = L) :
    ∃ col, A.Model (Finset.univ.erase d) L A.height col := by
  let col (i : I) := if A.height i < L then A.armColor i else decide (A.pos d < A.pos i)
  refine ⟨col, fun i _ => A.bound i, fun i _ j _ => A.mono i j, ?_, ?_⟩
  · intro i hi j hj hij heq
    by_cases ha : A.height i < L
    · rw [A.uniqueArm i j hij heq ha]
    · have hiL : A.height i = L := Nat.le_antisymm (A.bound i) (by omega)
      have hjL : A.height j = L := heq.symm.trans hiL
      by_cases he : i = j
      · rw [he]
      · have near := (A.adjoining i j hij hiL hjL he).1
        have hip : A.pos i ≠ A.pos d := fun hp =>
          (Finset.mem_erase.mp hi).1 (A.distinctPos i d hiL hd hp)
        have hjp : A.pos j ≠ A.pos d := fun hp =>
          (Finset.mem_erase.mp hj).1 (A.distinctPos j d hjL hd hp)
        have agree : (A.pos d < A.pos i) ↔ (A.pos d < A.pos j) := by omega
        simp [col,hiL,hjL,agree]
  · intro i hi c hc
    have h := A.pins i c hc
    by_cases ha : A.height i < L
    · simpa [col,ha] using h
    · rw [if_neg ha] at h
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · simp [col,ha,A.firstPos]
      · have hne : A.pos d ≠ A.pos A.last := fun hp =>
          (Finset.mem_erase.mp hi).1 ((A.distinctPos d A.last hd A.lastHeight hp).symm)
        have ht := Nat.lt_of_le_of_ne (A.lastPos d hd) hne
        simp [col,ha,ht]

theorem Layout.full_model [Fintype I] [DecidableEq I] (A : Layout x pin L) :
    ∃ lev col, A.Model Finset.univ (L+1) lev col := by
  let lev (i : I) := if A.edge i = true then L+1 else A.height i
  let col (i : I) := if A.height i < L then A.armColor i else decide (i = A.last)
  have mono : ∀ i j, x i ⊆ x j → lev i ≤ lev j := by
    intro i j hij
    by_cases he : i = j
    · rw [he]
    · by_cases e : A.edge i = true
      · exact (A.edgesTop i j e hij he).elim
      · by_cases ej : A.edge j = true
        · simpa [lev,e,ej] using (A.bound i).trans (Nat.le_succ L)
        · simpa [lev,e,ej] using A.mono i j hij
  refine ⟨lev,col,?_,fun i _ j _ => mono i j,?_,?_⟩
  · intro i _
    by_cases e : A.edge i = true
    · simp [lev,e]
    · simpa [lev,e] using (A.bound i).trans (Nat.le_succ L)
  · intro i _ j _ hij hh
    by_cases he : i = j
    · rw [he]
    · have ei : A.edge i ≠ true := fun h => A.edgesTop i j h hij he
      have ej : A.edge j ≠ true := by
        intro ej
        simp only [lev,if_neg ei,if_pos ej] at hh
        have hi := A.bound i
        omega
      have hb : A.height i = A.height j := by simpa [lev,ei,ej] using hh
      by_cases hl : A.height i < L
      · exact (he (A.uniqueArm i j hij hb hl)).elim
      · have hiL : A.height i = L := Nat.le_antisymm (A.bound i) (by omega)
        have hjL := hb.symm.trans hiL
        exact (ej (A.adjoining i j hij hiL hjL he).2.2).elim
  · intro i _ c hc
    have h := A.pins i c hc
    by_cases ha : A.height i < L
    · simpa [col,ha] using h
    · rw [if_neg ha] at h
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · simp [col,ha,A.different]
      · simp [col,ha]

theorem all_contains [DecidableEq I] [Fintype I] (Fits : Finset I → Prop)
    (mono : ∀ {S T}, S ⊆ T → Fits T → Fits S) (F : Finset I)
    (erase : ∀ i ∈ F, Fits (Finset.univ.erase i)) :
    ∀ S, ¬ Fits S → F ⊆ S := by
  intro S bad i hi
  by_contra h
  exact bad (mono (by
    intro j hj
    exact Finset.mem_erase.mpr ⟨fun e => h (e ▸ hj), Finset.mem_univ _⟩) (erase i hi))

end DervishSpineColors1308

namespace Lower1308
open PEqualNP.Outside.L_lib_1308.CircuitDonor.Donor1196
open PEqualNP.CircuitLowerBounds

private def out (C : Circuit) (tap : Fin 2 → Nat) (w : List Bool) (j : Fin 2) : Bool :=
  (C.wires w).getD (tap j) false

private theorem same_color_of_signature (C : Circuit) (tap : Fin 2 → Nat)
    (a b : List Bool) (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hmono : AltChain1196.below a b) (hlen : a.length = b.length)
    (ha : out C tap a 1 = !(out C tap a 0))
    (hb : out C tap b 1 = !(out C tap b 0))
    (heq : AltChain1196.circuitSignature C a = AltChain1196.circuitSignature C b) :
    out C tap a 0 = out C tap b 0 := by
  have hbelow := (AltChain1196.circuit_signature_convex C a b b hfan
    hmono (by intro _; exact le_refl _) hlen rfl heq).2.1
  have h0 := hbelow (tap 0)
  have h1 := hbelow (tap 1)
  change out C tap a 0 ≤ out C tap b 0 at h0
  change out C tap a 1 ≤ out C tap b 1 at h1
  unfold out at ha hb h0 h1 ⊢
  cases hax : (C.wires a).getD (tap 0) false <;>
    cases hbx : (C.wires b).getD (tap 0) false <;> simp_all
  all_goals exact False.elim ((by decide : ¬ (true : Bool) ≤ false) (by assumption))

theorem saturated_top (r : Nat) (q : Nat) (C : Circuit) (tap : Fin 2 → Nat)
    (x : Fin q → List Bool) (u : List Bool)
    (hq : q = 2^r) (hbudget : PEqualNP.NotBracket.notCount C ≤ r)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hlen : ∀ i, (x i).length = u.length)
    (hmono : ∀ a b, a ≤ b → AltChain1196.below (x a) (x b))
    (htop : ∀ i, AltChain1196.below (x i) u)
    (hcomp : ∀ i, out C tap (x i) 1 = !(out C tap (x i) 0))
    (hcompU : out C tap u 1 = !(out C tap u 0))
    (hflip : ∀ i : Fin (q-1), out C tap (x ⟨i.val, by omega⟩) 0 ≠
      out C tap (x ⟨i.val+1, by omega⟩) 0) :
    out C tap (x ⟨q-1, by rw [hq]; exact Nat.sub_lt (Nat.two_pow_pos r) (by omega)⟩) 0 = out C tap u 0 := by
  have hqpos : 0 < q := by rw [hq]; exact Nat.two_pow_pos r
  let last : Fin q := ⟨q-1, by omega⟩
  let y : Fin (q+1) → List Bool := fun i =>
    if hi : i.val < q then x ⟨i.val, hi⟩ else u
  have hyle : ∀ a b, a ≤ b → AltChain1196.below (y a) (y b) := by
    intro a b hab
    simp only [y]
    split
    · rename_i ha
      split
      · rename_i hb
        exact hmono ⟨a.val, ha⟩ ⟨b.val, hb⟩ (by exact hab)
      · exact htop ⟨a.val, ha⟩
    · rename_i ha
      have hb : ¬ b.val < q := by omega
      simp only [dif_neg hb]
      intro j
      exact le_refl _
  have hylen : ∀ i, (y i).length = u.length := by
    intro i; simp only [y]; split
    · exact hlen _
    · rfl
  have hycomp : ∀ i, out C tap (y i) 1 = !(out C tap (y i) 0) := by
    intro i; simp only [y]; split
    · exact hcomp _
    · exact hcompU
  by_contra hne
  have hsign : ∀ i : Fin q,
      AltChain1196.circuitSignature C (y (Fin.castSucc i)) ≠
      AltChain1196.circuitSignature C (y (Fin.succ i)) := by
    intro i heq
    have hle : Fin.castSucc i ≤ Fin.succ i := by change i.val ≤ i.val+1; omega
    have hs := same_color_of_signature C tap (y (Fin.castSucc i))
      (y (Fin.succ i)) hfan (hyle _ _ hle)
      (by rw [hylen, hylen]) (hycomp _) (hycomp _) heq
    by_cases hi : i.val+1 < q
    · have hsmall : i.val < q-1 := by omega
      have hi' : i.val < q := by omega
      have he : out C tap (x ⟨i.val, hi'⟩) 0 ≠
          out C tap (x ⟨i.val+1, hi⟩) 0 := hflip ⟨i.val, hsmall⟩
      exact he (by simpa [y, hi, hi', Fin.castSucc, Fin.succ] using hs)
    · have ilast : i.val = q-1 := by have := i.isLt; omega
      have hi' : i.val < q := i.isLt
      have hj : ¬ i.val+1 < q := by omega
      have hleft : y (Fin.castSucc i) = x last := by
        change (if h : i.val < q then x ⟨i.val, h⟩ else u) = x last
        rw [dif_pos hi']
        congr 1
        ext
        exact ilast
      have hright : y (Fin.succ i) = u := by
        change (if h : i.val+1 < q then x ⟨i.val+1, h⟩ else u) = u
        simp only [dif_neg hj]
      have hs' : out C tap (x last) 0 = out C tap u 0 := by
        simpa only [hleft, hright] using hs
      exact hne hs'
  have hconvex : ∀ a b c : Fin (q+1), a ≤ b → b ≤ c →
      AltChain1196.circuitSignature C (y a) = AltChain1196.circuitSignature C (y c) →
      AltChain1196.circuitSignature C (y a) = AltChain1196.circuitSignature C (y b) := by
    intro a b c hab hbc heq
    exact (AltChain1196.circuit_signature_convex C (y a) (y b) (y c) hfan
      (hyle _ _ hab) (hyle _ _ hbc) (by rw [hylen, hylen])
      (by rw [hylen, hylen]) heq).1
  have hlarge := AltChain1196.signature_bound q (PEqualNP.NotBracket.notCount C)
    (fun i => AltChain1196.circuitSignature C (y i)) hconvex hsign
  rw [hq] at hlarge
  have hp : 2 ^ PEqualNP.NotBracket.notCount C ≤ 2^r := Nat.pow_le_pow_right (by omega) hbudget
  omega

theorem opposite_arms_top (r q : Nat) (C : Circuit) (tap : Fin 2 → Nat)
    (x : Fin 2 → Fin q → List Bool) (top upper : List Bool)
    (hq : q = 2^r) (hbudget : PEqualNP.NotBracket.notCount C ≤ r)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hlen : ∀ a i, (x a i).length = upper.length)
    (hmono : ∀ a i j, i ≤ j → AltChain1196.below (x a i) (x a j))
    (hupper : ∀ a i, AltChain1196.below (x a i) upper)
    (hcomp : ∀ a i, out C tap (x a i) 1 = !(out C tap (x a i) 0))
    (hcompU : out C tap upper 1 = !(out C tap upper 0))
    (hshared : ∀ a, x a ⟨q-1, by rw [hq]; exact Nat.sub_lt (Nat.two_pow_pos r) (by omega)⟩ = top)
    (hinner : ∀ a (i : Fin (q-1)), i.val+1 < q-1 →
      out C tap (x a ⟨i.val, by omega⟩) 0 ≠
      out C tap (x a ⟨i.val+1, by omega⟩) 0)
    (hopposite : ∀ (hmore : 1 < q),
      out C tap (x 0 ⟨q-2, by omega⟩) 0 ≠
      out C tap (x 1 ⟨q-2, by omega⟩) 0) :
    out C tap top 0 = out C tap upper 0 := by
  have hqpos : 0 < q := by rw [hq]; exact Nat.two_pow_pos r
  let last : Fin q := ⟨q-1, by omega⟩
  have hchoice : ∃ a : Fin 2, ∀ i : Fin (q-1),
      out C tap (x a ⟨i.val, by omega⟩) 0 ≠
      out C tap (x a ⟨i.val+1, by omega⟩) 0 := by
    by_cases hone : q = 1
    · refine ⟨0, ?_⟩
      intro i
      have := i.isLt
      omega
    · have hmore : 1 < q := by omega
      have happ := hopposite hmore
      have hpick : ∃ a : Fin 2,
          out C tap (x a ⟨q-2, by omega⟩) 0 ≠ out C tap top 0 := by
        by_contra hn
        push_neg at hn
        exact happ ((hn 0).trans (hn 1).symm)
      obtain ⟨a, ha⟩ := hpick
      refine ⟨a, ?_⟩
      intro i
      by_cases hi : i.val+1 < q-1
      · exact hinner a i hi
      · have hbefore : (⟨i.val, by omega⟩ : Fin q) = ⟨q-2, by omega⟩ := by
          apply Fin.ext
          change i.val = q-2
          have := i.isLt
          omega
        have hafter : (⟨i.val+1, by omega⟩ : Fin q) = last := by
          apply Fin.ext
          change i.val+1 = q-1
          have := i.isLt
          omega
        rw [hbefore, hafter, hshared a]
        exact ha
  obtain ⟨a, ha⟩ := hchoice
  have hresult := saturated_top r q C tap (x a) upper hq hbudget hfan
    (hlen a) (hmono a) (hupper a) (hcomp a) hcompU ha
  simpa only [hshared a] using hresult

theorem pinned_path_contradiction (p : Nat) (v : Fin (p+1) → Bool)
    (u : Fin p → Bool) (left : ∀ i : Fin p, v ⟨i.val, by omega⟩ = u i)
    (right : ∀ i : Fin p, v ⟨i.val+1, by omega⟩ = u i)
    (c₀ c₁ : Bool) (hpin₀ : v ⟨0, by omega⟩ = c₀)
    (hpin₁ : v ⟨p, by omega⟩ = c₁) (hop : c₀ ≠ c₁) : False := by
  have hconst : ∀ j (hj : j < p+1), v ⟨j, hj⟩ = v ⟨0, by omega⟩ := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
      intro hj
      let i : Fin p := ⟨j, by omega⟩
      have hleft := left i
      have hright := right i
      have hprev : v ⟨j, by omega⟩ = v ⟨0, by omega⟩ := ih (by omega)
      exact (hright.trans hleft.symm).trans hprev
  exact hop (hpin₀.symm.trans ((hconst p (by omega)).symm.trans hpin₁))

end Lower1308

namespace DervishAssemble1308
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_lib_1308.CircuitDonor.Wiring1270
open PEqualNP.Outside.L_lib_1308.CircuitDonor.Donor1196
open DervishSpineColors1308
variable {I : Type} {n : ℕ}

theorem input_below {n : Nat} {s t : Finset (Fin n)} (hst : s ⊆ t) :
    AltChain1196.below (input s) (input t) := by
  intro i
  by_cases hi : i < n
  · have h : i < (List.ofFn (fun u : Fin n => decide (u ∈ s))).length := by simpa using hi
    have h' : i < (List.ofFn (fun u : Fin n => decide (u ∈ t))).length := by simpa using hi
    rw [input, input, List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h']
    rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ h']
    simp only [List.getElem_ofFn]
    by_cases hs : ⟨i,hi⟩ ∈ s
    · simp [hs, hst hs]
    · simp [hs]
  · rw [input, input, List.getD_append_right _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by simp; omega)]
    simpa only [List.length_ofFn] using (le_refl ([false,true].getD (i-n) false))

def Fits (x : I → Finset (Fin n)) (pin : I → Option Bool) (S : Finset I) (b : ℕ) : Prop :=
  ∃ (C : Circuit) (tap : Fin 2 → ℕ),
    MetaComplexity.FanInTwo C ∧ MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ (∀ a, tap a < n+2+C.size) ∧ NotBracket.notCount C ≤ b ∧
    ∀ i ∈ S, let v := fun (a : Fin 2) => (C.wires (input (x i))).getD (tap a) false
    v 1 = !(v 0) ∧ ∀ c, pin i = some c → v 0 = c

theorem fit_mono {x : I → Finset (Fin n)} {pin : I → Option Bool} {S T : Finset I} {a b : ℕ}
    (hS : S ⊆ T) (hb : a ≤ b) (h : Fits x pin T a) : Fits x pin S b := by
  obtain ⟨C,tap,fa,ba,op,wt,nb,pts⟩ := h
  exact ⟨C,tap,fa,ba,op,wt,nb.trans hb,fun i hi => pts i (hS hi)⟩

theorem fit_model {x : I → Finset (Fin n)} {pin : I → Option Bool} {L : ℕ}
    (A : Layout x pin L) {S : Finset I} {B b : ℕ} (hPow : B < 2^b)
    {lev : I → ℕ} {col : I → Bool} (M : A.Model S B lev col) : Fits x pin S b := by
  obtain ⟨bound,mono,agree,pins⟩ := M
  obtain ⟨C,tap,fa,ba,op,wt,nb,pts⟩ := DervishInterpolation1308.interpolation_circuit
    S x lev col b B hPow bound mono agree
  refine ⟨C,tap,fa,ba,op,wt,nb,?_⟩
  intro i hi
  obtain ⟨comp,color⟩ := pts i hi
  exact ⟨comp,fun c hc => color.trans (pins i hi c hc)⟩

theorem finish [Fintype I] [DecidableEq I]
    {x : I → Finset (Fin n)} {pin : I → Option Bool} {F : Finset I} (r : ℕ)
    (A : Layout x pin (2^r - 1)) (marked : ∀ i ∈ F, A.height i = 2^r - 1)
    (impossible : ¬ Fits x pin Finset.univ r) :
    (∀ b, Fits x pin Finset.univ b ↔ r < b) ∧
    (∀ i ∈ F, Fits x pin (Finset.univ.erase i) r) ∧
    ∀ S : Finset I, ¬ Fits x pin S r → F ⊆ S := by
  have hpos := Nat.two_pow_pos r
  have hfull : Fits x pin Finset.univ (r+1) := by
    obtain ⟨lev,col,M⟩ := A.full_model
    apply fit_model A _ M
    rw [Nat.pow_succ]
    omega
  have erase : ∀ i ∈ F, Fits x pin (Finset.univ.erase i) r := by
    intro i hi
    obtain ⟨col,M⟩ := A.erase_model i (marked i hi)
    exact fit_model A (by omega) M
  refine ⟨?_,erase,all_contains (fun S => Fits x pin S r) (fun h f => fit_mono h (le_refl r) f) F erase⟩
  intro b
  constructor
  · intro h
    by_contra hb
    exact impossible (fit_mono Finset.Subset.rfl (by omega) h)
  · intro h
    exact fit_mono Finset.Subset.rfl (by omega) hfull

end DervishAssemble1308

end PEqualNP.Outside.L_lib_1308

namespace PEqualNP.Outside.L_lib_1308.DervishRoutes1308
open PEqualNP PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_lib_1308.CircuitDonor.Wiring1270
open DervishAssemble1308 Lower1308
variable {I : Type} {n p r : ℕ}

def armColor (a : Fin 2) (i : ℕ) : Bool := decide ((a.val+i)%2 = 1)

theorem color_changes (a : Fin 2) (j : ℕ) : armColor a j ≠ armColor a (j+1) := by
  unfold armColor
  by_cases h : (a.val+j)%2 = 1
  · have g : (a.val+(j+1))%2 ≠ 1 := by omega
    simp [h,g]
  · have g : (a.val+(j+1))%2 = 1 := by omega
    simp [h,g]

theorem opposite_colors (j : ℕ) : armColor 0 j ≠ armColor 1 j := by
  simpa [armColor, Nat.add_comm 1 j] using color_changes 0 j

structure Routes (x : I → Finset (Fin n)) (pin : I → Option Bool) (p r : ℕ) where
  word : Fin (p+1) → I
  edge : Fin p → I
  arm : Fin (p+1) → Fin 2 → Fin (2^r-1) → I
  arm_mono : ∀ t a i j, i ≤ j → x (arm t a i) ⊆ x (arm t a j)
  arm_word : ∀ t a i, x (arm t a i) ⊆ x (word t)
  left : ∀ t : Fin p, x (word ⟨t.val,by omega⟩) ⊆ x (edge t)
  right : ∀ t : Fin p, x (word ⟨t.val+1,by omega⟩) ⊆ x (edge t)
  arm_pin : ∀ t a i, pin (arm t a i) = some (armColor a i.val)
  first_pin : pin (word ⟨0,by omega⟩) = some false
  last_pin : pin (word ⟨p,by omega⟩) = some true

variable {x : I → Finset (Fin n)} {pin : I → Option Bool}

def Routes.row (A : Routes x pin p r) (t : Fin (p+1)) (a : Fin 2) (i : Fin (2^r)) : I :=
  if h : i.val < 2^r-1 then A.arm t a ⟨i.val,h⟩ else A.word t

theorem Routes.row_mono (A : Routes x pin p r) (t : Fin (p+1)) (a : Fin 2)
    (i j : Fin (2^r)) (hij : i ≤ j) : x (A.row t a i) ⊆ x (A.row t a j) := by
  have hh : i.val ≤ j.val := hij
  by_cases h : j.val < 2^r-1
  · have hi : i.val < 2^r-1 := by omega
    simpa only [row, dif_pos hi,dif_pos h] using A.arm_mono t a ⟨i.val,hi⟩ ⟨j.val,h⟩ hh
  · by_cases hi : i.val < 2^r-1
    · simpa only [row,dif_pos hi,dif_neg h] using A.arm_word t a ⟨i.val,hi⟩
    · simp [row,hi,h]

theorem Routes.row_le_word (A : Routes x pin p r) (t : Fin (p+1)) (a : Fin 2)
    (i : Fin (2^r)) : x (A.row t a i) ⊆ x (A.word t) := by
  by_cases h : i.val < 2^r-1
  · simpa only [row,dif_pos h] using A.arm_word t a ⟨i.val,h⟩
  · simp [row,h]

theorem Routes.no_fit [Fintype I] (A : Routes x pin p r) : ¬ Fits x pin Finset.univ r := by
  rintro ⟨C,tap,fan,_,_,_,budget,points⟩
  let v (i : I) (a : Fin 2) := out C tap (input (x i)) a
  have comp (i : I) : v i 1 = !(v i 0) := (points i (Finset.mem_univ _)).1
  have spec (i : I) (c : Bool) (h : pin i = some c) : v i 0 = c :=
    (points i (Finset.mem_univ _)).2 c h
  have hrow (t : Fin (p+1)) (a : Fin 2) (i : Fin (2^r)) (h : i.val < 2^r-1) :
      v (A.row t a i) 0 = armColor a i.val := by
    rw [Routes.row,dif_pos h]
    exact spec _ _ (A.arm_pin t a ⟨i.val,h⟩)
  have force (t : Fin (p+1)) (z : I) (h : x (A.word t) ⊆ x z) : v (A.word t) 0 = v z 0 := by
    refine opposite_arms_top r (2^r) C tap (fun a i => input (x (A.row t a i)))
      (input (x (A.word t))) (input (x z)) rfl budget fan ?_ ?_ ?_ ?_ (comp z) ?_ ?_ ?_
    · intro a i
      simp only [input_len]
    · intro a i j hj
      exact input_below (A.row_mono t a i j hj)
    · intro a i
      exact input_below ((A.row_le_word t a i).trans h)
    · intro a i
      exact comp _
    · intro a
      simp [Routes.row]
    · intro a i hi
      change v (A.row t a ⟨i.val,by have := i.isLt; omega⟩) 0 ≠
        v (A.row t a ⟨i.val+1,by omega⟩) 0
      rw [hrow t a _ i.isLt,hrow t a _ hi]
      exact color_changes a i.val
    · intro hmore
      have h : 2^r-2 < 2^r-1 := by omega
      change v (A.row t 0 ⟨2^r-2,by omega⟩) 0 ≠ v (A.row t 1 ⟨2^r-2,by omega⟩) 0
      rw [hrow t 0 _ h,hrow t 1 _ h]
      exact opposite_colors _
  apply pinned_path_contradiction p (fun t => v (A.word t) 0) (fun t => v (A.edge t) 0)
    (fun t => force _ _ (A.left t)) (fun t => force _ _ (A.right t)) false true
  · exact spec _ _ A.first_pin
  · exact spec _ _ A.last_pin
  · decide

end PEqualNP.Outside.L_lib_1308.DervishRoutes1308

namespace PEqualNP.Outside.L_lib_1308.DervishAbstractRows1308
open DervishSpineColors1308 DervishRoutes1308 DervishAssemble1308

inductive Row (p r : ℕ)
  | word (t : Fin (p+1))
  | edge (t : Fin p)
  | arm (t : Fin (p+1)) (a : Fin 2) (j : Fin (2^r-1))

variable {I : Type} {p r n : ℕ}

def Rel : Row p r → Row p r → Prop
  | .word t, .word u => t = u
  | .word t, .edge u => t.val = u.val ∨ t.val = u.val + 1
  | .word _, .arm .. => False
  | .edge t, .edge u => t = u
  | .edge _, .word _ => False
  | .edge _, .arm .. => False
  | .arm t _ _, .word u => t = u
  | .arm t _ _, .edge u => t.val = u.val ∨ t.val = u.val + 1
  | .arm t a j, .arm u b k => t = u ∧ a = b ∧ j ≤ k

def height : Row p r → ℕ
  | .arm _ _ j => j.val
  | _ => 2^r-1

def pos : Row p r → ℕ
  | .word t => 2*t.val
  | .edge t => 2*t.val+1
  | .arm .. => 0

def isEdge : Row p r → Bool
  | .edge _ => true
  | _ => false

def color : Row p r → Bool
  | .arm _ a j => armColor a j.val
  | _ => false

def pin : Row p r → Option Bool
  | .word t => if t.val = 0 then some false else if t.val = p then some true else none
  | .edge _ => none
  | .arm _ a j => some (armColor a j.val)

def first : Row p r := .word ⟨0,by omega⟩
def last : Row p r := .word ⟨p,by omega⟩

@[simp] theorem height_ok (s : Row p r) : height s ≤ 2^r-1 := by
  cases s with
  | word _ | edge _ => exact le_refl _
  | arm _ _ j => exact Nat.le_of_lt j.isLt

@[simp] theorem arm_lt (t : Fin (p+1)) (a : Fin 2) (j : Fin (2^r-1)) :
    height (.arm t a j) < 2^r-1 := j.isLt

@[simp] theorem arm_not_top (t : Fin (p+1)) (a : Fin 2) (j : Fin (2^r-1)) :
    height (.arm t a j) ≠ 2^r-1 := Nat.ne_of_lt j.isLt

private theorem height_mono {i j : Row p r} (h : Rel i j) : height i ≤ height j := by
  cases i <;> cases j <;> simp_all [Rel, height]
  all_goals first | exact Nat.le_of_lt (by assumption) | exact h.2.2

private theorem unique_arm {i j : Row p r} (h : Rel i j) (hh : height i = height j)
    (hl : height i < 2^r-1) : i = j := by
  cases i <;> cases j <;> simp_all [Rel, height]
  all_goals first | exact Fin.ext hh | exact False.elim (Nat.ne_of_lt (Fin.isLt _) hh)

private theorem same_pos {i j : Row p r} (hi : height i = 2^r-1) (hj : height j = 2^r-1)
    (h : pos i = pos j) : i = j := by
  cases i <;> cases j <;>
    simp_all only [arm_not_top, pos, Row.word.injEq, Row.edge.injEq, Fin.ext_iff, reduceCtorEq] <;> omega

private theorem near {i j : Row p r} (h : Rel i j) (hi : height i = 2^r-1) (hj : height j = 2^r-1)
    (hne : i ≠ j) : (pos i ≤ pos j+1 ∧ pos j ≤ pos i+1) ∧ isEdge i = false ∧ isEdge j = true := by
  cases i <;> cases j <;> simp_all [Rel, pos, isEdge]
  omega

private theorem edge_top {i j : Row p r} (hi : isEdge i = true) (h : Rel i j) : i = j := by
  cases i <;> cases j <;> simp_all [Rel,isEdge]

private theorem last_pos {i : Row p r} (h : height i = 2^r-1) : pos i ≤ pos (last (p:=p) (r:=r)) := by
  cases i <;> simp_all only [arm_not_top,pos,last] <;> omega

private theorem pins_compatible {i : Row p r} {c : Bool} (h : pin i = some c) :
    if height i < 2^r-1 then color i = c else (i=first ∧ c=false) ∨ (i=last ∧ c=true) := by
  cases i with
  | word t =>
    change (if t.val = 0 then some false else if t.val = p then some true else none) = some c at h
    simp only [height,lt_self_iff_false,if_false,first,last,Row.word.injEq]
    split at h
    · rename_i hv
      exact Or.inl ⟨Fin.ext hv, (Option.some.inj h).symm⟩
    · split at h
      · rename_i hv
        exact Or.inr ⟨Fin.ext hv, (Option.some.inj h).symm⟩
      · contradiction
  | edge t => simp [pin] at h
  | arm t a j => simpa [arm_lt,pin,color] using h

theorem fit_rows [Fintype I] [DecidableEq I]
    (e : I ≃ Row p r) (x : I → Finset (Fin n)) (hp : 0<p) (F : Finset I)
    (order : ∀ i j, x i ⊆ x j ↔ Rel (e i) (e j))
    (marked : ∀ i ∈ F, height (e i) = 2^r-1) :
    (∀ b, Fits x (pin ∘ e) Finset.univ b ↔ r < b) ∧
    (∀ i ∈ F, Fits x (pin ∘ e) (Finset.univ.erase i) r) ∧
    ∀ S : Finset I, ¬ Fits x (pin ∘ e) S r → F ⊆ S := by
  let A : Layout x (pin ∘ e) (2^r-1) := {
    height := height ∘ e
    pos := pos ∘ e
    edge := isEdge ∘ e
    armColor := color ∘ e
    first := e.symm first
    last := e.symm last
    bound := fun i => height_ok (e i)
    mono := fun i j hij => height_mono ((order i j).mp hij)
    uniqueArm := fun i j hij hh hl => e.injective (unique_arm ((order i j).mp hij) hh hl)
    distinctPos := fun i j hi hj h => e.injective (same_pos hi hj h)
    adjoining := fun i j hij hi hj hn => near ((order i j).mp hij) hi hj (fun h => hn (e.injective h))
    edgesTop := fun i j hi hij hn => hn (e.injective (edge_top hi ((order i j).mp hij)))
    firstPos := by simp [pos,first]
    lastHeight := by simp [height,last]
    lastPos := fun i hi => by simpa [Function.comp_apply] using (last_pos hi : pos (e i) ≤ _)
    different := by
      intro h
      have h₀ := congrArg (pos ∘ e) h
      simp [pos,first,last] at h₀
      omega
    pins := fun i c h => by
      simp only [Function.comp_apply, ← e.apply_eq_iff_eq, Equiv.apply_symm_apply]
      exact pins_compatible h }
  let W : Routes x (pin ∘ e) p r := {
    word := fun t => e.symm (.word t)
    edge := fun t => e.symm (.edge t)
    arm := fun t a j => e.symm (.arm t a j)
    arm_mono := fun t a i j hi => by simp [order,Rel,hi]
    arm_word := fun t a j => by simp [order,Rel]
    left := fun t => by simp [order,Rel]
    right := fun t => by simp [order,Rel]
    arm_pin := fun t a j => by simp [pin]
    first_pin := by simp [pin]
    last_pin := by simp [pin, Nat.ne_of_gt hp] }
  exact finish r A marked W.no_fit

end PEqualNP.Outside.L_lib_1308.DervishAbstractRows1308

namespace PEqualNP.Outside.L_lib_1308

namespace Layout1308Geom

def railCoord (k p : Nat) (w : Fin k → Bool) (i : Fin k) : Fin (2*k+p) :=
  ⟨2*i.val + (w i).toNat, by
    have hb : (w i).toNat ≤ 1 := by cases w i <;> decide
    omega⟩

def rails (k p : Nat) (w : Fin k → Bool) : Finset (Fin (2*k+p)) :=
  Finset.univ.image (railCoord k p w)

lemma mem_rails_iff (k p : Nat) (w : Fin k → Bool) (j : Fin (2*k+p)) :
    j ∈ rails k p w ↔ ∃ i : Fin k, j.val = 2*i.val + (w i).toNat := by
  simp only [rails, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, congrArg Fin.val hi.symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Fin.ext hi.symm⟩

lemma rails_coord (k p : Nat) (w : Fin k → Bool) (i : Fin k) :
    railCoord k p w i ∈ rails k p w := by
  exact (mem_rails_iff k p w _).2 ⟨i, rfl⟩

lemma rails_subset_iff (k p : Nat) (w v : Fin k → Bool) :
    rails k p w ⊆ rails k p v ↔ w = v := by
  constructor
  · intro h
    funext i
    obtain ⟨j, hj⟩ := (mem_rails_iff k p v _).1 (h (rails_coord k p w i))
    change 2*i.val + (w i).toNat = 2*j.val + (v j).toNat at hj
    have hcoord : j = i := by
      apply Fin.ext
      have hb : (w i).toNat ≤ 1 := by cases w i <;> decide
      have hc : (v j).toNat ≤ 1 := by cases v j <;> decide
      omega
    subst j
    have hbool : (w i).toNat = (v i).toNat := by omega
    cases hw : w i <;> cases hv : v i <;> simp_all
  · rintro rfl
    exact Finset.Subset.rfl

lemma rails_injective (k p : Nat) : Function.Injective (rails k p) := by
  intro w v h
  exact (rails_subset_iff k p w v).1 (le_of_eq h)

lemma rails_incomparable (k p : Nat) {w v : Fin k → Bool} (h : w ≠ v) :
    ¬ rails k p w ⊆ rails k p v ∧ ¬ rails k p v ⊆ rails k p w := by
  exact ⟨fun hw => h ((rails_subset_iff k p w v).1 hw),
    fun hv => h ((rails_subset_iff k p v w).1 hv).symm⟩

lemma rails_coord_union (k p : Nat) (w v u : Fin k → Bool)
    (h : rails k p u ⊆ rails k p w ∪ rails k p v) (i : Fin k) :
    u i = w i ∨ u i = v i := by
  have hi := h (rails_coord k p u i)
  rw [Finset.mem_union] at hi
  rcases hi with hi | hi
  · obtain ⟨j, hj⟩ := (mem_rails_iff k p w _).1 hi
    change 2*i.val + (u i).toNat = 2*j.val + (w j).toNat at hj
    have hj' : j = i := by
      apply Fin.ext
      have hb : (u i).toNat ≤ 1 := by cases u i <;> decide
      have hc : (w j).toNat ≤ 1 := by cases w j <;> decide
      omega
    subst j
    left
    have hb : (u i).toNat = (w i).toNat := by omega
    cases hu : u i <;> cases hw : w i <;> simp_all
  · obtain ⟨j, hj⟩ := (mem_rails_iff k p v _).1 hi
    change 2*i.val + (u i).toNat = 2*j.val + (v j).toNat at hj
    have hj' : j = i := by
      apply Fin.ext
      have hb : (u i).toNat ≤ 1 := by cases u i <;> decide
      have hc : (v j).toNat ≤ 1 := by cases v j <;> decide
      omega
    subst j
    right
    have hb : (u i).toNat = (v i).toNat := by omega
    cases hu : u i <;> cases hv : v i <;> simp_all

lemma rails_union_endpoints (k p : Nat) (w v u : Fin k → Bool) (d : Fin k)
    (hagree : ∀ i : Fin k, i ≠ d → w i = v i)
    (h : rails k p u ⊆ rails k p w ∪ rails k p v) :
    u = w ∨ u = v := by
  rcases rails_coord_union k p w v u h d with hd | hd
  · left
    funext i
    by_cases hid : i = d
    · simpa [hid] using hd
    · rcases rails_coord_union k p w v u h i with hi | hi
      · exact hi
      · exact hi.trans (hagree i hid).symm
  · right
    funext i
    by_cases hid : i = d
    · simpa [hid] using hd
    · rcases rails_coord_union k p w v u h i with hi | hi
      · exact hi.trans (hagree i hid)
      · exact hi

lemma rails_below (k p : Nat) (w : Fin k → Bool) {j : Fin (2*k+p)}
    (h : j ∈ rails k p w) : j.val < 2*k := by
  obtain ⟨i, hi⟩ := (mem_rails_iff k p w j).1 h
  have hb : (w i).toNat ≤ 1 := by cases w i <;> decide
  omega

lemma rails_of_union_subset (k p : Nat) (w v : Fin k → Bool)
    (A B : Finset (Fin (2*k+p)))
    (hB : ∀ j ∈ B, 2*k ≤ j.val)
    (h : rails k p w ∪ A ⊆ rails k p v ∪ B) : w = v := by
  apply (rails_subset_iff k p w v).1
  intro j hj
  have hj' := h (Finset.mem_union_left A hj)
  rcases Finset.mem_union.mp hj' with hv | hb
  · exact hv
  · have hbelow := rails_below k p w hj
    have habove := hB j hb
    omega

lemma rails_of_union_two_subset (k p : Nat) (w v z : Fin k → Bool)
    (d : Fin k) (hagree : ∀ i : Fin k, i ≠ d → v i = z i)
    (A B : Finset (Fin (2*k+p))) (hB : ∀ j ∈ B, 2*k ≤ j.val)
    (h : rails k p w ∪ A ⊆ (rails k p v ∪ rails k p z) ∪ B) :
    w = v ∨ w = z := by
  apply rails_union_endpoints k p v z w d hagree
  intro j hj
  have hj' := h (Finset.mem_union_left A hj)
  rcases Finset.mem_union.mp hj' with hv | hb
  · exact hv
  · have hbelow := rails_below k p w hj
    have habove := hB j hb
    omega

def shared (k p : Nat) (ℓ : Nat) : Finset (Fin (2*k+p+2)) :=
  Finset.univ.filter (fun j => 2*k ≤ j.val ∧ j.val < 2*k+ℓ)

def selector (k p : Nat) (a : Fin 2) : Fin (2*k+p+2) :=
  ⟨2*k+p+a.val, by omega⟩

def word (k p : Nat) (w : Fin k → Bool) : Finset (Fin (2*k+p+2)) :=
  rails k (p+2) w ∪ shared k p p ∪ {selector k p 0, selector k p 1}

def arm (k p : Nat) (w : Fin k → Bool) (a : Fin 2) (ℓ : Nat) :
    Finset (Fin (2*k+p+2)) :=
  rails k (p+2) w ∪ shared k p ℓ ∪ {selector k p a}

lemma shared_below (k p ℓ : Nat) {j : Fin (2*k+p+2)} (h : j ∈ shared k p ℓ) :
    2*k ≤ j.val := by
  simpa [shared] using (Finset.mem_filter.mp h).2.1

lemma selector_above (k p : Nat) (a : Fin 2) :
    2*k ≤ (selector k p a).val := by
  simp only [selector]
  omega

lemma word_injective (k p : Nat) : Function.Injective (word k p) := by
  intro w v h
  apply rails_of_union_subset k (p+2) w v
    (shared k p p ∪ {selector k p 0, selector k p 1})
    (shared k p p ∪ {selector k p 0, selector k p 1})
  · intro j hj
    rcases Finset.mem_union.mp hj with hs | hs
    · exact shared_below k p p hs
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact selector_above k p 0
      · exact selector_above k p 1
  · simpa only [word, Finset.union_assoc] using (le_of_eq h)

lemma shared_mono (k p ℓ ℓ' : Nat) (h : ℓ ≤ ℓ') :
    shared k p ℓ ⊆ shared k p ℓ' := by
  intro j hj
  simp only [shared, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  omega

lemma arm_subset_word (k p : Nat) (w : Fin k → Bool) (a : Fin 2)
    (ℓ : Nat) (hℓ : ℓ ≤ p) : arm k p w a ℓ ⊆ word k p w := by
  intro j hj
  simp only [arm, word, Finset.mem_union] at hj ⊢
  rcases hj with (hr | hs) | ha
  · exact Or.inl (Or.inl hr)
  · exact Or.inl (Or.inr (shared_mono k p ℓ p hℓ hs))
  · have ha' : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    rcases ha' with rfl | rfl
    · exact Or.inr (by simpa only [Finset.mem_singleton, Finset.mem_insert] using Or.inl ha)
    · exact Or.inr (by simpa only [Finset.mem_singleton, Finset.mem_insert] using Or.inr ha)

lemma arm_mono (k p : Nat) (w : Fin k → Bool) (a : Fin 2)
    (ℓ ℓ' : Nat) (h : ℓ ≤ ℓ') : arm k p w a ℓ ⊆ arm k p w a ℓ' := by
  intro j hj
  simp only [arm, Finset.mem_union] at hj ⊢
  rcases hj with (hr | hs) | ha
  · exact Or.inl (Or.inl hr)
  · exact Or.inl (Or.inr (shared_mono k p ℓ ℓ' h hs))
  · exact Or.inr ha

def full (k p : Nat) : Finset (Fin (2*k+p+2)) :=
  shared k p p ∪ {selector k p 0, selector k p 1}

def edge (k p : Nat) (w v : Fin k → Bool) : Finset (Fin (2*k+p+2)) :=
  (rails k (p+2) w ∪ rails k (p+2) v) ∪ full k p

lemma full_above (k p : Nat) {j : Fin (2*k+p+2)} (hj : j ∈ full k p) :
    2*k ≤ j.val := by
  rcases Finset.mem_union.mp hj with hs | hs
  · exact shared_below k p p hs
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact selector_above k p 0
    · exact selector_above k p 1

lemma word_subset_edge_left (k p : Nat) (w v : Fin k → Bool) :
    word k p w ⊆ edge k p w v := by
  intro j hj
  simp only [word, edge, full, Finset.mem_union] at hj ⊢
  rcases hj with (hr | hs) | he
  · exact Or.inl (Or.inl hr)
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr he)

lemma word_subset_edge_right (k p : Nat) (w v : Fin k → Bool) :
    word k p v ⊆ edge k p w v := by
  intro j hj
  simp only [word, edge, full, Finset.mem_union] at hj ⊢
  rcases hj with (hr | hs) | he
  · exact Or.inl (Or.inr hr)
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr he)

lemma word_to_edge_endpoints (k p : Nat) (u w v : Fin k → Bool) (d : Fin k)
    (hagree : ∀ i, i ≠ d → w i = v i) (h : word k p u ⊆ edge k p w v) :
    u = w ∨ u = v := by
  apply rails_of_union_two_subset k (p+2) u w v d hagree (full k p) (full k p)
    (fun j hj => full_above k p hj)
  simpa only [word, edge, full, Finset.union_assoc] using h

lemma railCoord_not_mem_of_ne (k p : Nat) (w v : Fin k → Bool) (d : Fin k)
    (hd : w d ≠ v d) : railCoord k p v d ∉ rails k p w := by
  intro hm
  obtain ⟨i, hi⟩ := (mem_rails_iff k p w _).mp hm
  change 2*d.val + (v d).toNat = 2*i.val + (w i).toNat at hi
  have hb : (v d).toNat ≤ 1 := by cases v d <;> decide
  have hc : (w i).toNat ≤ 1 := by cases w i <;> decide
  have heq : i = d := by apply Fin.ext; omega
  subst i
  have hv : (v d).toNat = (w d).toNat := by omega
  cases hvv : v d <;> cases hww : w d <;> simp_all

lemma railCoord_not_mem_full (k p : Nat) (w : Fin k → Bool) (d : Fin k) :
    railCoord k (p+2) w d ∉ full k p := by
  intro hm
  have ha := full_above k p hm
  have hb := rails_below k (p+2) w (rails_coord k (p+2) w d)
  omega

lemma edge_ne_word_left (k p : Nat) (w v : Fin k → Bool)
    (h : w ≠ v) : edge k p w v ≠ word k p w := by
  obtain ⟨d, hd⟩ : ∃ d, w d ≠ v d := by
    by_contra hn
    apply h
    funext i
    by_contra hi
    exact hn ⟨i, hi⟩
  intro he
  have hm : railCoord k (p+2) v d ∈ edge k p w v := by
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (rails_coord k (p+2) v d))
  rw [he] at hm
  simp only [word, Finset.mem_union] at hm
  rcases hm with (hr | hs) | hs
  · exact railCoord_not_mem_of_ne k (p+2) w v d hd hr
  · exact railCoord_not_mem_full k p v d (Finset.mem_union_left _ hs)
  · exact railCoord_not_mem_full k p v d (Finset.mem_union_right _ hs)

lemma arm_to_word_root (k p : Nat) (u v : Fin k → Bool) (a : Fin 2) (ℓ : Nat)
    (h : arm k p u a ℓ ⊆ word k p v) : u = v := by
  apply rails_of_union_subset k (p+2) u v
    (shared k p ℓ ∪ {selector k p a}) (full k p)
    (fun j hj => full_above k p hj)
  simpa only [arm, word, full, Finset.union_assoc] using h

lemma word_subset_iff (k p : Nat) (u v : Fin k → Bool) :
    word k p u ⊆ word k p v ↔ u = v := by
  constructor
  · intro h
    apply rails_of_union_subset k (p+2) u v (full k p) (full k p)
      (fun j hj => full_above k p hj)
    simpa only [word, full, Finset.union_assoc] using h
  · rintro rfl
    exact Finset.Subset.rfl

lemma word_to_edge_iff (k p : Nat) (u w v : Fin k → Bool) (d : Fin k)
    (hagree : ∀ i, i ≠ d → w i = v i) :
    word k p u ⊆ edge k p w v ↔ u = w ∨ u = v := by
  constructor
  · exact word_to_edge_endpoints k p u w v d hagree
  · intro hu
    rcases hu with huw | huv
    · rw [huw]
      exact word_subset_edge_left k p w v
    · rw [huv]
      exact word_subset_edge_right k p w v

lemma arm_to_edge_iff (k p : Nat) (u w v : Fin k → Bool) (d : Fin k)
    (hagree : ∀ i, i ≠ d → w i = v i) (a : Fin 2) (ℓ : Nat) (hℓ : ℓ ≤ p) :
    arm k p u a ℓ ⊆ edge k p w v ↔ u = w ∨ u = v := by
  constructor
  · intro h
    apply rails_of_union_two_subset k (p+2) u w v d hagree
      (shared k p ℓ ∪ {selector k p a}) (full k p)
      (fun j hj => full_above k p hj)
    simpa only [arm, edge, Finset.union_assoc] using h
  · intro hu
    rcases hu with huw | huv
    · rw [huw]
      exact (arm_subset_word k p w a ℓ hℓ).trans (word_subset_edge_left k p w v)
    · rw [huv]
      exact (arm_subset_word k p v a ℓ hℓ).trans (word_subset_edge_right k p w v)

lemma selector_mem_arm_iff (k p : Nat) (w : Fin k → Bool) (a b : Fin 2)
    (ℓ : Nat) (hℓ : ℓ ≤ p) :
    selector k p a ∈ arm k p w b ℓ ↔ a = b := by
  constructor
  · intro h
    simp only [arm, Finset.mem_union, Finset.mem_singleton] at h
    rcases h with (hr | hs) | he
    · have hb := rails_below k (p+2) w hr
      have ha := selector_above k p a
      omega
    · have hs' := (Finset.mem_filter.mp hs).2.2
      change (selector k p a).val < 2*k+ℓ at hs'
      simp only [selector] at hs'
      omega
    · apply Fin.ext
      have hv := congrArg Fin.val he
      simp only [selector] at hv
      omega
  · rintro rfl
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

lemma selector_mem_word (k p : Nat) (w : Fin k → Bool) (a : Fin 2) :
    selector k p a ∈ word k p w := by
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  rcases ha with rfl | rfl
  · simp [word]
  · simp [word]

lemma word_not_subset_arm (k p : Nat) (w v : Fin k → Bool) (a : Fin 2)
    (ℓ : Nat) (hℓ : ℓ ≤ p) : ¬ word k p w ⊆ arm k p v a ℓ := by
  intro h
  have h0 := (selector_mem_arm_iff k p v 0 a ℓ hℓ).mp (h (selector_mem_word k p w 0))
  have h1 := (selector_mem_arm_iff k p v 1 a ℓ hℓ).mp (h (selector_mem_word k p w 1))
  have : (0 : Fin 2) = 1 := h0.trans h1.symm
  exact Fin.zero_ne_one this

lemma arm_to_arm_root (k p : Nat) (u v : Fin k → Bool) (a b : Fin 2)
    (ℓ ℓ' : Nat) (h : arm k p u a ℓ ⊆ arm k p v b ℓ') : u = v := by
  apply rails_of_union_subset k (p+2) u v
    (shared k p ℓ ∪ {selector k p a})
    (shared k p ℓ' ∪ {selector k p b})
  · intro j hj
    rcases Finset.mem_union.mp hj with hs | hs
    · exact shared_below k p ℓ' hs
    · have he := Finset.mem_singleton.mp hs
      rw [he]
      exact selector_above k p b
  · simpa only [arm, Finset.union_assoc] using h

lemma arm_subset_iff (k p : Nat) (u v : Fin k → Bool) (a b : Fin 2)
    (ℓ ℓ' : Nat) (hℓ : ℓ ≤ p) (hℓ' : ℓ' ≤ p) :
    arm k p u a ℓ ⊆ arm k p v b ℓ' ↔ u = v ∧ a = b ∧ ℓ ≤ ℓ' := by
  constructor
  · intro h
    have huw := arm_to_arm_root k p u v a b ℓ ℓ' h
    have hab := (selector_mem_arm_iff k p v a b ℓ' hℓ').mp
      (h (by simp [arm] : selector k p a ∈ arm k p u a ℓ))
    refine ⟨huw, hab, ?_⟩
    by_contra hn
    have hlt : ℓ' < ℓ := by omega
    let j : Fin (2*k+p+2) := ⟨2*k+ℓ', by omega⟩
    have hj : j ∈ arm k p u a ℓ := by
      simp only [arm, Finset.mem_union]
      exact Or.inl (Or.inr (by simp [shared, j]; omega))
    have hj' := h hj
    simp only [arm, Finset.mem_union] at hj'
    rcases hj' with (hr | hs) | he
    · have hb := rails_below k (p+2) v hr
      simp only [j] at hb
      omega
    · have hs' := (Finset.mem_filter.mp hs).2.2
      simp only [j] at hs'
      omega
    · have he' := congrArg Fin.val (Finset.mem_singleton.mp he)
      simp only [j, selector] at he'
      omega
  · rintro ⟨hu, ha, hlen⟩
    rw [hu, ha]
    exact arm_mono k p v b ℓ ℓ' hlen

lemma arm_to_word_iff (k p : Nat) (u v : Fin k → Bool) (a : Fin 2)
    (ℓ : Nat) (hℓ : ℓ ≤ p) : arm k p u a ℓ ⊆ word k p v ↔ u = v := by
  constructor
  · exact arm_to_word_root k p u v a ℓ
  · intro hu
    rw [hu]
    exact arm_subset_word k p v a ℓ hℓ

lemma edge_not_subset_word (k p : Nat) (w v u : Fin k → Bool)
    (h : w ≠ v) : ¬ edge k p w v ⊆ word k p u := by
  intro he
  have hw := (word_subset_iff k p w u).mp
    ((word_subset_edge_left k p w v).trans he)
  have hv := (word_subset_iff k p v u).mp
    ((word_subset_edge_right k p w v).trans he)
  exact h (hw.trans hv.symm)

lemma edge_not_subset_arm (k p : Nat) (w v u : Fin k → Bool) (a : Fin 2)
    (ℓ : Nat) (hℓ : ℓ ≤ p) : ¬ edge k p w v ⊆ arm k p u a ℓ := by
  intro he
  exact word_not_subset_arm k p w u a ℓ hℓ
    ((word_subset_edge_left k p w v).trans he)

lemma edge_swap (k p : Nat) (w v : Fin k → Bool) :
    edge k p w v = edge k p v w := by
  simp only [edge, Finset.union_comm (rails k (p+2) w)]

lemma edge_subset_iff (k p : Nat) (w v u z : Fin k → Bool)
    (hwv : w ≠ v) (d : Fin k) (hagree : ∀ i, i ≠ d → u i = z i) :
    edge k p w v ⊆ edge k p u z ↔
      (w = u ∧ v = z) ∨ (w = z ∧ v = u) := by
  constructor
  · intro he
    have hw := (word_to_edge_iff k p w u z d hagree).mp
      ((word_subset_edge_left k p w v).trans he)
    have hv := (word_to_edge_iff k p v u z d hagree).mp
      ((word_subset_edge_right k p w v).trans he)
    rcases hw with hw | hw <;> rcases hv with hv | hv
    · exact (hwv (hw.trans hv.symm)).elim
    · exact Or.inl ⟨hw, hv⟩
    · exact Or.inr ⟨hw, hv⟩
    · exact (hwv (hw.trans hv.symm)).elim
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Finset.Subset.rfl
    · rw [edge_swap]

end Layout1308Geom

namespace Layout1308Gray

def differsAt {k : Nat} (w v : Fin k → Bool) (d : Fin k) : Prop :=
  w d ≠ v d ∧ ∀ i, i ≠ d → w i = v i

def extend {k : Nat} (w : Fin k → Bool) (b : Bool) : Fin (k+1) → Bool :=
  Fin.snoc w b

lemma extend_injective {k : Nat} (b : Bool) :
    Function.Injective (fun w : Fin k → Bool => extend w b) := by
  intro a c h
  exact (Fin.snoc_inj.mp h).1

def grayWords : (k : Nat) → List (Fin k → Bool)
  | 0 => [fun i => Fin.elim0 i]
  | k+1 =>
    ((grayWords k).map (extend · false)) ++
    ((grayWords k).reverse.map (extend · true))

lemma grayWords_length (k : Nat) : (grayWords k).length = 2^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [grayWords, List.length_append, List.length_map, List.length_reverse, ih,
      pow_succ]
    omega

lemma grayWords_nodup (k : Nat) : (grayWords k).Nodup := by
  induction k with
  | zero => simp [grayWords]
  | succ k ih =>
    unfold grayWords
    apply List.Nodup.append
    · exact ih.map (extend_injective false)
    · exact (List.nodup_reverse.mpr ih).map (extend_injective true)
    · intro w hw hv
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      obtain ⟨u', hu', he⟩ := List.mem_map.mp hv
      have he' := congrFun he (Fin.last k)
      simpa [extend] using he'

def near {k : Nat} (w v : Fin k → Bool) : Prop :=
  ∃ d : Fin k, differsAt w v d

lemma near_symm {k : Nat} {w v : Fin k → Bool} (h : near w v) : near v w := by
  obtain ⟨d, hd, hs⟩ := h
  exact ⟨d, Ne.symm hd, fun i hi => (hs i hi).symm⟩

lemma near_extend {k : Nat} {w v : Fin k → Bool} (h : near w v) (b : Bool) :
    near (extend w b) (extend v b) := by
  obtain ⟨d, hd, hs⟩ := h
  refine ⟨d.castSucc, ?_, ?_⟩
  · simpa [differsAt, extend] using hd
  · intro i hi
    induction i using Fin.lastCases with
    | last => simp [extend]
    | cast i =>
      have hid : i ≠ d := by
        intro he
        exact hi (congrArg Fin.castSucc he)
      simpa [extend] using hs i hid

lemma near_switch {k : Nat} (w : Fin k → Bool) :
    near (extend w false) (extend w true) := by
  refine ⟨Fin.last k, ?_, ?_⟩
  · simp [extend]
  · intro i hi
    induction i using Fin.lastCases with
    | last => exact (hi rfl).elim
    | cast i => simp [extend]

lemma grayWords_chain (k : Nat) : (grayWords k).IsChain near := by
  induction k with
  | zero => simp [grayWords, List.isChain_singleton]
  | succ k ih =>
    unfold grayWords
    apply List.IsChain.append
    · exact List.isChain_map_of_isChain (extend · false)
        (fun a b h => near_extend h false) ih
    · apply List.isChain_map_of_isChain (extend · true)
        (fun a b h => near_extend h true)
      exact List.isChain_reverse.mpr
        (ih.imp (fun {a b} h => near_symm h))
    · intro x hx y hy
      have hex : ∃ w, (grayWords k).getLast? = some w := by
        cases he : grayWords k with
        | nil =>
          have hl := grayWords_length k
          rw [he] at hl
          simp only [List.length_nil] at hl
          have hp : 0 < 2^k := pow_pos (by omega) k
          omega
        | cons w ws =>
          exact ⟨ws.getLast?.getD w, by simp [he, List.getLast?_cons]⟩
      obtain ⟨w, hw⟩ := hex
      simp only [List.getLast?_map, List.head?_map, List.head?_reverse,
        hw, Option.map_some, Option.mem_some_iff] at hx hy
      subst x
      subst y
      exact near_switch w

def grayWord (k : Nat) (t : Fin (2^k)) : Fin k → Bool :=
  (grayWords k).get ⟨t.val, by rw [grayWords_length]; exact t.isLt⟩

lemma grayWord_injective (k : Nat) : Function.Injective (grayWord k) := by
  intro s t h
  have hi := (List.nodup_iff_injective_get.mp (grayWords_nodup k))
    (show (grayWords k).get ⟨s.val, by rw [grayWords_length]; exact s.isLt⟩ =
      (grayWords k).get ⟨t.val, by rw [grayWords_length]; exact t.isLt⟩ from h)
  exact Fin.ext (congrArg (fun j : Fin (grayWords k).length => j.val) hi)

lemma grayWord_near (k : Nat) (t : Fin (2^k-1)) :
    near (grayWord k ⟨t.val, by omega⟩)
      (grayWord k ⟨t.val+1, by omega⟩) := by
  have hlt : t.val+1 < (grayWords k).length := by
    rw [grayWords_length]
    omega
  have hpair := (List.isChain_iff_getElem.mp (grayWords_chain k)) t.val hlt
  simpa only [grayWord, List.get_eq_getElem] using hpair

end Layout1308Gray

end PEqualNP.Outside.L_lib_1308

namespace PEqualNP.Outside.L_lib_1308.DervishConcreteRows1308
open Layout1308Geom Layout1308Gray DervishAbstractRows1308

def gray (k : ℕ) (i : Fin ((2^k-1)+1)) : Fin k → Bool :=
  grayWord k ⟨i.val,by have hi := i.isLt; have := Nat.two_pow_pos k; omega⟩

def eleft {k : ℕ} (i : Fin (2^k-1)) : Fin ((2^k-1)+1) := ⟨i.val,by have := i.isLt; omega⟩
def eright {k : ℕ} (i : Fin (2^k-1)) : Fin ((2^k-1)+1) := ⟨i.val+1,by have := i.isLt; omega⟩

@[simp] theorem gray_eq {k : ℕ} {i j : Fin ((2^k-1)+1)} : gray k i = gray k j ↔ i = j := by
  constructor
  · intro h
    exact Fin.ext (congrArg (fun v : Fin (2^k) => v.val) (grayWord_injective k h))
  · rintro rfl
    rfl

private theorem gray_ne {k : ℕ} (i : Fin (2^k-1)) : gray k (eleft i) ≠ gray k (eright i) := by
  intro h
  have := congrArg Fin.val (gray_eq.mp h)
  simp only [eleft, eright] at this
  omega

private theorem gray_near {k : ℕ} (i : Fin (2^k-1)) : near (gray k (eleft i)) (gray k (eright i)) :=
  grayWord_near k i

def realize (k r : ℕ) : Row (2^k-1) r → Finset (Fin (2*k+(2^r-1)+2))
  | .word t => word k (2^r-1) (gray k t)
  | .edge t => edge k (2^r-1) (gray k (eleft t)) (gray k (eright t))
  | .arm t a j => arm k (2^r-1) (gray k t) a j.val

theorem realize_order (k r : ℕ) (i j : Row (2^k-1) r) :
    realize k r i ⊆ realize k r j ↔ DervishAbstractRows1308.Rel i j := by
  cases i with
  | word t =>
    cases j with
    | word u => simp [realize, DervishAbstractRows1308.Rel, word_subset_iff]
    | edge u =>
      obtain ⟨d, hd, h⟩ := gray_near u
      rw [realize,realize,word_to_edge_iff _ _ _ _ _ d h]
      simp [gray_eq,DervishAbstractRows1308.Rel,Fin.ext_iff,eleft,eright]
    | arm u b l =>
      simpa only [realize,DervishAbstractRows1308.Rel,iff_false] using word_not_subset_arm _ _ (gray k t) (gray k u) b l.val (Nat.le_of_lt l.isLt)
  | edge t =>
    cases j with
    | word u =>
      simpa only [realize,DervishAbstractRows1308.Rel,iff_false] using edge_not_subset_word _ _ _ _ (gray k u) (gray_ne t)
    | edge u =>
      obtain ⟨d, hd, h⟩ := gray_near u
      rw [realize,realize,edge_subset_iff _ _ _ _ _ _ (gray_ne t) d h]
      simp only [gray_eq,DervishAbstractRows1308.Rel,Fin.ext_iff,eleft,eright]
      omega
    | arm u b l =>
      simpa only [realize,DervishAbstractRows1308.Rel,iff_false] using edge_not_subset_arm _ _ _ _ (gray k u) b l.val (Nat.le_of_lt l.isLt)
  | arm t a l =>
    cases j with
    | word u =>
      rw [realize,realize,arm_to_word_iff _ _ _ _ _ _ (Nat.le_of_lt l.isLt)]
      simp [DervishAbstractRows1308.Rel]
    | edge u =>
      obtain ⟨d, hd, h⟩ := gray_near u
      rw [realize,realize,arm_to_edge_iff _ _ _ _ _ d h _ _ (Nat.le_of_lt l.isLt)]
      simp [DervishAbstractRows1308.Rel,Fin.ext_iff,eleft,eright]
    | arm u b j =>
      rw [realize,realize,arm_subset_iff _ _ _ _ _ _ _ _ (Nat.le_of_lt l.isLt) (Nat.le_of_lt j.isLt)]
      simp only [DervishAbstractRows1308.Rel, Fin.le_def, gray_eq]

theorem realize_inj (k r : ℕ) : Function.Injective (realize k r) := by
  intro i j h
  have a := (realize_order k r i j).mp (by rw [h])
  have b := (realize_order k r j i).mp (by rw [h])
  cases i <;> cases j <;> simp_all [DervishAbstractRows1308.Rel]
  exact Fin.le_antisymm a.2.2 b

end PEqualNP.Outside.L_lib_1308.DervishConcreteRows1308

namespace PEqualNP.Outside.L_lib_1308

namespace Layout1308Index

private lemma pow_two_ge_two {k : Nat} (hk : 1 ≤ k) : 2 ≤ 2^k := by
  calc 2 = 2^1 := by norm_num
    _ ≤ 2^k := pow_le_pow_right₀ (by norm_num) hk

def wordIdx (k q : Nat) (hq : 1 ≤ q) (hk : 1 ≤ k) (t : Fin (2^k)) :
    Fin (2*q*2^k-1) := by
  have ht : t.val < 2^k := t.isLt
  have hp : 0 < 2*q := by omega
  have hm := Nat.mul_le_mul_left (2*q) (show t.val+1 ≤ 2^k by omega)
  have heq : 2*q*(t.val+1) = 2*q*t.val+2*q := by ring
  rw [heq] at hm
  refine ⟨2*q*t.val, ?_⟩
  omega

def edgeIdx (k q : Nat) (hq : 1 ≤ q) (hk : 1 ≤ k) (t : Fin (2^k-1)) :
    Fin (2*q*2^k-1) := by
  have ht : t.val < 2^k-1 := t.isLt
  have hp : 0 < 2*q := by omega
  have hm := Nat.mul_le_mul_left (2*q) (show t.val+2 ≤ 2^k by omega)
  have heq : 2*q*(t.val+2) = 2*q*t.val+4*q := by ring
  rw [heq] at hm
  refine ⟨2*q*t.val+2*q-1, ?_⟩
  omega

lemma wordIdx_inj (k q : Nat) (hq : 1 ≤ q) (hk : 1 ≤ k) :
    Function.Injective (wordIdx k q hq hk) := by
  intro s t h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 2*q*s.val = 2*q*t.val at hv
  have hp : 0 < 2*q := by omega
  nlinarith

lemma edgeIdx_inj (k q : Nat) (hq : 1 ≤ q) (hk : 1 ≤ k) :
    Function.Injective (edgeIdx k q hq hk) := by
  intro s t h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 2*q*s.val+2*q-1 = 2*q*t.val+2*q-1 at hv
  have hp : 0 < 2*q := by omega
  have hv' : 2*q*s.val = 2*q*t.val := by omega
  nlinarith

lemma word_edge_disjoint (k q : Nat) (hq : 1 ≤ q) (hk : 1 ≤ k) :
    Disjoint (Finset.univ.image (wordIdx k q hq hk))
      (Finset.univ.image (edgeIdx k q hq hk)) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hi
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hj
  have hval := congrArg Fin.val (hs.trans ht.symm)
  dsimp [wordIdx, edgeIdx] at hval
  have hq' : 2 ≤ 2*q := by omega
  by_cases hst : s.val ≤ t.val
  · have hm := Nat.mul_le_mul_left (2*q) hst
    omega
  · have hm := Nat.mul_le_mul_left (2*q) (show t.val+1 ≤ s.val by omega)
    have heq : 2*q*(t.val+1) = 2*q*t.val+2*q := by ring
    rw [heq] at hm
    omega

def marked (k q : Nat) (hq : 1 ≤ q) (hk : 1 ≤ k) :
    Finset (Fin (2*q*2^k-1)) :=
  Finset.univ.image (wordIdx k q hq hk) ∪
    Finset.univ.image (edgeIdx k q hq hk)

lemma marked_card (k q : Nat) (hq : 1 ≤ q) (hk : 1 ≤ k) :
    (marked k q hq hk).card = 2^(k+1)-1 := by
  rw [marked, Finset.card_union_of_disjoint (word_edge_disjoint k q hq hk)]
  rw [Finset.card_image_of_injective _ (wordIdx_inj k q hq hk),
    Finset.card_image_of_injective _ (edgeIdx_inj k q hq hk)]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [pow_succ]
  omega

def armIdx (k q : Nat) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (t : Fin (2^k)) (a : Fin 2) (l : Fin (q-1)) : Fin (2*q*2^k-1) := by
  have ht : t.val < 2^k := t.isLt
  have hl : l.val < q-1 := l.isLt
  have ha : a.val < 2 := a.isLt
  have hm := Nat.mul_le_mul_left (2*q) (show t.val+1 ≤ 2^k by omega)
  have heq : 2*q*(t.val+1) = 2*q*t.val+2*q := by ring
  rw [heq] at hm
  refine ⟨2*q*t.val+1+2*l.val+a.val, ?_⟩
  omega

lemma armIdx_after_word (k q : Nat) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (t : Fin (2^k)) (a : Fin 2) (l : Fin (q-1)) :
    (wordIdx k q hq hk t).val < (armIdx k q hq hk t a l).val := by
  simp only [wordIdx, armIdx]
  omega

lemma armIdx_before_next_edge (k q : Nat) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (t : Fin (2^k-1)) (a : Fin 2) (l : Fin (q-1)) :
    (armIdx k q hq hk ⟨t.val, by omega⟩ a l).val <
    (edgeIdx k q hq hk t).val := by
  simp only [armIdx, edgeIdx]
  have hl := l.isLt
  have ha := a.isLt
  omega

lemma index_cases (k q : Nat) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (i : Fin (2*q*2^k-1)) :
    (∃ t : Fin (2^k), i = wordIdx k q hq hk t) ∨
    (∃ (t : Fin (2^k)) (a : Fin 2) (l : Fin (q-1)),
      i = armIdx k q hq hk t a l) ∨
    (∃ t : Fin (2^k-1), i = edgeIdx k q hq hk t) := by
  let B := 2*q
  let W := 2^k
  have hB : 0 < B := by dsimp [B]; omega
  have hM : i.val < B*W-1 := i.isLt
  have hW : i.val / B < W := by
    apply (Nat.div_lt_iff_lt_mul hB).mpr
    calc i.val < B*W := by omega
      _ = W*B := Nat.mul_comm B W
  let t : Fin W := ⟨i.val/B, hW⟩
  have hs : i.val % B < B := Nat.mod_lt _ hB
  have hdecomp : i.val = B*(i.val/B)+i.val % B := by
    calc i.val = i.val % B + B*(i.val/B) := (Nat.mod_add_div i.val B).symm
      _ = B*(i.val/B)+i.val % B := Nat.add_comm _ _
  by_cases h0 : i.val % B = 0
  · left
    refine ⟨t, ?_⟩
    apply Fin.ext
    dsimp [wordIdx, t, W, B] at *
    omega
  right
  by_cases he : i.val % B = B-1
  · right
    have ht : i.val / B < W-1 := by
      by_contra hn
      have hh : W-1 ≤ i.val/B := by omega
      have hm := Nat.mul_le_mul_left B hh
      have hWpos : 1 ≤ W := by
        have hp : 0 < 2^k := pow_pos (by norm_num) k
        dsimp [W]
        omega
      have hmul : B*(W-1)+B = B*W := by
        calc B*(W-1)+B = B*((W-1)+1) := by ring
          _ = B*W := by rw [Nat.sub_add_cancel hWpos]
      omega
    refine ⟨⟨i.val / B, ht⟩, ?_⟩
    apply Fin.ext
    dsimp [edgeIdx, B, W] at *
    omega
  · left
    have hmid : 1 ≤ i.val % B ∧ i.val % B ≤ B-2 := by omega
    let u := i.val % B-1
    have hu : u < 2*(q-1) := by dsimp [u, B] at *; omega
    let l : Fin (q-1) := ⟨u/2, by
      apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
      simpa only [Nat.mul_comm] using hu⟩
    let a : Fin 2 := ⟨u%2, Nat.mod_lt _ (by omega)⟩
    refine ⟨t, a, l, ?_⟩
    have hud : u = 2*(u/2)+u%2 := by
      calc u = u%2+2*(u/2) := (Nat.mod_add_div u 2).symm
        _ = 2*(u/2)+u%2 := Nat.add_comm _ _
    apply Fin.ext
    dsimp [armIdx, a, l, t, u, B, W] at *
    omega

lemma armIdx_inj (k q : Nat) (hq : 1 ≤ q) (hk : 1 ≤ k)
    {t s : Fin (2^k)} {a b : Fin 2} {l h : Fin (q-1)}
    (he : armIdx k q hq hk t a l = armIdx k q hq hk s b h) :
    t = s ∧ a = b ∧ l = h := by
  have hv := congrArg Fin.val he
  change 2*q*t.val+1+2*l.val+a.val = 2*q*s.val+1+2*h.val+b.val at hv
  have hlt := l.isLt
  have hht := h.isLt
  have hat := a.isLt
  have hbt := b.isLt
  have hts : t.val = s.val := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hts | hst
    · have hm := Nat.mul_le_mul_left (2*q) (show t.val+1 ≤ s.val by omega)
      have heq : 2*q*(t.val+1) = 2*q*t.val+2*q := by ring
      rw [heq] at hm
      omega
    · have hm := Nat.mul_le_mul_left (2*q) (show s.val+1 ≤ t.val by omega)
      have heq : 2*q*(s.val+1) = 2*q*s.val+2*q := by ring
      rw [heq] at hm
      omega
  have hts' : t = s := Fin.ext hts
  subst s
  have hab : a.val = b.val := by omega
  have hlh : l.val = h.val := by omega
  exact ⟨rfl, Fin.ext hab, Fin.ext hlh⟩

lemma block_eq (B t s rem rem' : Nat) (hB : 0 < B)
    (hrem : rem < B) (hrem' : rem' < B)
    (he : B*t+rem = B*s+rem') : t = s ∧ rem = rem' := by
  have hts : t = s := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hm := Nat.mul_le_mul_left B (show t+1 ≤ s by omega)
      have hstep : B*(t+1) = B*t+B := by ring
      rw [hstep] at hm
      omega
    · have hm := Nat.mul_le_mul_left B (show s+1 ≤ t by omega)
      have hstep : B*(s+1) = B*s+B := by ring
      rw [hstep] at hm
      omega
  subst s
  exact ⟨rfl, by omega⟩

lemma wordIdx_ne_armIdx (k q : Nat) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (t s : Fin (2^k)) (a : Fin 2) (l : Fin (q-1)) :
    wordIdx k q hq hk t ≠ armIdx k q hq hk s a l := by
  intro he
  have hv := congrArg Fin.val he
  change 2*q*t.val = 2*q*s.val+1+2*l.val+a.val at hv
  have hrem : 1+2*l.val+a.val < 2*q := by
    have hl := l.isLt
    have ha := a.isLt
    omega
  have hh := block_eq (2*q) t.val s.val 0 (1+2*l.val+a.val) (by omega)
    (by omega) hrem (by omega : 2*q*t.val+0 = 2*q*s.val+(1+2*l.val+a.val))
  omega

lemma edgeIdx_ne_armIdx (k q : Nat) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (t : Fin (2^k-1)) (s : Fin (2^k)) (a : Fin 2) (l : Fin (q-1)) :
    edgeIdx k q hq hk t ≠ armIdx k q hq hk s a l := by
  intro he
  have hv := congrArg Fin.val he
  change 2*q*t.val+2*q-1 = 2*q*s.val+1+2*l.val+a.val at hv
  have hrem : 1+2*l.val+a.val < 2*q-1 := by
    have hl := l.isLt
    have ha := a.isLt
    omega
  have hh := block_eq (2*q) t.val s.val (2*q-1) (1+2*l.val+a.val)
    (by omega) (by omega) (by omega) (by omega :
      2*q*t.val+(2*q-1) = 2*q*s.val+(1+2*l.val+a.val))
  omega

lemma wordIdx_ne_edgeIdx (k q : Nat) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (t : Fin (2^k)) (s : Fin (2^k-1)) :
    wordIdx k q hq hk t ≠ edgeIdx k q hq hk s := by
  intro he
  have hv := congrArg Fin.val he
  change 2*q*t.val = 2*q*s.val+2*q-1 at hv
  have hh := block_eq (2*q) t.val s.val 0 (2*q-1)
    (by omega) (by omega) (by omega) (by omega :
      2*q*t.val+0 = 2*q*s.val+(2*q-1))
  omega

end Layout1308Index

end PEqualNP.Outside.L_lib_1308

namespace PEqualNP.Outside.L_lib_1308.DervishIndexEquiv1308
open DervishAbstractRows1308 Layout1308Index DervishConcreteRows1308

private theorem one_le_pow (k : ℕ) : 1 ≤ 2^k := Nat.two_pow_pos k

def wide (k : ℕ) (t : Fin ((2^k-1)+1)) : Fin (2^k) :=
  ⟨t.val,by have := t.isLt; have := one_le_pow k; omega⟩

def thin (k : ℕ) (t : Fin (2^k)) : Fin ((2^k-1)+1) :=
  ⟨t.val,by have := t.isLt; have := one_le_pow k; omega⟩

@[simp] theorem wide_thin (k : ℕ) (t : Fin (2^k)) : wide k (thin k t) = t := rfl
private theorem wide_inj (k : ℕ) : Function.Injective (wide k) := fun _ _ h =>
  Fin.ext (congrArg (fun t : Fin (2^k) => t.val) h)

def turn {L : ℕ} (j : Fin L) : Fin L := ⟨L-1-j.val,by have := j.isLt; omega⟩
@[simp] theorem turn_turn {L : ℕ} (j : Fin L) : turn (turn j) = j := by
  apply Fin.ext
  have h := j.isLt
  simp only [turn]
  omega
private theorem turn_inj (L : ℕ) : Function.Injective (turn (L:=L)) := fun i j h =>
  calc i = turn (turn i) := (turn_turn i).symm
    _ = turn (turn j) := congrArg turn h
    _ = j := turn_turn j

def encode (k r : ℕ) (hk : 1 ≤ k) : Row (2^k-1) r → Fin (2*2^r*2^k-1)
  | .word t => wordIdx k (2^r) (one_le_pow r) hk (wide k t)
  | .edge t => edgeIdx k (2^r) (one_le_pow r) hk t
  | .arm t a j => armIdx k (2^r) (one_le_pow r) hk (wide k t) a (turn j)

theorem encode_inj (k r : ℕ) (hk : 1 ≤ k) : Function.Injective (encode k r hk) := by
  intro i j h
  cases i <;> cases j <;> simp only [encode] at h
  case word.word => exact congrArg Row.word (wide_inj k (wordIdx_inj k _ _ hk h))
  case word.edge => exact (wordIdx_ne_edgeIdx k _ _ hk _ _ h).elim
  case word.arm => exact (wordIdx_ne_armIdx k _ _ hk _ _ _ _ h).elim
  case edge.word => exact (wordIdx_ne_edgeIdx k _ _ hk _ _ h.symm).elim
  case edge.edge => exact congrArg Row.edge (edgeIdx_inj k _ _ hk h)
  case edge.arm => exact (edgeIdx_ne_armIdx k _ _ hk _ _ _ _ h).elim
  case arm.word => exact (wordIdx_ne_armIdx k _ _ hk _ _ _ _ h.symm).elim
  case arm.edge => exact (edgeIdx_ne_armIdx k _ _ hk _ _ _ _ h.symm).elim
  case arm.arm =>
    obtain ⟨ht,ha,hj⟩ := armIdx_inj k _ _ hk h
    rw [wide_inj k ht, ha, turn_inj _ hj]

theorem encode_surj (k r : ℕ) (hk : 1 ≤ k) : Function.Surjective (encode k r hk) := by
  intro i
  rcases index_cases k (2^r) (one_le_pow r) hk i with ⟨t,rfl⟩ | ⟨t,a,j,rfl⟩ | ⟨t,rfl⟩
  · exact ⟨.word (thin k t),by simp [encode]⟩
  · exact ⟨.arm (thin k t) a (turn j),by simp [encode]⟩
  · exact ⟨.edge t,rfl⟩

noncomputable def decodeEquiv (k r : ℕ) (hk : 1 ≤ k) : Fin (2*2^r*2^k-1) ≃ Row (2^k-1) r :=
  (Equiv.ofBijective (encode k r hk) ⟨encode_inj k r hk,encode_surj k r hk⟩).symm

@[simp] theorem decode_encode (k r : ℕ) (hk : 1 ≤ k) (b : Row (2^k-1) r) :
    decodeEquiv k r hk (encode k r hk b) = b :=
  (decodeEquiv k r hk).apply_symm_apply b

@[simp] theorem encode_decode (k r : ℕ) (hk : 1 ≤ k) (i : Fin (2*2^r*2^k-1)) :
    encode k r hk (decodeEquiv k r hk i) = i :=
  (decodeEquiv k r hk).symm_apply_apply i

def markedRows (k r : ℕ) (hk : 1 ≤ k) : Finset (Fin (2*2^r*2^k-1)) :=
  marked k (2^r) (one_le_pow r) hk

theorem marked_height (k r : ℕ) (hk : 1 ≤ k) (i : Fin (2*2^r*2^k-1))
    (hi : i ∈ markedRows k r hk) : height (decodeEquiv k r hk i) = 2^r-1 := by
  rcases Finset.mem_union.mp hi with hw | he
  · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hw
    have he : encode k r hk (.word (thin k t)) = wordIdx k (2^r) (one_le_pow r) hk t := by simp [encode]
    rw [← he,decode_encode]
    rfl
  · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp he
    change height (decodeEquiv k r hk (encode k r hk (.edge t))) = _
    rw [decode_encode]
    rfl

end PEqualNP.Outside.L_lib_1308.DervishIndexEquiv1308

namespace PEqualNP.Outside.L_lib_1308.DervishFinalAdapter1308
open DervishAbstractRows1308 DervishAssemble1308
open DervishIndexEquiv1308 DervishConcreteRows1308 Layout1308Index

noncomputable def table (k r : ℕ) (hk : 1 ≤ k) : Fin (2*2^r*2^k-1) → Finset (Fin (2*k+(2^r-1)+2)) :=
  realize k r ∘ decodeEquiv k r hk

private theorem table_order (k r : ℕ) (hk : 1 ≤ k) (i j : Fin (2*2^r*2^k-1)) :
    table k r hk i ⊆ table k r hk j ↔
      DervishAbstractRows1308.Rel (decodeEquiv k r hk i) (decodeEquiv k r hk j) :=
  realize_order k r _ _

def Covers {I : Type} {n : ℕ} (x : I → Finset (Fin n)) (i j : I) : Prop :=
  i ≠ j ∧ x i ⊆ x j ∧ ∀ z, x i ⊆ x z → x z ⊆ x j → z = i ∨ z = j

def Adj {I : Type} {n : ℕ} (x : I → Finset (Fin n)) (i j : I) : Prop :=
  Covers x i j ∨ Covers x j i

def HasseScores {m n : ℕ} (x : Fin m → Finset (Fin n)) : Prop :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  (∀ i : Fin m, (Finset.univ.filter (fun j : Fin m => j.val < i.val ∧ Adj x i j)).card =
      (if i.val = 0 then 0 else 1)) ∧
  (∀ i : Fin m, (Finset.univ.filter (fun j : Fin m => Adj x i j)).card ≤ 4)

theorem finish_exact (scores : ∀ k r (hk : 1 ≤ k), HasseScores (table k r hk)) : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ k r : Nat, 1 ≤ k →
  let q := 2^r
  let n := 2*k+(q-1)+2
  let m := 2*q*2^k-1
  ∃ (x : Fin m → Finset (Fin n)) (pin : Fin m → Option Bool) (F : Finset (Fin m)),
    Function.Injective x ∧ F.card = 2^(k+1)-1 ∧
    let cover := fun i j => i ≠ j ∧ x i ⊆ x j ∧
      ∀ z, x i ⊆ x z → x z ⊆ x j → z = i ∨ z = j
    let adj := fun i j => cover i j ∨ cover j i
    (∀ i : Fin m, (Finset.univ.filter (fun j : Fin m => j.val < i.val ∧ adj i j)).card =
      (if i.val = 0 then 0 else 1)) ∧
    (∀ i : Fin m, (Finset.univ.filter (fun j : Fin m => adj i j)).card ≤ 4) ∧
    let fits := fun (S : Finset (Fin m)) (b : Nat) =>
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin 2 → Nat),
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
        C.output < n+2+C.size ∧ (∀ a, tap a < n+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
        ∀ i ∈ S, let v := fun (a : Fin 2) =>
          (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false,true])).getD (tap a) false
          v 1 = !(v 0) ∧ ∀ c, pin i = some c → v 0 = c
    (∀ b, fits Finset.univ b ↔ r < b) ∧
    (∀ i ∈ F, fits (Finset.univ.erase i) r) ∧
    ∀ S : Finset (Fin m), ¬ fits S r → F ⊆ S) := by
  classical
  intro k r hk
  let x := table k r hk
  let F := markedRows k r hk
  let pc := DervishAbstractRows1308.pin ∘ decodeEquiv k r hk
  have hi : Function.Injective x := (realize_inj k r).comp (decodeEquiv k r hk).injective
  have hF : F.card = 2^(k+1)-1 := marked_card k (2^r) (Nat.two_pow_pos r) hk
  have gp : 0 < 2^k-1 := by
    have h : 2 ≤ 2^k := by
      calc 2 = 2^1 := by norm_num
        _ ≤ 2^k := pow_le_pow_right₀ (by norm_num) hk
    omega
  have model := @fit_rows _ _ _ _ inferInstance (fun i j => Classical.propDecidable (i=j))
    (decodeEquiv k r hk) x gp F (table_order k r hk) (marked_height k r hk)
  obtain ⟨early,deg⟩ := scores k r hk
  refine ⟨x,pc,F,hi,hF,early,deg,?_⟩
  have hinput (z : Finset (Fin (2*k+(2^r-1)+2))) :
      (List.ofFn (fun j => @decide (j ∈ z) (Classical.propDecidable _)) ++ [false,true]) =
        PEqualNP.Outside.L_lib_1308.CircuitDonor.Wiring1270.input z := by
    unfold PEqualNP.Outside.L_lib_1308.CircuitDonor.Wiring1270.input
    exact congrArg (fun f : Fin (2*k+(2^r-1)+2) → Bool => List.ofFn f ++ [false,true])
      (funext fun j => congrArg (@decide (j ∈ z)) (Subsingleton.elim _ _))
  simp only [hinput]
  exact ⟨model.1,model.2.1,model.2.2⟩

end PEqualNP.Outside.L_lib_1308.DervishFinalAdapter1308

namespace PEqualNP.Outside.L_lib_1308

namespace Layout1308Cover

inductive Row (p h : Nat)
  | word (t : Fin (p+1))
  | edge (t : Fin p)
  | arm (t : Fin (p+1)) (a : Fin 2) (j : Fin h)
  deriving DecidableEq, Fintype

def Rel {p h : Nat} : Row p h → Row p h → Prop
  | .word t, .word u => t = u
  | .word t, .edge u => t.val = u.val ∨ t.val = u.val + 1
  | .word _, .arm .. => False
  | .edge t, .edge u => t = u
  | .edge _, .word _ => False
  | .edge _, .arm .. => False
  | .arm t _ _, .word u => t = u
  | .arm t _ _, .edge u => t.val = u.val ∨ t.val = u.val + 1
  | .arm t a j, .arm u b k => t = u ∧ a = b ∧ j ≤ k

def Covers {p h : Nat} (i j : Row p h) : Prop :=
  i ≠ j ∧ Rel i j ∧ ∀ z, Rel i z → Rel z j → z = i ∨ z = j

def TreeCover {p h : Nat} : Row p h → Row p h → Prop
  | .arm t a j, .arm u b k => t = u ∧ a = b ∧ j.val + 1 = k.val
  | .arm t _ j, .word u => t = u ∧ j.val + 1 = h
  | .word t, .edge u => t.val = u.val ∨ t.val = u.val + 1
  | _, _ => False

lemma covers_arm_arm {p h : Nat} (t u : Fin (p+1)) (a b : Fin 2) (j k : Fin h) :
    Covers (.arm t a j) (.arm u b k) ↔
      t = u ∧ a = b ∧ j.val + 1 = k.val := by
  constructor
  · rintro ⟨hne, hrel, hgap⟩
    obtain ⟨htu, hab, hjk⟩ := hrel
    have hlt : j.val < k.val := by
      have hdiff : j ≠ k := by
        intro he
        exact hne (by rw [htu, hab, he])
      have hn : j.val ≠ k.val := by intro he; exact hdiff (Fin.ext he)
      omega
    refine ⟨htu, hab, ?_⟩
    by_contra hh
    have hbetween : j.val+1 < k.val := by omega
    let z : Row p h := .arm t a ⟨j.val+1, by omega⟩
    have hi : Rel (.arm t a j) z := by
      change t = t ∧ a = a ∧ j ≤ (⟨j.val+1, by omega⟩ : Fin h)
      exact ⟨rfl, rfl, Fin.le_iff_val_le_val.mpr (by change j.val ≤ j.val+1; omega)⟩
    have hz : Rel z (.arm u b k) := by
      change t = u ∧ a = b ∧ (⟨j.val+1, by omega⟩ : Fin h) ≤ k
      exact ⟨htu, hab, Fin.le_iff_val_le_val.mpr (by change j.val+1 ≤ k.val; omega)⟩
    rcases hgap z hi hz with he | he
    · have hv := congrArg (fun z : Row p h => match z with | .arm _ _ j => j.val | _ => 0) he
      simp [z] at hv
    · have hv := congrArg (fun z : Row p h => match z with | .arm _ _ j => j.val | _ => 0) he
      simp [z] at hv
      omega
  · rintro ⟨rfl, rfl, hjk⟩
    refine ⟨?_, ?_, ?_⟩
    · intro he
      have hv := congrArg (fun z : Row p h => match z with | .arm _ _ j => j.val | _ => 0) he
      simp at hv
      omega
    · change t = t ∧ a = a ∧ j ≤ k
      exact ⟨rfl, rfl, Fin.le_iff_val_le_val.mpr (by omega)⟩
    · intro z hiz hz
      cases z with
      | arm v c l =>
        obtain ⟨hvt, hca, hjl⟩ := hiz
        obtain ⟨_, _, hlk⟩ := hz
        have hh : l.val = j.val ∨ l.val = k.val := by
          simp only [Fin.le_iff_val_le_val] at hjl hlk
          omega
        rcases hh with hj | hk
        · exact Or.inl (by subst v; subst c; exact congrArg (Row.arm t a) (Fin.ext hj))
        · exact Or.inr (by subst v; subst c; exact congrArg (Row.arm t a) (Fin.ext hk))
      | word v => simp [Rel] at hz
      | edge v => simp [Rel] at hz

lemma covers_arm_word {p h : Nat} (t u : Fin (p+1)) (a : Fin 2) (j : Fin h) :
    Covers (.arm t a j) (.word u) ↔ t = u ∧ j.val + 1 = h := by
  constructor
  · rintro ⟨_, hrel, hgap⟩
    have hlt : j.val < h := j.isLt
    refine ⟨hrel, ?_⟩
    by_contra hh
    have hnext : j.val+1 < h := by omega
    let z : Row p h := .arm t a ⟨j.val+1, hnext⟩
    have hi : Rel (.arm t a j) z := by
      change t = t ∧ a = a ∧ j ≤ (⟨j.val+1, hnext⟩ : Fin h)
      exact ⟨rfl, rfl, Fin.le_iff_val_le_val.mpr (by change j.val ≤ j.val+1; omega)⟩
    have hz : Rel z (.word u) := by
      change t = u
      exact hrel
    rcases hgap z hi hz with he | he
    · have hv := congrArg (fun z : Row p h => match z with | .arm _ _ j => j.val | _ => 0) he
      simp [z] at hv
    · have hv := congrArg (fun z : Row p h => match z with | .word _ => true | _ => false) he
      simp [z] at hv
  · rintro ⟨htu, hmax⟩
    refine ⟨by simp, htu, ?_⟩
    intro z hiz hz
    cases z with
    | arm v b l =>
      obtain ⟨htv, hab, hjl⟩ := hiz
      change v = u at hz
      have hl : l = j := Fin.ext (by
        have hv := l.isLt
        simp only [Fin.le_iff_val_le_val] at hjl
        omega)
      exact Or.inl (by rw [← htv, ← hab, hl])
    | word v =>
      change t = v at hiz
      change v = u at hz
      exact Or.inr (by rw [hz])
    | edge v => simp [Rel] at hz

lemma covers_word_edge {p : Nat} (h : Nat) (t : Fin (p+1)) (u : Fin p) :
    Covers (Row.word (h:=h) t) (Row.edge (h:=h) u) ↔
      t.val = u.val ∨ t.val = u.val+1 := by
  constructor
  · exact fun h => h.2.1
  · intro ht
    refine ⟨by simp, ht, ?_⟩
    intro z hiz hz
    cases z with
    | word v =>
      change t = v at hiz
      exact Or.inl (by rw [hiz])
    | edge v =>
      change v = u at hz
      exact Or.inr (by rw [hz])
    | arm v b j => simp [Rel] at hiz

lemma not_covers_arm_edge {p h : Nat} (t : Fin (p+1)) (a : Fin 2)
    (j : Fin h) (u : Fin p) : ¬ Covers (.arm t a j) (.edge u) := by
  intro hc
  let z : Row p h := .word t
  have hi : Rel (.arm t a j) z := rfl
  have hz : Rel z (.edge u) := hc.2.1
  rcases hc.2.2 z hi hz with he | he
  · simp [z] at he
  · simp [z] at he

lemma covers_iff_tree {p h : Nat} (i j : Row p h) :
    Covers i j ↔ TreeCover i j := by
  cases i with
  | word t =>
    cases j with
    | word u =>
      change Covers (Row.word (h:=h) t) (.word u) ↔ False
      constructor
      · intro hc
        exact hc.1 (congrArg Row.word hc.2.1)
      · exact False.elim
    | edge u => exact covers_word_edge h t u
    | arm u b k => simp [Covers, TreeCover, Rel]
  | edge t =>
    cases j with
    | word u => simp [Covers, TreeCover, Rel]
    | edge u =>
      change Covers (Row.edge (h:=h) t) (.edge u) ↔ False
      constructor
      · intro hc
        exact hc.1 (congrArg Row.edge hc.2.1)
      · exact False.elim
    | arm u b k => simp [Covers, TreeCover, Rel]
  | arm t a v =>
    cases j with
    | word u => exact covers_arm_word t u a v
    | edge u =>
      change Covers (.arm t a v) (.edge u) ↔ False
      constructor
      · exact not_covers_arm_edge t a v u
      · exact False.elim
    | arm u b k => exact covers_arm_arm t u a b v k

def Adj {p h : Nat} (i j : Row p h) : Prop := Covers i j ∨ Covers j i

lemma adj_iff_tree {p h : Nat} (i j : Row p h) :
    Adj i j ↔ TreeCover i j ∨ TreeCover j i := by
  exact or_congr (covers_iff_tree i j) (covers_iff_tree j i)

def wordCode {p h : Nat} (t : Fin (p+1)) : Row p h → Fin 4
  | .arm _ a _ => ⟨a.val, by omega⟩
  | .edge u => ⟨2 + if u.val = t.val then 0 else 1, by split_ifs <;> omega⟩
  | .word _ => 0

lemma word_degree_le_four {p h : Nat} (t : Fin (p+1)) :
    (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
     (Finset.univ.filter (Adj (Row.word (h:=h) t))).card ≤ 4) := by
  classical
  calc
    _ ≤ (Finset.univ : Finset (Fin 4)).card := by
      apply Finset.card_le_card_of_injOn (wordCode t)
      · intro x hx
        exact Finset.mem_univ _
      · intro x hx y hy hc
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
        rw [adj_iff_tree] at hx hy
        cases x with
        | word u => simp [TreeCover] at hx
        | arm u a j =>
          have hxa : u = t ∧ j.val+1=h := by simpa [TreeCover] using hx
          cases y with
          | word v => simp [TreeCover] at hy
          | edge v =>
            have hv := congrArg Fin.val hc
            simp only [wordCode] at hv
            split_ifs at hv <;> omega
          | arm v b k =>
            have hya : v = t ∧ k.val+1=h := by simpa [TreeCover] using hy
            have hab : a = b := Fin.ext (congrArg (fun z : Fin 4 => z.val) hc)
            have hjk : j = k := Fin.ext (by omega)
            rw [hxa.1, hya.1, hab, hjk]
        | edge u =>
          have hxu : t.val = u.val ∨ t.val = u.val+1 := by
            simpa [TreeCover] using hx
          cases y with
          | word v => simp [TreeCover] at hy
          | arm v b k =>
            have hv := congrArg Fin.val hc
            simp only [wordCode] at hv
            split_ifs at hv <;> omega
          | edge v =>
            have hyu : t.val = v.val ∨ t.val = v.val+1 := by
              simpa [TreeCover] using hy
            have hv := congrArg Fin.val hc
            simp only [wordCode] at hv
            have huv : u = v := by
              apply Fin.ext
              split_ifs at hv <;> omega
            subst v
            rfl
    _ = 4 := by simp

def edgeCode {p h : Nat} (u : Fin p) : Row p h → Fin 4
  | .word t => ⟨if t.val = u.val then 0 else 1, by split_ifs <;> omega⟩
  | _ => 2

lemma edge_degree_le_four {p h : Nat} (u : Fin p) :
    (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
     (Finset.univ.filter (Adj (Row.edge (h:=h) u))).card ≤ 4) := by
  classical
  calc
    _ ≤ (Finset.univ : Finset (Fin 4)).card := by
      apply Finset.card_le_card_of_injOn (edgeCode u)
      · intro x hx
        exact Finset.mem_univ _
      · intro x hx y hy hc
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
        rw [adj_iff_tree] at hx hy
        cases x with
        | edge v => simp [TreeCover] at hx
        | arm v b k => simp [TreeCover] at hx
        | word t =>
          have hxt : t.val = u.val ∨ t.val = u.val+1 := by
            simpa [TreeCover] using hx
          cases y with
          | edge v => simp [TreeCover] at hy
          | arm v b k => simp [TreeCover] at hy
          | word s =>
            have hys : s.val = u.val ∨ s.val = u.val+1 := by
              simpa [TreeCover] using hy
            have hv := congrArg (fun z : Fin 4 => z.val) hc
            simp only [edgeCode] at hv
            have hts : t = s := by
              apply Fin.ext
              split_ifs at hv <;> omega
            rw [hts]
    _ = 4 := by simp

def armCode {p h : Nat} (j : Fin h) : Row p h → Fin 4
  | .arm _ _ k => ⟨if k.val < j.val then 0 else 1, by split_ifs <;> omega⟩
  | .word _ => 2
  | .edge _ => 3

lemma arm_degree_le_four {p h : Nat} (t : Fin (p+1)) (a : Fin 2) (j : Fin h) :
    (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
     (Finset.univ.filter (Adj (Row.arm t a j))).card ≤ 4) := by
  classical
  calc
    _ ≤ (Finset.univ : Finset (Fin 4)).card := by
      apply Finset.card_le_card_of_injOn (armCode j)
      · intro x hx
        exact Finset.mem_univ _
      · intro x hx y hy hc
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
        rw [adj_iff_tree] at hx hy
        cases x with
        | edge v => simp [TreeCover] at hx
        | word u =>
          have hxu : t = u := by
            rcases hx with h1 | h2
            · exact h1.1
            · simp [TreeCover] at h2
          cases y with
          | edge v => simp [TreeCover] at hy
          | arm v b k =>
            have hv := congrArg (fun z : Fin 4 => z.val) hc
            simp only [armCode] at hv
            split_ifs at hv <;> omega
          | word v =>
            have hyv : t = v := by
              rcases hy with h1 | h2
              · exact h1.1
              · simp [TreeCover] at h2
            rw [← hxu, ← hyv]
        | arm u b k =>
          have hx' : (t=u ∧ a=b ∧ j.val+1=k.val) ∨
              (u=t ∧ b=a ∧ k.val+1=j.val) := by simpa [TreeCover] using hx
          cases y with
          | edge v => simp [TreeCover] at hy
          | word v =>
            have hv := congrArg (fun z : Fin 4 => z.val) hc
            simp only [armCode] at hv
            split_ifs at hv <;> omega
          | arm v c l =>
            have hy' : (t=v ∧ a=c ∧ j.val+1=l.val) ∨
                (v=t ∧ c=a ∧ l.val+1=j.val) := by simpa [TreeCover] using hy
            have hv := congrArg (fun z : Fin 4 => z.val) hc
            simp only [armCode] at hv
            have hkv : k.val = l.val := by
              split_ifs at hv <;> rcases hx' with hxu | hxu <;>
                rcases hy' with hyv | hyv <;> omega
            have hkj : k = l := Fin.ext hkv
            have htu : u = t := by rcases hx' with hxu | hxu; exact hxu.1.symm; exact hxu.1
            have htv : v = t := by rcases hy' with hyv | hyv; exact hyv.1.symm; exact hyv.1
            have hab : b = a := by rcases hx' with hxu | hxu; exact hxu.2.1.symm; exact hxu.2.1
            have hac : c = a := by rcases hy' with hyv | hyv; exact hyv.2.1.symm; exact hyv.2.1
            rw [htu, htv, hab, hac, hkj]
    _ = 4 := by simp

lemma degree_le_four {p h : Nat} (i : Row p h) :
    (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
     (Finset.univ.filter (Adj i)).card ≤ 4) := by
  classical
  cases i with
  | word t => exact word_degree_le_four t
  | edge u => exact edge_degree_le_four u
  | arm t a j => exact arm_degree_le_four t a j

def idx {p h : Nat} : Row p h → Nat
  | .word t => 2*(h+1)*t.val
  | .edge u => 2*(h+1)*u.val+2*(h+1)-1
  | .arm t a j => 2*(h+1)*t.val+1+2*(h-1-j.val)+a.val

lemma idx_arm_gt_word {p h : Nat} (t : Fin (p+1)) (a : Fin 2) (j : Fin h) :
    idx (Row.word (h:=h) t) < idx (.arm t a j) := by
  simp only [idx]
  omega

lemma idx_arm_lt_word_next {p h : Nat} (t : Fin (p+1)) (a : Fin 2) (j : Fin h) :
    idx (.arm t a j) < 2*(h+1)*(t.val+1) := by
  simp only [idx]
  have hj := j.isLt
  have ha := a.isLt
  have hstep : 2*(h+1)*(t.val+1) = 2*(h+1)*t.val+2*(h+1) := by ring
  rw [hstep]
  omega

lemma idx_word_ne_zero {p h : Nat} (t : Fin (p+1)) :
    idx (Row.word (h:=h) t) = 0 ↔ t.val = 0 := by
  simp only [idx]
  have hh : 0 < 2*(h+1) := by omega
  constructor
  · intro hz
    by_contra hn
    have ht : 1 ≤ t.val := by omega
    have hm := Nat.mul_le_mul_left (2*(h+1)) ht
    omega
  · intro hz
    simp [hz]

lemma earlier_word_iff {p h : Nat} (t : Fin (p+1)) (y : Row p h) :
    (Adj (.word t) y ∧ idx y < idx (Row.word (h:=h) t)) ↔
      ∃ u : Fin p, t.val = u.val+1 ∧ y = .edge u := by
  constructor
  · rintro ⟨ha, he⟩
    rw [adj_iff_tree] at ha
    cases y with
    | word u => simp [TreeCover] at ha
    | arm u a j =>
      have htmp : u = t ∧ j.val+1=h := by simpa [TreeCover] using ha
      have hu : u = t := htmp.1
      subst u
      exact False.elim ((Nat.not_lt.mpr (Nat.le_of_lt (idx_arm_gt_word t a j))) he)
    | edge u =>
      have hu : t.val = u.val ∨ t.val = u.val+1 := by simpa [TreeCover] using ha
      have htn : t.val ≠ u.val := by
        intro ht
        have hq : 2 ≤ 2*(h+1) := by omega
        change 2*(h+1)*u.val+2*(h+1)-1 < 2*(h+1)*t.val at he
        rw [ht] at he
        omega
      exact ⟨u, hu.resolve_left htn, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    constructor
    · exact (adj_iff_tree _ _).mpr (Or.inl (Or.inr hu))
    · change 2*(h+1)*u.val+2*(h+1)-1 < 2*(h+1)*t.val
      have hstep : 2*(h+1)*(u.val+1) = 2*(h+1)*u.val+2*(h+1) := by ring
      rw [hu, hstep]
      omega

lemma earlier_edge_iff {p h : Nat} (u : Fin p) (y : Row p h) :
    (Adj (.edge u) y ∧ idx y < idx (Row.edge (h:=h) u)) ↔
      y = Row.word (h:=h) ⟨u.val, by omega⟩ := by
  constructor
  · rintro ⟨ha, he⟩
    rw [adj_iff_tree] at ha
    cases y with
    | edge v => simp [TreeCover] at ha
    | arm t a j => simp [TreeCover] at ha
    | word t =>
      have hu : t.val = u.val ∨ t.val = u.val+1 := by simpa [TreeCover] using ha
      have hn : t.val ≠ u.val+1 := by
        intro hh
        change 2*(h+1)*t.val < 2*(h+1)*u.val+2*(h+1)-1 at he
        rw [hh] at he
        have hstep : 2*(h+1)*(u.val+1) = 2*(h+1)*u.val+2*(h+1) := by ring
        rw [hstep] at he
        omega
      exact congrArg (Row.word (h:=h)) (Fin.ext (hu.resolve_right hn))
  · intro hy
    subst y
    constructor
    · exact (adj_iff_tree _ _).mpr (Or.inr (Or.inl rfl))
    · change 2*(h+1)*u.val < 2*(h+1)*u.val+2*(h+1)-1
      omega

lemma idx_arm_lt_iff {p h : Nat} (t : Fin (p+1)) (a : Fin 2) (j k : Fin h) :
    idx (.arm t a j) < idx (.arm t a k) ↔ k.val < j.val := by
  simp only [idx]
  have hj := j.isLt
  have hk := k.isLt
  omega

lemma earlier_arm_iff {p h : Nat} (t : Fin (p+1)) (a : Fin 2) (j : Fin h)
    (y : Row p h) :
    (Adj (.arm t a j) y ∧ idx y < idx (.arm t a j)) ↔
      (j.val+1=h ∧ y=.word t) ∨
      (∃ k : Fin h, j.val+1=k.val ∧ y=.arm t a k) := by
  constructor
  · rintro ⟨ha, he⟩
    rw [adj_iff_tree] at ha
    cases y with
    | edge u => simp [TreeCover] at ha
    | word u =>
      have htmp : t=u ∧ j.val+1=h := by simpa [TreeCover] using ha
      exact Or.inl ⟨htmp.2, congrArg Row.word htmp.1.symm⟩
    | arm u b k =>
      have htmp : (t=u ∧ a=b ∧ j.val+1=k.val) ∨
          (u=t ∧ b=a ∧ k.val+1=j.val) := by simpa [TreeCover] using ha
      rcases htmp with hh | hh
      · exact Or.inr ⟨k, hh.2.2, by rw [hh.1, hh.2.1]⟩
      · have ht : u=t := hh.1
        have hb : b=a := hh.2.1
        rw [ht, hb] at he
        have hbefore := (idx_arm_lt_iff t a k j).mp he
        omega
  · rintro (⟨hj, hy⟩ | ⟨k, hk, hy⟩)
    · subst y
      constructor
      · exact (adj_iff_tree _ _).mpr (Or.inl ⟨rfl, hj⟩)
      · exact idx_arm_gt_word t a j
    · subst y
      constructor
      · exact (adj_iff_tree _ _).mpr (Or.inl ⟨rfl, rfl, hk⟩)
      · exact (idx_arm_lt_iff t a k j).mpr (by omega)

lemma filter_card_one {α : Type*} [Fintype α] [DecidableEq α]
    (P : α → Prop) [DecidablePred P] (a : α) (h : ∀ x, P x ↔ x = a) :
    (Finset.univ.filter P).card = 1 := by
  have he : Finset.univ.filter P = {a} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact h x
  simp [he]

lemma filter_card_zero {α : Type*} [Fintype α] [DecidableEq α]
    (P : α → Prop) [DecidablePred P] (h : ∀ x, ¬ P x) :
    (Finset.univ.filter P).card = 0 := by
  have he : Finset.univ.filter P = ∅ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [h x]
  simp [he]

lemma earlier_word_card {p h : Nat} (t : Fin (p+1))
    [DecidablePred (fun y : Row p h =>
      idx y < idx (Row.word (h:=h) t) ∧ Adj (.word t) y)] :
    (Finset.univ.filter (fun y : Row p h =>
      idx y < idx (Row.word (h:=h) t) ∧ Adj (.word t) y)).card =
      if t.val = 0 then 0 else 1 := by
  by_cases hzero : t.val = 0
  · rw [if_pos hzero]
    apply filter_card_zero
    intro y hy
    obtain ⟨u, hu, _⟩ := (earlier_word_iff t y).mp ⟨hy.2,hy.1⟩
    omega
  · rw [if_neg hzero]
    let u : Fin p := ⟨t.val-1, by omega⟩
    have hu : t.val = u.val+1 := by dsimp [u]; omega
    apply filter_card_one _ (Row.edge (h:=h) u)
    intro y
    constructor
    · intro hy
      obtain ⟨v,hv,hvy⟩ := (earlier_word_iff t y).mp ⟨hy.2,hy.1⟩
      have hvu : v = u := Fin.ext (by dsimp [u] at *; omega)
      rw [hvy,hvu]
    · intro hy
      rw [hy]
      have hh := (earlier_word_iff t (Row.edge (h:=h) u)).mpr ⟨u,hu,rfl⟩
      exact ⟨hh.2,hh.1⟩

lemma earlier_edge_card {p h : Nat} (u : Fin p)
    [DecidablePred (fun y : Row p h =>
      idx y < idx (Row.edge (h:=h) u) ∧ Adj (.edge u) y)] :
    (Finset.univ.filter (fun y : Row p h =>
      idx y < idx (Row.edge (h:=h) u) ∧ Adj (.edge u) y)).card = 1 := by
  apply filter_card_one _ (Row.word (h:=h) ⟨u.val, by omega⟩)
  intro y
  constructor
  · intro hy
    exact (earlier_edge_iff u y).mp ⟨hy.2, hy.1⟩
  · intro hy
    have hh := (earlier_edge_iff u y).mpr hy
    exact ⟨hh.2,hh.1⟩

lemma earlier_arm_card {p h : Nat} (t : Fin (p+1)) (a : Fin 2) (j : Fin h)
    [DecidablePred (fun y : Row p h =>
      idx y < idx (.arm t a j) ∧ Adj (.arm t a j) y)] :
    (Finset.univ.filter (fun y : Row p h =>
      idx y < idx (.arm t a j) ∧ Adj (.arm t a j) y)).card = 1 := by
  by_cases hj : j.val+1=h
  · apply filter_card_one _ (Row.word (h:=h) t)
    intro y
    constructor
    · intro hy
      rcases (earlier_arm_iff t a j y).mp ⟨hy.2,hy.1⟩ with hh | ⟨k, hk, _⟩
      · exact hh.2
      · have hlt := k.isLt
        omega
    · intro hy
      have hh := (earlier_arm_iff t a j y).mpr (Or.inl ⟨hj,hy⟩)
      exact ⟨hh.2,hh.1⟩
  · let k : Fin h := ⟨j.val+1, by omega⟩
    apply filter_card_one _ (Row.arm t a k)
    intro y
    constructor
    · intro hy
      rcases (earlier_arm_iff t a j y).mp ⟨hy.2,hy.1⟩ with hh | ⟨v, hv, hy'⟩
      · exact (hj hh.1).elim
      · have hvk : v = k := Fin.ext (by dsimp [k]; omega)
        rw [hy', hvk]
    · intro hy
      have hh := (earlier_arm_iff t a j y).mpr
        (Or.inr ⟨k, by dsimp [k], hy⟩)
      exact ⟨hh.2,hh.1⟩

lemma earlier_card {p h : Nat} (i : Row p h)
    [DecidablePred (fun y : Row p h => idx y < idx i ∧ Adj i y)] :
    (Finset.univ.filter (fun y : Row p h => idx y < idx i ∧ Adj i y)).card =
      (if idx i = 0 then 0 else 1) := by
  cases i with
  | word t =>
    simpa only [idx_word_ne_zero] using (earlier_word_card (h:=h) t)
  | edge u =>
    have hidx : idx (Row.edge (h:=h) u) ≠ 0 := by
      simp only [idx]
      omega
    simpa only [if_neg hidx] using (earlier_edge_card (h:=h) u)
  | arm t a j =>
    have hidx : idx (Row.arm t a j) ≠ 0 := by
      have hh := idx_arm_gt_word t a j
      omega
    simpa only [if_neg hidx] using (earlier_arm_card t a j)

end Layout1308Cover

end PEqualNP.Outside.L_lib_1308

namespace PEqualNP.Outside.L_lib_1308.DervishHasseTransfer1308
open DervishFinalAdapter1308 DervishIndexEquiv1308

def rowEquiv (p r : ℕ) : DervishAbstractRows1308.Row p r ≃ Layout1308Cover.Row p (2^r-1) where
  toFun
    | .word t => .word t
    | .edge t => .edge t
    | .arm t a j => .arm t a j
  invFun
    | .word t => .word t
    | .edge t => .edge t
    | .arm t a j => .arm t a j
  left_inv i := by cases i <;> rfl
  right_inv i := by cases i <;> rfl

theorem rel_row (p r : ℕ) (i j : DervishAbstractRows1308.Row p r) :
    DervishAbstractRows1308.Rel i j ↔ Layout1308Cover.Rel (rowEquiv p r i) (rowEquiv p r j) := by
  cases i <;> cases j <;> rfl

noncomputable def beta (k r : ℕ) (hk : 1 ≤ k) :
    Fin (2*2^r*2^k-1) ≃ Layout1308Cover.Row (2^k-1) (2^r-1) :=
  (decodeEquiv k r hk).trans (rowEquiv (2^k-1) r)

theorem cover_beta (k r : ℕ) (hk : 1 ≤ k) (i j : Fin (2*2^r*2^k-1)) :
    Covers (table k r hk) i j ↔ Layout1308Cover.Covers (beta k r hk i) (beta k r hk j) := by
  let e := beta k r hk
  have h (i j) : table k r hk i ⊆ table k r hk j ↔ Layout1308Cover.Rel (e i) (e j) :=
    (DervishConcreteRows1308.realize_order k r _ _).trans (rel_row _ _ _ _)
  constructor
  · rintro ⟨hne,hij,hmid⟩
    refine ⟨fun g => hne (e.injective g),(h i j).mp hij,?_⟩
    intro z hz hz'
    obtain ⟨w,rfl⟩ := e.surjective z
    exact (hmid w ((h i w).mpr hz) ((h w j).mpr hz')).imp (congrArg e) (congrArg e)
  · rintro ⟨hne,hij,hmid⟩
    refine ⟨fun g => hne (congrArg e g),(h i j).mpr hij,?_⟩
    intro w hw hw'
    exact (hmid (e w) ((h i w).mp hw) ((h w j).mp hw')).imp (fun g => e.injective g) (fun g => e.injective g)

theorem adj_beta (k r : ℕ) (hk : 1 ≤ k) (i j : Fin (2*2^r*2^k-1)) :
    Adj (table k r hk) i j ↔ Layout1308Cover.Adj (beta k r hk i) (beta k r hk j) :=
  or_congr (cover_beta k r hk i j) (cover_beta k r hk j i)

theorem card_transport {I J : Type} [Fintype I] [Fintype J] (e : I ≃ J)
    (P : I → Prop) (Q : J → Prop) (h : ∀ i, P i ↔ Q (e i)) :
    (letI : ∀ P : Prop, Decidable P := Classical.propDecidable;
      (Finset.univ.filter P).card = (Finset.univ.filter Q).card) := by
  classical
  have m := congrArg Finset.card (show (Finset.univ.filter P).map e.toEmbedding = Finset.univ.filter Q from by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact (h i).mp hi
    · intro hj
      exact ⟨e.symm j,(h _).mpr (by simpa only [Equiv.apply_symm_apply] using hj), e.apply_symm_apply j⟩)
  simpa only [Finset.card_map] using m

theorem degree (k r : ℕ) (hk : 1 ≤ k) (i : Fin (2*2^r*2^k-1)) :
    (letI : ∀ P : Prop, Decidable P := Classical.propDecidable;
      (Finset.univ.filter (Adj (table k r hk) i)).card ≤ 4) := by
  classical
  rw [card_transport (beta k r hk) _ _ (adj_beta k r hk i)]
  exact Layout1308Cover.degree_le_four _

open DervishAbstractRows1308

theorem idx_encode (k r : ℕ) (hk : 1 ≤ k) (j : Row (2^k-1) r) :
    Layout1308Cover.idx (rowEquiv (2^k-1) r j) = (encode k r hk j).val := by
  have hq : (2^r-1)+1 = 2^r := Nat.sub_add_cancel (Nat.two_pow_pos r)
  cases j <;>
    simp [rowEquiv,Layout1308Cover.idx,encode,wide,turn,hq,Layout1308Index.wordIdx,
      Layout1308Index.edgeIdx,Layout1308Index.armIdx]

theorem idx_beta (k r : ℕ) (hk : 1 ≤ k) (i : Fin (2*2^r*2^k-1)) :
    Layout1308Cover.idx (beta k r hk i) = i.val :=
  (idx_encode k r hk (decodeEquiv k r hk i)).trans (congrArg Fin.val (encode_decode k r hk i))

theorem earlier (k r : ℕ) (hk : 1 ≤ k) (i : Fin (2*2^r*2^k-1)) :
    (letI : ∀ P : Prop, Decidable P := Classical.propDecidable;
      (Finset.univ.filter (fun j : Fin (2*2^r*2^k-1) => j.val < i.val ∧ Adj (table k r hk) i j)).card =
        (if i.val = 0 then 0 else 1)) := by
  classical
  have he (j : Fin (2*2^r*2^k-1)) :
      j.val < i.val ∧ Adj (table k r hk) i j ↔
        Layout1308Cover.idx (beta k r hk j) < Layout1308Cover.idx (beta k r hk i) ∧
          Layout1308Cover.Adj (beta k r hk i) (beta k r hk j) := by
    rw [idx_beta,idx_beta,adj_beta]
  rw [card_transport (beta k r hk)
    (fun j => j.val < i.val ∧ Adj (table k r hk) i j)
    (fun y => Layout1308Cover.idx y < Layout1308Cover.idx (beta k r hk i) ∧
      Layout1308Cover.Adj (beta k r hk i) y) he]
  have h := Layout1308Cover.earlier_card (beta k r hk i)
  by_cases hi : i.val = 0 <;> simpa only [idx_beta,hi,if_true,if_false] using h

theorem all_scores (k r : ℕ) (hk : 1 ≤ k) : HasseScores (table k r hk) :=
  ⟨earlier k r hk, degree k r hk⟩

end PEqualNP.Outside.L_lib_1308.DervishHasseTransfer1308

theorem PEqualNP.Outside.L_lib_1308 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ k r : Nat, 1 ≤ k →
  let q := 2^r
  let n := 2*k+(q-1)+2
  let m := 2*q*2^k-1
  ∃ (x : Fin m → Finset (Fin n)) (pin : Fin m → Option Bool) (F : Finset (Fin m)),
    Function.Injective x ∧ F.card = 2^(k+1)-1 ∧
    let cover := fun i j => i ≠ j ∧ x i ⊆ x j ∧
      ∀ z, x i ⊆ x z → x z ⊆ x j → z = i ∨ z = j
    let adj := fun i j => cover i j ∨ cover j i
    (∀ i : Fin m, (Finset.univ.filter (fun j : Fin m => j.val < i.val ∧ adj i j)).card =
      (if i.val = 0 then 0 else 1)) ∧
    (∀ i : Fin m, (Finset.univ.filter (fun j : Fin m => adj i j)).card ≤ 4) ∧
    let fits := fun (S : Finset (Fin m)) (b : Nat) =>
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin 2 → Nat),
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
        C.output < n+2+C.size ∧ (∀ a, tap a < n+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
        ∀ i ∈ S, let v := fun (a : Fin 2) =>
          (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false,true])).getD (tap a) false
          v 1 = !(v 0) ∧ ∀ c, pin i = some c → v 0 = c
    (∀ b, fits Finset.univ b ↔ r < b) ∧
    (∀ i ∈ F, fits (Finset.univ.erase i) r) ∧
    ∀ S : Finset (Fin m), ¬ fits S r → F ⊆ S) := by
  exact PEqualNP.Outside.L_lib_1308.DervishFinalAdapter1308.finish_exact
    PEqualNP.Outside.L_lib_1308.DervishHasseTransfer1308.all_scores


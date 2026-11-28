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

namespace PEqualNP.Outside.L_lib_1270

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
namespace DervishRepresent1196

abbrev Z (k : Nat) := Fin k → Fin 3 → Bool
abbrev W (k : Nat) := Fin k → Fin 3 → Bool → Bool

def Valid {k : Nat} (z : Z k) : Prop := ∀ i,
  ¬ (z i 0 = true ∧ z i 1 = true ∧ z i 2 = true)

def Solves {k : Nat} (z : Z k) (w : W k) : Prop :=
  (∀ i j, (w i j false || w i j true) = z i j ∧
    ¬ (w i j false = true ∧ w i j true = true)) ∧
  (∀ i c, ¬ (w i 0 false = true ∧ w i 1 c = true) ∧
          ¬ (w i 0 true = true ∧ w i 2 c = true))

def labels {k : Nat} (a : Fin k → Bool) : Z k :=
  fun i j => if j = 0 then a i else false

def tap {k : Nat} (z b : Z k) : W k := fun i j c => z i j && decide (b i j = c)

private theorem tap_one (z b : Bool) :
    (z && decide (b = false) || z && decide (b = true)) = z ∧
    ¬ ((z && decide (b = false)) = true ∧ (z && decide (b = true)) = true) := by
  cases z <;> cases b <;> decide

theorem choose_solves {k : Nat} {z : Z k} (h : Valid z) :
    Solves z (tap z (labels (fun i => z i 1))) := by
  constructor
  · intro i j; exact tap_one _ _
  · intro i c
    have hv := h i
    have h10 : (1 : Fin 3) ≠ 0 := by decide
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    simp only [tap, labels, h10, h20, if_false, if_true]
    cases hz0 : z i 0 <;> cases hz1 : z i 1 <;> cases hz2 : z i 2 <;> cases c <;>
      simp_all

theorem valid_of_solves {k : Nat} {z : Z k} {w : W k} (h : Solves z w) : Valid z := by
  intro i hv
  obtain ⟨a,b,c⟩ := hv
  have hit (j : Fin 3) (hj : z i j = true) : ∃ side, w i j side = true := by
    have hv := (h.1 i j).1.trans hj
    cases hx : w i j false with
    | false => exact ⟨true, by simpa [hx] using hv⟩
    | true => exact ⟨false, hx⟩
  obtain ⟨side,ha⟩ := hit 0 a
  cases side with
  | false =>
    obtain ⟨s,hs⟩ := hit 1 b
    exact (h.2 i s).1 ⟨ha,hs⟩
  | true =>
    obtain ⟨s,hs⟩ := hit 2 c
    exact (h.2 i s).2 ⟨ha,hs⟩

theorem valid_iff {k : Nat} (z : Z k) : Valid z ↔ ∃ w, Solves z w :=
  ⟨fun h => ⟨_,choose_solves h⟩, fun ⟨_,h⟩ => valid_of_solves h⟩

def request {k : Nat} (a : Fin k → Bool) : Z k :=
  fun i j => if j = 0 then true else if j = 1 then a i else !(a i)

theorem request_valid {k : Nat} (a : Fin k → Bool) : Valid (request a) := by
  intro i
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  simp only [request, h10, h20, h21, if_false, if_true]
  cases a i <;> decide

theorem request_forces {k : Nat} (a : Fin k → Bool) (b : Z k)
    (h : Solves (request a) (tap (request a) b)) : ∀ i, b i 0 = a i := by
  intro i
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have h₁ := (h.2 i (b i 1)).1
  have h₂ := (h.2 i (b i 2)).2
  simp only [tap, request, if_true, h10, h20, h21, if_false, decide_true, Bool.and_true,
    Bool.true_and] at h₁ h₂
  have f : b i 0 = false → a i = false := by simpa using h₁
  have t : b i 0 = true → a i = true := by simpa using h₂
  by_cases hbit : b i 0 = true
  · exact hbit.trans (t hbit).symm
  · have hbit' : b i 0 = false := by
      cases hb : b i 0 <;> simp_all
    exact hbit'.trans (f hbit').symm

theorem list_iff (k t : Nat) :
    (∃ L : Fin t → Z k, ∀ z, Valid z → ∃ l,
      Solves z (fun i j c => z i j && decide (L l i j = c))) ↔ 2^k ≤ t := by
  classical
  have card : Fintype.card (Fin k → Bool) = 2^k := by simp
  constructor
  · rintro ⟨L,H⟩
    have hs : Function.Surjective (fun l : Fin t => fun i : Fin k => L l i 0) := by
      intro a
      obtain ⟨l, hl⟩ := H (request a) (request_valid a)
      exact ⟨l, funext (request_forces a (L l) hl)⟩
    have hc := Fintype.card_le_of_surjective _ hs
    simpa [card] using hc
  · intro hb
    let e : (Fin k → Bool) ≃ Fin (2^k) := Fintype.equivFinOfCardEq card
    let L : Fin t → Z k := fun l => labels (if hl : l.val < 2^k then
      e.symm ⟨l.val,hl⟩ else fun _ => false)
    refine ⟨L, ?_⟩
    intro z hv
    let a : Fin k → Bool := fun i => z i 1
    let s := e a
    let l : Fin t := ⟨s.val, s.isLt.trans_le hb⟩
    refine ⟨l, ?_⟩
    have hL : L l = labels a := by
      dsimp only [L, l]
      rw [dif_pos s.isLt]
      change labels (e.symm s) = labels a
      rw [show s = e a from rfl, e.symm_apply_apply]
    change Solves z (tap z (L l))
    rw [hL]
    exact choose_solves hv

end DervishRepresent1196

namespace DervishRepresent1196

private def centerRow : Fin 3 → Bool := fun j => decide (j = 0)
private def leaf (b : Bool) : Fin 3 := if b then 2 else 1
private def afterRow (b : Bool) : Fin 3 → Bool := fun j => decide (j = 0 ∨ j = leaf b)

private theorem valid_center : ¬ (centerRow 0 = true ∧ centerRow 1 = true ∧ centerRow 2 = true) := by decide
private theorem valid_after (b : Bool) :
    ¬ (afterRow b 0 = true ∧ afterRow b 1 = true ∧ afterRow b 2 = true) := by
  cases b <;> decide

private theorem valid_update {k : Nat} {z : Z k} (hz : Valid z) (i : Fin k) (r : Fin 3 → Bool)
    (hr : ¬ (r 0 = true ∧ r 1 = true ∧ r 2 = true)) : Valid (Function.update z i r) := by
  intro j
  by_cases h : j = i
  · subst j; simpa using hr
  · simpa [Function.update_of_ne h] using hz j

private def rounds {k : Nat} (w : Z k → W k) : Nat → Z k
  | 0 => fun _ _ => false
  | m+1 => if hm : m < k then
      let i : Fin k := ⟨m,hm⟩
      let u := Function.update (rounds w m) i centerRow
      Function.update (rounds w m) i (afterRow (w u i 0 true))
    else rounds w m

private def stage {k : Nat} (w : Z k → W k) (t : Nat) : Z k :=
  if ht : t % 2 = 1 ∧ t / 2 < k then
    Function.update (rounds w (t/2)) ⟨t/2,ht.2⟩ centerRow
  else rounds w (t/2)

private theorem round_valid {k : Nat} (w : Z k → W k) (m : Nat) : Valid (rounds w m) := by
  induction m with
  | zero => intro i; simp [rounds]
  | succ m ih =>
    by_cases hm : m < k
    · simp only [rounds, dif_pos hm]
      apply valid_update ih
      apply valid_after
    · simpa only [rounds, dif_neg hm] using ih

private theorem round_fresh {k : Nat} (w : Z k → W k) (m : Nat) (i : Fin k) (hi : m ≤ i.val) (j : Fin 3) :
    rounds w m i j = false := by
  induction m with
  | zero => rfl
  | succ m ih =>
    by_cases hm : m < k
    · have hne : i ≠ (⟨m,hm⟩ : Fin k) := by
        intro e
        have := congrArg Fin.val e
        simp only [Fin.val_mk] at this
        omega
      simpa only [rounds, dif_pos hm, Function.update_of_ne hne] using ih (by omega)
    · simpa only [rounds, dif_neg hm] using ih (by omega)

private theorem stage_valid {k : Nat} (w : Z k → W k) (t : Nat) : Valid (stage w t) := by
  unfold stage
  split
  · exact valid_update (round_valid _ _) _ _ valid_center
  · exact round_valid _ _

private theorem stage_even {k : Nat} (w : Z k → W k) (m : Nat) : stage w (2*m) = rounds w m := by
  have hn : ¬ ((2*m)%2=1 ∧ (2*m)/2<k) := by omega
  unfold stage
  rw [dif_neg hn, show (2*m)/2=m by omega]

private theorem stage_odd {k : Nat} (w : Z k → W k) (m : Nat) (hm : m < k) :
    stage w (2*m+1) = Function.update (rounds w m) (⟨m,hm⟩ : Fin k) centerRow := by
  have ht : (2*m+1)%2=1 ∧ (2*m+1)/2<k := by omega
  have hd : (2*m+1)/2 = m := by omega
  have hf : (⟨(2*m+1)/2,ht.2⟩ : Fin k) = ⟨m,hm⟩ := Fin.ext hd
  unfold stage
  rw [dif_pos ht, hf, hd]

private theorem stage_odd_out {k : Nat} (w : Z k → W k) (m : Nat) (hm : ¬ m < k) :
    stage w (2*m+1) = rounds w m := by
  have ht : ¬ ((2*m+1)%2=1 ∧ (2*m+1)/2<k) := by omega
  unfold stage
  rw [dif_neg ht, show (2*m+1)/2=m by omega]

private theorem stage_step {k : Nat} (w : Z k → W k) (t : Nat) : stage w t ≤ stage w (t+1) := by
  let m := t / 2
  by_cases h : t % 2 = 0
  · have he : t = 2*m := by dsimp [m]; omega
    rw [he, stage_even]
    by_cases hm : m < k
    · rw [stage_odd w m hm]
      intro i j
      by_cases hi : i = (⟨m,hm⟩ : Fin k)
      · subst i
        rw [round_fresh w m ⟨m,hm⟩ (by simp) j]
        exact Bool.false_le _
      · simp only [Function.update_of_ne hi, le_refl]
    · rw [stage_odd_out w m hm]
  · have he : t = 2*m+1 := by dsimp [m]; omega
    have hs : 2*m+1+1 = 2*(m+1) := by omega
    rw [he, hs, stage_even]
    by_cases hm : m < k
    · rw [stage_odd w m hm]
      simp only [rounds, dif_pos hm]
      intro i j
      by_cases hi : i = (⟨m,hm⟩ : Fin k)
      · subst i
        simp only [Function.update_self]
        cases hc : centerRow j with
        | false => exact Bool.false_le _
        | true =>
          have hj : j = 0 := of_decide_eq_true hc
          simp [hj,afterRow]
      · simp only [Function.update_of_ne hi, le_refl]
    · rw [stage_odd_out w m hm]
      simp only [rounds, dif_neg hm, le_refl]

private theorem tip_active {k : Nat} {z : Z k} {u : W k} (h : Solves z u)
    (i : Fin k) (j : Fin 3) (hz : z i j = true) : ∃ c, u i j c = true := by
  have he := (h.1 i j).1.trans hz
  cases hx : u i j false with
  | false => exact ⟨true, by simpa [hx] using he⟩
  | true => exact ⟨false,hx⟩

private theorem stage_fall {k : Nat} (w : Z k → W k) (hw : ∀ z, Valid z → Solves z (w z))
    (i : Fin k) : ∃ b, w (stage w (2*i.val+1)) i 0 b = true ∧
      w (stage w (2*i.val+2)) i 0 b = false := by
  let u := stage w (2*i.val+1)
  let v := stage w (2*i.val+2)
  let b := w u i 0 true
  have hu := hw u (stage_valid w _)
  have hv := hw v (stage_valid w _)
  have hc : u i 0 = true := by
    change stage w (2*i.val+1) i 0 = true
    rw [stage_odd w i.val i.isLt]
    simp [centerRow]
  have huout : w u i 0 b = true := by
    have he := (hu.1 i 0).1.trans hc
    dsimp only [b]
    cases hh : w u i 0 true <;> simp_all
  have hvactive : v i (leaf b) = true := by
    change stage w (2*i.val+2) i (leaf b) = true
    rw [show 2*i.val+2 = 2*(i.val+1) by omega, stage_even]
    simp only [rounds, dif_pos i.isLt]
    have hmid : Function.update (rounds w i.val) i centerRow = u := by
      exact (stage_odd w i.val i.isLt).symm
    change (Function.update (rounds w i.val) i (afterRow
      (w (Function.update (rounds w i.val) i centerRow) i 0 true))) i (leaf b) = true
    rw [hmid, Function.update_self]
    simp [afterRow,b]
  obtain ⟨c,hc'⟩ := tip_active hv i (leaf b) hvactive
  refine ⟨b,huout,?_⟩
  cases hb : b with
  | false =>
    have hbad : w v i 1 c = true := by simpa [leaf,hb] using hc'
    have hn := (hv.2 i c).1
    cases hout : w v i 0 false <;> simp_all
  | true =>
    have hbad : w v i 2 c = true := by simpa [leaf,hb] using hc'
    have hn := (hv.2 i c).2
    cases hout : w v i 0 true <;> simp_all

theorem adaptive_chain {k : Nat} (w : Z k → W k) (hw : ∀ z, Valid z → Solves z (w z)) :
    ∃ z : Fin (2*k+1) → Z k, Monotone z ∧ (∀ t, Valid (z t)) ∧
      ∀ i : Fin k, ∃ b,
        w (z ⟨2*i.val+1,by have := i.isLt; omega⟩) i 0 b = true ∧
        w (z ⟨2*i.val+2,by have := i.isLt; omega⟩) i 0 b = false := by
  have hm : Monotone (stage w) := monotone_nat_of_le_succ (stage_step w)
  exact ⟨fun t => stage w t.val, fun _ _ h => hm h,
    fun _ => stage_valid w _, fun i => stage_fall w hw i⟩

end DervishRepresent1196

namespace DervishRepresent1196

open PEqualNP.CircuitLowerBounds

def input {k : Nat} (z : Z k) : List Bool :=
  (List.ofFn (fun i => List.ofFn (z i))).flatten ++ [false,true]

private theorem ofFn_rel {α : Type*} {R : α → α → Prop} {n : Nat}
    {f g : Fin n → α} (h : ∀ i, R (f i) (g i)) :
    List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero => simpa using (List.Forall₂.nil : List.Forall₂ R [] [])
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (ih (fun i => h i.succ))

private theorem append_rel {α : Type*} {R : α → α → Prop}
    {a b c d : List α} (h : List.Forall₂ R a b) (g : List.Forall₂ R c d) :
    List.Forall₂ R (a++c) (b++d) := by
  induction h with
  | nil => exact g
  | cons h₀ _ ih => exact List.Forall₂.cons h₀ ih

private theorem flat_rel {α : Type*} {R : α → α → Prop} {a b : List (List α)}
    (h : List.Forall₂ (List.Forall₂ R) a b) : List.Forall₂ R a.flatten b.flatten := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons h₀ _ ih => exact append_rel h₀ ih

private theorem below_of_rel {a b : List Bool} (h : List.Forall₂ (· ≤ ·) a b) :
    AltChain1196.below a b := by
  induction h with
  | nil => intro j; exact le_rfl
  | cons h₀ h₁ ih =>
    intro j
    cases j with
    | zero => exact h₀
    | succ j => exact ih j

theorem input_below {k : Nat} {a b : Z k} (h : a ≤ b) :
    AltChain1196.below (input a) (input b) := by
  apply below_of_rel
  apply append_rel
  · exact flat_rel (ofFn_rel (fun i => ofFn_rel (fun j => h i j)))
  · exact List.Forall₂.cons le_rfl (List.Forall₂.cons le_rfl List.Forall₂.nil)

theorem input_length {k : Nat} (z : Z k) : (input z).length = 3*k+2 := by
  simp [input, List.length_flatten, List.map_ofFn, Function.comp_def, Nat.mul_comm]

def Fits (k s r : Nat) : Prop := ∃ (C : Circuit)
    (tap : Fin k → Fin 3 → Bool → Fin (3*k+2+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (3*k+2) C ∧ C.output < 3*k+2+C.size ∧
    C.size ≤ s ∧ PEqualNP.NotBracket.notCount C ≤ r ∧ ∀ z : Z k,
      (C.eval (input z) = true ↔ ¬ Valid z) ∧ (Valid z →
        Solves z (fun i j c => (C.wires (input z)).getD (tap i j c).val false))

theorem lower_exact (k s r : Nat) (h : Fits k s r) : k < 2^r := by
  obtain ⟨C,tap,fan,_,_,_,nots,hr⟩ := h
  let w : Z k → W k := fun z i j c => (C.wires (input z)).getD (tap i j c).val false
  obtain ⟨z,mono,valid,falls⟩ := adaptive_chain w (fun z hz => (hr z).2 hz)
  have mk := AltChain1196.circuit_multioutput_markov k (3*k+2) C (fun t => input (z t)) fan
    (fun t => input_length (z t)) (fun _ _ h => input_below (mono h)) (by
      intro i
      obtain ⟨b,hb₁,hb₂⟩ := falls i
      exact ⟨(tap i 0 b).val,hb₁,hb₂⟩)
  exact mk.trans_le (Nat.pow_le_pow_right (by decide) nots)

end DervishRepresent1196

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

namespace DervishRepresent1196

open PEqualNP.CircuitLowerBounds
open DervishBuild1196.Build

theorem upper_exact (k r : Nat) (h : k < 2^r) : Fits k (3*k^2+13*k) r := by
  obtain ⟨v,nb,vc,vn,V⟩ := DervishWire1196.inverted_bits k r h
  obtain ⟨t,out,tap,_,tc,tn,O,T⟩ := DervishWire1196.recover_wires v nb V
  let C : Circuit := ⟨t.gates,out⟩
  let taps : Fin k → Fin 3 → Bool → Fin (3*k+2+C.size) :=
    fun i j b => ⟨tap i j b,(T i j b).1⟩
  have cst : C.size ≤ 3*k^2+13*k := tc.trans (Upper1196Unary.total_upper_budget k v.cost vc)
  have nst : PEqualNP.NotBracket.notCount C ≤ r := tn.trans_le vn
  refine ⟨C,taps,t.fan,t.back,O.1,cst,nst,?_⟩
  intro z
  constructor
  · change (t.circ.wires (DervishWire1196.input z)).getD out false = true ↔ ¬ Valid z
    rw [O.2 z]
    exact DervishWire1196.invalid_spec z
  · intro hz
    have he : (fun i j b => (C.wires (input z)).getD (taps i j b).val false) =
        Upper1196Functional.recovered z (fun i => !(z i 1)) := by
      funext i j b
      exact (T i j b).2 z
    rw [he]
    exact Upper1196Functional.recovered_solves z (fun i => !(z i 1)) (fun _ => rfl) hz

end DervishRepresent1196

end Donor1196

namespace DervishCount1270
open PEqualNP.CircuitLowerBounds

def canonOp : GateOp → GateOp
  | .mod m => if m ≤ 2 then .mod m else .mod 0
  | g => g

def codes : List GateOp := [.and, .or, .not, .maj, .mod 0, .mod 1, .mod 2]

theorem canonOp_mem (g : GateOp) : canonOp g ∈ codes := by
  cases g with
  | and => simp [canonOp, codes]
  | or => simp [canonOp, codes]
  | not => simp [canonOp, codes]
  | maj => simp [canonOp, codes]
  | mod m =>
    by_cases h : m ≤ 2
    · have hm : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      rcases hm with rfl | rfl | rfl <;> simp [canonOp, codes]
    · simp [canonOp, codes, h]

theorem canonOp_eval (g : GateOp) (xs : List Bool) (h : xs.length ≤ 2) :
    (canonOp g).eval xs = g.eval xs := by
  cases g with
  | and => rfl
  | or => rfl
  | not => rfl
  | maj => rfl
  | mod m =>
    by_cases hm : m ≤ 2
    · simp [canonOp, hm]
    · have hc : xs.count true ≤ xs.length := List.count_le_length
      have hlt : xs.count true < m := by omega
      simp [canonOp, hm, GateOp.eval, Nat.mod_eq_of_lt hlt]

def canonGate (g : Gate) : Gate := ⟨canonOp g.op, g.inputs⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

theorem canonStep (g : Gate) (w : List Bool) (h : g.inputs.length ≤ 2) :
    step w (canonGate g) = step w g := by
  unfold step canonGate
  rw [canonOp_eval _ _ (by simpa using h)]

theorem canonFold (gs : List Gate) (w : List Bool)
    (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.map canonGate).foldl step w = gs.foldl step w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons, canonStep g w (h g (by simp))]
    apply ih
    intro k hk
    exact h k (by simp [hk])

def canonCircuit (c : Circuit) : Circuit := ⟨c.gates.map canonGate, c.output⟩

theorem canon_wires (c : Circuit) (w : List Bool)
    (h : ∀ g ∈ c.gates, g.inputs.length ≤ 2) :
    (canonCircuit c).wires w = c.wires w :=
  canonFold c.gates w h

theorem canon_size (c : Circuit) : (canonCircuit c).size = c.size := by
  simp [canonCircuit, Circuit.size]

end DervishCount1270

namespace DervishTraceCode1270
open PEqualNP.CircuitLowerBounds

abbrev ArgCode (K : ℕ) := Unit ⊕ (Fin K ⊕ (Fin K × Fin K))
abbrev GateCode (K : ℕ) := Fin 7 × ArgCode K
abbrev Code (K S : ℕ) := Fin K × (Fin S → Option (GateCode K))

def ops : List GateOp := [.and, .or, .not, .maj, .mod 0, .mod 1, .mod 2]

def decodeArgs {K : ℕ} : ArgCode K → List ℕ
  | .inl _ => []
  | .inr (.inl i) => [i.val]
  | .inr (.inr (i,j)) => [i.val,j.val]

def decodeGate {K : ℕ} (g : GateCode K) : Gate :=
  ⟨ops.get g.1, decodeArgs g.2⟩

def decodeGates {K S : ℕ} (a : Fin S → Option (GateCode K)) : List Gate :=
  ((List.ofFn a).filterMap id).map decodeGate

theorem decodeArgs_cover (K : ℕ) (is : List ℕ) (hlen : is.length ≤ 2)
    (hindex : ∀ i ∈ is, i < K) : ∃ a : ArgCode K, decodeArgs a = is := by
  cases is with
  | nil => exact ⟨.inl (), rfl⟩
  | cons i tail =>
    have hi := hindex i (by simp)
    cases tail with
    | nil => exact ⟨.inr (.inl ⟨i,hi⟩), rfl⟩
    | cons j tail =>
      have hj := hindex j (by simp)
      cases tail with
      | nil => exact ⟨.inr (.inr (⟨i,hi⟩, ⟨j,hj⟩)), rfl⟩
      | cons k tail => simp at hlen

theorem decodeGate_cover (K : ℕ) (g : Gate) (hop : g.op ∈ ops)
    (hlen : g.inputs.length ≤ 2) (hindex : ∀ i ∈ g.inputs, i < K) :
    ∃ a : GateCode K, decodeGate a = g := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hop
  obtain ⟨a,ha⟩ := decodeArgs_cover K g.inputs hlen hindex
  refine ⟨(i,a), ?_⟩
  change (⟨ops.get i,decodeArgs a⟩ : Gate) = g
  rw [hi, ha]

theorem padList {α : Type} (S : ℕ) (xs : List α) (h : xs.length ≤ S) :
    ∃ a : Fin S → Option α, (List.ofFn a).filterMap id = xs := by
  induction S generalizing xs with
  | zero =>
    have hxs : xs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    subst xs
    exact ⟨fun i => Fin.elim0 i, by simp⟩
  | succ S ih =>
    cases xs with
    | nil =>
      obtain ⟨a,ha⟩ := ih [] (by simp)
      refine ⟨fun i => Fin.cases none a i, ?_⟩
      simpa [List.ofFn_succ] using ha
    | cons x xs =>
      have hxs : xs.length ≤ S := by simpa using h
      obtain ⟨a,ha⟩ := ih xs hxs
      refine ⟨fun i => Fin.cases (some x) a i, ?_⟩
      simpa [List.ofFn_succ, id] using congrArg (List.cons x) ha

theorem representList (K : ℕ) (gs : List Gate)
    (h : ∀ g ∈ gs, g.op ∈ ops ∧ g.inputs.length ≤ 2 ∧ ∀ i ∈ g.inputs, i < K) :
    ∃ a : List (GateCode K), a.map decodeGate = gs ∧ a.length = gs.length := by
  induction gs with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons g gs ih =>
    obtain ⟨hOp,hLen,hIndex⟩ := h g (by simp)
    obtain ⟨a,ha⟩ := decodeGate_cover K g hOp hLen hIndex
    obtain ⟨as,has,hlen⟩ := ih (fun v hv => h v (by simp [hv]))
    exact ⟨a::as, by simp [ha,has],by simp [hlen]⟩

theorem represent (K S : ℕ) (gs : List Gate) (tap : ℕ) (htap : tap < K)
    (hsize : gs.length ≤ S)
    (h : ∀ g ∈ gs, g.op ∈ ops ∧ g.inputs.length ≤ 2 ∧ ∀ i ∈ g.inputs, i < K) :
    ∃ a : Code K S, a.1.val = tap ∧ decodeGates a.2 = gs := by
  obtain ⟨gsCode, hgsCode, hlen⟩ := representList K gs h
  obtain ⟨a,ha⟩ := padList S gsCode (by simpa [hlen] using hsize)
  exact ⟨(⟨tap,htap⟩,a), rfl, (congrArg (List.map decodeGate) ha).trans hgsCode⟩

theorem code_card (K S : ℕ) :
    Fintype.card (Code K S) = K*(1+7*(1+K+K^2))^S := by
  simp [Code, GateCode, ArgCode, pow_two, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

end DervishTraceCode1270

namespace DervishCountArithmetic1270

theorem linear_lt_half (t : Nat) (ht : 6 ≤ t) : 3*t+8 < 2^(t-1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction k with
  | zero => decide
  | succ k ih =>
    have hs : 6 + (k + 1) - 1 = (6 + k - 1) + 1 := by omega
    rw [hs, pow_succ]
    omega

theorem input_bound (t : Nat) (ht : 6 ≤ t) : 4*t+4 ≤ 2^t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 6 + (k + 1) = (6 + k) + 1 by omega, pow_succ]
    omega

theorem code_alphabet_le (t K : Nat) (hK₀ : 1 ≤ K) (hK : K ≤ 2^(t+1)) :
    1 + 7*(1+K+K^2) ≤ 2^(2*t+7) := by
  have hKK : K ≤ K*K := by simpa using Nat.mul_le_mul_left K hK₀
  have h1KK : 1 ≤ K*K := hK₀.trans hKK
  calc
    1 + 7*(1+K+K^2) ≤ 32*K^2 := by
      rw [pow_two]
      omega
    _ ≤ 32 * (2^(t+1))^2 := Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left hK 2)
    _ = 2^(2*t+7) := by
      rw [show (32 : Nat) = 2^5 by decide, ← pow_mul, ← pow_add]
      congr 1
      omega

theorem trace_exp_bound (t : Nat) (ht : 6 ≤ t) :
    (t+1) + (2*t+7)*2^t < 2^(2*t-1) := by
  have hS : 0 < (2 : Nat)^t := Nat.pow_pos (by decide)
  have h1 : 1 ≤ (2 : Nat)^t := by omega
  have hA : t+1 ≤ 2^t*(t+1) := by simpa using Nat.mul_le_mul_right (t+1) h1
  calc
    (t+1) + (2*t+7)*2^t ≤ 2^t*(t+1) + (2*t+7)*2^t := Nat.add_le_add_right hA _
    _ = 2^t*(3*t+8) := by
      rw [Nat.mul_comm (2*t+7), ← Nat.mul_add]
      congr 1
      omega
    _ < 2^t*2^(t-1) := Nat.mul_lt_mul_of_pos_left (linear_lt_half t ht) hS
    _ = 2^(2*t-1) := by rw [← pow_add]; congr 1; omega

theorem trace_card_budget (t : Nat) (ht : 6 ≤ t) :
    let S := 2^t
    let K := 4*t+4+S
    K * (1+7*(1+K+K^2))^S < 2^(2^(2*t-1)) := by
  dsimp
  have hK : 4*t+4+2^t ≤ 2^(t+1) := by
    rw [pow_succ]
    have hs := input_bound t ht
    omega
  have hK₀ : 1 ≤ 4*t+4+2^t := by omega
  have hB := code_alphabet_le t (4*t+4+2^t) hK₀ hK
  calc
    _ ≤ 2^(t+1) * (2^(2*t+7))^(2^t) :=
      Nat.mul_le_mul hK (Nat.pow_le_pow_left hB _)
    _ = 2^((t+1)+(2*t+7)*2^t) := by rw [← pow_mul, ← pow_add]
    _ < _ := Nat.pow_lt_pow_right (by decide) (trace_exp_bound t ht)

end DervishCountArithmetic1270

namespace DervishTraceCount1270
open PEqualNP.CircuitLowerBounds
open DervishTraceCode1270 (Code decodeGates)

theorem read_mem_lt {N : ℕ} {C : Circuit}
    (h : PEqualNP.MetaComplexity.NestedCover.ReadsBack N C)
    {g : Gate} (hg : g ∈ C.gates) {i : ℕ} (hi : i ∈ g.inputs) : i < N + C.size := by
  obtain ⟨k,hk⟩ := List.mem_iff_get.mp hg
  have hAt : PEqualNP.MetaComplexity.NestedCover.gateAt C k.val = g := by
    rw [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_get C.gates _ k, hk]
  have hk' := h k.val k.isLt i (by rwa [hAt])
  have hlen : k.val < C.size := k.isLt
  omega

abbrev CodeAt (N S : ℕ) := Code (N+S) S

def trace {α : Type} (N S : ℕ) (encode : α → List Bool)
    (a : CodeAt N S) (z : α) : Bool :=
  let C : Circuit := ⟨decodeGates a.2, a.1.val⟩
  (C.wires (encode z)).getD a.1.val false

theorem trace_covers {α : Type} (N S : ℕ) (encode : α → List Bool)
    (C : Circuit) (p : Fin (N+C.size)) (hs : C.size ≤ S)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hback : PEqualNP.MetaComplexity.NestedCover.ReadsBack N C) :
    ∃ a : CodeAt N S, ∀ z, trace N S encode a z = (C.wires (encode z)).getD p.val false := by
  let D := DervishCount1270.canonCircuit C
  have hDSize : D.gates.length ≤ S := (DervishCount1270.canon_size C).le.trans hs
  have hTap : p.val < N+S := p.isLt.trans_le (Nat.add_le_add_left hs N)
  have hValid : ∀ g ∈ D.gates, g.op ∈ DervishTraceCode1270.ops ∧
      g.inputs.length ≤ 2 ∧ ∀ i ∈ g.inputs, i < N+S := by
    intro g hg
    change g ∈ C.gates.map DervishCount1270.canonGate at hg
    obtain ⟨orig, ho, rfl⟩ := List.mem_map.mp hg
    refine ⟨DervishCount1270.canonOp_mem _, hlen orig ho, ?_⟩
    intro i hi
    exact (read_mem_lt hback ho hi).trans_le (Nat.add_le_add_left hs N)
  obtain ⟨a, ha, hg⟩ := DervishTraceCode1270.represent (N+S) S D.gates p.val hTap hDSize hValid
  refine ⟨a, fun z => ?_⟩
  change ((⟨decodeGates a.2, a.1.val⟩ : Circuit).wires (encode z)).getD a.1.val false = _
  rw [ha, hg]
  have hWire : ((⟨D.gates,p.val⟩ : Circuit).wires (encode z)) = D.wires (encode z) := rfl
  rw [hWire, DervishCount1270.canon_wires C (encode z) hlen]

theorem exact_exp (b : ℕ) (hb : 6 ≤ b) :
    let r := 2^b-1
    let t := r/2
    6 ≤ t ∧ r = 2*t+1 := by
  dsimp
  have hLo : 2^6 ≤ (2:ℕ)^b := Nat.pow_le_pow_right (by decide) hb
  have hL : (64:ℕ) ≤ 2^b := hLo
  have hEven : (2:ℕ)^b = 2^(b-1)*2 := by
    conv_lhs => rw [show b = (b-1)+1 by omega, pow_succ]
  omega

theorem code_small (b : ℕ) (hb : 6 ≤ b) :
    let r := 2^b-1
    Fintype.card (CodeAt (2*r+2) (2^(r/2))) < Fintype.card (Finset (Fin (r-2)) → Bool) := by
  dsimp only
  set r : ℕ := 2^b-1
  set t : ℕ := r/2
  have h := exact_exp b hb
  change 6 ≤ t ∧ r = 2*t+1 at h
  rw [DervishTraceCode1270.code_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_finset,
    Fintype.card_fin]
  simpa only [show 2*r+2+2^t = 4*t+4+2^t by omega, show r-2 = 2*t-1 by omega] using
    DervishCountArithmetic1270.trace_card_budget t h.1

theorem missing_trace (b : ℕ) (hb : 6 ≤ b) :
    let r := 2^b-1
    ∀ word : Finset (Fin (r-2)) → Finset (Fin (2*r)),
    ∃ f : Finset (Fin (r-2)) → Bool,
    ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*r+2) C →
      ∀ p : Fin (2*r+2+C.size),
      (∀ z, (C.wires (List.ofFn (fun i : Fin (2*r) => decide (i ∈ word z)) ++ [false,true])).getD p.val false = f z) →
      2^(r/2) < C.size := by
  classical
  dsimp only
  set r : ℕ := 2^b-1
  intro word
  let enc : Finset (Fin (r-2)) → List Bool := fun z =>
    List.ofFn (fun i : Fin (2*r) => decide (i ∈ word z)) ++ [false,true]
  let tr := trace (2*r+2) (2^(r/2)) enc
  have hNS : ¬ Function.Surjective tr := by
    intro hS
    exact (Nat.not_le_of_lt (code_small b hb)) (Fintype.card_le_of_surjective tr hS)
  obtain ⟨f,hf⟩ := not_forall.mp hNS
  refine ⟨f, ?_⟩
  intro C hC hB p hOutput
  by_contra! hSz
  obtain ⟨a,ha⟩ := trace_covers (2*r+2) (2^(r/2)) enc C p hSz (fun g hg => (hC g hg).2) hB
  exact hf ⟨a, funext fun z => (ha z).trans (hOutput z)⟩

end DervishTraceCount1270

namespace Rank

variable {α : Type*} [DecidableEq α]

private def rank (r : ℕ) (bad : Finset (Finset α)) (x : Finset α) : ℕ :=
  if x ∈ bad then r - 1 else min r x.card

private theorem rank_of_bad (r : ℕ) (bad : Finset (Finset α)) (x : Finset α)
    (hx : x ∈ bad) : rank r bad x = r - 1 := by simp [rank, hx]

private theorem rank_of_good (r : ℕ) (bad : Finset (Finset α)) (x : Finset α)
    (hx : x ∉ bad) : rank r bad x = min r x.card := by simp [rank, hx]

private theorem rank_mono (r : ℕ) (hr : 2 ≤ r) (bad : Finset (Finset α))
    (hbad : ∀ x ∈ bad, x.card = r) : Monotone (rank r bad) := by
  intro x y hxy
  by_cases hx : x ∈ bad
  · rw [rank_of_bad _ _ _ hx]
    by_cases hy : y ∈ bad
    · rw [rank_of_bad _ _ _ hy]
    · rw [rank_of_good _ _ _ hy]
      have hcard : r ≤ y.card := (hbad x hx) ▸ Finset.card_le_card hxy
      omega
  · rw [rank_of_good _ _ _ hx]
    by_cases hy : y ∈ bad
    · rw [rank_of_bad _ _ _ hy]
      have hcard : x.card ≤ r := (hbad y hy) ▸ Finset.card_le_card hxy
      have hne : x ≠ y := by intro he; exact hx (he ▸ hy)
      have hlt : x.card < y.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hxy, hne⟩)
      have hxlt : x.card < r := (hbad y hy) ▸ hlt
      have heq : min r x.card = x.card := min_eq_right (Nat.le_of_lt hxlt)
      rw [heq]
      omega
    · rw [rank_of_good _ _ _ hy]
      exact min_le_min_left _ (Finset.card_le_card hxy)

private theorem min_submod (r a b i u : ℕ) (hi : i ≤ a) (hi' : i ≤ b)
    (hu : a ≤ u) (hu' : b ≤ u) (hsum : u + i = a + b) :
    min r u + min r i ≤ min r a + min r b := by omega

private theorem min_slack_one (r b i u : ℕ) (hi : i < b)
    (hi' : i < r) (hu : r < u) (hsum : u + i = r + b) :
    min r u + min r i + 1 ≤ min r r + min r b := by omega

private theorem min_slack_two (r i u : ℕ) (hi : i + 2 ≤ r)
    (hu : r ≤ u) :
    min r u + min r i + 2 ≤ min r r + min r r := by omega

private theorem rank_le_uniform (r : ℕ) (bad : Finset (Finset α))
    (hbad : ∀ x ∈ bad, x.card = r) (x : Finset α) :
    rank r bad x ≤ min r x.card := by
  by_cases hx : x ∈ bad
  · rw [rank_of_bad _ _ _ hx, hbad x hx]
    omega
  · rw [rank_of_good _ _ _ hx]

private theorem rank_submod (r : ℕ) (bad : Finset (Finset α))
    (hbad : ∀ x ∈ bad, x.card = r)
    (hsep : ∀ x ∈ bad, ∀ y ∈ bad, x ≠ y → (x ∩ y).card + 2 ≤ r)
    (x y : Finset α) :
    rank r bad (x ∪ y) + rank r bad (x ∩ y) ≤ rank r bad x + rank r bad y := by
  by_cases hxy : x ⊆ y
  · rw [Finset.union_eq_right.mpr hxy, Finset.inter_eq_left.mpr hxy]
    omega
  by_cases hyx : y ⊆ x
  · rw [Finset.union_eq_left.mpr hyx, Finset.inter_eq_right.mpr hyx]
  have hi_x : (x ∩ y).card < x.card := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, by
      intro he; exact hxy (Finset.inter_eq_left.mp he)⟩)
  have hi_y : (x ∩ y).card < y.card := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, by
      intro he; exact hyx (Finset.inter_eq_right.mp he)⟩)
  have hu_x : x.card < (x ∪ y).card := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, by
      intro he; exact hyx (Finset.union_eq_left.mp he.symm)⟩)
  have hu_y : y.card < (x ∪ y).card := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_right, by
      intro he; exact hxy (Finset.union_eq_right.mp he.symm)⟩)
  have hsum := Finset.card_union_add_card_inter x y
  have hupper : rank r bad (x ∪ y) + rank r bad (x ∩ y) ≤
      min r (x ∪ y).card + min r (x ∩ y).card :=
    Nat.add_le_add (rank_le_uniform r bad hbad _) (rank_le_uniform r bad hbad _)
  apply le_trans hupper
  by_cases hx : x ∈ bad
  · rw [rank_of_bad _ _ _ hx]
    by_cases hy : y ∈ bad
    · rw [rank_of_bad _ _ _ hy]
      have hne : x ≠ y := by intro he; exact hxy (he ▸ Finset.Subset.rfl)
      have hsmall := hsep x hx y hy hne
      have hxcard := hbad x hx
      have hycard := hbad y hy
      rw [hxcard] at hi_x hu_x hsum
      rw [hycard] at hi_y hu_y hsum
      have hh := min_slack_two r (x ∩ y).card (x ∪ y).card hsmall (Nat.le_of_lt hu_x)
      omega
    · rw [rank_of_good _ _ _ hy]
      have hxcard := hbad x hx
      rw [hxcard] at hi_x hu_x hsum
      have hh := min_slack_one r y.card (x ∩ y).card (x ∪ y).card hi_y hi_x hu_x hsum
      omega
  · rw [rank_of_good _ _ _ hx]
    by_cases hy : y ∈ bad
    · rw [rank_of_bad _ _ _ hy]
      have hycard := hbad y hy
      rw [hycard] at hi_y hu_y hsum
      have hh := min_slack_one r x.card (x ∩ y).card (x ∪ y).card hi_x hi_y hu_y
        (by omega)
      omega
    · rw [rank_of_good _ _ _ hy]
      exact min_submod r x.card y.card (x ∩ y).card (x ∪ y).card
        (Nat.le_of_lt hi_x) (Nat.le_of_lt hi_y)
        (Nat.le_of_lt hu_x) (Nat.le_of_lt hu_y) hsum

private theorem rank_matroid [Fintype α] (r : ℕ) (hr : 2 ≤ r)
    (hrn : r < Fintype.card α) (bad : Finset (Finset α))
    (hbad : ∀ x ∈ bad, x.card = r)
    (hsep : ∀ x ∈ bad, ∀ y ∈ bad, x ≠ y → (x ∩ y).card + 2 ≤ r) :
    rank r bad ∅ = 0 ∧ Monotone (rank r bad) ∧
      (∀ x, rank r bad x ≤ x.card) ∧
      (∀ x y, rank r bad (x ∪ y) + rank r bad (x ∩ y) ≤
        rank r bad x + rank r bad y) ∧ rank r bad Finset.univ = r := by
  have hempty : (∅ : Finset α) ∉ bad := by
    intro h; have hh := hbad ∅ h; simp at hh; omega
  have huniv : (Finset.univ : Finset α) ∉ bad := by
    intro h; have hh := hbad Finset.univ h; simp only [Finset.card_univ] at hh; omega
  refine ⟨?_, rank_mono r hr bad hbad, ?_, rank_submod r bad hbad hsep, ?_⟩
  · simp [rank_of_good _ _ _ hempty]
  · intro x
    by_cases hx : x ∈ bad
    · rw [rank_of_bad _ _ _ hx, hbad x hx]; omega
    · rw [rank_of_good _ _ _ hx]; exact min_le_right _ _
  · rw [rank_of_good _ _ _ huniv]
    simp only [Finset.card_univ]
    exact min_eq_left (Nat.le_of_lt hrn)

private theorem rank_small (r : ℕ) (bad : Finset (Finset α))
    (hbad : ∀ x ∈ bad, x.card = r) (x : Finset α)
    (hx : x.card < r) : rank r bad x = x.card := by
  have hnot : x ∉ bad := by
    intro h; have hh := hbad x h; omega
  rw [rank_of_good _ _ _ hnot, min_eq_right (Nat.le_of_lt hx)]

private theorem rank_large (r : ℕ) (bad : Finset (Finset α))
    (hbad : ∀ x ∈ bad, x.card = r) (x : Finset α)
    (hx : r < x.card) : rank r bad x = r := by
  have hnot : x ∉ bad := by
    intro h; have hh := hbad x h; omega
  rw [rank_of_good _ _ _ hnot, min_eq_left (Nat.le_of_lt hx)]

private theorem rank_bases (r : ℕ) (hr : 1 ≤ r) (bad : Finset (Finset α))
    (hbad : ∀ x ∈ bad, x.card = r) (x : Finset α)
    (hx : x.card = r) : rank r bad x = if x ∈ bad then r - 1 else r := by
  split_ifs with hb
  · exact rank_of_bad r bad x hb
  · rw [rank_of_good r bad x hb, hx, min_self]

private theorem rank_insert_code (r : ℕ) (hr : 1 ≤ r) (bad : Finset (Finset α))
    (hbad : ∀ x ∈ bad, x.card = r) (x : Finset α) (j : α)
    (hx : x.card + 1 = r) (hj : j ∉ x) :
    rank r bad x = r - 1 ∧
    rank r bad (insert j x) = if insert j x ∈ bad then r - 1 else r := by
  have hins : (insert j x).card = r := by simp [Finset.card_insert_of_notMem hj, ← hx]
  constructor
  · rw [rank_small r bad hbad x (by omega)]; omega
  · exact rank_bases r hr bad hbad (insert j x) hins

private def data (q : ℕ) (z : Finset (Fin q)) (i : Fin q) : Fin (2 * (q + 2)) :=
  ⟨2 * i.val + (if i ∈ z then 1 else 0), by
    have hi := i.isLt
    split_ifs <;> omega⟩

private def parity (q : ℕ) (z : Finset (Fin q)) : Fin (2 * (q + 2)) :=
  ⟨2 * q + z.card % 2, by omega⟩

private def probe (q : ℕ) : Fin (2 * (q + 2)) := ⟨2 * q + 2, by omega⟩

private def word (q : ℕ) (z : Finset (Fin q)) : Finset (Fin (2 * (q + 2))) :=
  insert (parity q z) (Finset.univ.image (data q z))

private theorem data_inj (q : ℕ) (z : Finset (Fin q)) :
    Function.Injective (data q z) := by
  intro i k h
  have hi := i.isLt
  have hk := k.isLt
  have he : 2 * i.val + (if i ∈ z then 1 else 0) =
      2 * k.val + (if k ∈ z then 1 else 0) := congrArg Fin.val h
  have hh : i.val = k.val := by
    by_cases hi : i ∈ z <;> by_cases hk : k ∈ z <;> simp [hi, hk] at he <;> omega
  exact Fin.ext hh

private theorem parity_outside (q : ℕ) (z : Finset (Fin q)) :
    parity q z ∉ Finset.univ.image (data q z) := by
  intro h
  rcases Finset.mem_image.mp h with ⟨i, _, he⟩
  have hb := i.isLt
  have hdata : (data q z i).val < 2*q := by
    simp only [data]; split_ifs <;> omega
  have hp : 2*q ≤ (parity q z).val := by simp [parity]
  rw [he] at hdata
  omega

private theorem word_card (q : ℕ) (z : Finset (Fin q)) :
    (word q z).card = q + 1 := by
  rw [word, Finset.card_insert_of_notMem (parity_outside q z),
    Finset.card_image_of_injective _ (data_inj q z)]
  simp

private theorem probe_outside (q : ℕ) (z : Finset (Fin q)) :
    probe q ∉ word q z := by
  rw [word, Finset.mem_insert, Finset.mem_image]
  push_neg
  constructor
  · intro h
    have hv : (probe q).val = (parity q z).val := congrArg Fin.val h
    simp only [probe, parity] at hv
    omega
  · intro i _ he
    have hb := i.isLt
    have hd : (data q z i).val < 2*q := by
      simp only [data]; split_ifs <;> omega
    have hp : 2*q ≤ (probe q).val := by simp [probe]
    rw [he] at hd
    omega

private def odd (q : ℕ) (i : Fin q) : Fin (2 * (q + 2)) :=
  ⟨2*i.val+1, by have hi := i.isLt; omega⟩

private theorem odd_word_iff (q : ℕ) (z : Finset (Fin q)) (i : Fin q) :
    odd q i ∈ word q z ↔ i ∈ z := by
  constructor
  · intro h
    simp only [word, Finset.mem_insert, Finset.mem_image] at h
    rcases h with hp | ⟨k, _, hk⟩
    · have hv : (odd q i).val = (parity q z).val := congrArg Fin.val hp
      simp [odd, parity] at hv
      have hi := i.isLt
      omega
    · have hv : (data q z k).val = (odd q i).val := congrArg Fin.val hk
      have hi := i.isLt
      have hki := k.isLt
      have heq : k = i := by
        apply Fin.ext
        simp only [data, odd] at hv
        by_cases hm : k ∈ z <;> simp [hm] at hv <;> omega
      subst k
      simp only [data, odd] at hv
      by_cases hm : i ∈ z
      · exact hm
      · simp [hm] at hv
  · intro hi
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp [data, odd, hi]

private theorem word_inj (q : ℕ) : Function.Injective (word q) := by
  intro z w he
  ext i
  rw [← odd_word_iff q z i, ← odd_word_iff q w i, he]

private theorem rank_insert_small (r : ℕ) (bad : Finset (Finset α))
    (hbad : ∀ x ∈ bad, x.card = r) (x : Finset α) (j : α)
    (hj : j ∉ x) (hx : x.card + 1 < r) :
    rank r bad (insert j x) = rank r bad x + 1 := by
  have hc : (insert j x).card = x.card + 1 := Finset.card_insert_of_notMem hj
  rw [rank_small r bad hbad _ (by omega), rank_small r bad hbad _ (by omega), hc]

private theorem rank_insert_bad (r : ℕ) (bad : Finset (Finset α))
    (hbad : ∀ x ∈ bad, x.card = r) (x : Finset α) (j : α)
    (hx : x ∈ bad) (hj : j ∉ x) (hr : 1 ≤ r) :
    rank r bad (insert j x) = rank r bad x + 1 := by
  have hc : r < (insert j x).card := by
    rw [Finset.card_insert_of_notMem hj, hbad x hx]; omega
  rw [rank_large r bad hbad _ hc, rank_of_bad _ _ _ hx]
  omega

private theorem rank_insert_large (r : ℕ) (bad : Finset (Finset α))
    (hbad : ∀ x ∈ bad, x.card = r) (x : Finset α) (j : α)
    (hx : r < x.card) : rank r bad (insert j x) = rank r bad x := by
  have hc : r < (insert j x).card := lt_of_lt_of_le hx (Finset.card_le_card (Finset.subset_insert j x))
  rw [rank_large r bad hbad _ hc, rank_large r bad hbad _ hx]

private def badWords {β : Type*} [Fintype β] [DecidableEq β]
    (f : β → Bool) (j : α) (w : β → Finset α) : Finset (Finset α) :=
  (Finset.univ.filter (fun z => f z = false)).image (fun z => insert j (w z))

private theorem mem_badWords {β : Type*} [Fintype β] [DecidableEq β]
    (f : β → Bool) (j : α) (w : β → Finset α) (x : Finset α) :
    x ∈ badWords f j w ↔ ∃ z, f z = false ∧ x = insert j (w z) := by
  simp only [badWords, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩

private theorem badWords_card {β : Type*} [Fintype β] [DecidableEq β]
    (r : ℕ) (f : β → Bool) (j : α) (w : β → Finset α)
    (hcard : ∀ z, (w z).card + 1 = r) (hj : ∀ z, j ∉ w z)
    (x : Finset α) (hx : x ∈ badWords f j w) : x.card = r := by
  obtain ⟨z, _, rfl⟩ := (mem_badWords f j w x).mp hx
  rw [Finset.card_insert_of_notMem (hj z)]
  exact hcard z

private theorem badWords_sep {β : Type*} [Fintype β] [DecidableEq β]
    (r : ℕ) (f : β → Bool) (j : α) (w : β → Finset α)
    (hj : ∀ z, j ∉ w z) (hinj : Function.Injective w)
    (hsep : ∀ z w', z ≠ w' → ((insert j (w z)) ∩ (insert j (w w'))).card + 2 ≤ r)
    (x : Finset α) (hx : x ∈ badWords f j w)
    (y : Finset α) (hy : y ∈ badWords f j w)
    (hxy : x ≠ y) : (x ∩ y).card + 2 ≤ r := by
  obtain ⟨z, _, rfl⟩ := (mem_badWords f j w x).mp hx
  obtain ⟨w', _, rfl⟩ := (mem_badWords f j w y).mp hy
  have hne : z ≠ w' := by
    intro he; subst w'; exact hxy rfl
  exact hsep z w' hne

private theorem word_matroid [Fintype α] {β : Type*} [Fintype β] [DecidableEq β]
    (r : ℕ) (hr : 2 ≤ r) (hrn : r < Fintype.card α)
    (f : β → Bool) (j : α) (w : β → Finset α)
    (hcard : ∀ z, (w z).card + 1 = r) (hj : ∀ z, j ∉ w z)
    (hinj : Function.Injective w)
    (hsep : ∀ z w', z ≠ w' → ((insert j (w z)) ∩ (insert j (w w'))).card + 2 ≤ r) :
    (rank r (badWords f j w) ∅ = 0 ∧ Monotone (rank r (badWords f j w)) ∧
      (∀ x, rank r (badWords f j w) x ≤ x.card) ∧
      (∀ x y, rank r (badWords f j w) (x ∪ y) + rank r (badWords f j w) (x ∩ y) ≤
        rank r (badWords f j w) x + rank r (badWords f j w) y) ∧
      rank r (badWords f j w) Finset.univ = r) ∧
    (∀ x, rank r (badWords f j w) x =
      if ∃ z, f z = false ∧ x = insert j (w z) then r - 1 else min r x.card) := by
  constructor
  · apply rank_matroid r hr hrn
    · exact badWords_card r f j w hcard hj
    · exact badWords_sep r f j w hj hinj hsep
  · intro x
    simp only [rank, mem_badWords]

private theorem data_eq_iff (q : ℕ) (z w : Finset (Fin q)) (i k : Fin q) :
    data q z i = data q w k ↔ i = k ∧ (i ∈ z ↔ i ∈ w) := by
  constructor
  · intro he
    have hv : (data q z i).val = (data q w k).val := congrArg Fin.val he
    have hidx : i = k := by
      apply Fin.ext
      simp only [data] at hv
      by_cases hi : i ∈ z <;> by_cases hk : k ∈ w <;> simp [hi, hk] at hv <;> omega
    subst k
    constructor
    · rfl
    · simp only [data] at hv
      by_cases hi : i ∈ z <;> by_cases hk : i ∈ w <;> simp [hi, hk] at hv ⊢ <;> omega
  · rintro ⟨rfl, he⟩
    apply Fin.ext
    simp [data]
    by_cases hi : i ∈ z <;> by_cases hk : i ∈ w <;> simp_all

private theorem data_mem_word_iff (q : ℕ) (z w : Finset (Fin q)) (i : Fin q) :
    data q z i ∈ word q w ↔ (i ∈ z ↔ i ∈ w) := by
  rw [word, Finset.mem_insert, Finset.mem_image]
  have hpar : data q z i ≠ parity q w := by
    intro he
    have hv : (data q z i).val = (parity q w).val := congrArg Fin.val he
    have hi := i.isLt
    simp only [data, parity] at hv
    by_cases h : i ∈ z <;> simp [h] at hv <;> omega
  simp only [hpar, false_or, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk⟩
    have ⟨hidx, hbit⟩ := (data_eq_iff q z w i k).mp hk.symm
    subst k
    exact hbit
  · intro hbit
    exact ⟨i, (data_eq_iff q z w i i).mpr ⟨rfl, hbit⟩ |>.symm⟩

private theorem parity_mem_word_iff (q : ℕ) (z w : Finset (Fin q)) :
    parity q z ∈ word q w ↔ z.card % 2 = w.card % 2 := by
  rw [word, Finset.mem_insert]
  have hnot : parity q z ∉ Finset.univ.image (data q w) := by
    intro h
    rcases Finset.mem_image.mp h with ⟨i, _, he⟩
    have hb := i.isLt
    have hv : (data q w i).val = (parity q z).val := congrArg Fin.val he
    simp only [data, parity] at hv
    by_cases hi : i ∈ w <;> simp [hi] at hv <;> omega
  simp only [hnot, or_false]
  constructor
  · intro h
    have hv : (parity q z).val = (parity q w).val := congrArg Fin.val h
    simp only [parity] at hv
    omega
  · intro h
    exact Fin.ext (by simp [parity, h])

private theorem two_disagreements (q : ℕ) (z w : Finset (Fin q))
    (hne : z ≠ w) (hpar : z.card % 2 = w.card % 2) :
    ∃ i k : Fin q, i ≠ k ∧ ¬(i ∈ z ↔ i ∈ w) ∧ ¬(k ∈ z ↔ k ∈ w) := by
  obtain ⟨i, hi⟩ : ∃ i : Fin q, ¬(i ∈ z ↔ i ∈ w) := by
    by_contra hh
    apply hne
    ext i
    exact Classical.not_not.mp ((not_exists.mp hh) i)
  by_contra hh
  have hrest : z.erase i = w.erase i := by
    ext k
    by_cases hki : k = i
    · subst k; simp
    · have hkw : k ∈ z ↔ k ∈ w := by
        by_contra hc
        exact hh ⟨i, k, (fun he => hki he.symm), hi, hc⟩
      simpa [hki] using hkw
  by_cases hiz : i ∈ z
  · have hiw : i ∉ w := by intro h; exact hi ⟨fun _ => h, fun _ => hiz⟩
    have hc1 := Finset.card_erase_add_one hiz
    have hc2 := Finset.erase_eq_of_notMem hiw
    rw [hc2] at hrest
    rw [hrest] at hc1
    omega
  · have hiw : i ∈ w := by
      by_contra hh; exact hi ⟨False.elim ∘ hiz, False.elim ∘ hh⟩
    have hc1 := Finset.card_erase_add_one hiw
    have hc2 := Finset.erase_eq_of_notMem hiz
    rw [hc2] at hrest
    rw [← hrest] at hc1
    omega

private theorem two_missing (s t : Finset α) (a b : α) (ha : a ∈ s)
    (hat : a ∉ t) (hb : b ∈ s) (hbt : b ∉ t) (hne : a ≠ b) :
    (s ∩ t).card + 2 ≤ s.card := by
  have hsub : ({a, b} : Finset α) ⊆ s \ t := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp [ha, hat, hb, hbt]
  have htwo : 2 ≤ (s \ t).card := by
    have hh := Finset.card_le_card hsub
    simpa [hne] using hh
  have hsum := Finset.card_sdiff_add_card_inter s t
  omega

private theorem data_selected (q : ℕ) (z : Finset (Fin q)) (i : Fin q) :
    data q z i ∈ word q z := by
  simp only [word]
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

private theorem data_disagree (q : ℕ) (z w : Finset (Fin q)) (i : Fin q)
    (hi : ¬(i ∈ z ↔ i ∈ w)) : data q z i ∉ word q w := by
  intro h
  exact hi ((data_mem_word_iff q z w i).mp h)

private theorem data_ne_index (q : ℕ) (z : Finset (Fin q)) (i k : Fin q)
    (hik : i ≠ k) : data q z i ≠ data q z k := fun he => hik (data_inj q z he)

private theorem word_distance (q : ℕ) (z w : Finset (Fin q))
    (hne : z ≠ w) : ((word q z) ∩ (word q w)).card + 2 ≤ q + 1 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin q, ¬(i ∈ z ↔ i ∈ w) := by
    by_contra hh
    apply hne
    ext i
    exact Classical.not_not.mp ((not_exists.mp hh) i)
  have hfirst := data_selected q z i
  have hfirstw := data_disagree q z w i hi
  by_cases hpar : z.card % 2 = w.card % 2
  · obtain ⟨a, b, hab, ha, hb⟩ := two_disagreements q z w hne hpar
    have hbound := two_missing (word q z) (word q w) (data q z a) (data q z b)
      (data_selected q z a) (data_disagree q z w a ha)
      (data_selected q z b) (data_disagree q z w b hb) (data_ne_index q z a b hab)
    rw [word_card q z] at hbound
    omega
  · have hparz : parity q z ∈ word q z := Finset.mem_insert_self _ _
    have hparw : parity q z ∉ word q w := by
      intro hh
      exact hpar ((parity_mem_word_iff q z w).mp hh)
    have hne' : data q z i ≠ parity q z := by
      intro he
      exact parity_outside q z (he.symm ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    have hbound := two_missing (word q z) (word q w) (data q z i) (parity q z)
      hfirst hfirstw hparz hparw hne'
    rw [word_card q z] at hbound
    omega

private theorem inserted_word_distance (q : ℕ) (z w : Finset (Fin q))
    (hne : z ≠ w) :
    ((insert (probe q) (word q z)) ∩ (insert (probe q) (word q w))).card + 2 ≤ q + 2 := by
  have heq : (insert (probe q) (word q z)) ∩ (insert (probe q) (word q w)) =
      insert (probe q) ((word q z) ∩ (word q w)) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert]
    tauto
  rw [heq, Finset.card_insert_of_notMem (fun hh => probe_outside q z (Finset.mem_inter.mp hh).1)]
  have hh := word_distance q z w hne
  omega

private theorem concrete_matroid (q : ℕ) (f : Finset (Fin q) → Bool) :
    (rank (q+2) (badWords f (probe q) (word q)) ∅ = 0 ∧
      Monotone (rank (q+2) (badWords f (probe q) (word q))) ∧
      (∀ x, rank (q+2) (badWords f (probe q) (word q)) x ≤ x.card) ∧
      (∀ x y, rank (q+2) (badWords f (probe q) (word q)) (x ∪ y) +
        rank (q+2) (badWords f (probe q) (word q)) (x ∩ y) ≤
        rank (q+2) (badWords f (probe q) (word q)) x +
        rank (q+2) (badWords f (probe q) (word q)) y) ∧
      rank (q+2) (badWords f (probe q) (word q)) Finset.univ = q+2) ∧
    (∀ x, rank (q+2) (badWords f (probe q) (word q)) x =
      if ∃ z, f z = false ∧ x = insert (probe q) (word q z)
      then q+1 else min (q+2) x.card) := by
  have hrn : q + 2 < Fintype.card (Fin (2 * (q + 2))) := by simp
  simpa only [show q + 2 - 1 = q + 1 by omega] using
    word_matroid (q+2) (by omega) hrn f (probe q) (word q)
      (by intro z; rw [word_card]) (probe_outside q)
      (word_inj q) (inserted_word_distance q)

private theorem inserted_word_mem_bad_iff (q : ℕ) (f : Finset (Fin q) → Bool)
    (z : Finset (Fin q)) :
    insert (probe q) (word q z) ∈ badWords f (probe q) (word q) ↔ f z = false := by
  rw [mem_badWords]
  constructor
  · rintro ⟨w, hw, he⟩
    have hword : word q z = word q w := by
      have hh := congrArg (fun s : Finset (Fin (2 * (q+2))) => s.erase (probe q)) he
      simpa [Finset.erase_eq_of_notMem (probe_outside q z),
        Finset.erase_eq_of_notMem (probe_outside q w)] using hh
    exact (word_inj q hword) ▸ hw
  · intro hz
    exact ⟨z, hz, rfl⟩

private theorem concrete_rank_code (q : ℕ) (f : Finset (Fin q) → Bool)
    (z : Finset (Fin q)) :
    rank (q+2) (badWords f (probe q) (word q)) (word q z) = q+1 ∧
    rank (q+2) (badWords f (probe q) (word q)) (insert (probe q) (word q z)) =
      if f z = false then q+1 else q+2 := by
  have hh := rank_insert_code (q+2) (by omega)
    (badWords f (probe q) (word q))
    (badWords_card (q+2) f (probe q) (word q) (by intro z; rw [word_card]) (probe_outside q))
    (word q z) (probe q) (by rw [word_card]) (probe_outside q z)
  simpa only [show q + 2 - 1 = q+1 by omega, inserted_word_mem_bad_iff] using hh

private theorem exact_constants (b : ℕ) (hb : 6 ≤ b) :
    let r := 2^b-1
    let q := r-2
    q+2 = r ∧ 2*(q+2) = 2*r := by
  have hpow : 2^6 ≤ 2^b := Nat.pow_le_pow_right (by omega) hb
  dsimp
  omega

end Rank

namespace DervishPacking1270
open PEqualNP
open PEqualNP.CircuitLowerBounds

abbrev Mat (n r : ℕ) (R : Finset (Fin n) → ℕ) : Prop :=
  R ∅ = 0 ∧ Monotone R ∧ (∀ x, R x ≤ x.card) ∧
  (∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y) ∧ R Finset.univ = r

abbrev Fits {n : ℕ} (R : Finset (Fin n) → ℕ) (g : Finset (Fin n) → Fin n → Bool) : Prop :=
  (∀ x j, R x < R (insert j x) → g x j = true) ∧ (∀ x j, j ∈ x → g x j = false)

abbrev Computes {n : ℕ} (C : Circuit) (g : Finset (Fin n) → Fin n → Bool) : Prop :=
  MetaComplexity.FanInTwo C ∧ MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
  C.output < n+2+C.size ∧ ∃ tap : Fin n → Fin (n+2+C.size),
    ∀ x j, (C.wires (List.ofFn (fun i : Fin n => decide (i∈x)) ++ [false,true])).getD (tap j).val false = g x j

noncomputable def RankFormula {n q : ℕ} (r : ℕ) (j : Fin n) (word : Finset (Fin q) → Finset (Fin n))
    (f : Finset (Fin q) → Bool) (R : Finset (Fin n) → ℕ) : Prop := by
  classical
  exact ∀ x, R x = if ∃ z, f z = false ∧ x = insert j (word z) then r-1 else min r x.card

theorem rank_package (r q : ℕ) (hq : q+2=r) :
    ∃ (j : Fin (2*r)) (word : Finset (Fin q) → Finset (Fin (2*r)))
      (rank : (Finset (Fin q) → Bool) → Finset (Fin (2*r)) → ℕ),
    Function.Injective word ∧ (∀ z, (word z).card = r-1 ∧ j ∉ word z) ∧
    ∀ f, Mat (2*r) r (rank f) ∧ RankFormula r j word f (rank f) := by
  subst r
  refine ⟨Rank.probe q, Rank.word q, (fun f => Rank.rank (q+2) (Rank.badWords f (Rank.probe q) (Rank.word q))),
    Rank.word_inj q, ?_, ?_⟩
  · intro z
    exact ⟨(Rank.word_card q z).trans (by omega), Rank.probe_outside q z⟩
  · intro f
    obtain ⟨hm,hf⟩ := Rank.concrete_matroid q f
    refine ⟨hm, ?_⟩
    intro x
    have hh := hf x
    by_cases h : ∃ z, f z = false ∧ x = insert (Rank.probe q) (Rank.word q z)
    · simpa only [if_pos h,show q+2-1=q+1 by omega] using hh
    · simpa only [if_neg h] using hh

theorem fits_nonmember {n : ℕ} (R : Finset (Fin n) → ℕ) :
    Fits R (fun x j => decide (j ∉ x)) := by
  constructor
  · intro x j h
    apply decide_eq_true
    intro hj
    exact (Nat.lt_irrefl _) ((Finset.insert_eq_of_mem hj) ▸ h)
  · intro x j hj
    simp [hj]

theorem size_of_forced (b : ℕ) (hb : 6 ≤ b)
    {j : Fin (2*(2^b-1))}
    (word : Finset (Fin ((2^b-1)-2)) → Finset (Fin (2*(2^b-1)))) :
    ∃ f : Finset (Fin ((2^b-1)-2)) → Bool,
    ∀ C g, Computes C g → (∀ z, g (word z) j = f z) → 2^((2^b-1)/2) < C.size := by
  obtain ⟨f,hf⟩ := DervishTraceCount1270.missing_trace b hb word
  refine ⟨f, ?_⟩
  rintro C g ⟨hC,hB,_,tap,htap⟩ hForced
  exact hf C hC hB (tap j) (fun z => (htap (word z) j).trans (hForced z))

end DervishPacking1270

namespace DervishPacking1270
open PEqualNP PEqualNP.CircuitLowerBounds

noncomputable def ComputesClassical {n : ℕ} (C : Circuit) (g : Finset (Fin n) → Fin n → Bool) : Prop :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  MetaComplexity.FanInTwo C ∧ MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
  C.output < n+2+C.size ∧ ∃ tap : Fin n → Fin (n+2+C.size),
    ∀ x j, (C.wires (List.ofFn (fun i : Fin n => decide (i∈x)) ++ [false,true])).getD (tap j).val false = g x j

theorem computes_iff {n : ℕ} (C : Circuit) (g : Finset (Fin n) → Fin n → Bool) :
    ComputesClassical C g ↔ Computes C g := by
  unfold ComputesClassical Computes
  have h : ∀ x : Finset (Fin n), (fun i : Fin n => @decide (i ∈ x) (Classical.propDecidable _)) =
      (fun i : Fin n => decide (i ∈ x)) := by
    intro x
    funext i
    exact congrArg (fun d => @decide (i ∈ x) d) (Subsingleton.elim _ _)
  simp only [h]

theorem classicalDecEq_fin (n : ℕ) :
    (fun a b : Fin n => Classical.propDecidable (a = b)) = instDecidableEqFin n := by
  funext a b
  exact Subsingleton.elim _ _

theorem classical_insert_fin {n : ℕ} (i : Fin n) (x : Finset (Fin n)) :
    @insert _ _ (@Finset.instInsert (Fin n) (fun a b => Classical.propDecidable (a=b))) i x = insert i x := by
  rw [classicalDecEq_fin]

theorem classical_max_fin {n : ℕ} (x y : Finset (Fin n)) :
    @max _ (@Finset.instMax (Fin n) (fun a b => Classical.propDecidable (a=b))) x y = x ∪ y := by
  rw [classicalDecEq_fin]

theorem classical_min_fin {n : ℕ} (x y : Finset (Fin n)) :
    @min _ (@Finset.instMin (Fin n) (fun a b => Classical.propDecidable (a=b))) x y = x ∩ y := by
  rw [classicalDecEq_fin]

theorem classical_nonmem_fin {n : ℕ} (x : Finset (Fin n)) (i : Fin n) :
    @decide (i ∉ x) (Classical.propDecidable _) = decide (i ∉ x) :=
  congrArg (fun d => @decide (i ∉ x) d) (Subsingleton.elim _ _)

theorem assembled_if
    (first : ∀ b : ℕ, ∀ n, ∀ R : Finset (Fin n) → ℕ, Monotone R → (∀ x, R x < 2^b) →
      ∃ C g, Computes C g ∧ Fits R g ∧ NotBracket.notCount C = b)
    (saturate : ∀ b : ℕ, 6 ≤ b →
      let r := 2^b-1
      let n := 2*r
      let q := r-2
      ∀ (j : Fin n) (word : Finset (Fin q) → Finset (Fin n)) (f : Finset (Fin q) → Bool)
        (R : Finset (Fin n) → ℕ), Function.Injective word →
        (∀ z, (word z).card = r-1 ∧ j ∉ word z) → Mat n r R → RankFormula r j word f R →
        ∀ C g, Computes C g → Fits R g →
        b ≤ NotBracket.notCount C ∧ (NotBracket.notCount C ≤ b → ∀ z, g (word z) j = f z))
    (second : ∀ b : ℕ, 6 ≤ b →
      let n := 2*(2^b-1)
      ∃ C, Computes C (fun (x : Finset (Fin n)) (i : Fin n) => decide (i ∉ x)) ∧
         NotBracket.notCount C = b+1 ∧ C.size ≤ 16*(n+2)^3) :
(letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ b : Nat, 6 ≤ b →
  let r := 2^b-1
  let n := 2*r
  let q := r-2
  let mat := fun (R : Finset (Fin n) → Nat) =>
    R ∅ = 0 ∧ Monotone R ∧ (∀ x, R x ≤ x.card) ∧
    (∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y) ∧ R Finset.univ = r
  let fits := fun (R : Finset (Fin n) → Nat) (g : Finset (Fin n) → Fin n → Bool) =>
    (∀ x j, R x < R (insert j x) → g x j = true) ∧ (∀ x j, j ∈ x → g x j = false)
  let computes := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (g : Finset (Fin n) → Fin n → Bool) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ ∃ tap : Fin n → Fin (n+2+C.size),
      ∀ x j, let input := List.ofFn (fun i : Fin n => decide (i∈x)) ++ [false,true]
             (C.wires input).getD (tap j).val false = g x j
  ∃ (j : Fin n) (word : Finset (Fin q) → Finset (Fin n))
    (rank : (Finset (Fin q) → Bool) → Finset (Fin n) → Nat),
    Function.Injective word ∧ (∀ z, (word z).card = r-1 ∧ j ∉ word z) ∧
    (∀ f, mat (rank f) ∧ ∀ x, rank f x =
      if ∃ z, f z = false ∧ x = insert j (word z) then r-1 else min r x.card) ∧
    (∀ f, (∃ C g, computes C g ∧ fits (rank f) g ∧ PEqualNP.NotBracket.notCount C = b) ∧
      ∀ C g, computes C g → fits (rank f) g →
        b ≤ PEqualNP.NotBracket.notCount C ∧
        (PEqualNP.NotBracket.notCount C ≤ b → ∀ z, g (word z) j = f z)) ∧
    (∃ C, let g := fun (x : Finset (Fin n)) (i : Fin n) => decide (i ∉ x)
          computes C g ∧ (∀ f, fits (rank f) g) ∧
          PEqualNP.NotBracket.notCount C = b+1 ∧ C.size ≤ 16*(n+2)^3) ∧
    ∃ f, ∀ C g, computes C g → fits (rank f) g → PEqualNP.NotBracket.notCount C ≤ b →
      2^(r/2) < C.size) := by
  intro b hb
  dsimp only
  simp only [classical_insert_fin, classical_max_fin, classical_min_fin, classical_nonmem_fin]
  set r : ℕ := 2^b-1
  have hq : (r-2)+2=r := (Rank.exact_constants b hb).1
  obtain ⟨j,word,rank,hInj,hWords,hRank⟩ := rank_package r (r-2) hq
  refine ⟨j,word,rank,hInj,hWords,?_,?_,?_,?_⟩
  · intro f
    have h := hRank f
    refine ⟨h.1, ?_⟩
    intro x
    have hFormula := h.2 x
    by_cases hBad : ∃ z, f z = false ∧ x = insert j (word z)
    · simpa only [if_pos hBad] using hFormula
    · simpa only [if_neg hBad] using hFormula
  · intro f
    have h := hRank f
    constructor
    · have hpow : 0 < (2:ℕ)^b := Nat.pow_pos (by decide)
      have hBound : ∀ x, rank f x < 2^b := by
        intro x
        have hLE : rank f x ≤ r := (h.1.2.1 (Finset.subset_univ x)).trans_eq h.1.2.2.2.2
        omega
      obtain ⟨C,g,hc,hf,hn⟩ := first b (2*r) (rank f) h.1.2.1 hBound
      exact ⟨C,g,(computes_iff C g).mpr hc,hf,hn⟩
    · intro C g hc hf
      exact saturate b hb j word f (rank f) hInj hWords h.1 h.2 C g ((computes_iff C g).mp hc) hf
  · obtain ⟨C,hc,hn,hs⟩ := second b hb
    refine ⟨C,?_,?_,hn,hs⟩
    · exact (computes_iff C _).mpr hc
    · intro f
      exact fits_nonmember (rank f)
  · obtain ⟨f,hf⟩ := size_of_forced b hb (j := j) word
    refine ⟨f,?_⟩
    intro C g hc hfit hn
    have h := hRank f
    have hc' := (computes_iff C g).mp hc
    exact hf C g hc' ((saturate b hb j word f (rank f) hInj hWords h.1 h.2 C g hc' hfit).2 hn)

end DervishPacking1270

namespace Inverter1270
open PEqualNP.Outside.L_lib_1270.Donor1196
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

open PEqualNP.Outside.L_lib_1270.Donor1196
open DervishBuild1196 DervishBuild1196.Build Sort1196

def wordInput {n : Nat} (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true]

theorem wordInput_len {n : Nat} (x : Finset (Fin n)) : (wordInput x).length = n+2 := by
  simp [wordInput]

theorem raw_bit {n : Nat} (x : Finset (Fin n)) (j : Fin n) :
    (wordInput x).getD j.val false = decide (j ∈ x) := by
  rw [wordInput, getD_append_left (by simp)]
  simp

theorem zero_bit {n : Nat} (x : Finset (Fin n)) :
    (wordInput x).getD n false = false := by
  rw [wordInput, List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem input_taps (n : Nat) (s : Build (n+2)) :
    Sort1196.Taps (sortKit (input := wordInput (n:=n)) wordInput_len) s
      (List.ofFn (fun j : Fin n => fun x : Finset (Fin n) => decide (j ∈ x))) := by
  apply DervishWire1196.taps_of_indexed
  intro j hj
  have hn : j<n := by simpa using hj
  let i : Fin n := ⟨j,hn⟩
  refine ⟨j,?_⟩
  have h := read_input (input := wordInput (n:=n)) wordInput_len s j (by omega : j<n+2)
  change Read wordInput s j _
  have hf : (List.ofFn (fun j : Fin n => fun x : Finset (Fin n) => decide (j ∈ x))).getD j
      (fun _ => false) = fun x => decide (i ∈ x) := by
    simp [List.getD_eq_getElem?_getD, hn, i]
  rw [hf]
  exact ⟨h.1, fun x => (h.2 x).trans (by simpa [i] using raw_bit x i)⟩

theorem zero_read (n : Nat) (s : Build (n+2)) :
    Read (wordInput (n:=n)) s n (fun _ => false) := by
  have h := read_input (input := wordInput (n:=n)) wordInput_len s n (by omega : n<n+2)
  convert h using 1
  funext x
  exact (zero_bit x).symm

theorem input_inversion (n b : Nat) (hn : n < 2^b) :
    ∃ t : Build (n+2), ∃ tap : Fin n → Nat,
      t.cost ≤ 3*(n*(n-1))+4*n ∧ t.nots ≤ b ∧
      ∀ x j, (t.circ.wires (wordInput x)).getD (tap j) false = decide (j ∉ x) ∧
      (tap j) < n+2+t.cost := by
  classical
  let s := Build.empty (n+2)
  let fs : List (Finset (Fin n) → Bool) :=
    List.ofFn (fun j : Fin n => fun x => decide (j ∈ x))
  have fl : fs.length = n := List.length_ofFn
  obtain ⟨t,it,_,tc,tn,vi⟩ := invert_reads (input := wordInput (n:=n))
    wordInput_len hn s fs fl (input_taps n s) n (zero_read n s)
  have vtap : ∀ j : Fin n, ∃ r,
      Read wordInput t r (fun x => decide (j ∉ x)) := by
    intro j
    have va := vi j.val j.isLt
    refine ⟨it j.val,?_⟩
    convert va using 1
    funext x
    simp [fs, Sort1196.neg, List.getD_eq_getElem?_getD, j.isLt]
  choose tap ht using vtap
  refine ⟨t,tap,?_,?_,?_⟩
  · simpa [s,Build.cost,Build.empty] using tc
  · simpa [s,Build.nots,Build.circ,Build.empty,PEqualNP.NotBracket.notCount] using tn
  · intro x j
    exact ⟨(ht j).2 x,(ht j).1⟩

theorem pad_nots {X : Type} {w : Nat} (input : X → List Bool)
    (hlen : ∀ x, (input x).length = w) (d : Nat) (s : Build w)
    (zero : Nat) (vz : Read input s zero (fun _ => false)) :
    ∃ t : Build w, Ext s t ∧ t.cost ≤ s.cost+d ∧ t.nots = s.nots+d := by
  induction d generalizing s zero with
  | zero => exact ⟨s,List.prefix_rfl,by omega,by omega⟩
  | succ d ih =>
      obtain ⟨u,a,E,ca,na⟩ := emitNot hlen vz
      obtain ⟨t,Et,ct,nt⟩ := ih u zero (read_persist hlen E vz)
      refine ⟨t,E.trans Et,?_,?_⟩ <;> omega

theorem complement_circuit (n b : Nat) (hn : n < 2^b) :
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
      (tap : Fin n → Fin (n+2+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧
      (∀ x j, (C.wires (wordInput x)).getD (tap j).val false = decide (j ∉ x)) ∧
      PEqualNP.NotBracket.notCount C = b ∧
      C.size ≤ 3*(n*(n-1))+4*n+b := by
  classical
  obtain ⟨t,read,ct,nt,vr⟩ := input_inversion n b hn
  have zero : Read wordInput t n (fun _ => false) := zero_read n t
  obtain ⟨u,E,cu,nu⟩ := pad_nots wordInput wordInput_len (b-t.nots) t n zero
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨u.gates,0⟩
  let tap : Fin n → Fin (n+2+C.size) := fun j =>
    ⟨read j, by
      have h := (vr ∅ j).2
      have hcu : t.cost ≤ C.size := by
        simpa [C, Build.cost, PEqualNP.CircuitLowerBounds.Circuit.size] using E.length_le
      exact h.trans_le (Nat.add_le_add_left hcu (n+2))⟩
  have uv (j : Fin n) : Read wordInput t (read j) (fun x => decide (j ∉ x)) :=
    ⟨(vr ∅ j).2,fun x => (vr x j).1⟩
  refine ⟨C,tap,?_,?_,?_,?_,?_,?_⟩
  · exact u.fan
  · exact u.back
  · simp [C]
  · intro x j
    exact (read_persist wordInput_len E (uv j)).2 x
  · change u.nots=b
    omega
  · change u.cost ≤ 3*(n*(n-1))+4*n+b
    omega

end Inverter1270

namespace Wiring1270
open PEqualNP.Outside.L_lib_1270.Donor1196
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

theorem build_insert_threshold_bank (r : Nat) (R : Finset (Fin n) → Nat)
    (hmono : Monotone R) (s : Build (n+2)) :
    ∃ t : Build (n+2), Ext s t ∧ t.nots = s.nots ∧
      ∀ j : Fin n, ∀ k : Fin r,
        good t (fun x => decide (k.val+1 ≤ R (insert j x))) := by
  let fs : Fin n × Fin r → Finset (Fin n) → Bool :=
    fun jk x => decide (jk.2.val+1 ≤ R (insert jk.1 x))
  obtain ⟨t,E,N,V⟩ := build_bank
    (Finset.univ : Finset (Fin n × Fin r)) fs (by
      intro jk _ x y hxy hx
      exact decide_eq_true ((decide_eq_true_eq.mp hx).trans
        (hmono (Finset.insert_subset_insert jk.1 hxy)))) s
  exact ⟨t,E,N,fun j k => V (j,k) (Finset.mem_univ _)⟩

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

def gain (R : Finset (Fin n) → Nat) (x : Finset (Fin n)) (j : Fin n) : Bool :=
  decide (R x < R (insert j x))

def gain_bit (R : Finset (Fin n) → Nat) (j : Fin n) (k : Fin r)
    (x : Finset (Fin n)) : Bool :=
  decide (k.val+1 ≤ R (insert j x)) && !(decide (k.val+1 ≤ R x))

theorem gain_bit_iff (R : Finset (Fin n) → Nat) (j : Fin n) (k : Fin r)
    (x : Finset (Fin n)) :
    gain_bit R j k x = true ↔ k.val+1 ≤ R (insert j x) ∧ R x < k.val+1 := by
  simp [gain_bit]

theorem gain_as_any (r : Nat) (R : Finset (Fin n) → Nat)
    (hbound : ∀ x, R x ≤ r) (j : Fin n) :
    any_bools (Finset.univ : Finset (Fin r)) (gain_bit R j) = fun x => gain R x j := by
  funext x
  apply Bool.eq_iff_iff.mpr
  change any_bools Finset.univ (gain_bit R j) x = true ↔ gain R x j = true
  simp only [gain, any_bools, decide_eq_true_eq, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k,hk⟩
    have h := (gain_bit_iff R j k x).mp hk
    omega
  · intro h
    let k : Fin r := ⟨R x, (h.trans_le (hbound _))⟩
    exact ⟨k,(gain_bit_iff R j k x).mpr (by dsimp [k]; omega)⟩

theorem build_gain_bank (r : Nat) (R : Finset (Fin n) → Nat)
    (hbound : ∀ x, R x ≤ r) (s : Build (n+2))
    (hp : ∀ j : Fin n, ∀ k : Fin r,
      good s (fun x => decide (k.val+1 ≤ R (insert j x))))
    (hn : ∀ k : Fin r, good s (fun x => !(decide (k.val+1 ≤ R x)))) :
    ∃ t : Build (n+2), Ext s t ∧ t.nots = s.nots ∧
      ∀ j : Fin n, good t (fun x => gain R x j) := by
  classical
  obtain ⟨u,E,N,H⟩ := build_and_bank
    (Finset.univ : Finset (Fin n × Fin r))
    (fun jk x => decide (jk.2.val+1 ≤ R (insert jk.1 x)))
    (fun jk x => !(decide (jk.2.val+1 ≤ R x))) s
    (fun jk _ => hp jk.1 jk.2)
    (fun jk _ => hn jk.2)
  have hh : ∀ j : Fin n, ∀ k : Fin r, good u (gain_bit R j k) := by
    intro j k
    exact H (j,k) (Finset.mem_univ _)
  have go (idx : Finset (Fin n)) (v : Build (n+2))
      (hv : ∀ j : Fin n, ∀ k : Fin r, good v (gain_bit R j k)) :
      ∃ t : Build (n+2), Ext v t ∧ t.nots = v.nots ∧
        ∀ j ∈ idx, good t (fun x => gain R x j) := by
    induction idx using Finset.induction_on generalizing v with
    | empty => exact ⟨v,List.prefix_rfl,rfl,by simp⟩
    | @insert j idx hj ih =>
        obtain ⟨v',Ev,Nv,V⟩ := build_or_reads (Finset.univ : Finset (Fin r))
          (gain_bit R j) v (fun k _ => hv j k)
        have V' : good v' (fun x => gain R x j) := by
          rw [gain_as_any r R hbound j] at V
          exact V
        obtain ⟨t,Et,Nt,Ht⟩ := ih v' (fun i k => good_persist Ev (hv i k))
        refine ⟨t,Ev.trans Et,by omega,?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact good_persist Et V'
        · exact Ht i hi
  obtain ⟨t,Et,Nt,Ht⟩ := go Finset.univ u hh
  exact ⟨t,E.trans Et,by omega,fun j => Ht j (Finset.mem_univ _)⟩

def threshold_fs (r : Nat) (R : Finset (Fin n) → Nat) :
    List (Finset (Fin n) → Bool) :=
  List.ofFn (fun k : Fin r => fun x => decide (k.val+1 ≤ R x))

theorem threshold_fs_get (r : Nat) (R : Finset (Fin n) → Nat)
    (k : Fin r) :
    (threshold_fs r R).getD k.val (fun _ => false) =
      (fun x => decide (k.val+1 ≤ R x)) := by
  simp [threshold_fs, List.getD_eq_getElem?_getD, k.isLt]

theorem build_rank_gain (b r : Nat) (hr : r < 2^b)
    (R : Finset (Fin n) → Nat) (hmono : Monotone R)
    (hbound : ∀ x, R x ≤ r) :
    ∃ t : Build (n+2), t.nots ≤ b ∧
      ∀ j : Fin n, good t (fun x => gain R x j) := by
  classical
  let s := Build.empty (n+2)
  obtain ⟨t,Et,Nt,Vt⟩ := build_threshold_bank r R hmono s
  let fs := threshold_fs r R
  have fl : fs.length = r := by simp [fs,threshold_fs]
  have taps : Sort1196.Taps (sortKit (input := input (n:=n)) input_len) t fs := by
    apply DervishWire1196.taps_of_indexed
    intro i hi
    have hi' : i < r := by simpa [fs, threshold_fs] using hi
    let k : Fin r := ⟨i,hi'⟩
    obtain ⟨a,ha⟩ := Vt k
    refine ⟨a,?_⟩
    change Read input t a ((threshold_fs r R).getD k.val (fun _ => false))
    rw [threshold_fs_get r R k]
    exact ha
  obtain ⟨zeroWire,hz⟩ := good_zero t
  obtain ⟨u,negTap,Eu,_,Nu,vu⟩ := Inverter1270.invert_reads
    (input := input (n:=n)) input_len hr t fs fl taps zeroWire hz
  have hneg : ∀ k : Fin r,
      good u (fun x => !(decide (k.val+1 ≤ R x))) := by
    intro k
    refine ⟨negTap k.val,?_⟩
    have va := vu k.val k.isLt
    change Read input u (negTap k.val)
      (Sort1196.neg ((threshold_fs r R).getD k.val (fun _ => false))) at va
    rw [threshold_fs_get r R k] at va
    exact va
  obtain ⟨v,Ev,Nv,Vv⟩ := build_insert_threshold_bank r R hmono u
  obtain ⟨z,Ez,Nz,Vz⟩ := build_gain_bank r R hbound v Vv
    (fun k => good_persist Ev (hneg k))
  refine ⟨z,?_,Vz⟩
  have hs : s.nots = 0 := by simp [s,Build.nots,Build.circ,Build.empty,
    PEqualNP.NotBracket.notCount]
  omega

theorem first_upper (b r : Nat) (hr : r < 2^b)
    (R : Finset (Fin n) → Nat) (hmono : Monotone R)
    (hbound : ∀ x, R x ≤ r) :
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
      (g : Finset (Fin n) → Fin n → Bool),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧
      (∃ tap : Fin n → Fin (n+2+C.size),
        ∀ x j,
          (C.wires (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true])).getD
            (tap j).val false = g x j) ∧
      (∀ x j, R x < R (insert j x) → g x j = true) ∧
      (∀ x j, j ∈ x → g x j = false) ∧
      PEqualNP.NotBracket.notCount C = b := by
  classical
  obtain ⟨u,Nu,Vu⟩ := build_rank_gain b r hr R hmono hbound
  obtain ⟨zeroWire,hz⟩ := good_zero u
  obtain ⟨v,E,_,Nv⟩ := Inverter1270.pad_nots input input_len
    (b-u.nots) u zeroWire hz
  have Vv : ∀ j : Fin n, good v (fun x => gain R x j) :=
    fun j => good_persist E (Vu j)
  choose addr haddr using Vv
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨v.gates,0⟩
  let tap : Fin n → Fin (n+2+C.size) := fun j =>
    ⟨addr j, by
      have h := (haddr j).1
      simpa only [C, PEqualNP.CircuitLowerBounds.Circuit.size,
        Build.size, Build.cost] using h⟩
  refine ⟨C,gain R,?_,?_,?_,⟨tap,?_⟩,?_,?_,?_⟩
  · exact v.fan
  · exact v.back
  · simp [C]
  · intro x j
    exact (haddr j).2 x
  · intro x j h
    exact decide_eq_true h
  · intro x j hj
    simp [gain, Finset.insert_eq_of_mem hj]
  · change v.nots=b
    omega

end Wiring1270

namespace Inverter1270

theorem bit_count_le_pow (b : Nat) : b+1 ≤ 2^b := by
  induction b with
  | zero => norm_num
  | succ b ih =>
      rw [pow_succ]
      omega

theorem second_bound (b : Nat) (hb : 6 ≤ b) :
    let r := 2^b-1
    let n := 2*r
    n < 2^(b+1) ∧
      3*(n*(n-1))+4*n+(b+1) ≤ 16*(n+2)^3 := by
  have hp : 2 ≤ 2^b := by
    have hh : 1 ≤ b := by omega
    obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hh
    rw [pow_add,pow_one]
    have : 0 < 2^d := pow_pos (by omega) d
    omega
  have hn : b+1 ≤ 2*(2^b-1) := by
    have := bit_count_le_pow b
    omega
  have hnpos : 1 ≤ 2*(2^b-1) := by omega
  constructor
  · rw [pow_succ]
    omega
  · have hlarge (n : Nat) (hnpos : 1 ≤ n) (hb : b+1 ≤ n) :
      3*(n*(n-1))+4*n+(b+1) ≤ 16*(n+2)^3 := by
      have hsub : n*(n-1) ≤ n*n := Nat.mul_le_mul_left _ (Nat.sub_le n 1)
      nlinarith [sq_nonneg (n:ℤ)]
    exact hlarge _ hnpos hn

end Inverter1270

namespace Markov1270
open PEqualNP.Outside.L_lib_1270.Donor1196

private def initial {α : Type*} [DecidableEq α] {m : Nat}
    (e : Fin m ↪ α) (i : Fin (m+1)) : Finset α :=
  (Finset.univ.filter (fun t : Fin m => t.val < i.val)).image e

private theorem initial_mem {α : Type*} [DecidableEq α] {m : Nat}
    (e : Fin m ↪ α) (i : Fin (m+1)) (x : α) :
    x ∈ initial e i ↔ ∃ t : Fin m, t.val < i.val ∧ e t = x := by
  simp [initial]

private theorem initial_mono {α : Type*} [DecidableEq α] {m : Nat}
    (e : Fin m ↪ α) {i j : Fin (m+1)} (h : i ≤ j) :
    initial e i ⊆ initial e j := by
  intro x hx
  obtain ⟨t,ht,hx⟩ := (initial_mem e i x).mp hx
  exact (initial_mem e j x).mpr ⟨t, by omega, hx⟩

private theorem initial_zero {α : Type*} [DecidableEq α] {m : Nat}
    (e : Fin m ↪ α) : initial e ⟨0,by omega⟩ = ∅ := by
  ext x
  simp [initial_mem]

private theorem initial_card {α : Type*} [DecidableEq α] {m : Nat}
    (e : Fin m ↪ α) (i : Fin (m+1)) : (initial e i).card = i.val := by
  rw [initial, Finset.card_image_iff.mpr (fun _ _ _ _ h => e.injective h)]
  rw [Fin.card_filter_val_lt]
  omega

private theorem initial_next {α : Type*} [DecidableEq α] {m : Nat}
    (e : Fin m ↪ α) (i : Fin m) :
    initial e ⟨i.val+1, by omega⟩ = insert (e i) (initial e ⟨i.val,by omega⟩) := by
  ext x
  simp only [initial_mem, Finset.mem_insert]
  constructor
  · rintro ⟨t,ht,rfl⟩
    by_cases h : t = i
    · left; exact congrArg e h
    · right; exact ⟨t, by omega, rfl⟩
  · rintro (rfl | ⟨t,ht,rfl⟩)
    · exact ⟨i,by omega,rfl⟩
    · exact ⟨t,by omega,rfl⟩

private def wordEmb {α : Type*} [LinearOrder α] {m : Nat}
    (s : Finset α) (hs : s.card = m) : Fin m ↪ α :=
  ⟨fun t => (s.orderIsoOfFin hs t).val,
    fun a b h => (s.orderIsoOfFin hs).injective (Subtype.ext h)⟩

private theorem initial_last {α : Type*} [LinearOrder α] {m : Nat}
    (s : Finset α) (hs : s.card = m) :
    initial (wordEmb s hs) ⟨m,by omega⟩ = s := by
  ext x
  simp only [initial_mem]
  constructor
  · rintro ⟨t,_,rfl⟩; exact (s.orderIsoOfFin hs t).2
  · intro hx
    let t := (s.orderIsoOfFin hs).symm ⟨x,hx⟩
    refine ⟨t, t.isLt, ?_⟩
    exact congrArg Subtype.val ((s.orderIsoOfFin hs).apply_symm_apply ⟨x,hx⟩)

private def whole {α : Type*} [DecidableEq α] {m : Nat}
    (e : Fin m ↪ α) (j a : α) (i : Fin (m+3)) : Finset α :=
  if hi : i.val ≤ m then initial e ⟨i.val,by omega⟩
  else if i.val = m+1 then insert j (initial e ⟨m,by omega⟩)
  else insert a (insert j (initial e ⟨m,by omega⟩))

private theorem whole_prefix {α : Type*} [DecidableEq α] {m : Nat}
    (e : Fin m ↪ α) (j a : α) (i : Fin (m+3)) (hi : i.val ≤ m) :
    whole e j a i = initial e ⟨i.val,by omega⟩ := by simp [whole, hi]

private theorem whole_probe {α : Type*} [DecidableEq α] {m : Nat}
    (e : Fin m ↪ α) (j a : α) :
    whole e j a ⟨m+1,by omega⟩ = insert j (initial e ⟨m,by omega⟩) := by
  simp [whole]

private theorem whole_after {α : Type*} [DecidableEq α] {m : Nat}
    (e : Fin m ↪ α) (j a : α) :
    whole e j a ⟨m+2,by omega⟩ = insert a (insert j (initial e ⟨m,by omega⟩)) := by
  simp [whole]

private theorem whole_mono {α : Type*} [DecidableEq α] {m : Nat}
    (e : Fin m ↪ α) (j a : α) {i k : Fin (m+3)} (hik : i ≤ k) :
    whole e j a i ⊆ whole e j a k := by
  have hki := k.isLt
  have hik' : i.val ≤ k.val := hik
  by_cases hi : i.val ≤ m
  · rw [whole_prefix e j a i hi]
    by_cases hk : k.val ≤ m
    · rw [whole_prefix e j a k hk]
      exact initial_mono e (show (⟨i.val,by omega⟩ : Fin (m+1)) ≤ ⟨k.val,by omega⟩ by omega)
    · have hsub : initial e ⟨i.val,by omega⟩ ⊆ initial e ⟨m,by omega⟩ :=
        initial_mono e (show (⟨i.val,by omega⟩ : Fin (m+1)) ≤ ⟨m,by omega⟩ by omega)
      by_cases he : k.val = m+1
      · have hke : k = ⟨m+1,by omega⟩ := Fin.ext he
        rw [hke, whole_probe]
        exact hsub.trans (Finset.subset_insert _ _)
      · have hke : k = ⟨m+2,by omega⟩ := Fin.ext (by change k.val = m+2; omega)
        rw [hke, whole_after]
        exact (hsub.trans (Finset.subset_insert _ _)).trans (Finset.subset_insert _ _)
  · have hie : i.val = m+1 ∨ i.val = m+2 := by omega
    rcases hie with hie | hie
    · have hie' : i = ⟨m+1,by omega⟩ := Fin.ext hie
      rw [hie', whole_probe]
      by_cases hk : k.val = m+1
      · have hke : k = ⟨m+1,by omega⟩ := Fin.ext hk
        rw [hke, whole_probe]
      · have hke : k = ⟨m+2,by omega⟩ := Fin.ext (by change k.val = m+2; omega)
        rw [hke, whole_after]
        exact Finset.subset_insert _ _
    · have hie' : i = ⟨m+2,by omega⟩ := Fin.ext hie
      have hke : k = ⟨m+2,by omega⟩ := Fin.ext (by omega)
      rw [hie', hke]

private def input {n : Nat} (s : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i ∈ s)) ++ [false,true]

private theorem input_length {n : Nat} (s : Finset (Fin n)) :
    (input s).length = n+2 := by simp [input]

private theorem input_below {n : Nat} {s t : Finset (Fin n)} (hst : s ⊆ t) :
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

theorem markov_finset_chain {n k : Nat} (C : PEqualNP.CircuitLowerBounds.Circuit)
    (state : Fin (k+1) → Finset (Fin n))
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hmono : ∀ i j, i ≤ j → state i ⊆ state j)
    (hfall : ∀ i : Fin k, ∃ w : ℕ,
       (C.wires (input (state ⟨i.val,by omega⟩))).getD w false = true ∧
       (C.wires (input (state ⟨i.val+1,by omega⟩))).getD w false = false) :
    k < 2 ^ PEqualNP.NotBracket.notCount C := by
  let x : Fin (2*k+1) → List Bool := fun t =>
    input (state ⟨t.val/2,by omega⟩)
  apply AltChain1196.circuit_multioutput_markov k (n+2) C x hfan
  · intro t; exact input_length _
  · intro a b hab
    exact input_below (hmono _ _ (show (⟨a.val/2,by omega⟩ : Fin (k+1)) ≤
      ⟨b.val/2,by omega⟩ by change a.val/2 ≤ b.val/2; omega))
  · intro i
    obtain ⟨w,hw⟩ := hfall i
    refine ⟨w,?_,?_⟩
    · have hd : (2*i.val+1)/2 = i.val := by omega
      simpa only [x, hd] using hw.1
    · have hd : (2*i.val+2)/2 = i.val+1 := by omega
      simpa only [x, hd] using hw.2

theorem false_rank_forced {n m b : Nat}
    (s : Finset (Fin n)) (hs : s.card = m) (j : Fin n) (hj : j ∉ s)
    (hn : m+1 < n)
    (R : Finset (Fin n) → Nat) (g : Finset (Fin n) → Fin n → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (tap : Fin n → Fin (n+2+C.size))
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hread : ∀ x t, (C.wires (input x)).getD (tap t).val false = g x t)
    (hsmall : ∀ x, x.card < m+1 → R x = x.card)
    (hbad : R (insert j s) = m)
    (hlarge : ∀ x, m+1 < x.card → R x = m+1)
    (hfit : ∀ x t, R x < R (insert t x) → g x t = true)
    (hzero : ∀ x t, t ∈ x → g x t = false)
    (hb : m+2 = 2^b)
    (hnot : PEqualNP.NotBracket.notCount C ≤ b) :
    g s j = false := by
  have hscard : (insert j s).card = m+1 := by simp [Finset.card_insert_of_notMem hj,hs]
  by_contra hfalse
  have ht : g s j = true := by cases h : g s j <;> simp_all

  obtain ⟨a,_,ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := insert j s) (t := (Finset.univ : Finset (Fin n))) (by simpa [hscard] using hn)
  let e := wordEmb s hs
  let state : Fin (m+3) → Finset (Fin n) := whole e j a
  have he_end : initial e ⟨m,by omega⟩ = s := initial_last s hs
  have hmk : m+2 < 2 ^ PEqualNP.NotBracket.notCount C := by
    apply markov_finset_chain C state hfan
    · intro i k hik; exact whole_mono e j a hik
    · intro i
      by_cases hi : i.val < m
      · let t : Fin m := ⟨i.val, hi⟩
        have hst : state ⟨i.val,by omega⟩ = initial e ⟨i.val,by omega⟩ := by
          change whole e j a ⟨i.val,by omega⟩ = _
          exact whole_prefix e j a _ (show i.val ≤ m by omega)
        have hst' : state ⟨i.val+1,by omega⟩ =
            insert (e t) (initial e ⟨i.val,by omega⟩) := by
          change whole e j a ⟨i.val+1,by omega⟩ = _
          rw [whole_prefix e j a _ (show i.val+1 ≤ m by omega), initial_next e t]
        have hnotmem : e t ∉ initial e ⟨i.val,by omega⟩ := by
          intro he
          obtain ⟨u, hu, htu⟩ := (initial_mem e _ _).mp he
          have htu' : u = t := e.injective htu
          omega
        have hc : (initial e ⟨i.val,by omega⟩).card = i.val := initial_card e _
        have hc' : (insert (e t) (initial e ⟨i.val,by omega⟩)).card = i.val+1 := by
          rw [Finset.card_insert_of_notMem hnotmem, hc]
        have hrank : R (initial e ⟨i.val,by omega⟩) <
            R (insert (e t) (initial e ⟨i.val,by omega⟩)) := by
          rw [hsmall _ (by omega : (initial e ⟨i.val,by omega⟩).card < m+1),
              hsmall _ (by omega : (insert (e t) (initial e ⟨i.val,by omega⟩)).card < m+1),hc,hc']
          omega
        refine ⟨(tap (e t)).val, ?_,?_⟩
        · rw [hst,hread]; exact hfit _ _ hrank
        · rw [hst',hread]; exact hzero _ _ (Finset.mem_insert_self _ _)
      · by_cases heq : i.val = m
        · have hst : state ⟨i.val,by omega⟩ = s := by
            simp [state,whole,heq,he_end]
          have hst' : state ⟨i.val+1,by omega⟩ = insert j s := by
            simp [state,whole,heq,he_end]
          refine ⟨(tap j).val, ?_,?_⟩
          · rw [hst,hread]; exact ht
          · rw [hst',hread]; exact hzero _ _ (Finset.mem_insert_self _ _)
        · have heq : i.val = m+1 := by omega
          have hst : state ⟨i.val,by omega⟩ = insert j s := by
            simp [state,whole,heq,he_end]
          have hst' : state ⟨i.val+1,by omega⟩ = insert a (insert j s) := by
            simp [state,whole,heq,he_end]
          have hc : (insert a (insert j s)).card = m+2 := by
            rw [Finset.card_insert_of_notMem ha,hscard]
          have hrank : R (insert j s) < R (insert a (insert j s)) := by
            rw [hbad, hlarge _ (by omega : m+1 < (insert a (insert j s)).card)]
            omega
          refine ⟨(tap a).val, ?_,?_⟩
          · rw [hst,hread]; exact hfit _ _ hrank
          · rw [hst',hread]; exact hzero _ _ (Finset.mem_insert_self _ _)
  have hmk' : m+2 < 2^b := hmk.trans_le (Nat.pow_le_pow_right (by omega) hnot)
  omega

theorem baseline_not_lower {n m b : Nat}
    (s : Finset (Fin n)) (hs : s.card = m) (a : Fin n) (ha : a ∉ s)
    (R : Finset (Fin n) → Nat) (g : Finset (Fin n) → Fin n → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (tap : Fin n → Fin (n+2+C.size))
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hread : ∀ x t, (C.wires (input x)).getD (tap t).val false = g x t)
    (hsmall : ∀ x, x.card < m+1 → R x = x.card)
    (hnormal : R (insert a s) = m+1)
    (hfit : ∀ x t, R x < R (insert t x) → g x t = true)
    (hzero : ∀ x t, t ∈ x → g x t = false)
    (hb : m+2 = 2^b) : b ≤ PEqualNP.NotBracket.notCount C := by
  let e := wordEmb s hs
  let state : Fin (m+2) → Finset (Fin n) := fun i =>
    whole e a a ⟨i.val,by omega⟩
  have he_end : initial e ⟨m,by omega⟩ = s := initial_last s hs
  have hmk : m+1 < 2 ^ PEqualNP.NotBracket.notCount C := by
    apply markov_finset_chain C state hfan
    · intro i k hik
      exact whole_mono e a a (show (⟨i.val,by omega⟩ : Fin (m+3)) ≤
        ⟨k.val,by omega⟩ by exact hik)
    · intro i
      by_cases hi : i.val < m
      · let t : Fin m := ⟨i.val, hi⟩
        have hst : state ⟨i.val,by omega⟩ = initial e ⟨i.val,by omega⟩ :=
          whole_prefix e a a _ (show i.val ≤ m by omega)
        have hst' : state ⟨i.val+1,by omega⟩ =
            insert (e t) (initial e ⟨i.val,by omega⟩) := by
          change whole e a a ⟨i.val+1,by omega⟩ = _
          rw [whole_prefix e a a _ (show i.val+1 ≤ m by omega), initial_next e t]
        have hnotmem : e t ∉ initial e ⟨i.val,by omega⟩ := by
          intro he
          obtain ⟨u, hu, htu⟩ := (initial_mem e _ _).mp he
          have htu' : u = t := e.injective htu
          omega
        have hc : (initial e ⟨i.val,by omega⟩).card = i.val := initial_card e _
        have hc' : (insert (e t) (initial e ⟨i.val,by omega⟩)).card = i.val+1 := by
          rw [Finset.card_insert_of_notMem hnotmem, hc]
        have hrank : R (initial e ⟨i.val,by omega⟩) <
            R (insert (e t) (initial e ⟨i.val,by omega⟩)) := by
          rw [hsmall _ (by omega : (initial e ⟨i.val,by omega⟩).card < m+1),
              hsmall _ (by omega : (insert (e t) (initial e ⟨i.val,by omega⟩)).card < m+1),hc,hc']
          omega
        refine ⟨(tap (e t)).val, ?_,?_⟩
        · rw [hst,hread]; exact hfit _ _ hrank
        · rw [hst',hread]; exact hzero _ _ (Finset.mem_insert_self _ _)
      · have heq : i.val = m := by omega
        have hst : state ⟨i.val,by omega⟩ = s := by
          simp [state,whole,heq,he_end]
        have hst' : state ⟨i.val+1,by omega⟩ = insert a s := by
          simp [state,whole,heq,he_end]
        have hrank : R s < R (insert a s) := by
          rw [hsmall s (by omega : s.card < m+1), hnormal,hs]
          omega
        refine ⟨(tap a).val, ?_,?_⟩
        · rw [hst,hread]; exact hfit _ _ hrank
        · rw [hst',hread]; exact hzero _ _ (Finset.mem_insert_self _ _)
  by_contra hnot
  have hle : PEqualNP.NotBracket.notCount C + 1 ≤ b := by omega
  have hp : 1 ≤ 2 ^ PEqualNP.NotBracket.notCount C :=
    pow_pos (by omega : 0 < 2) _
  have hpow : 2 ^ (PEqualNP.NotBracket.notCount C + 1) ≤ 2^b :=
    Nat.pow_le_pow_right (by omega) hle
  rw [pow_succ] at hpow
  omega

end Markov1270

namespace DervishPacking1270
open PEqualNP PEqualNP.CircuitLowerBounds

theorem second_exact (b : ℕ) (hb : 6 ≤ b) :
    let n := 2*(2^b-1)
    ∃ C, Computes C (fun (x : Finset (Fin n)) (i : Fin n) => decide (i ∉ x)) ∧
      NotBracket.notCount C = b+1 ∧ C.size ≤ 16*(n+2)^3 := by
  dsimp only
  obtain ⟨hn,hS⟩ := Inverter1270.second_bound b hb
  obtain ⟨C,tap,hfan,hbck,hout,htap,hnts,hsz⟩ := Inverter1270.complement_circuit _ (b+1) hn
  exact ⟨C,⟨hfan,hbck,hout,tap,htap⟩,hnts,hsz.trans hS⟩

theorem saturate_exact (b : ℕ) (hb : 6 ≤ b) :
    let r := 2^b-1
    let n := 2*r
    let q := r-2
    ∀ (j : Fin n) (word : Finset (Fin q) → Finset (Fin n)) (f : Finset (Fin q) → Bool)
      (R : Finset (Fin n) → ℕ), Function.Injective word →
      (∀ z, (word z).card = r-1 ∧ j ∉ word z) → Mat n r R → RankFormula r j word f R →
      ∀ C g, Computes C g → Fits R g →
      b ≤ NotBracket.notCount C ∧ (NotBracket.notCount C ≤ b → ∀ z, g (word z) j = f z) := by
  dsimp only
  set r : ℕ := 2^b-1
  set n : ℕ := 2*r
  set m : ℕ := r-1
  have hbigPow : (2:ℕ)^6 ≤ 2^b := Nat.pow_le_pow_right (by decide) hb
  have hbig : 64 ≤ (2:ℕ)^b := hbigPow
  have hm1 : m+1 = r := by omega
  have hm2 : m+2 = 2^b := by omega
  have hnr : m+1 < n := by omega
  intro j word f R hInj hWord _ hFormula C g hComp hFit
  rcases hComp with ⟨hFan,_,_,tap,hRead⟩
  have hc (z) : (insert j (word z)).card = r := by
    rw [Finset.card_insert_of_notMem (hWord z).2, (hWord z).1]
    exact hm1
  have small (x : Finset (Fin n)) (hx : x.card < m+1) : R x = x.card := by
    have hN : ¬∃ z, f z = false ∧ x = insert j (word z) := by
      rintro ⟨z,_,rfl⟩
      rw [hc] at hx
      omega
    simpa only [if_neg hN, Nat.min_eq_right (by omega : x.card ≤ r)] using hFormula x
  have large (x : Finset (Fin n)) (hx : m+1 < x.card) : R x = m+1 := by
    have hN : ¬∃ z, f z = false ∧ x = insert j (word z) := by
      rintro ⟨z,_,rfl⟩
      rw [hc] at hx
      omega
    simpa only [if_neg hN, Nat.min_eq_left (by omega : r ≤ x.card),hm1] using hFormula x
  have regular (z) (hz : f z = true) : R (insert j (word z)) = r := by
    have hN : ¬∃ y, f y = false ∧ insert j (word z) = insert j (word y) := by
      rintro ⟨y, hy, he⟩
      have he' : word z = word y := by
        have ee := congrArg (Finset.erase · j) he
        simpa only [Finset.erase_insert (hWord z).2, Finset.erase_insert (hWord y).2] using ee
      have := hInj he'
      subst y
      exact Bool.noConfusion (hz.symm.trans hy)
    simpa only [if_neg hN, hc, Nat.min_self] using hFormula (insert j (word z))
  constructor
  · let z : Finset (Fin (r-2)) := ∅
    let s := word z
    have hs : s.card = m := (hWord z).1
    have hj : j ∉ s := (hWord z).2
    obtain ⟨a,_,ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := insert j s) (t := (Finset.univ : Finset (Fin n))) (by simpa [s,hc,hm1] using hnr)
    have ha0 : a ∉ s := fun h => ha (Finset.mem_insert_of_mem h)
    have hj0 : j ∉ insert a s := by
      intro h
      rcases Finset.mem_insert.mp h with he | hm
      · exact ha (he ▸ Finset.mem_insert_self j s)
      · exact hj hm
    have hc' : (insert a s).card = r := by rw [Finset.card_insert_of_notMem ha0, hs, hm1]
    have hN : ¬∃ y, f y = false ∧ insert a s = insert j (word y) := by
      rintro ⟨y,_,he⟩
      exact hj0 (he ▸ Finset.mem_insert_self j (word y))
    have hnormal : R (insert a s) = m+1 := by
      simpa only [if_neg hN, hc', Nat.min_self, hm1] using hFormula (insert a s)
    exact Markov1270.baseline_not_lower s hs a ha0 R g C tap hFan hRead small hnormal hFit.1 hFit.2 hm2
  · intro hnot z
    cases hz : f z with
    | false =>
      have hrank : R (insert j (word z)) = m := by
        simpa only [if_pos (show ∃ y, f y = false ∧ insert j (word z) = insert j (word y) from
          ⟨z,hz,rfl⟩)] using hFormula (insert j (word z))
      exact Markov1270.false_rank_forced (word z) (hWord z).1 j (hWord z).2 hnr R g C tap hFan hRead
        small hrank large hFit.1 hFit.2 hm2 hnot
    | true =>
      apply hFit.1
      rw [small _ (by have := (hWord z).1; omega), (hWord z).1, regular z hz]
      omega

theorem first_exact (b n : ℕ) (R : Finset (Fin n) → ℕ) (hm : Monotone R)
    (hR : ∀ x, R x < 2^b) : ∃ C g, Computes C g ∧ Fits R g ∧ NotBracket.notCount C = b := by
  have hp : 0 < (2:ℕ)^b := Nat.pow_pos (by decide)
  have hlt : 2^b-1 < (2:ℕ)^b := by omega
  have hbnd (x) : R x ≤ 2^b-1 := by have := hR x; omega
  obtain ⟨C,g,hfan,hbck,ho,ht,hfit,hzero,hc⟩ := Wiring1270.first_upper (n := n) b _ hlt R hm hbnd
  exact ⟨C,g,⟨hfan,hbck,ho,ht⟩,⟨hfit,hzero⟩,hc⟩

end DervishPacking1270
end PEqualNP.Outside.L_lib_1270

theorem PEqualNP.Outside.L_lib_1270 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ b : Nat, 6 ≤ b →
  let r := 2^b-1
  let n := 2*r
  let q := r-2
  let mat := fun (R : Finset (Fin n) → Nat) =>
    R ∅ = 0 ∧ Monotone R ∧ (∀ x, R x ≤ x.card) ∧
    (∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y) ∧ R Finset.univ = r
  let fits := fun (R : Finset (Fin n) → Nat) (g : Finset (Fin n) → Fin n → Bool) =>
    (∀ x j, R x < R (insert j x) → g x j = true) ∧ (∀ x j, j ∈ x → g x j = false)
  let computes := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (g : Finset (Fin n) → Fin n → Bool) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ ∃ tap : Fin n → Fin (n+2+C.size),
      ∀ x j, let input := List.ofFn (fun i : Fin n => decide (i∈x)) ++ [false,true]
             (C.wires input).getD (tap j).val false = g x j
  ∃ (j : Fin n) (word : Finset (Fin q) → Finset (Fin n))
    (rank : (Finset (Fin q) → Bool) → Finset (Fin n) → Nat),
    Function.Injective word ∧ (∀ z, (word z).card = r-1 ∧ j ∉ word z) ∧
    (∀ f, mat (rank f) ∧ ∀ x, rank f x =
      if ∃ z, f z = false ∧ x = insert j (word z) then r-1 else min r x.card) ∧
    (∀ f, (∃ C g, computes C g ∧ fits (rank f) g ∧ PEqualNP.NotBracket.notCount C = b) ∧
      ∀ C g, computes C g → fits (rank f) g →
        b ≤ PEqualNP.NotBracket.notCount C ∧
        (PEqualNP.NotBracket.notCount C ≤ b → ∀ z, g (word z) j = f z)) ∧
    (∃ C, let g := fun (x : Finset (Fin n)) (i : Fin n) => decide (i ∉ x)
          computes C g ∧ (∀ f, fits (rank f) g) ∧
          PEqualNP.NotBracket.notCount C = b+1 ∧ C.size ≤ 16*(n+2)^3) ∧
    ∃ f, ∀ C g, computes C g → fits (rank f) g → PEqualNP.NotBracket.notCount C ≤ b →
      2^(r/2) < C.size) := by
  exact PEqualNP.Outside.L_lib_1270.DervishPacking1270.assembled_if PEqualNP.Outside.L_lib_1270.DervishPacking1270.first_exact
    PEqualNP.Outside.L_lib_1270.DervishPacking1270.saturate_exact PEqualNP.Outside.L_lib_1270.DervishPacking1270.second_exact

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1427_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (w : List Bool) := gs.foldl
  (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w

def tick (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def code : List Gate → List Bool → List Bool
  | [], _ => []
  | g::gs, w =>
    let a := tick w g
    match g.op with
    | .not => (g.op.eval (g.inputs.map fun i => w.getD i false)) :: code gs a
    | _ => code gs a

def mark (g : Gate) : Bool := match g.op with | .not => true | _ => false

theorem code_len (gs : List Gate) (w : List Bool) :
    (code gs w).length = (gs.filter mark).length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    cases h : g.op <;> simp [code,h,mark,List.filter_cons,ih]

def ordered (x y : List Bool) :=
  x.length=y.length ∧ ∀ i, x.getD i false=true → y.getD i false=true

theorem extend_order {x y : List Bool} (w : ordered x y) {a b : Bool}
    (ab : a=true → b=true) : ordered (x++[a]) (y++[b]) := by
  refine ⟨by simp [w.1],?_⟩
  intro i
  by_cases before : i < x.length
  · rw [List.getD_append _ _ _ _ before,List.getD_append _ _ _ _ (w.1 ▸ before)]
    exact w.2 i
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by rw [←w.1]; omega),←w.1]
    cases i-x.length <;> simpa using ab <;> simp

theorem output_order {gs : List Gate}
    (ops : ∀ g∈gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    {x y : List Bool} (w : ordered x y) (same : code gs x=code gs y) :
    ordered (run gs x) (run gs y) := by
  induction gs generalizing x y with
  | nil => exact w
  | cons g gs ih =>
    have rest (a) (ha : a∈gs) := ops a (List.mem_cons_of_mem _ ha)
    change ordered (run gs (tick x g)) (run gs (tick y g))
    have casesG := ops g (List.mem_cons_self ..)
    rcases casesG with h|h|h
    · apply ih rest (extend_order w ?_) (by simpa only [code,tick,h] using same)
      simp only [h,GateOp.eval,List.all_eq_true,List.mem_map,forall_exists_index,and_imp]
      intro all z i hi ei
      subst z
      exact w.2 i (all _ _ hi rfl)
    · apply ih rest (extend_order w ?_) (by simpa only [code,tick,h] using same)
      simp only [h,GateOp.eval,List.any_eq_true,List.mem_map]
      rintro ⟨z,⟨i,hi,rfl⟩,yes⟩
      exact ⟨_,⟨i,hi,rfl⟩,w.2 i yes⟩
    · simp only [code,h,List.cons.injEq] at same
      apply ih rest (extend_order w ?_) same.2
      rw [h]
      exact fun e => same.1.symm.trans e

theorem input_order {n : Nat} {x y : Fin n → Bool} (xy : ∀ i, x i=true → y i=true) :
    ordered (List.ofFn x ++ [false,true]) (List.ofFn y ++ [false,true]) := by
  refine ⟨by simp,?_⟩
  intro i
  by_cases h : i<n
  · rw [List.getD_append _ _ _ _ (by simpa),List.getD_append _ _ _ _ (by simpa)]
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,h] using xy ⟨i,h⟩
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h),
        List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h)]
    simp
def driverNumber : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 0 else 2^bs.length) + driverNumber bs

theorem driver_bound (l : List Bool) : driverNumber l < 2^l.length := by
  induction l with
  | nil => decide
  | cons b bs ih => cases b <;> simp [driverNumber,pow_succ] <;> omega

theorem driver_injective {a b : List Bool} (len : a.length=b.length)
    (num : driverNumber a=driverNumber b) : a=b := by
  induction a generalizing b with
  | nil => simpa using len.symm
  | cons x xs ih =>
    cases b with
    | nil => simp at len
    | cons y ys =>
      have sz : xs.length=ys.length := by simpa using len
      have h₁ := driver_bound xs
      have h₂ := driver_bound ys
      rw [sz] at h₁
      cases x <;> cases y <;> simp [driverNumber,sz] at num ⊢ <;> first | exact ih sz num | omega

theorem driver_mono (gs : List Gate) (ops : ∀ g∈gs, g.op=.and ∨ g.op=.or ∨ g.op=.not)
    {a b : List Bool} (ab : ordered a b) :
    driverNumber (code gs a) ≤ driverNumber (code gs b) := by
  induction gs generalizing a b with
  | nil => rfl
  | cons g gs ih =>
    have tailops := fun h (hh : h∈gs) => ops h (by simp [hh])
    have oneops : ∀ u ∈ [g], u.op=.and ∨ u.op=.or ∨ u.op=.not := by
      simpa using ops g (by simp)
    have growth (same : code [g] a=code [g] b) : ordered (tick a g) (tick b g) :=
      output_order oneops ab same
    rcases ops g (by simp) with eq|eq|eq
    · simp only [code,eq]
      exact ih tailops (growth (by simp [code,eq]))
    · simp only [code,eq]
      exact ih tailops (growth (by simp [code,eq]))
    · let out (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
      have anti : out b=true → out a=true := by
        cases inp : g.inputs with
        | nil => simp [out,eq,inp,GateOp.eval]
        | cons i more =>
          simp only [out,eq,inp,GateOp.eval,List.map_cons,List.headD_cons,Bool.not_eq_true']
          intro bz
          cases az : a.getD i false
          · rfl
          · have := ab.2 i az
            simp_all
      have len : (code gs (tick a g)).length=(code gs (tick b g)).length := by simp [code_len]
      change driverNumber (code (g::gs) a) ≤ driverNumber (code (g::gs) b)
      simp only [code,eq]
      rw [←eq]
      change driverNumber (out a :: code gs (tick a g)) ≤ driverNumber (out b :: code gs (tick b g))
      by_cases same : out a=out b
      · have next : ordered (tick a g) (tick b g) := extend_order ab (by change out a=true → out b=true; rw [same]; exact id)
        simpa only [driverNumber,same,len,Nat.add_le_add_iff_left] using
          Nat.add_le_add_left (ih tailops next) (if out b then 0 else 2^(code gs (tick b g)).length)
      · have zero : out b=false := by cases hb : out b <;> simp_all
        have one : out a=true := by cases ha : out a <;> simp_all
        have bound := driver_bound (code gs (tick a g))
        rw [len] at bound
        simp only [driverNumber,one,zero,Bool.false_eq_true,if_false,if_true,Nat.zero_add]
        omega

theorem mark_count (C : Circuit) :
    (C.gates.filter mark).length = PEqualNP.NotBracket.notCount C := by
  unfold PEqualNP.NotBracket.notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases eq : g.op <;> simp [mark,eq]

theorem ordered_refl (x : List Bool) : ordered x x := ⟨rfl, fun _ h => h⟩

theorem ordered_append {a b c d : List Bool} (h1 : ordered a b) (h2 : ordered c d) :
    ordered (a++c) (b++d) := by
  refine ⟨by simp [h1.1,h2.1],?_⟩
  intro i
  by_cases h : i < a.length
  · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (h1.1 ▸ h)]
    exact h1.2 i
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by rw [←h1.1]; omega),←h1.1]
    exact h2.2 _

theorem ordered_ofFn {r : Nat} {f g : Fin r → Bool} (fg : ∀ j, f j = true → g j = true) :
    ordered (List.ofFn f) (List.ofFn g) := by
  refine ⟨by simp,?_⟩
  intro i
  by_cases h : i < r
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,h] using fg ⟨i,h⟩
  · simp [List.getD_eq_getElem?_getD,h]

theorem dn_top (l : List Bool) (a : Nat) (h : driverNumber l < 2^a) :
    ∀ i, i + a < l.length → l.getD i false = true := by
  induction l with
  | nil => intro i hi; simp at hi
  | cons b bs ih =>
    intro i hi
    simp only [List.length_cons] at hi
    have hb : driverNumber bs < 2^a := by
      simp only [driverNumber] at h
      omega
    cases i with
    | zero =>
      cases b
      · exfalso
        have : 2^a ≤ 2^bs.length := Nat.pow_le_pow_right (by norm_num) (by omega)
        simp [driverNumber] at h
        omega
      · simp
    | succ i => simpa using ih hb i (by omega)

theorem dn_step (gs : List Gate) (ops : ∀ g∈gs, g.op=.and ∨ g.op=.or ∨ g.op=.not)
    {a b : List Bool} (ab : ordered a b) (t : Nat) (h1 : (run gs a).getD t false = true)
    (h2 : (run gs b).getD t false = false) :
    driverNumber (code gs a) + 1 ≤ driverNumber (code gs b) := by
  have mono := driver_mono gs ops ab
  by_contra hh
  have eq : driverNumber (code gs a) = driverNumber (code gs b) := by omega
  have same := driver_injective (by simp [code_len]) eq
  have := (output_order ops ab same).2 t h1
  rw [h2] at this
  exact Bool.noConfusion this

theorem head_true (C : Circuit) (ops : ∀ g∈C.gates, g.op=.and ∨ g.op=.or ∨ g.op=.not)
    (a L : Nat) (z : Nat → List Bool) (ord : ∀ i, i < L → ordered (z i) (z (i+1)))
    (fall : ∀ i, i < L → ∃ t, (run C.gates (z i)).getD t false = true ∧
      (run C.gates (z (i+1))).getD t false = false)
    (hL : 2^PEqualNP.NotBracket.notCount C ≤ L + 2^a) (z' : List Bool) (o' : ordered z' (z 0)) :
    ∀ i, i + a < PEqualNP.NotBracket.notCount C → (code C.gates z').getD i false = true := by
  have key : ∀ i, i ≤ L →
      driverNumber (code C.gates (z 0)) + i ≤ driverNumber (code C.gates (z i)) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      obtain ⟨t,h1,h2⟩ := fall i (by omega)
      have s1 := dn_step _ ops (ord i (by omega)) t h1 h2
      have s2 := ih (by omega)
      omega
  have h1 := key L le_rfl
  have h2 := driver_bound (code C.gates (z L))
  rw [code_len,mark_count] at h2
  have h3 := driver_mono C.gates ops o'
  intro i hi
  apply dn_top _ a (by omega)
  rw [code_len,mark_count]
  exact hi

theorem run_append (a b : List Gate) (w : List Bool) : run (a++b) w = run b (run a w) := by
  simp [run,List.foldl_append]

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    show (run gs (tick w g)).length = _
    rw [ih]
    simp [tick]
    omega

theorem run_singleton (g : Gate) (w : List Bool) :
    run [g] w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

theorem getD_run (gs : List Gate) (w : List Bool) (i : Nat) (h : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    show (run gs (tick w g)).getD i false = _
    rw [ih _ (by simp [tick]; omega)]
    simp only [tick]
    rw [List.getD_append _ _ _ _ h]

theorem getD_snoc_length (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

theorem wire_gate (C : Circuit) (n : Nat) (back : ReadsBack n C) (xs : List Bool) (len : xs.length=n)
    (a : Nat) (ha : a < C.size) :
    (C.wires xs).getD (n+a) false =
      (gateAt C a).op.eval ((gateAt C a).inputs.map (fun i => (C.wires xs).getD i false)) := by
  let front := C.gates.take a
  let rest := C.gates.drop (a+1)
  let g := gateAt C a
  have geta : g=C.gates[a] := by simp [g,gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ha]
  have split : C.gates=(front++[g])++rest := by
    rw [geta,←List.take_succ_eq_append_getElem ha,List.take_append_drop]
  have whole : C.wires xs=run rest (run [g] (run front xs)) := by
    change run C.gates xs=_
    conv_lhs => rw [split,run_append,run_append]
  have fw : (run front xs).length=n+a := by
    simp [run_length,front,len,List.length_take,Nat.min_eq_left (show a ≤ C.gates.length by exact ha.le)]
  have sw : (run [g] (run front xs)).length=n+a+1 := by rw [run_length,fw]; simp
  have old (i) (hi : i∈g.inputs) : (C.wires xs).getD i false=(run front xs).getD i false := by
    have good := back a ha i hi
    rw [whole,getD_run _ _ _ (sw ▸ (by omega)),getD_run _ _ _ (fw ▸ good)]
  change _=g.op.eval _
  rw [whole,getD_run _ _ _ (sw ▸ (by omega)),run_singleton,←fw,getD_snoc_length]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (old i hi).symm.trans (by rw [whole,run_singleton])

def remap (ρ : Nat → Nat) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

theorem gateAt_map (gs : List Gate) (o : Nat) (ρ : Nat → Nat) (j : Nat) :
    gateAt ⟨gs.map (remap ρ), o⟩ j = remap ρ (gateAt ⟨gs, o⟩ j) := by
  simp only [gateAt,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases gs[j]? <;> simp [remap]

theorem notCount_map (gs : List Gate) (o o' : Nat) (ρ : Nat → Nat) :
    PEqualNP.NotBracket.notCount ⟨gs.map (remap ρ), o⟩ = PEqualNP.NotBracket.notCount ⟨gs, o'⟩ := by
  unfold PEqualNP.NotBracket.notCount
  simp only [List.filter_map,List.length_map]
  rfl

def rho (n r t : Nat) : Nat := if t < n then t else if t < n+r+1 then n else t - r

theorem tail_getD (r k : Nat) :
    (List.replicate r false ++ [false,true]).getD k false = decide (k = r+1) := by
  induction r generalizing k with
  | zero => rcases k with _|_|k <;> simp
  | succ r ih =>
    cases k with
    | zero => simp [List.replicate_succ]
    | succ k => simpa [List.replicate_succ,List.getD_eq_getElem?_getD] using ih k

theorem inputs_agree (n r : Nat) (u : List Bool) (hu : u.length = n) (t : Nat) (ht : t < n+r+2) :
    (u ++ [false,true]).getD (rho n r t) false =
      (u ++ List.replicate r false ++ [false,true]).getD t false := by
  by_cases h1 : t < n
  · have : rho n r t = t := by unfold rho; simp [h1]
    rw [this,List.append_assoc,List.getD_append _ _ _ _ (by omega),List.getD_append _ _ _ _ (by omega)]
  · have h0 := tail_getD 0 (rho n r t - n)
    simp only [List.replicate_zero,List.nil_append] at h0
    rw [List.append_assoc,List.getD_append_right _ _ _ _ (by unfold rho; split_ifs <;> omega),
      List.getD_append_right _ _ _ _ (by omega),hu,h0,tail_getD]
    congr 1
    simp only [eq_iff_iff]
    unfold rho
    split_ifs <;> omega

def valid (N : Nat) (C : Circuit) : Prop :=
  FanInTwo C ∧ ReadsBack N C ∧ C.output < N + C.size

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g::gs) w = run gs (tick w g) := rfl

theorem code_append (a b : List Gate) (w : List Bool) :
    code (a++b) w = code a w ++ code b (run a w) := by
  induction a generalizing w with
  | nil => rfl
  | cons g a ih => cases h : g.op <;> simp [code,h,ih,run_cons]

theorem code_at' (a : List Gate) (g : Gate) (b : List Gate) (w : List Bool) (gop : g.op = .not) :
    (code (a ++ g :: b) w).getD (a.filter mark).length false =
      (run (a ++ g :: b) w).getD (w.length + a.length) false := by
  rw [code_append,List.getD_append_right _ _ _ _ (by rw [code_len]),code_len,Nat.sub_self,
    run_append,run_cons,getD_run _ _ _ (by simp [tick,run_length]),tick,←run_length,
    getD_snoc_length]
  simp [code,gop,tick]

theorem skip_getD (a : List Gate) (g : Gate) (b : List Gate) (j : Nat) (d : Gate) :
    (a++b).getD j d = (a ++ g :: b).getD (if j < a.length then j else j+1) d := by
  split_ifs with h
  · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),
      show j + 1 - a.length = (j - a.length) + 1 by omega]
    simp

theorem rank_split (l : List Gate) (e : Nat) (h : e < (l.filter mark).length) :
    ∃ a g b, l = a ++ g :: b ∧ mark g = true ∧ (a.filter mark).length = e := by
  induction l generalizing e with
  | nil => simp at h
  | cons g l ih =>
    by_cases hm : mark g = true
    · cases e with
      | zero => exact ⟨[], g, l, rfl, hm, rfl⟩
      | succ e =>
        obtain ⟨a,g',b,rfl,h1,h2⟩ := ih e (by simpa [List.filter_cons,hm] using h)
        exact ⟨g::a, g', b, rfl, h1, by simp [List.filter_cons,hm,h2]⟩
    · obtain ⟨a,g',b,rfl,h1,h2⟩ := ih e (by simpa [List.filter_cons,hm] using h)
      exact ⟨g::a, g', b, rfl, h1, by simp [List.filter_cons,hm,h2]⟩

theorem take_getD {l l' : List Bool} {e i : Nat} (h : l.take e = l'.take e) (hi : i < e) :
    l.getD i false = l'.getD i false := by
  have := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_take,hi,if_true] at this
  simp [List.getD_eq_getElem?_getD,this]

def rho1 (N p τ t : Nat) : Nat := if t = N+p then τ else if N+p < t then t-1 else t

theorem step' (N τ : Nat) (a : List Gate) (g : Gate) (b : List Gate) (out : Nat)
    (hv : valid N ⟨a ++ g :: b, out⟩) (hτ : τ < N) (gop : g.op = .not) :
    ∃ C1 : Circuit, valid N C1 ∧
      PEqualNP.NotBracket.notCount C1 + 1 = PEqualNP.NotBracket.notCount ⟨a ++ g :: b, out⟩ ∧
      C1.size = Circuit.size ⟨a ++ g :: b, out⟩ ∧
      ∀ x : List Bool, x.length = N → x.getD τ false = true →
        ((code (a ++ g :: b) x).getD (a.filter mark).length false = true →
          C1.eval x = Circuit.eval ⟨a ++ g :: b, out⟩ x ∧
          (code C1.gates x).take (a.filter mark).length =
            (code (a ++ g :: b) x).take (a.filter mark).length) ∧
        ((code (a ++ g :: b) x).getD (a.filter mark).length false = false → C1.eval x = true) := by
  obtain ⟨C, hC⟩ : ∃ C : Circuit, C = ⟨a ++ g :: b, out⟩ := ⟨_, rfl⟩
  rw [←hC] at hv ⊢
  have hgates : C.gates = a ++ g :: b := by rw [hC]
  have hout0 : C.output = out := by rw [hC]
  obtain ⟨fan, back, hout⟩ := hv
  have hsz : C.size = a.length + b.length + 1 := by
    simp [Circuit.size,hgates]
    omega
  have hlen : C.gates.length = a.length + b.length + 1 := hsz
  have hgp : gateAt C a.length = g := by
    rw [gateAt,hgates,List.getD_append_right _ _ _ _ le_rfl]
    simp
  have gin : ∀ i ∈ g.inputs, i < N + a.length := fun i hi =>
    back a.length (by omega) i (by rw [hgp]; exact hi)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Nat → Nat, ρ = rho1 N a.length τ := ⟨_, rfl⟩
  have ρlt : ∀ t, t < N + a.length → ρ t = t := by
    intro t ht
    rw [hρ]
    unfold rho1
    split_ifs <;> omega
  have ρp : ρ (N + a.length) = τ := by
    rw [hρ]
    unfold rho1
    simp
  obtain ⟨fin, hfin⟩ : ∃ fin : Gate, fin = ⟨.or, ρ out :: g.inputs.take 1⟩ := ⟨_, rfl⟩
  obtain ⟨C1, hC1⟩ : ∃ C1 : Circuit,
    C1 = ⟨(a ++ b).map (remap ρ) ++ [fin], N + (a.length + b.length)⟩ := ⟨_, rfl⟩
  have hg1s : C1.gates = (a ++ b).map (remap ρ) ++ [fin] := by rw [hC1]
  have hsz1 : C1.size = a.length + b.length + 1 := by
    simp [Circuit.size,hg1s]
    omega
  have hlen1 : C1.gates.length = a.length + b.length + 1 := hsz1
  have hgA : ∀ j, j < a.length + b.length →
      gateAt C1 j = remap ρ (gateAt C (if j < a.length then j else j+1)) := by
    intro j hj
    have e1 : gateAt C1 j = gateAt ⟨(a++b).map (remap ρ), 0⟩ j := by
      unfold gateAt
      rw [hg1s]
      exact List.getD_append _ _ _ _ (by simp; omega)
    rw [e1,gateAt_map]
    congr 1
    unfold gateAt
    rw [hgates]
    exact skip_getD a g b j _
  have hgF : gateAt C1 (a.length + b.length) = fin := by
    unfold gateAt
    rw [hg1s,List.getD_append_right _ _ _ _ (by simp)]
    simp
  have back1 : ReadsBack N C1 := by
    intro j hj i hi
    rw [hlen1] at hj
    by_cases hjl : j < a.length + b.length
    · rw [hgA j hjl] at hi
      simp only [remap,List.mem_map] at hi
      obtain ⟨i0, hi0, rfl⟩ := hi
      have := back (if j < a.length then j else j+1) (by rw [hlen]; split_ifs <;> omega) i0 hi0
      rw [hρ]
      unfold rho1
      split_ifs at this ⊢ <;> omega
    · have hje : j = a.length + b.length := by omega
      subst hje
      rw [hgF,hfin] at hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · rw [hout0] at hout
        rw [hρ]
        unfold rho1
        split_ifs <;> omega
      · have := gin i (List.mem_of_mem_take hi)
        omega
  refine ⟨C1, ⟨?_, back1, ?_⟩, ?_, by rw [hsz1,hsz], ?_⟩
  · intro g' hg'
    rw [hg1s] at hg'
    simp only [List.mem_append,List.mem_map,List.mem_singleton] at hg'
    rcases hg' with ⟨g0, hg0, rfl⟩ | rfl
    · have : g0 ∈ C.gates := by
        rw [hgates]
        simp only [List.mem_append,List.mem_cons] at hg0 ⊢
        tauto
      simpa [remap] using fan g0 this
    · rw [hfin]
      refine ⟨by simp, ?_⟩
      simp only [List.length_cons,List.length_take]
      omega
  · rw [hsz1,hC1]
    show N + (a.length + b.length) < _
    omega
  · rw [←mark_count,←mark_count,hg1s,hgates]
    simp only [List.filter_append,List.filter_map,List.length_append,List.length_map]
    have c1 : (mark ∘ remap ρ) = mark := rfl
    have c2 : mark fin = false := by rw [hfin]; rfl
    have c3 : mark g = true := by simp [mark,gop]
    simp [c1,c2,c3,List.filter_cons]
    omega
  · intro x hx hxτ
    have wS_in : ∀ t, t < N → (C1.wires x).getD t false = x.getD t false := fun t ht =>
      getD_run _ _ _ (by omega)
    have wC_in : ∀ t, t < N → (C.wires x).getD t false = x.getD t false := fun t ht =>
      getD_run _ _ _ (by omega)
    have hvv : (C.wires x).getD (N + a.length) false =
        !((g.inputs.map fun i => (C.wires x).getD i false).headD false) := by
      rw [wire_gate C N back x hx a.length (by omega),hgp,gop]
      rfl
    have hcode : (code (a ++ g :: b) x).getD (a.filter mark).length false =
        (C.wires x).getD (N + a.length) false := by
      rw [code_at' a g b x gop,hx]
      show _ = (run C.gates x).getD _ false
      rw [hgates]
    have key : ∀ t, t < N + C.size →
        ((C.wires x).getD (N + a.length) false = true ∨ t < N + a.length) →
        (C1.wires x).getD (ρ t) false = (C.wires x).getD t false := by
      intro t
      induction t using Nat.strong_induction_on with
      | _ t ih =>
        intro ht hyp
        by_cases hin : t < N
        · rw [ρlt t (by omega),wS_in t hin,wC_in t hin]
        · obtain ⟨j, rfl⟩ : ∃ j, t = N + j := ⟨t - N, by omega⟩
          by_cases hjp : j = a.length
          · subst hjp
            rw [ρp,wS_in τ hτ,hxτ]
            rcases hyp with h | h
            · exact h.symm
            · omega
          · obtain ⟨j', hj'⟩ : ∃ j', j' = if j < a.length then j else j - 1 := ⟨_, rfl⟩
            have hjj : (if j' < a.length then j' else j'+1) = j := by
              rw [hj']
              split_ifs <;> omega
            have hj'lt : j' < a.length + b.length := by
              rw [hj']
              split_ifs <;> omega
            have eρ : ρ (N + j) = N + j' := by
              rw [hρ,hj']
              unfold rho1
              split_ifs <;> omega
            have bj := back j (by omega)
            rw [eρ,wire_gate C1 N back1 x hx j' (by omega),
              wire_gate C N back x hx j (by omega),hgA j' hj'lt,hjj]
            simp only [remap,List.map_map]
            congr 1
            apply List.map_congr_left
            intro i hi
            have := bj i hi
            refine ih i (by omega) (by omega) ?_
            rcases hyp with h | h
            · exact Or.inl h
            · exact Or.inr (by omega)
    have hev1 : C1.eval x = ((C1.wires x).getD (ρ out) false ||
        (((g.inputs.take 1).map fun i => (C1.wires x).getD i false).any id)) := by
      show (C1.wires x).getD C1.output false = _
      rw [show C1.output = N + (a.length + b.length) by rw [hC1],
        wire_gate C1 N back1 x hx _ (by omega),hgF,hfin]
      simp [GateOp.eval]
    have hevC : C.eval x = (C.wires x).getD out false := by
      show (C.wires x).getD C.output false = _
      rw [hout0]
    have hout' : out < N + C.size := by
      rw [←hout0]
      exact hout
    constructor
    · intro hc
      rw [hcode] at hc
      refine ⟨?_, ?_⟩
      · rw [hev1,hevC,key out hout' (Or.inl hc)]
        rw [hc] at hvv
        cases hin : g.inputs with
        | nil => simp
        | cons i rest =>
          have im : i ∈ g.inputs := by simp [hin]
          have hi : (C.wires x).getD i false = false := by simpa [hin] using hvv.symm
          have ki := key i (by have := gin i im; omega) (Or.inl hc)
          rw [ρlt i (gin i im),hi] at ki
          rw [show (i :: rest).take 1 = [i] from rfl]
          simp only [List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,ki,Bool.or_false]
      · have ha : a.map (remap ρ) = a := by
          have each : ∀ g0 ∈ a, remap ρ g0 = g0 := by
            intro g0 hg0
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg0
            have gj : gateAt C j = a[j] := by
              unfold gateAt
              rw [hgates,List.getD_append _ _ _ _ hj]
              simp [List.getD_eq_getElem?_getD,hj]
            have bj := back j (by omega)
            rw [gj] at bj
            have im : a[j].inputs.map ρ = a[j].inputs := by
              conv_rhs => rw [←List.map_id a[j].inputs]
              apply List.map_congr_left
              intro i hi
              exact ρlt i (by have := bj i hi; omega)
            show (⟨a[j].op, a[j].inputs.map ρ⟩ : Gate) = a[j]
            rw [im]
          conv_rhs => rw [←List.map_id a]
          exact List.map_congr_left each
        rw [hg1s,List.map_append,ha,List.append_assoc,code_append,
          List.take_left' (code_len _ _),code_append,List.take_left' (code_len _ _)]
    · intro hc
      rw [hcode] at hc
      rw [hc] at hvv
      rw [hev1]
      cases hin : g.inputs with
      | nil => simp [hin] at hvv
      | cons i rest =>
        have im : i ∈ g.inputs := by simp [hin]
        have hi : (C.wires x).getD i false = true := by simpa [hin] using hvv
        have ki := key i (by have := gin i im; omega) (Or.inr (gin i im))
        rw [ρlt i (gin i im),hi] at ki
        rw [show (i :: rest).take 1 = [i] from rfl]
        simp only [List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,ki,Bool.or_false,Bool.or_true]

theorem elim (N τ : Nat) (C : Circuit) (hv : valid N C) (e : Nat)
    (he : e ≤ PEqualNP.NotBracket.notCount C) (hτ : τ < N) :
    ∃ C' : Circuit, valid N C' ∧
      PEqualNP.NotBracket.notCount C' + e = PEqualNP.NotBracket.notCount C ∧ C'.size = C.size ∧
      ∀ x : List Bool, x.length = N → x.getD τ false = true → τ < N →
        ((∀ i, i < e → (code C.gates x).getD i false = true) → C'.eval x = C.eval x) ∧
        (¬ (∀ i, i < e → (code C.gates x).getD i false = true) → C'.eval x = true) := by
  induction e generalizing C with
  | zero =>
    exact ⟨C, hv, rfl, rfl, fun x _ _ _ => ⟨fun _ => rfl, fun h => absurd (fun i hi => by omega) h⟩⟩
  | succ e ih =>
    · obtain ⟨a,g,b,hsplit,hm,h2⟩ := rank_split C.gates e (by rw [mark_count]; omega)
      obtain ⟨gates, out⟩ := C
      simp only at hsplit
      subst hsplit
      have gop : g.op = .not := by
        cases h : g.op <;> first | rfl | (simp [mark,h] at hm)
      obtain ⟨C1, hv1, hn1, hs1, h1⟩ := step' N τ a g b out hv hτ gop
      rw [h2] at h1
      obtain ⟨C', hv', hn', hs', hC'⟩ := ih C1 hv1 (by omega)
      refine ⟨C', hv', by omega, by omega, ?_⟩
      intro x hx ht _
      obtain ⟨s1,s2⟩ := h1 x hx ht
      obtain ⟨i1,i2⟩ := hC' x hx ht hτ
      constructor
      · intro all
        obtain ⟨ev, tk⟩ := s1 (all e (by omega))
        rw [←ev]
        apply i1
        intro i hi
        rw [take_getD tk hi]
        exact all i (by omega)
      · intro nall
        cases hb : (code (a ++ g :: b) x).getD e false with
        | false =>
          by_cases q : ∀ i, i < e → (code C1.gates x).getD i false = true
          · rw [i1 q]
            exact s2 hb
          · exact i2 q
        | true =>
          obtain ⟨ev, tk⟩ := s1 hb
          apply i2
          intro q
          apply nall
          intro i hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · rw [←take_getD tk h]
            exact q i h
          · rw [h]
            exact hb

theorem restrict (n r : Nat) (C : Circuit) (hv : valid (n+r+2) C) :
    ∃ S : Circuit, valid (n+2) S ∧
      PEqualNP.NotBracket.notCount S = PEqualNP.NotBracket.notCount C ∧ S.size = C.size ∧
      ∀ u : List Bool, u.length = n →
        S.eval (u ++ [false,true]) = C.eval (u ++ List.replicate r false ++ [false,true]) := by
  obtain ⟨fan, back, hout⟩ := hv
  have hsz : C.size = C.gates.length := rfl
  let S : Circuit := ⟨C.gates.map (remap (rho n r)), rho n r C.output⟩
  have hsize : S.size = C.size := by simp [S,Circuit.size]
  have hg : ∀ j, gateAt S j = remap (rho n r) (gateAt C j) := fun j => gateAt_map _ _ _ j
  have backS : ReadsBack (n+2) S := by
    intro j hj i hi
    rw [hg] at hi
    simp only [remap,List.mem_map] at hi
    obtain ⟨i0, hi0, rfl⟩ := hi
    have hj' : j < C.gates.length := by simpa [S] using hj
    have := back j hj' i0 hi0
    unfold rho
    split_ifs <;> omega
  refine ⟨S, ⟨?_, backS, ?_⟩, notCount_map _ _ _ _, hsize, ?_⟩
  · intro g hg'
    simp only [S,List.mem_map] at hg'
    obtain ⟨g0, hg0, rfl⟩ := hg'
    simpa [remap] using fan g0 hg0
  · show rho n r C.output < n + 2 + S.size
    rw [hsize]
    unfold rho
    split_ifs <;> omega
  · intro u hu
    obtain ⟨xs, hxs⟩ : ∃ xs, xs = u ++ [false,true] := ⟨_, rfl⟩
    obtain ⟨xc, hxc⟩ : ∃ xc, xc = u ++ List.replicate r false ++ [false,true] := ⟨_, rfl⟩
    have lxs : xs.length = n+2 := by rw [hxs]; simp [hu]
    have lxc : xc.length = n+r+2 := by rw [hxc]; simp [hu]; omega
    rw [←hxs,←hxc]
    have key : ∀ t, t < n+r+2+C.size →
        (S.wires xs).getD (rho n r t) false = (C.wires xc).getD t false := by
      intro t
      induction t using Nat.strong_induction_on with
      | _ t ih =>
        intro ht
        by_cases hin : t < n+r+2
        · have a1 : rho n r t < xs.length := by
            rw [lxs]
            unfold rho
            split_ifs <;> omega
          rw [show S.wires xs = run S.gates xs from rfl,show C.wires xc = run C.gates xc from rfl,
            getD_run _ _ _ a1,getD_run _ _ _ (by omega),hxs,hxc]
          exact inputs_agree n r u hu t hin
        · obtain ⟨j, rfl⟩ : ∃ j, t = n+r+2+j := ⟨t-(n+r+2), by omega⟩
          have e : rho n r (n+r+2+j) = n+2+j := by
            unfold rho
            split_ifs <;> omega
          have bj := back j (by omega)
          rw [e,wire_gate S (n+2) backS xs lxs j (by omega),
            wire_gate C (n+r+2) back xc lxc j (by omega),hg]
          simp only [remap,List.map_map]
          congr 1
          apply List.map_congr_left
          intro i hi
          have := bj i hi
          exact ih i (by omega) (by omega)
    exact key C.output hout

end PEqualNP.Outside.L_lib_1427_aux

open PEqualNP.Outside.L_lib_1427_aux in
theorem PEqualNP.Outside.L_lib_1427 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let valid := fun (n : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) D ∧ D.output < n+2+D.size
let bits := fun (r : Nat) (Y : Finset Nat) => List.ofFn (fun j : Fin r => decide (j.val ∈ Y))
∀ (n r b a : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) (P : Finset Nat → Prop) (bad : Finset Nat → Bool),
  a ≤ b → valid (n+r) D → PEqualNP.NotBracket.notCount D ≤ b →
  let K := 2^b-2^a+1
  let I := fun X Y : Finset Nat => bits n X ++ bits r Y ++ [false,true]
  (∀ X ⊆ Finset.range n, P X → D.eval (I X ∅) = bad X) →
  (∀ X ⊆ Finset.range n, P X → bad X=false →
    ∃ Y : Fin K → Finset Nat, Monotone Y ∧ (∀ j, Y j ⊆ Finset.range r) ∧
      ∀ i j, i.val+1=j.val → ∃ t < n+r+2+D.size,
        (D.wires (I X (Y i))).getD t false = true ∧ (D.wires (I X (Y j))).getD t false = false) →
  ∃ S : PEqualNP.CircuitLowerBounds.Circuit, valid n S ∧ PEqualNP.NotBracket.notCount S ≤ a ∧
    S.size-PEqualNP.NotBracket.notCount S ≤ D.size-PEqualNP.NotBracket.notCount D+(b-a) ∧
    ∀ X ⊆ Finset.range n, P X → S.eval (bits n X ++ [false,true]) = bad X) := by
  intro valid bits n r b a D P bad hab hval hnot K I hev hchain
  obtain ⟨fan, back, hout⟩ := hval
  have ops : ∀ g∈D.gates, g.op=.and ∨ g.op=.or ∨ g.op=.not := fun g hg => by
    simpa using (fan g hg).1
  obtain ⟨D', ⟨fan', back', hout'⟩, hc, hs, hE⟩ :=
    elim (n+r+2) (n+r+1) D ⟨fan,back,hout⟩ (PEqualNP.NotBracket.notCount D - a) (Nat.sub_le _ _)
      (by omega)
  obtain ⟨S, hvS, hnS, hsS, hS⟩ := restrict n r D' ⟨fan',back',hout'⟩
  have hmle : PEqualNP.NotBracket.notCount D ≤ D.size := List.length_filter_le _ _
  refine ⟨S, hvS, by omega, by omega, ?_⟩
  intro X hX hP
  have hbits : bits r ∅ = List.replicate r false := by simp [bits]
  have e1 : S.eval (bits n X ++ [false,true]) = D'.eval (I X ∅) := by
    have := hS (bits n X) (by simp [bits])
    simpa [I,hbits] using this
  rw [e1]
  have hlen : (I X ∅).length = n+r+2 := by
    simp [I,bits]
    omega
  have hlen2 : (bits n X ++ bits r ∅).length = n+r := by simp [bits]
  have hτ : (I X ∅).getD (n+r+1) false = true := by
    show ((bits n X ++ bits r ∅) ++ [false,true]).getD (n+r+1) false = true
    rw [List.getD_append_right _ _ _ _ (by omega),hlen2]
    simp
  obtain ⟨hA, hB⟩ := hE (I X ∅) hlen hτ (by omega)
  have ordI : ∀ A B : Finset Nat, A ⊆ B → ordered (I X A) (I X B) := fun A B hAB =>
    ordered_append (ordered_append (ordered_refl _)
      (ordered_ofFn fun j h => by
        simp only [decide_eq_true_eq] at h ⊢
        exact hAB h)) (ordered_refl _)
  cases hb : bad X with
  | true =>
    by_cases all : ∀ i, i < PEqualNP.NotBracket.notCount D - a →
        (code D.gates (I X ∅)).getD i false = true
    · exact (hA all).trans ((hev X hX hP).trans hb)
    · exact hB all
  | false =>
    obtain ⟨Y, mono, sub, fall⟩ := hchain X hX hP hb
    have K1 : 1 ≤ K := Nat.le_add_left 1 _
    have p2a : 2^a ≤ 2^b := Nat.pow_le_pow_right (by norm_num) hab
    have p2m : 2^PEqualNP.NotBracket.notCount D ≤ 2^b := Nat.pow_le_pow_right (by norm_num) hnot
    have KL : K - 1 + 2^a = 2^b := by
      show 2^b-2^a+1-1+2^a = 2^b
      omega
    have all : ∀ i, i < PEqualNP.NotBracket.notCount D - a →
        (code D.gates (I X ∅)).getD i false = true := by
      intro i hi
      refine head_true D ops a (K-1) (fun i => I X (Y ⟨min i (K-1), by omega⟩)) ?_ ?_ (by omega)
        (I X ∅) (ordI _ _ (Finset.empty_subset _)) i (by omega)
      · intro i hi
        exact ordI _ _ (mono (by simp only [Fin.le_def]; omega))
      · intro i hi
        obtain ⟨t,_,h1,h2⟩ := fall ⟨min i (K-1), by omega⟩ ⟨min (i+1) (K-1), by omega⟩
          (by simp only; omega)
        exact ⟨t,h1,h2⟩
    rw [hA all, hev X hX hP, hb]

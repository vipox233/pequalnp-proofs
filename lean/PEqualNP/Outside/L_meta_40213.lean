import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40213

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276808426 * 2 ^ 32 + 4272482472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x9000041020194294#64 ++ 0xa4000104080650a5#64 ++ 0xee023cf1e03fc7ff#64 ++ 0xfb808f3c780ff1ff#64 : BitVec 256),
   (0x600cd14690c4994b#64 ++ 0x18033451a4312652#64 ++ 0xde1dd34e91c4f9cd#64 ++ 0xf78774d3a4713e73#64 : BitVec 256),
   (0x4061628b16062c62#64 ++ 0x501858a2c5818b18#64 ++ 0xbde1e38f1e073e73#64 ++ 0xef7878e3c781cf9c#64 : BitVec 256),
   (0x81b603f00b683780#64 ++ 0x606d80fc02da0de0#64 ++ 0x7ffe03f01ff83f83#64 ++ 0x5fff80fc07fe0fe0#64 : BitVec 256),
   (0x02dbfc001db7c003#64 ++ 0x80b6ff00076df000#64 ++ 0xfbfffc001fffc003#64 ++ 0x3effff0007fff000#64 : BitVec 256),
   (0x00ffbbedc0000000#64 ++ 0x003feefb70000000#64 ++ 0xf8ffffffe0000000#64 ++ 0xfe3ffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [7, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000f1e0000000 0xc000003c78000000

def z1 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xf8ffffffe0000000 0xfe3ffffff8000000

def z2 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfbfffc001fffc003 0x3effff0007fff000

def z3 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xbde1e38f1e073e73 0xef7878e3c781cf9c

def z4 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xde1dd34e91c4f9cd 0xf78774d3a4713e73

def z5 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x7ffe03f01ff83f83 0x5fff80fc07fe0fe0

def z6 : W := mkw 0x9000041020194294 0xa4000104080650a5 0xee023cf1e03fc7ff 0xfb808f3c780ff1ff

def z7 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x15fc03f01fc03f80 0x457f00fc07f00fe0

def z8 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0x101dc30e11c03800 0x040770c384700e00

def z9 : W := mkw 0xf00cd556b0dddbdf 0xbc033555ac3776f7 0xfe1ffffff1ffffff 0xff87fffffc7fffff

def z10 : W := mkw 0x606df3cf96c6bd6b 0x581b7cf3e5b1af5a 0xfffdf3cf9fc7ffff 0xffff7cf3e7f1ffff

def z11 : W := mkw 0x0049b80dc0000000 0x00126e0370000000 0x8001fc0fe0000000 0xa0007f03f8000000

def z12 : W := mkw 0x40fffbefd6062c62 0x503ffefbf5818b18 0xfdfffffffe073e73 0xff7fffffff81cf9c

def z13 : W := mkw 0x0092000009200000 0x0024800002480000 0x7bfe00001ff80003 0x1eff800007fe0000

def z14 : W := mkw 0x01b603e00b603500 0x406d80f802d80d40 0x11fc03001fc03800 0x047f00c007f00e00

def z15 : W := mkw 0xd061669b361f6ef6 0xf41859a6cd87dbbd 0xffe3fffffe3fffff 0xfff8ffffff8fffff

def z16 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xfcffffffe0070673 0xff3ffffff801c19c

def z17 : W := mkw 0x0000000000000000 0x0000000000000000 0xac00208100070673 0xeb0008204001c19c

def z18 : W := mkw 0x81f723f90b683780 0x607dc8fe42da0de0 0xffffe3ff1ff83f83 0xfffff8ffc7fe0fe0

def z19 : W := mkw 0x00b202a000000000 0x002c80a800000000 0x20e200b000000000 0x0838802c00000000

def z20 : W := mkw 0x4000400210040842 0x1000100084010210 0x9c01c30e10043841 0xe70070c384010e10

def z21 : W := mkw 0x812403f002483780 0x604900fc00920de0 0x040003f000003f80 0x410000fc00000fe0

def z22 : W := mkw 0x4269fe8b1697ec63 0xd09a7fa2c5a5fb18 0xbde1ff8f1e07fe73 0xef787fe3c781ff9c

def z23 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0x53ffdc001ff8c000 0x14fff70007fe3000

def z24 : W := mkw 0x0004014000401100 0x0001005000100440 0x5e1c034011c03981 0x578700d004700e60

def z25 : W := mkw 0xe1bed3f69becbfcb 0x786fb4fda6fb2ff2 0xffffd3fe9ffcffcf 0xfffff4ffa7ff3ff3

def z26 : W := mkw 0xf008d416b09dcadf 0xbc023505ac2772b7 0xee03fcffe03fc7ff 0xfb80ff3ff80ff1ff

def z27 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0x3de1c38e1e003e03 0x4f7870e387800f80

def z28 : W := mkw 0xc161629b1f6e3fe2 0x705858a6c7db8ff8 0xbfe1e38f1fff3ff3 0xeff878e3c7ffcffc

def z29 : W := mkw 0x90f32eb960194294 0xa43ccbae580650a5 0x20e22cb1603b0632 0x08388b2c580ec18c

def z30 : W := mkw 0x0041600014060002 0x0010580005018000 0xb9e1e0001e070003 0x2e7878000781c000

def z31 : W := mkw 0x0020028002002400 0x400800a000800900 0x3de003801e003e03 0x4f7800e007800f80

def z32 : W := mkw 0x4041600b14060862 0x10105802c5018218 0x8001e00f00070070 0xa0007803c001c01c

def z33 : W := mkw 0x1000040020114014 0x8400010008045005 0x00002c0160030030 0x00000b005800c00c

def z34 : W := mkw 0x00f32aa940000000 0x003ccaaa50000000 0x00e0000000000000 0x0038000000000000

def z35 : W := mkw 0x02089c000091c001 0x8082270000247000 0x00001c000000c000 0x0000070000003000

def z36 : W := mkw 0xf000441230dddbdf 0xbc0011048c3776f7 0x0600000011ffffff 0x01800000047fffff

def z37 : W := mkw 0x8000001000080280 0x20000004000200a0 0x6e0200f000380783 0x5b80803c000e01e0

def z38 : W := mkw 0x0249fc0dd497c003 0x80927f037525f000 0x8001fc0fe007c000 0xa0007f03f801f000

def z39 : W := mkw 0x8000001000080280 0x20000004000200a0 0x0600000000380783 0x01800000000e01e0

def z40 : W := mkw 0x0000040000114000 0x8000010000045000 0xea023c00003fc003 0x3a808f00000ff000

def z41 : W := mkw 0x02dbf8001da68003 0x00b6fe000769a000 0x11fdc0001fc00000 0x047f700007f00000

def z42 : W := mkw 0x902407fde0194294 0xa40901ff780650a5 0xee023fffe03fc7ff 0xfb808ffff80ff1ff

def z43 : W := mkw 0x40f3628b1f262c62 0x503cd8a2c7c98b18 0xffffe38f1fff3e73 0xfffff8e3c7ffcf9c

def z44 : W := mkw 0x609ed14699e4994b 0x1827b451a6792652 0xffffd34e9ffcf9cf 0xfffff4d3a7ff3e73

def z45 : W := mkw 0x83fffff01ffff783 0xe0fffffc07fffde0 0xfffffff01fffff83 0x7ffffffc07ffffe0

def z46 : W := mkw 0x40fffbefd6062c62 0x503ffefbf5818b18 0xbdfde38f1e073e73 0xef7f78e3c781cf9c

def z47 : W := mkw 0x4000000200000840 0x1000000080000210 0x0400030e00003840 0xc10000c380000e10

def z48 : W := mkw 0xc1b603fb0b683fe0 0x706d80fec2da0ff8 0x7ffe03ff1ff83ff3 0xdfff80ffc7fe0ffc

def z49 : W := mkw 0x6008d0069084884b 0x18023401a4212212 0x8001d00e8004c04c 0xa0007403a0013013

def z50 : W := mkw 0x92dbfc103dbfc297 0xa4b6ff040f6ff0a5 0xfffffcf1ffffc7ff 0xffffff3c7ffff1ff

def z51 : W := mkw 0x22dffd449df7d10b 0x88b7ff51277df442 0xfbfffc409fffc18f 0x3effff1027fff063

def z52 : W := mkw 0x0008d4001095c003 0x8002350004257000 0xfa1ffc0011ffc003 0x3e87ff00047ff000

def z53 : W := mkw 0x0061228900000000 0x001848a240000000 0xb8e1e38f00000000 0xee3878e3c0000000

def z54 : W := mkw 0x00f32aa940000000 0x003ccaaa50000000 0x20e22cb160000000 0x08388b2c58000000

def z55 : W := mkw 0x42fbfa8b1fa6ac63 0x50befea2c7e9ab18 0xbdfde38f1fc73e73 0xef7f78e3c7f1cf9c

def z56 : W := mkw 0x9000041020194294 0xa4000104080650a5 0xce001040803fc7ff 0xf3800410200ff1ff

def z57 : W := mkw 0xf00cd156b0cc9bdf 0x3c033455ac3326f7 0xde1dd3fff1c4fffd 0xf78774fffc713fff

def z58 : W := mkw 0x1000040020114014 0x8400010008045005 0x80003c01e007c07c 0xa0000f007801f01f

def z59 : W := mkw 0x00b603e000000000 0x002d80f800000000 0x78fe03f000000000 0x5e3f80fc00000000

def z60 : W := mkw 0x81ffbbfdcb683780 0x607feeff72da0de0 0xfffffffffff83f83 0xfffffffffffe0fe0

def z61 : W := mkw 0xe12cd3f692ccbfcb 0x784b34fda4b32ff2 0xde1dd3fe91c4ffcd 0xf78774ffa4713ff3

def z62 : W := mkw 0x0061228906022420 0x401848a241808908 0x21e020810e030632 0x087808204380c18c

def z63 : W := mkw 0x200c914480c09109 0x0803245120302442 0x421c104081c0c18c 0x1087041020703063

def z64 : W := mkw 0x00ffbbedc6022420 0x403feefb71808908 0xf9ffffffee030632 0xfe7ffffffb80c18c

def z65 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x53fe03701ff83980 0x14ff80dc07fe0e60

def z66 : W := mkw 0x0249fc001db7c003 0x80927f00076df000 0x8301fc001fffc003 0x20c07f0007fff000

def z67 : W := mkw 0x00fffbedd4060002 0x003ffefb75018000 0xf9fffffffe070003 0xfe7fffffff81c000

def z68 : W := mkw 0x000cd14010c49103 0x0003345004312440 0xde1dd34011c4f981 0x778774d004713e60

def z69 : W := mkw 0x0249fc001497c003 0x80927f000525f000 0x8001fc000007c000 0x20007f000001f000

def z70 : W := mkw 0xe19ed17699ec9bcb 0x3867b45da67b26f2 0xde1fd37e91fcf9cd 0xf787f4dfa47f3e73

def z71 : W := mkw 0x02dbfc001497c003 0x80b6ff000525f000 0xf8fffc000007c000 0x3e3fff000001f000

def z72 : W := mkw 0x4020028b02002c60 0x500800a2c0800b18 0x0400038f00003e70 0xc10000e3c0000f9c

def z73 : W := mkw 0x42fbfe8b1fb7ec63 0xd0beffa2c7edfb18 0xffffff8f1ffffe73 0xffffffe3c7ffff9c

def z74 : W := mkw 0x81b202b00b282680 0x606c80ac02ca09a0 0x21e200b00e380602 0x0878802c038e0180

def z75 : W := mkw 0x000cd14490848003 0x0003345124212000 0xda1dd34e91c4c001 0xf68774d3a4713000

def z76 : W := mkw 0x81b603f00b282680 0x606d80fc02ca09a0 0x79fe03f00e380602 0x5e7f80fc038e0180

def z77 : W := mkw 0x4000400216062c62 0x5000100085818b18 0xad0020811e073e73 0xeb4008204781cf9c

def z78 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0x10fdc30e00000000 0x043f70c380000000

def z79 : W := mkw 0x9000041020194294 0xa4000104080650a5 0x06000000003fc7ff 0x01800000000ff1ff

def z80 : W := mkw 0x0020028002002400 0x400800a000800900 0x0400038000003e00 0x410000e000000f80

def z81 : W := mkw 0x8100001002483780 0x6040000400920de0 0x0400000000003f80 0x0100000000000fe0

def z82 : W := mkw 0x6008d0069084884b 0x18023401a4212212 0xda1dd00e91c4c04d 0xb6877403a4713013

def z83 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0xfffe13f09ffcffcf 0xffff84fc27ff3ff3

def z84 : W := mkw 0x5061668b36176c76 0xd41859a2cd85db1d 0xbde1ff8ffe07fe7f 0xef787fe3ff81ff9f

def z85 : W := mkw 0x810401500b683780 0x6041005402da0de0 0x5f1c03401ff83f83 0x57c700d007fe0fe0

def z86 : W := mkw 0x029a9c0009b1c001 0x80a6a700026c7000 0x421e1c0001f8c000 0x10878700007e3000

def z87 : W := mkw 0x00f32aa940000000 0x003ccaaa50000000 0xb8e3efbf60000000 0xee38fbefd8000000

def z88 : W := mkw 0xc1f763fb1f6e3fe2 0x707dd8fec7db8ff8 0xffffe3ff1fff3ff3 0xfffff8ffc7ffcffc

def z89 : W := mkw 0xe1bed3f69becbfcb 0x786fb4fda6fb2ff2 0x7fffc3fe1ff83f83 0x5ffff0ff87fe0fe0

def z90 : W := mkw 0x6000400210c4994b 0x1800100084312652 0x0600000011c4f9cd 0x0180000004713e73

def z91 : W := mkw 0x4061628b14060862 0x101858a2c5018218 0xb8e1e38f00070070 0xee3878e3c001c01c

def z92 : W := mkw 0x002c93edc0000000 0x000b24fb70000000 0xd81dd3ffe0000000 0xf60774fff8000000

def z93 : W := mkw 0x0041200904020020 0x0010480241008008 0x0000200100030030 0x000008004000c00c

def z94 : W := mkw 0x92dbfc103dbfc297 0xa4b6ff040f6ff0a5 0xfbfffcb17fffc633 0x3effff2c5ffff18c

def z95 : W := mkw 0x90ffbffde0194294 0xa43fefff780650a5 0xfeffffffe03fc7ff 0xffbffffff80ff1ff

def z96 : W := mkw 0x1049bc0de0114014 0x84126f0378045005 0x8001fc0fe007c07c 0xa0007f03f801f01f

def z97 : W := mkw 0x4008d00210848843 0x1002340084212210 0xde1dd30e11c4f841 0xf78774c384713e10

def z98 : W := mkw 0x006523edc0000000 0x001948fb70000000 0xb8e1e3ffe0000000 0xee3878fff8000000

def z99 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0xfffe23f11fff3ff3 0xffff88fc47ffcffc

def z100 : W := mkw 0x020040001da68003 0x008010000769a000 0x010000001fc00000 0x0040000007f00000

def z101 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0x521dd34e91c0f98c 0x148774d3a4703e63

def z102 : W := mkw 0x9061269920194294 0xa41849a6480650a5 0xfee3ffffe03fc7ff 0xffb8fffff80ff1ff

def z103 : W := mkw 0x6004014680401948 0x18010051a0100652 0x0400034e800039cc 0xc10000d3a0000e73

def z104 : W := mkw 0x0041600014060002 0x0010580005018000 0xbde1e0811e070673 0xef7878204781c19c

def z105 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0x11e1c30e1e003800 0x047870c387800e00

def z106 : W := mkw 0x60fffbefd084884b 0x183ffefbf4212212 0xf8ffffffe004c04c 0xfe3ffffff8013013

def z107 : W := mkw 0x4000400214060862 0x1000100085018218 0x0000000000070070 0x000000000001c01c

def z108 : W := mkw 0x006dbbedc0000000 0x001b6efb70000000 0x8001ffffe0000000 0xe0007ffff8000000

def z109 : W := mkw 0x002403e000000000 0x000900f800000000 0x000003f000000000 0x400000fc00000000

def z110 : W := mkw 0x606df3cf96c6bd6b 0x581b7cf3e5b1af5a 0x11fdc30e1fc03800 0x047f70c387f00e00

def z111 : W := mkw 0x0000000000000000 0x0000000000000000 0xc800104080000000 0xf200041020000000

def z112 : W := mkw 0x01ffbbedcb603500 0x407feefb72d80d40 0x11fdc30e1fc03800 0x047f70c387f00e00

def z113 : W := mkw 0x604df94fd0c4994b 0x18137e53f4312652 0xde1dff4ff1c4f9cd 0xf7877fd3fc713e73

def z114 : W := mkw 0xe3fffff69fffffcb 0xf8fffffda7fffff2 0xfffffffe9fffffcf 0xffffffffa7fffff3

def z115 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z116 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xfe1df3cf91c7ffff 0xff877cf3e471ffff

def z117 : W := mkw 0x9000041020194294 0xa4000104080650a5 0x20022cb1603b0632 0x08008b2c580ec18c

def z118 : W := mkw 0x91b206b02b396694 0xe46c81ac0ace59a5 0x21e22cb16e3b0632 0x08788b2c5b8ec18c

def z119 : W := mkw 0x62ffffcf9ff7fd6b 0xd8bffff3e7fdff5a 0xffffffcf9fffffff 0xfffffff3e7ffffff

def z120 : W := mkw 0x8104017000481380 0x2041005c001204e0 0x0000007000000180 0x0000001c00000060

def z121 : W := mkw 0x83fffffddffff783 0xe0ffffff77fffde0 0xffffffffffffff83 0xffffffffffffffe0

def z122 : W := mkw 0x812002b002082680 0x604800ac008209a0 0x000000b000000600 0x0000002c00000180

def z123 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0x10fdc3ffe0000000 0xc43f70fff8000000

def z124 : W := mkw 0x00be9be4c0000000 0x002fa6f930000000 0x78fe1ff0e0000000 0x5e3f87fc38000000

def z125 : W := mkw 0x606df3cf96c6bd6b 0x581b7cf3e5b1af5a 0xbdfde38f1fc73e73 0xef7f78e3c7f1cf9c

def z126 : W := mkw 0x91b607f02b797794 0xe46d81fc0ade5de5 0xfffe3ff1ffffffff 0xffff8ffc7fffffff

def z127 : W := mkw 0x009e9964c0000000 0x0027a65930000000 0x401e1c70e0000000 0x1007871c38000000

def z128 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0x161dc30e11c4f9cd 0x058770c384713e73

def z129 : W := mkw 0x8196017009681380 0x2065805c025a04e0 0x421e007001f80180 0x1087801c007e0060

def z130 : W := mkw 0x02ffffedddb7c003 0x80bffffb776df000 0xfbffffffffffc003 0xfefffffffffff000

def z131 : W := mkw 0x812403fdc2483780 0x604900ff70920de0 0x040003ffe0003f80 0xc10000fff8000fe0

def z132 : W := mkw 0x4061668b16176c62 0xd01859a2c585db18 0xffe3ff8f1e3ffe73 0xfff8ffe3c78fff9c

def z133 : W := mkw 0x8092001009280280 0x20248004024a00a0 0x7ffe00f01ff80783 0x5fff803c07fe01e0

def z134 : W := mkw 0x42dbfc0b1db7c863 0x90b6ff02c76df218 0xfbfffc0f1fffc073 0xbeffff03c7fff01c

def z135 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0x30ffefbf60000000 0x0c3ffbefd8000000

def z136 : W := mkw 0x00b603e009200000 0x002d80f802480000 0x7bfe03f01ff80003 0x5eff80fc07fe0000

def z137 : W := mkw 0x4069f28b1686ac63 0x501a7ca2c5a1ab18 0xfffdf38f1fc7fe73 0xffff7ce3c7f1ff9c

def z138 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xc21ffc0001ffc000 0x3087ff00007ff000

def z139 : W := mkw 0x9000041020194294 0xa4000104080650a5 0x42021c70e038c18c 0x1080871c380e3063

def z140 : W := mkw 0x0008d00010848003 0x0002340004212000 0x8001d0000004c000 0x2000740000013000

def z141 : W := mkw 0x8192003009280280 0x2064800c024a00a0 0x0002003000380000 0x0000800c000e0000

def z142 : W := mkw 0x209e9964c0c09109 0x0827a65930302442 0x421e1c70e1c0c18c 0x1087871c38703063

def z143 : W := mkw 0x0000000000000000 0x0000000000000000 0x680200f000000000 0x5a00803c00000000

def z144 : W := mkw 0x4041600b14060862 0x10105802c5018218 0x9c01e30f10073871 0xe70078c3c401ce1c

def z145 : W := mkw 0x6000400216c6bd6b 0x5800100085b1af5a 0x070000001fc7ffff 0x01c0000007f1ffff

def z146 : W := mkw 0x0061228900000000 0x001848a240000000 0xf8e3ffffe0000000 0xfe38fffff8000000

def z147 : W := mkw 0x5041640b34174876 0x94105902cd05d21d 0x8001fc0fe007c07c 0xa0007f03f801f01f

def z148 : W := mkw 0x0249fc001497c003 0x80927f000525f000 0xda1dfc0011c7c001 0x36877f000471f000

def z149 : W := mkw 0x002403edc0000000 0x000900fb70000000 0x000003ffe0000000 0xc00000fff8000000

def z150 : W := mkw 0x000c914480000000 0x0003245120000000 0xd81dd34e80000000 0xf60774d3a0000000

def z151 : W := mkw 0x02dbbc000d334000 0x80b6ef00034cd000 0xf9fffc000e3b0002 0x3e7fff00038ec000

def z152 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfbfffcf1ffffc003 0xfeffff3c7ffff000

def z153 : W := mkw 0x00ffbbe000000000 0x003feef800000000 0xf8fffff000000000 0x7e3ffffc00000000

def z154 : W := mkw 0x81ffbbfdc9681380 0x207feeff725a04e0 0xfaffffffe1f80180 0xfebffffff87e0060

def z155 : W := mkw 0x0004014000401100 0x0001005000100440 0x101c030011c03800 0x040700c004700e00

def z156 : W := mkw 0x020044001db7c003 0x80801100076df000 0x030000001fffc003 0x00c0000007fff000

def z157 : W := mkw 0x0000400010848003 0x0000100004212000 0x0200000011c4c001 0x0080000004713000

def z158 : W := mkw 0x81b202b00b282680 0x606c80ac02ca09a0 0x7bfe00b01ff80603 0x1eff802c07fe0180

def z159 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xa1e1e08f0e070672 0xa8787823c381c19c

def z160 : W := mkw 0x60fffbefd0c4994b 0x183ffefbf4312652 0xfefffffff1c4f9cd 0xffbffffffc713e73

def z161 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0x31ffec001ffb0002 0x0c7ffb0007fec000

def z162 : W := mkw 0x0004014000401100 0x0001005000100440 0xde1c134091c4f9cd 0xf78704d024713e73

def z163 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0x5e1dc34e11c03981 0x578770d384700e60

def z164 : W := mkw 0x62dff9469de6994b 0x18b7fe51a779a652 0xdffdd34e9fc4f9cd 0xf7ff74d3a7f13e73

def z165 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0x9c1dc30e11c43841 0xe70770c384710e10

def z166 : W := mkw 0x002002a940000000 0x000800aa50000000 0x000000b160000000 0x0000002c58000000

def z167 : W := mkw 0x812002900b683780 0x604800a402da0de0 0x3fe003801ff83f83 0x4ff800e007fe0fe0

def z168 : W := mkw 0x60bed3e690c4994b 0x182fb4f9a4312652 0xfeffd3fe91c4f9cd 0xffbff4ffa4713e73

def z169 : W := mkw 0x029244001db7c003 0x80a49100076df000 0x7bfe00001fffc003 0x1eff800007fff000

def z170 : W := mkw 0x0008d00010848003 0x0002340004212000 0x101dc00011c00000 0x0407700004700000

def z171 : W := mkw 0x02d32c000d334000 0x80b4cb00034cd000 0x21e22c000e3b0002 0x08788b00038ec000

def z172 : W := mkw 0x0000000000000000 0x0000000000000000 0x80003c01e0000000 0xa0000f0078000000

def z173 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xfde3fffffe073e73 0xff78ffffff81cf9c

def z174 : W := mkw 0x602cd3cf92c4bd6b 0x580b34f3e4b12f5a 0xde1dd3cf91c4fffd 0xf78774f3e4713fff

def z175 : W := mkw 0x9000001020080294 0x24000004080200a5 0x040000f1e00007fc 0xc100003c780001ff

def z176 : W := mkw 0x0061228906022420 0x401848a241808908 0x01e000000e000000 0x0078000003800000

def z177 : W := mkw 0x6249fc069497c84b 0x98927f01a525f212 0x8001fc0e8007c04c 0xa0007f03a001f013

def z178 : W := mkw 0x91ffbffdeb797794 0xe47fefff7ade5de5 0xffffffffffffffff 0xffffffffffffffff

def z179 : W := mkw 0x81f322b90f2a26a0 0x607cc8ae43ca89a8 0x21e220b10e3b0632 0x0878882c438ec18c

def z180 : W := mkw 0xd041641b341f4af6 0xb4105906cd07d2bd 0xee03fcffe03fc7ff 0xfb80ff3ff80ff1ff

def z181 : W := mkw 0x0000000000000000 0x0000000000000000 0xce0010408004c1cd 0xf380041020013073

def z182 : W := mkw 0x4000400216062c62 0x5000100085818b18 0x050000001e073e73 0x014000000781cf9c

def z183 : W := mkw 0x02fbfea95db7c003 0x80beffaa576df000 0xfbfffcb17fffc003 0x3effff2c5ffff000

def z184 : W := mkw 0x00fbba8900000000 0x003eeea240000000 0xf8ffff8f00000000 0xfe3fffe3c0000000

def z185 : W := mkw 0x93fffff03ffff797 0xe4fffffc0ffffde5 0xfffffff1ffffffff 0xfffffffc7fffffff

def z186 : W := mkw 0x9000041020194294 0xa4000104080650a5 0xee023c00003fc7ff 0x3b808f00000ff1ff

def z187 : W := mkw 0x9000001020080294 0x24000004080200a5 0x6e0200f1e03807ff 0xdb80803c780e01ff

def z188 : W := mkw 0x0020028002002400 0x400800a000800900 0x11e003001e003800 0x047800c007800e00

def z189 : W := mkw 0x029a9c0009b1c001 0x80a6a700026c7000 0x7bfe1c001ff8c003 0x1eff870007fe3000

def z190 : W := mkw 0xe10040121becbfcb 0x7840100486fb2ff2 0x070000001ffcffcf 0x01c0000007ff3ff3

def z191 : W := mkw 0x819200100b683780 0x6064800402da0de0 0x7ffe00001ff83f83 0x1fff800007fe0fe0

def z192 : W := mkw 0x4020428216062c62 0x500810a085818b18 0x3de003801e073e73 0x4f7800e00781cf9c

def z193 : W := mkw 0x00dfb96dc0000000 0x0037ee5b70000000 0xc01ffc7fe0000000 0xb007ff1ff8000000

def z194 : W := mkw 0x62dbfc069db7c84b 0x98b6ff01a76df212 0xfbfffc0e9fffc04f 0xbeffff03a7fff013

def z195 : W := mkw 0x0049b80dc0000000 0x00126e0370000000 0xe803fcffe0000000 0xfa00ff3ff8000000

def z196 : W := mkw 0x909e9d74e0194294 0xa427a75d380650a5 0xee1e3cf1e03fc7ff 0xfb878f3c780ff1ff

def z197 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x17fc03001ff83f83 0x05ff00c007fe0fe0

def z198 : W := mkw 0x02ffbfedcd334000 0x80bfeffb734cd000 0xf9ffffffee3b0002 0xfe7ffffffb8ec000

def z199 : W := mkw 0x0000400014060002 0x0000100005018000 0x010000001e070003 0x004000000781c000

def z200 : W := mkw 0x229e9d4489f1d109 0x88a7a751227c7442 0x421e1c4081f8c18c 0x10878710207e3063

def z201 : W := mkw 0x812403f002483780 0x604900fc00920de0 0x5e1c03f011c03f81 0x578700fc04700fe0

def z202 : W := mkw 0xc12403fb02483fe0 0x704900fec0920ff8 0x040003ff00003ff0 0xc10000ffc0000ffc

def z203 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0x91fdfc001fc7c000 0x247f7f0007f1f000

def z204 : W := mkw 0x42ffffefdfb7ec63 0xd0bffffbf7edfb18 0xfffffffffffffe73 0xffffffffffffff9c

def z205 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8023cf1e0000000 0xfa008f3c78000000

def z206 : W := mkw 0x0004014000401100 0x0001005000100440 0x0400034000003980 0x410000d000000e60

def z207 : W := mkw 0x1000040020114014 0x8400010008045005 0xea023c01e03fc07f 0xba808f00780ff01f

def z208 : W := mkw 0x4041600b16062c62 0x50105802c5818b18 0x8501e00f1e073e73 0xa1407803c781cf9c

def z209 : W := mkw 0x0008d00010848003 0x0002340004212000 0xda1dd00011c4c001 0x3687740004713000

def z210 : W := mkw 0x62dffd469df7d94b 0x98b7ff51a77df652 0xffffff4e9ffff9cf 0xffffffd3a7fffe73

def z211 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0x15e1c30e1e073e73 0x057870c38781cf9c

def z212 : W := mkw 0xc1b643f21b6c3fc2 0x706d90fc86db0ff0 0xffffc3fe1ffc3fc3 0xfffff0ff87ff0ff0

def z213 : W := mkw 0xd020029b22082ef4 0x740800a6c8820bbd 0x040003ffe0003ffc 0xc10000fff8000fff

def z214 : W := mkw 0x9000041020194294 0xa4000104080650a5 0xa0023cb1e03fc67e 0xa8008f2c780ff19f

def z215 : W := mkw 0x00b603e002002400 0x402d80f800800900 0x7dfe03f01e003e03 0x5f7f80fc07800f80

def z216 : W := mkw 0x81ffbbfdcb282680 0x607feeff72ca09a0 0xf9ffffffee380602 0xfe7ffffffb8e0180

def z217 : W := mkw 0x40ffbbefc2002c60 0x503feefbf0800b18 0xfcffffffe0003e70 0xff3ffffff8000f9c

def z218 : W := mkw 0x9000041020194294 0xa4000104080650a5 0xea023cb1603fc633 0x3a808f2c580ff18c

def z219 : W := mkw 0x20ffbbedc0c09109 0x083feefb70302442 0xfaffffffe1c0c18c 0xfebffffff8703063

def z220 : W := mkw 0x0020028000000000 0x000800a000000000 0x38e0038000000000 0x4e3800e000000000

def z221 : W := mkw 0xf00cd556b0dddbdf 0xbc033555ac3776f7 0xde1dd34e91ffffff 0xf78774d3a47fffff

def z222 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x461e03f001f83f80 0x518780fc007e0fe0

def z223 : W := mkw 0x0008900000808001 0x0002240000202000 0x421c100001c0c000 0x1087040000703000

def z224 : W := mkw 0x0092000000000000 0x0024800000000000 0x78fe000000000000 0x1e3f800000000000

def z225 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0x8401d34e8004f9cc 0xe10074d3a0013e73

def z226 : W := mkw 0x00ffbbedc2002400 0x403feefb70800900 0xfdfffffffe003e03 0xff7fffffff800f80

def z227 : W := mkw 0x0000000000000000 0x0000000000000000 0x800010008004c04c 0xa000040020013013

def z228 : W := mkw 0x0096014009601100 0x0025805002580440 0x7ffe03401ff83983 0x5fff80d007fe0e60

def z229 : W := mkw 0x61bed3e69be4bd4b 0x586fb4f9a6f92f52 0x11fdc30e1fc03800 0x047f70c387f00e00

def z230 : W := mkw 0x01ffbbedcb603500 0x407feefb72d80d40 0xf9ffffffffc03800 0xfe7ffffffff00e00

def z231 : W := mkw 0x624dfd4694d7d94b 0x98937f51a535f652 0xde1dff4e91c7f9cd 0xf7877fd3a471fe73

def z232 : W := mkw 0x0041640014174002 0x801059000505d000 0xfbe3fc001e3fc003 0x3ef8ff00078ff000

def z233 : W := mkw 0x00040164c0000000 0x0001005930000000 0x00000070e0000000 0x0000001c38000000

def z234 : W := mkw 0xd0fffffff61f6ef6 0xf43ffffffd87dbbd 0xfffffffffe3fffff 0xffffffffff8fffff

def z235 : W := mkw 0xa1be93f48be8b789 0x686fa4fd22fa2de2 0x7ffe13f09ff8ff8f 0x5fff84fc27fe3fe3

def z236 : W := mkw 0x810000100b282680 0x6040000402ca09a0 0x010000000e380602 0x00400000038e0180

def z237 : W := mkw 0x92d32c102d3b4294 0xa4b4cb040b4ed0a5 0x21e22cb16e3b0632 0x08788b2c5b8ec18c

def z238 : W := mkw 0x9000041020194294 0xa4000104080650a5 0x00020c3060380000 0x0000830c180e0000

def z239 : W := mkw 0x90dbbc1020194294 0xa436ef04080650a5 0xfefffcf1e03fc7ff 0xffbfff3c780ff1ff

def z240 : W := mkw 0x41f763eb1f663d62 0x507dd8fac7d98f58 0x11fdc30e1fc03800 0x047f70c387f00e00

def z241 : W := mkw 0x406563cb16463d62 0x501958f2c5918f58 0xfffde3cf1fc73ff3 0xffff78f3c7f1cffc

def z242 : W := mkw 0x009ad00019a48003 0x0026b40006692000 0xfbffd0001ffcc003 0x3efff40007ff3000

def z243 : W := mkw 0x609ed966d0c4994b 0x1827b659b4312652 0xde1fdf7ef1c4f9cd 0xf787f7dfbc713e73

def z244 : W := mkw 0x81be9bf4cb683780 0x606fa6fd32da0de0 0x7ffe1ff0fff83f83 0x5fff87fc3ffe0fe0

def z245 : W := mkw 0x0092000009200000 0x0024800002480000 0x421e000001f80000 0x10878000007e0000

def z246 : W := mkw 0x03fffbe01fe6b503 0x40fffef807f9ad40 0x11fdc3001fc03800 0x047f70c007f00e00

def z247 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0x78ffc3fe00000000 0x5e3ff0ff80000000

def z248 : W := mkw 0x6008d00210c4994b 0x1802340084312652 0xde1dd00011c4f9cd 0x3787740004713e73

def z249 : W := mkw 0x00dfb94480000000 0x0037ee5120000000 0xf8ffff4e80000000 0xfe3fffd3a0000000

def z250 : W := mkw 0x00ffbbedc9200000 0x003feefb72480000 0xfbfffffffff80003 0xfefffffffffe0000

def z251 : W := mkw 0x8000001000080280 0x20000004000200a0 0x040000f000000780 0x4100003c000001e0

def z252 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0x15e1c38f1e003e70 0xc57870e3c7800f9c

def z253 : W := mkw 0x02f32e890f336420 0xc0bccba243ccd908 0x21e22c810e3b0632 0x08788b20438ec18c

def z254 : W := mkw 0x9000001020080294 0x24000004080200a5 0xce0010f1e004c7fd 0xf380043c780131ff

def z255 : W := mkw 0xc10040121f6e3fe2 0x7040100487db8ff8 0x070000001fff3ff3 0x01c0000007ffcffc

def z256 : W := mkw 0x0092000009200000 0x0024800002480000 0x11fc00001fc00000 0x047f000007f00000

def z257 : W := mkw 0x6000000200401948 0x1800000080100652 0x04000000000039cc 0x0100000000000e73

def z258 : W := mkw 0x0000000dc0000000 0x0000000370000000 0x0000000fe0000000 0x80000003f8000000

def z259 : W := mkw 0xf0fffffff0dddbdf 0xbc3ffffffc3776f7 0xfefffffff1ffffff 0xffbffffffc7fffff

def z260 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0x141dc34e91c039cc 0xc50770d3a4700e73

def z261 : W := mkw 0x4020028b02002c60 0x500800a2c0800b18 0xac00238f00073e73 0xeb0008e3c001cf9c

def z262 : W := mkw 0x200c914480c09109 0x0803245120302442 0xce1c104081c4c1cd 0xf387041020713073

def z263 : W := mkw 0x02d32c000d334000 0x80b4cb00034cd000 0xebe23c000e3fc003 0x3af88f00038ff000

def z264 : W := mkw 0x0041200004020000 0x0010480001008000 0x21e020000e030002 0x087808000380c000

def z265 : W := mkw 0x9020069022196694 0xe40801a4088659a5 0xffe23ff1fe3fffff 0xfff88ffc7f8fffff

def z266 : W := mkw 0x02d32c000d334000 0x80b4cb00034cd000 0x7bfe2c001ffb0003 0x1eff8b0007fec000

def z267 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0x90fdff0fe0000000 0xa43f7fc3f8000000

def z268 : W := mkw 0x604df14f94c6996b 0x18137c53e531a65a 0xde1df34f91c7f9fd 0xf7877cd3e471fe7f

def z269 : W := mkw 0x606df3cf90c4994b 0x181b7cf3e4312652 0xfefdf3cf91c4f9cd 0xffbf7cf3e4713e73

def z270 : W := mkw 0x9000001020080294 0x24000004080200a5 0xac0020f1e00707ff 0xeb00083c7801c1ff

def z271 : W := mkw 0x910004102b797794 0xe44001040ade5de5 0xef023cf1ffffffff 0xfbc08f3c7fffffff

def z272 : W := mkw 0x9092041029394294 0xa42481040a4e50a5 0xfffe3cf1ffffc7ff 0xffff8f3c7ffff1ff

def z273 : W := mkw 0x00dbb80000000000 0x0036ee0000000000 0xf8fffc0000000000 0x3e3fff0000000000

def z274 : W := mkw 0x0041200900000000 0x0010480240000000 0x8001e00f00000000 0xa0007803c0000000

def z275 : W := mkw 0x02fbfe891fb7e423 0xc0beffa247edf908 0xfbfffc811fffc633 0x3effff2047fff18c

def z276 : W := mkw 0x9000041020194294 0xa4000104080650a5 0x020000000038c18c 0x00800000000e3063

def z277 : W := mkw 0x0092000009200000 0x0024800002480000 0x21e200000e380002 0x08788000038e0000

def z278 : W := mkw 0x02d36c001db7c003 0x80b4db00076df000 0x23e22c001fffc003 0x08f88b0007fff000

def z279 : W := mkw 0xb00c9554a0d9d39d 0xac032555283674e7 0xee1e3cf1e1ffc7ff 0xfb878f3c787ff1ff

def z280 : W := mkw 0x8000001000080280 0x20000004000200a0 0x4202007000380180 0x1080801c000e0060

def z281 : W := mkw 0x0061628914060002 0x001858a245018000 0xb9e1e38f1e070003 0xee7878e3c781c000

def z282 : W := mkw 0x400cd14690040842 0x10033451a4010210 0xdc1dd34e90043841 0xf70774d3a4010e10

def z283 : W := mkw 0x42f36e8b1f376c62 0xd0bcdba2c7cddb18 0xbde3ef8f1e3f3e73 0xef78fbe3c78fcf9c

def z284 : W := mkw 0x60fffbefd0c4994b 0x183ffefbf4312652 0xf8fffffff1c03800 0xfe3ffffffc700e00

def z285 : W := mkw 0x200c914480c09109 0x0803245120302442 0xda1dd34e81c0c18c 0xf68774d3a0703063

def z286 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0xfffe3ff1fff83f83 0xffff8ffc7ffe0fe0

def z287 : W := mkw 0x02ffffedddb7c003 0x80bffffb776df000 0xfbffff0e1fffc003 0x3effffc387fff000

def z288 : W := mkw 0x0020028902002420 0x400800a240800908 0x0000008100000630 0x000000204000018c

def z289 : W := mkw 0x0000000000000000 0x0000000000000000 0x6a02000000380003 0x1a808000000e0000

def z290 : W := mkw 0x00d360001d260002 0x0034d80007498000 0xfbffe0001fff0003 0x3efff80007ffc000

def z291 : W := mkw 0x8000001000080280 0x20000004000200a0 0xee0220f1003f07f3 0xfb80883c400fc1fc

def z292 : W := mkw 0x009a980000000000 0x0026a60000000000 0x401e1c0000000000 0x1007870000000000

def z293 : W := mkw 0x6000400210c4994b 0x1800100084312652 0x0000000011c03800 0x0000000004700e00

def z294 : W := mkw 0x00d3280000000000 0x0034ca0000000000 0x20e22c0000000000 0x08388b0000000000

def z295 : W := mkw 0x00dbb80009200000 0x0036ee0002480000 0xfbfffc001ff80003 0x3effff0007fe0000

def z296 : W := mkw 0x912407f022597794 0xe44901fc08965de5 0xee023ff1e03fffff 0xfb808ffc780fffff

def z297 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xfeffffffe004c1cd 0xffbffffff8013073

def z298 : W := mkw 0x4069fa8fd6062c62 0x501a7ea3f5818b18 0xbde1ff8ffe073e73 0xef787fe3ff81cf9c

def z299 : W := mkw 0x81b603fdcb683780 0x606d80ff72da0de0 0x7ffe03fffff83f83 0xdfff80fffffe0fe0

def z300 : W := mkw 0x00fffbedd0848003 0x003ffefb74212000 0xfafffffff1c4c001 0xfebffffffc713000

def z301 : W := mkw 0x6004014680401948 0x18010051a0100652 0xce00134e8004f9cd 0xf38004d3a0013e73

def z302 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0x461c104091c4f9cd 0x1187041024713e73

def z303 : W := mkw 0x810000100b683780 0x6040000402da0de0 0x070000001ff83f83 0x01c0000007fe0fe0

def z304 : W := mkw 0x0041600014060002 0x0010580005018000 0x11e1c0001e000000 0x0478700007800000

def z305 : W := mkw 0x60ffbbefc0401948 0x183feefbf0100652 0xfcffffffe00039cc 0xff3ffffff8000e73

def z306 : W := mkw 0x02dbf8001da68003 0x00b6fe000769a000 0x7bffc0001ff80003 0x1efff00007fe0000

def z307 : W := mkw 0xd0004412361f6ef6 0xf40011048d87dbbd 0xef023cf1fe3fffff 0xfbc08f3c7f8fffff

def z308 : W := mkw 0x0208d4001db7c003 0x80823500076df000 0xdb1dd0001fffc003 0x36c7740007fff000

def z309 : W := mkw 0xf06df7dfb6dfffff 0xfc1b7df7edb7ffff 0xffffffffffffffff 0xffffffffffffffff

def z310 : W := mkw 0x00ffbbedc0401100 0x003feefb70100440 0xfefffffff1c03981 0xffbffffffc700e60

def z311 : W := mkw 0xf1bed7f6bbfdffdf 0xfc6fb5fdaeff7ff7 0xffffffffffffffff 0xffffffffffffffff

def z312 : W := mkw 0x4261668b1fb7ec63 0xd09859a2c7edfb18 0xbfe1e38f1ffffe73 0xeff878e3c7ffff9c

def z313 : W := mkw 0x02dbf8001da68003 0x00b6fe000769a000 0xdbfdd0001fc4c001 0x36ff740007f13000

def z314 : W := mkw 0x000c914480401100 0x0003245120100440 0xde1dd34e91c03981 0xf78774d3a4700e60

def z315 : W := mkw 0x902403fde0080294 0x240900ff780200a5 0x040003ffe00007fc 0xc10000fff80001ff

def z316 : W := mkw 0x91b603f02b683794 0x646d80fc0ada0de5 0x7ffe03f1fff83fff 0xdfff80fc7ffe0fff

def z317 : W := mkw 0x40fffbefd0040842 0x103ffefbf4010210 0xfcfffffff0043841 0xff3ffffffc010e10

def z318 : W := mkw 0x600cd1469084884b 0x18033451a4212212 0xd81dd34e8004c04c 0xf60774d3a0013013

def z319 : W := mkw 0x81f723f90f6a37a0 0x607dc8fe43da8de8 0x7ffe23f11ffb3fb3 0x5fff88fc47fecfec

def z320 : W := mkw 0x6008d0069084884b 0x18023401a4212212 0xce01d04e8004c1cd 0xf3807413a0013073

def z321 : W := mkw 0xe10cd1569becbfcb 0x78433455a6fb2ff2 0xdf1dd34e9ffcffcf 0xf7c774d3a7ff3ff3

def z322 : W := mkw 0x90612699261b66b4 0xe41849a64986d9ad 0x21e22cb16e3b0632 0x08788b2c5b8ec18c

def z323 : W := mkw 0xb00c9554a0d9d39d 0xac032555283674e7 0x421e1c70e1f8c18c 0x1087871c387e3063

def z324 : W := mkw 0x01b603e00b603500 0x406d80f802d80d40 0x5ffc03401fc03981 0x57ff00d007f00e60

def z325 : W := mkw 0x4041600b14060862 0x10105802c5018218 0xb9e1e00f1e070073 0xae787803c781c01c

def z326 : W := mkw 0x9000041020194294 0xa4000104080650a5 0x26022cb1603fc7ff 0x09808b2c580ff1ff

def z327 : W := mkw 0xf000441230dddbdf 0xbc0011048c3776f7 0xee023cf1f1ffffff 0xfb808f3c7c7fffff

def z328 : W := mkw 0x600cd54690d5d94b 0x98033551a4357652 0xfe1fff4e91fff9cf 0xff87ffd3a47ffe73

def z329 : W := mkw 0x60fffbefd0c4994b 0x183ffefbf4312652 0x10fdc30e11c03800 0x043f70c384700e00

def z330 : W := mkw 0x00dbb80dc0000000 0x0036ee0370000000 0xf8fffc0fe0000000 0xbe3fff03f8000000

def z331 : W := mkw 0x40fffbefd6062c62 0x503ffefbf5818b18 0xf9fffffffe003800 0xfe7fffffff800e00

def z332 : W := mkw 0x90ffbbfde0080294 0x243feeff780200a5 0xfcffffffe00007fc 0xff3ffffff80001ff

def z333 : W := mkw 0x40fffbefd4060862 0x103ffefbf5018218 0xf8ffffffe0070070 0xfe3ffffff801c01c

def z334 : W := mkw 0x406563efd6062c62 0x501958fbf5818b18 0xbde1e3fffe073e73 0xef7878ffff81cf9c

def z335 : W := mkw 0x1000040020114014 0x8400010008045005 0x00001c00e000c00c 0x0000070038003003

def z336 : W := mkw 0x62dbfc021df7d94b 0x98b6ff00877df652 0xfffffc001ffff9cf 0x3fffff0007fffe73

def z337 : W := mkw 0x0041600014060002 0x0010580005018000 0x8001e00000070000 0x200078000001c000

def z338 : W := mkw 0xc16563fb164e3fe2 0x705958fec5938ff8 0xbde1e3ff1e073ff3 0xef7878ffc781cffc

def z339 : W := mkw 0x812403f002483780 0x604900fc00920de0 0x3de003f01e003f83 0x4f7800fc07800fe0

def z340 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xf8ffff0e00000000 0x3e3fffc380000000

def z341 : W := mkw 0x62ffffefddf7d94b 0x98bffffbf77df652 0xfffffffffffff9cf 0xfffffffffffffe73

def z342 : W := mkw 0x02dffd64ddb7c003 0x80b7ff59376df000 0xfbfffc70ffffc003 0x3effff1c3ffff000

def z343 : W := mkw 0x0092040009314000 0x80248100024c5000 0xfbfe3c001fffc003 0x3eff8f0007fff000

def z344 : W := mkw 0x02ffffe01db7c003 0x80bffff8076df000 0xfbfffff01fffc003 0x7efffffc07fff000

def z345 : W := mkw 0xe1fffbffdbecbfcb 0x787ffefff6fb2ff2 0xfffffffffffcffcf 0xffffffffffff3ff3

def z346 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c00030010003801 0x470000c004000e00

def z347 : W := mkw 0x02dbbc0009b1c001 0x80b6ef00026c7000 0xfafffc0001f8c000 0x3ebfff00007e3000

def z348 : W := mkw 0x83dbfc101ffff783 0xe0f6ff0407fffde0 0xfffffc001fffff83 0x3fffff0007ffffe0

def z349 : W := mkw 0x029adc0019b5c003 0x80a6b700066d7000 0xda1fdc0011fcc001 0x3687f700047f3000

def z350 : W := mkw 0x819601700b683780 0x6065805c02da0de0 0x471e00701ff83f83 0x11c7801c07fe0fe0

def z351 : W := mkw 0x40f36aab56062c62 0x503cdaaad5818b18 0xbde3efbf7e073e73 0xef78fbefdf81cf9c

def z352 : W := mkw 0x92dbfc103dbfc297 0xa4b6ff040f6ff0a5 0xfffffc001fffc7ff 0x3fffff0007fff1ff

def z353 : W := mkw 0x92d32c102d3b4294 0xa4b4cb040b4ed0a5 0xefe23cf1ee3fc7ff 0xfbf88f3c7b8ff1ff

def z354 : W := mkw 0x012403e002403500 0x404900f800900d40 0x0000030000003800 0x000000c000000e00

def z355 : W := mkw 0x81b202b00b282680 0x606c80ac02ca09a0 0x3de203b01e383e03 0x4f7880ec078e0f80

def z356 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x25e203f00e383f82 0x497880fc038e0fe0

def z357 : W := mkw 0x42fbfe8b1fb7ec63 0xd0beffa2c7edfb18 0xfbffff0e1ffff803 0x3effffc387fffe00

def z358 : W := mkw 0x91b607f02b797794 0xe46d81fc0ade5de5 0x7ffe2ff17ffb3fb3 0x5fff8bfc5ffecfec

def z359 : W := mkw 0x0008900480000000 0x0002240120000000 0x8001d00e80000000 0xa0007403a0000000

def z360 : W := mkw 0x0008d00010848003 0x0002340004212000 0xde1dd04091c4c1cd 0xf787741024713073

def z361 : W := mkw 0x002403c002403500 0x400900f000900d40 0x7ffc03c01fc03f83 0x5fff00f007f00fe0

def z362 : W := mkw 0x8000001000080280 0x20000004000200a0 0xee0210f0803cc7cf 0xfb80843c200f31f3

def z363 : W := mkw 0x9000041020194294 0xa4000104080650a5 0x00000000003b0632 0x00000000000ec18c

def z364 : W := mkw 0x0000000000401100 0x0000000000100440 0x0600000011c03981 0x0180000004700e60

def z365 : W := mkw 0x6004414210c4994b 0x1801105084312652 0x5e1c034011c4f9cd 0x578700d004713e73

def z366 : W := mkw 0x6049f00f9486886b 0x18127c03e521a21a 0x8001f00f8007c07c 0xa0007c03e001f01f

def z367 : W := mkw 0x9004055020595394 0xa4010154081654e5 0xfe1e3ff1f1ffffff 0xff878ffc7c7fffff

def z368 : W := mkw 0xd061669b361f6ef6 0xf41859a6cd87dbbd 0xbde3efbf7e3f3e73 0xef78fbefdf8fcf9c

def z369 : W := mkw 0x81b603f009681380 0x206d80fc025a04e0 0x7afe03f001f80180 0x5ebf80fc007e0060

def z370 : W := mkw 0x02dbfc0dddb7c003 0x80b6ff03776df000 0xfbfffc0fffffc003 0xbeffff03fffff000

def z371 : W := mkw 0x00dbbc0000114000 0x8036ef0000045000 0xfafffc00003fc003 0x3ebfff00000ff000

def z372 : W := mkw 0x4000400210040842 0x1000100084010210 0xde01d34e9004f9cd 0xf78074d3a4013e73

def z373 : W := mkw 0x020044001497c003 0x808011000525f000 0x000000000007c000 0x000000000001f000

def z374 : W := mkw 0x90b607f020194294 0xa42d81fc080650a5 0xfefe3ff1e03fc7ff 0xffbf8ffc780ff1ff

def z375 : W := mkw 0x0000000000000000 0x0000000000000000 0x4e00004000000181 0x5380001000000060

def z376 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xffe1f3cf9e07ffff 0xfff87cf3e781ffff

def z377 : W := mkw 0x02dbf8001da68003 0x00b6fe000769a000 0xf9fffc001fc00000 0x3e7fff0007f00000

def z378 : W := mkw 0x83f32eb00f3b6680 0xe0fccbac03ced9a0 0x21e22cb00e3b0602 0x08788b2c038ec180

def z379 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0x9de1c30e1e043841 0xe77870c387810e10

def z380 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xb8fde38f00000000 0xee3f78e3c0000000

def z381 : W := mkw 0x0000000000000000 0x0000000000000000 0x20022cb160000000 0x08008b2c58000000

def z382 : W := mkw 0x1000040020114014 0x8400010008045005 0x000000000007c07c 0x000000000001f01f

def z383 : W := mkw 0x1000040020114014 0x8400010008045005 0xe8023cf1e007c07c 0xfa008f3c7801f01f

def z384 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xc21dd04e81c4c1cc 0xb0877413a0713073

def z385 : W := mkw 0x9196057029795394 0xa465815c0a5e54e5 0xee1e3cf1e1ffc7ff 0xfb878f3c787ff1ff

def z386 : W := mkw 0x80ffbbfdc0080280 0x203feeff700200a0 0xfeffffffe0380783 0xffbffffff80e01e0

def z387 : W := mkw 0x620cd5469df7d94b 0x98833551a77df652 0xdf1dd34e9ffff9cf 0xf7c774d3a7fffe73

def z388 : W := mkw 0x60fffbefd6c6bd6b 0x583ffefbf5b1af5a 0xffffffffffc7ffff 0xfffffffffff1ffff

def z389 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xb9e1e38f1e003800 0xee7878e3c7800e00

def z390 : W := mkw 0x0041280940000000 0x00104a0250000000 0x00002c0160000000 0x00000b0058000000

def z391 : W := mkw 0x90f32eb960194294 0xa43ccbae580650a5 0xeee23cf1e03fc7ff 0xfbb88f3c780ff1ff

def z392 : W := mkw 0x90ffbffde0194294 0xa43fefff780650a5 0xf8ffffffe03b0632 0xfe3ffffff80ec18c

def z393 : W := mkw 0x000c914480000000 0x0003245120000000 0x101dc30e00000000 0x040770c380000000

def z394 : W := mkw 0xd2fbfe9b3fbfeef7 0xf4beffa6cfeffbbd 0xffffffffffffffff 0xffffffffffffffff

def z395 : W := mkw 0x83dffd701dffd383 0xa0f7ff5c077ff4e0 0xfbfffc701fffc183 0x3effff1c07fff060

def z396 : W := mkw 0xf2dffd56bdffdbdf 0xbcb7ff55af7ff6f7 0xffffffffffffffff 0xffffffffffffffff

def z397 : W := mkw 0x61bed3e69be4bd4b 0x586fb4f9a6f92f52 0xdffdd34e9fc4f9cd 0xf7ff74d3a7f13e73

def z398 : W := mkw 0x81ffbbf00b683780 0x607feefc02da0de0 0xfffffff01ff83f83 0x7ffffffc07fe0fe0

def z399 : W := mkw 0x4000400216062c62 0x5000100085818b18 0x010000001e003800 0x0040000007800e00

def z400 : W := mkw 0x819e9974c9681380 0x2067a65d325a04e0 0x421e1c70e1f80180 0x1087871c387e0060

def z401 : W := mkw 0x000c914480000000 0x0003245120000000 0xde1dd34e8004c1cd 0xf78774d3a0013073

def z402 : W := mkw 0x83fbfeb01fbfe683 0xe0feffac07eff9a0 0xfbfffcb01fffc603 0x3effff2c07fff180

def z403 : W := mkw 0xc1fffbffdf6e3fe2 0x707ffefff7db8ff8 0xffffffffffff3ff3 0xffffffffffffcffc

def z404 : W := mkw 0x929a9c1029b9c295 0xa4a6a7040a6e70a5 0x421e1c70e1f8c18c 0x1087871c387e3063

def z405 : W := mkw 0x6008d0069084884b 0x18023401a4212212 0x9c01d30e9004f84d 0xe70074c3a4013e13

def z406 : W := mkw 0x81b202b00b683780 0x606c80ac02da0de0 0x27e200b01ff83f83 0x09f8802c07fe0fe0

def z407 : W := mkw 0xd061669b361f6ef6 0xf41859a6cd87dbbd 0xbfe1e38f1e3fffff 0xeff878e3c78fffff

def z408 : W := mkw 0x0020028002002400 0x400800a000800900 0x21e000800e000602 0x0878002003800180

def z409 : W := mkw 0xd1f767fb3f7f7ff6 0xf47dd9fecfdfdffd 0xffffffffffffffff 0xffffffffffffffff

def z410 : W := mkw 0x009e9964c0000000 0x0027a65930000000 0xe81e3cf1e0000000 0xfa078f3c78000000

def z411 : W := mkw 0x029a9c0009b1c001 0x80a6a700026c7000 0xea1e3c0001ffc003 0x3a878f00007ff000

def z412 : W := mkw 0x81be93f48b683780 0x606fa4fd22da0de0 0xffffd3fe9ff83f83 0xfffff4ffa7fe0fe0

def z413 : W := mkw 0x0000000000000000 0x0000000000000000 0xca0010000004c001 0x3280040000013000

def z414 : W := mkw 0x01b603e00b603500 0x406d80f802d80d40 0x7bfe03001ff83803 0x1eff80c007fe0e00

def z415 : W := mkw 0x9000041020194294 0xa4000104080650a5 0x62023cf1e03bc7be 0x18808f3c780ef1ef

def z416 : W := mkw 0x700cd546b0d5d95f 0x9c033551ac357657 0xde1dff4ff1c7f9fd 0xf7877fd3fc71fe7f

def z417 : W := mkw 0x8000041000194280 0xa0000104000650a0 0xee023cf0003fc783 0x7b808f3c000ff1e0

def z418 : W := mkw 0x02dbbc000db3c001 0x80b6ef00036cf000 0x63fe3c000ffbc002 0x18ff8f0003fef000

def z419 : W := mkw 0x00fbbaadc0000000 0x003eeeab70000000 0xa0e3fcbfe0000000 0xa838ff2ff8000000

def z420 : W := mkw 0x6008d0069084884b 0x18023401a4212212 0x0001c00e00000000 0x0000700380000000

def z421 : W := mkw 0x600cd14696c6bd6b 0x58033451a5b1af5a 0xdf1dd34e9fc7ffff 0xf7c774d3a7f1ffff

def z422 : W := mkw 0x9000041020194294 0xa4000104080650a5 0xea023cf1e038c18c 0xfa808f3c780e3063

def z423 : W := mkw 0x4000000b00000860 0x10000002c0000218 0x0000000f00000070 0x80000003c000001c

def z424 : W := mkw 0xe12403f682483fc8 0x784900fda0920ff2 0x040003fe80003fcc 0xc10000ffa0000ff3

def z425 : W := mkw 0x82dbfc101dbfc283 0xa0b6ff04076ff0a0 0xfffffcf01fffc783 0x7fffff3c07fff1e0

def z426 : W := mkw 0x9196057029795394 0xa465815c0a5e54e5 0x421e1c70e1f8c18c 0x1087871c387e3063

def z427 : W := mkw 0x4041600b14060862 0x10105802c5018218 0xac01e08f00070673 0xeb007823c001c19c

def z428 : W := mkw 0x6049f80fd084884b 0x18127e03f4212212 0x8001fc0fe004c04c 0xa0007f03f8013013

def z429 : W := mkw 0x02d328000d220000 0x00b4ca0003488000 0x01e000000e000000 0x0078000003800000

def z430 : W := mkw 0x602cd3c692c4bd4b 0x580b34f1a4b12f52 0xfffdd3ce9fc4ffcf 0xffff74f3a7f13ff3

def z431 : W := mkw 0x9000041020194294 0xa4000104080650a5 0x84003cf1e007c7fc 0xe1000f3c7801f1ff

def z432 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xb9e1e30e1e073803 0x2e7878c38781ce00

def z433 : W := mkw 0xd061629b360e2ef6 0x741858a6cd838bbd 0xbde1e3fffe073fff 0xef7878ffff81cfff

def z434 : W := mkw 0x9000041020194294 0xa4000104080650a5 0xac022cb1603f0673 0xeb008b2c580fc19c

def z435 : W := mkw 0x0000000000000000 0x0000000000000000 0x5a1c000011c00001 0x1687000004700000

def z436 : W := mkw 0x0049f00014868003 0x00127c000521a000 0xfbfdf0001fc7c003 0x3eff7c0007f1f000

def z437 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0x25e020811e073e73 0x097808204781cf9c

def z438 : W := mkw 0x830044101ffff783 0xe0c0110407fffde0 0x070000001fffff83 0x01c0000007ffffe0

def z439 : W := mkw 0x81ffbbfdc2483780 0x607feeff70920de0 0xfcffffffe0003f80 0xff3ffffff8000fe0

def z440 : W := mkw 0x9000041020194294 0xa4000104080650a5 0xc2023c71e03fc1fc 0xb0808f1c780ff07f

def z441 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400000000070673 0x010000000001c19c

def z442 : W := mkw 0x91b607f02b797794 0xe46d81fc0ade5de5 0x7ffe03f01fffffff 0x5fff80fc07ffffff

def z443 : W := mkw 0xe1b603f68b683fc8 0x786d80fda2da0ff2 0x7ffe03fe9ff83fcf 0xdfff80ffa7fe0ff3

def z444 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8023c0000000000 0x3a008f0000000000

def z445 : W := mkw 0x00dbb80000000000 0x0036ee0000000000 0x10fdc00000000000 0x043f700000000000

def z446 : W := mkw 0x90416410341f4296 0xa41059040d07d0a5 0xffe3fcf1fe3fc7ff 0xfff8ff3c7f8ff1ff

def z447 : W := mkw 0x90612699261b66b4 0xe41849a64986d9ad 0xefe23cf1ee3fc7ff 0xfbf88f3c7b8ff1ff

def z448 : W := mkw 0x91b206b02b396694 0xe46c81ac0ace59a5 0xefe23cf1ee3fc7ff 0xfbf88f3c7b8ff1ff

def z449 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x31fe03b01ff83e02 0x0c7f80ec07fe0f80

def z450 : W := mkw 0x9000041020194294 0xa4000104080650a5 0xea023c70e03fc18f 0x3a808f1c380ff063

def z451 : W := mkw 0x02d36c001d374002 0x80b4db00074dd000 0xb9e3ec001e3f0003 0x2e78fb00078fc000

def z452 : W := mkw 0x9000041020194294 0xa4000104080650a5 0x6e021cf0e038c78f 0x5b80873c380e31e3

def z453 : W := mkw 0x40fffbefd6062c62 0x503ffefbf5818b18 0x11fdc30e1e003800 0x047f70c387800e00

def z454 : W := mkw 0x0000000000000000 0x0000000000000000 0x060000000004c1cd 0x0180000000013073

def z455 : W := mkw 0x9008d410309dc297 0xa40235040c2770a5 0xfe1ffcf1f1ffc7ff 0xff87ff3c7c7ff1ff

def z456 : W := mkw 0x81f32ab94b282680 0x607ccaae52ca09a0 0x21e22cb16e380602 0x08788b2c5b8e0180

def z457 : W := mkw 0x42fbfa8b1fa6ac63 0x50befea2c7e9ab18 0x11fdc30e1fc03800 0x047f70c387f00e00

def z458 : W := mkw 0x02412c0004134000 0x80904b000104d000 0x00002c0000030000 0x00000b000000c000

def z459 : W := mkw 0x10ffbfede0114014 0x843feffb78045005 0xf8ffffffe007c07c 0xfe3ffffff801f01f

def z460 : W := mkw 0x9000041020194294 0xa4000104080650a5 0x86003c01e03fc7ff 0xa1800f00780ff1ff

def z461 : W := mkw 0x0000000000000000 0x0000000000000000 0x39e000001e000003 0x0e78000007800000

def z462 : W := mkw 0x42dbfc021db7c843 0x90b6ff00876df210 0xffffff0e1ffff843 0xffffffc387fffe10

def z463 : W := mkw 0x6008d00690c4994b 0x18023401a4312652 0x8601d00e91c4f9cd 0xa1807403a4713e73

def z464 : W := mkw 0x9000041020194294 0xa4000104080650a5 0x6e0200f0003fc7ff 0x5b80803c000ff1ff

def z465 : W := mkw 0x000c914480000000 0x0003245120000000 0xf81fffffe0000000 0xfe07fffff8000000

def z466 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0x901dd30e91c4f84c 0xa40774c3a4713e13

def z467 : W := mkw 0x9000041020194294 0xa4000104080650a5 0xae002081003fc7ff 0xeb800820400ff1ff

def z468 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0x31e1e38f1e033e32 0x0c7878e3c780cf8c

def z469 : W := mkw 0x00dbf80010848003 0x0036fe0004212000 0xfafffc0011c4c001 0x3ebfff0004713000

def z470 : W := mkw 0x4000400210040842 0x1000100084010210 0x8001c00e00040040 0xa000700380010010

def z471 : W := mkw 0x009e9964c0000000 0x0027a65930000000 0x001c000000000000 0x0007000000000000

def z472 : W := mkw 0xc3fffffb1fffffe3 0xf0fffffec7fffff8 0xffffffff1ffffff3 0xffffffffc7fffffc

def z473 : W := mkw 0x0061228906022420 0x401848a241808908 0x3de023811e033e33 0x4f7808e04780cf8c

def z474 : W := mkw 0x912403f022483794 0x644900fc08920de5 0x040003f1e0003ffc 0xc10000fc78000fff

def z475 : W := mkw 0x9000001020080294 0x24000004080200a5 0x04000000000007fc 0x01000000000001ff

def z476 : W := mkw 0x0000000000000000 0x0000000000000000 0xa800208100000000 0xea00082040000000

def z477 : W := mkw 0x00089804c0000000 0x0002260130000000 0x00001c00e0000000 0x0000070038000000

def z478 : W := mkw 0x200c914480c09109 0x0803245120302442 0x001c000001c00000 0x0007000000700000

def z479 : W := mkw 0x600441469044194a 0x18011051a4110652 0x9c01c34e900439cd 0xe70070d3a4010e73

def z480 : W := mkw 0x00fbbaa940000000 0x003eeeaa50000000 0xf8fffcb160000000 0x3e3fff2c58000000

def z481 : W := mkw 0x812403f002483780 0x604900fc00920de0 0x6e0203f000383f83 0x5b8080fc000e0fe0

def z482 : W := mkw 0x0000000009200000 0x0000000002480000 0x030000001ff80003 0x00c0000007fe0000

def z483 : W := mkw 0x2008900480808009 0x0802240120202002 0x000010008000c00c 0x0000040020003003

def z484 : W := mkw 0x606df3cf96c6bd6b 0x581b7cf3e5b1af5a 0xdffdd34e9fc4f9cd 0xf7ff74d3a7f13e73

def z485 : W := mkw 0x00be9bedc0000000 0x002fa6fb70000000 0x401e1fffe0000000 0xd00787fff8000000

def z486 : W := mkw 0x00f72bedc0000000 0x003dcafb70000000 0x20e22fffe0000000 0xc8388bfff8000000

def z487 : W := mkw 0x4000400210040842 0x1000100084010210 0xbc01e38f10073e73 0xef0078e3c401cf9c

def z488 : W := mkw 0x0049b80000000000 0x00126e0000000000 0x8001fc0000000000 0x20007f0000000000

def z489 : W := mkw 0x6000000680000848 0x18000001a0000212 0x0000000e8000004c 0x80000003a0000013

def z490 : W := mkw 0xf0040556a0595bdc 0xbc010155a81656f7 0xee023fffe03fffff 0xfb808ffff80fffff

def z491 : W := mkw 0x60fffbefd0c4994b 0x183ffefbf4312652 0xdefdd34e91c4f9cd 0xf7bf74d3a4713e73

def z492 : W := mkw 0x81f763f01f6e3782 0x607dd8fc07db8de0 0xffffe3f01fff3f83 0x7ffff8fc07ffcfe0

def z493 : W := mkw 0x0000000000000000 0x0000000000000000 0xa800200000070003 0x2a0008000001c000

def z494 : W := mkw 0x604df14694c6994b 0x18137c51a531a652 0xfffdf34e9fc7f9cf 0xffff7cd3a7f1fe73

def z495 : W := mkw 0x62dff9469de6994b 0x18b7fe51a779a652 0x11fdc30e1fc03800 0x047f70c387f00e00

def z496 : W := mkw 0x9000001020080294 0x24000004080200a5 0x000000b160000630 0x0000002c5800018c

def z497 : W := mkw 0x83f72ff00f7b7780 0xe0fdcbfc03dedde0 0x7ffe2ff01ffb3f83 0x5fff8bfc07fecfe0

def z498 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xfe1ffffff1c4f9cd 0xff87fffffc713e73

def z499 : W := mkw 0x8196017009681380 0x2065805c025a04e0 0x7bfe00701ff80183 0x1eff801c07fe0060

def z500 : W := mkw 0x602403cf82403d68 0x580900f3e0900f5a 0x040003cf80003ffc 0xc10000f3e0000fff

def z501 : W := mkw 0x0061628016062402 0x401858a005818900 0xbde1e3801e073e03 0x6f7878e00781cf80

def z502 : W := mkw 0x1000000020000014 0x0400000008000005 0x00000001e000007c 0x800000007800001f

def z503 : W := mkw 0x004db94dc0000000 0x00136e5370000000 0xd81dff4fe0000000 0xf6077fd3f8000000

def z504 : W := mkw 0x920044103dbfc297 0xa48011040f6ff0a5 0x070000001fffc7ff 0x01c0000007fff1ff

def z505 : W := mkw 0x0061228900000000 0x001848a240000000 0xbce1e38f00070673 0xef3878e3c001c19c

def z506 : W := mkw 0x9000041020194294 0xa4000104080650a5 0xe8023cf1e03b0632 0xfa008f3c780ec18c

def z507 : W := mkw 0x0000040000114000 0x8000010000045000 0xee023c81003fc673 0xfb808f20400ff19c

def z508 : W := mkw 0x02ffffedd497c003 0x80bffffb7525f000 0xf8ffffffe007c000 0xfe3ffffff801f000

def z509 : W := mkw 0x7008d406b095c85f 0x9c023501ac257217 0x8001fc0fe007c07c 0xa0007f03f801f01f

def z510 : W := mkw 0x0249fc001497c003 0x80927f000525f000 0xea03fc00003fc003 0x3a80ff00000ff000

def z511 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000200100070070 0xa00008004001c01c

def z512 : W := mkw 0x00b603e000000000 0x002d80f800000000 0xf8fe3ff1e0000000 0xfe3f8ffc78000000

def z513 : W := mkw 0x4020028b02002c60 0x500800a2c0800b18 0x0000030e00003800 0x000000c380000e00

def z514 : W := mkw 0x4020428212042c42 0x500810a084810b10 0xbde1c38e1e043e43 0xef7870e387810f90

def z515 : W := mkw 0x00dfb964c0000000 0x0037ee5930000000 0xf8fffc70e0000000 0x3e3fff1c38000000

def z516 : W := mkw 0x009e9964c0000000 0x0027a65930000000 0xd81fdf7ee0000000 0xf607f7dfb8000000

def z517 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000208100030632 0x080008204000c18c

def z518 : W := mkw 0x6000400210c4994b 0x1800100084312652 0x9e01c30e11c4f9cd 0xe78070c384713e73

def z519 : W := mkw 0x1000040020114014 0x8400010008045005 0xce003c41e007c1fd 0xf3800f107801f07f

def z520 : W := mkw 0x002403edc0000000 0x000900fb70000000 0x0000030e00000000 0x000000c380000000

def z521 : W := mkw 0x0096016000000000 0x0025805800000000 0x401e007000000000 0x1007801c00000000

def z522 : W := mkw 0x929a9c1029b9c295 0xa4a6a7040a6e70a5 0xee1e3cf1e1ffc7ff 0xfb878f3c787ff1ff

def z523 : W := mkw 0x0000000000000000 0x0000000000000000 0xee0030c18007c7ff 0xfb800c306001f1ff

def z524 : W := mkw 0x4004414210441942 0x1001105084110650 0xde1dc34e11c439c1 0xf78770d384710e70

def z525 : W := mkw 0x4041600216062c62 0x5010580085818b18 0xbde1e0001e073e73 0x2f7878000781cf9c

def z526 : W := mkw 0x0000000002002400 0x4000000000800900 0x050000001e003e03 0x0140000007800f80

def z527 : W := mkw 0xf00cd556b0dddbdf 0xbc033555ac3776f7 0xde1fdf7ef1fcf9cd 0xf787f7dfbc7f3e73

def z528 : W := mkw 0x812403f00b683780 0x604900fc02da0de0 0x070003f01ff83f83 0x41c000fc07fe0fe0

def z529 : W := mkw 0x0000000000000000 0x0000000000000000 0xec023cf1e0070673 0xfb008f3c7801c19c

def z530 : W := mkw 0x0000400010040002 0x0000100004010000 0x9801c00010040001 0x2600700004010000

def z531 : W := mkw 0x606563cf96463d6a 0x581958f3e5918f5a 0xbde1e3cf9e073fff 0xef7878f3e781cfff

def z532 : W := mkw 0x0000040000114000 0x8000010000045000 0x80003c000007c000 0x20000f000001f000

def z533 : W := mkw 0x8196017009681380 0x2065805c025a04e0 0x5e1e037011f83981 0x578780dc047e0e60

def z534 : W := mkw 0x200c914480c09109 0x0803245120302442 0x5e1c134091c0f98d 0x578704d024703e63

def z535 : W := mkw 0xe1fff3ff9feebfeb 0x787ffcffe7fbaffa 0xfffff3ff9fffffff 0xfffffcffe7ffffff

def z536 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0x50ffdf7ee0000000 0x143ff7dfb8000000

def z537 : W := mkw 0x602cd3efd0c4994b 0x180b34fbf4312652 0xde1dd3fff1c4f9cd 0xf78774fffc713e73

def z538 : W := mkw 0x00dbb80000000000 0x0036ee0000000000 0xf8fffcf1e0000000 0xfe3fff3c78000000

def z539 : W := mkw 0x0069ba8dc0000000 0x001a6ea370000000 0xb8e1ff8fe0000000 0xee387fe3f8000000

def z540 : W := mkw 0x0020028900000000 0x000800a240000000 0x0000038f00000000 0xc00000e3c0000000

def z541 : W := mkw 0x0061228900000000 0x001848a240000000 0x20e0208100000000 0x0838082040000000

def z542 : W := mkw 0x0000000000000000 0x0000000000000000 0xee023cf1e004c1cd 0xfb808f3c78013073

def z543 : W := mkw 0x81b607f00b797780 0xe06d81fc02de5de0 0xfffe3ff01fffff83 0x7fff8ffc07ffffe0

def z544 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xa1e3fc000e3fc002 0x2878ff00038ff000

def z545 : W := mkw 0x41f763eb1f663d62 0x507dd8fac7d98f58 0xbdfde38f1fc73e73 0xef7f78e3c7f1cf9c

def z546 : W := mkw 0x402403efc2002c60 0x500900fbf0800b18 0x040003ffe0003e70 0xc10000fff8000f9c

def z547 : W := mkw 0x4049f80fd4060862 0x10127e03f5018218 0x8001fc0fe0070070 0xa0007f03f801c01c

def z548 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c00000000040041 0xe300000000010010

def z549 : W := mkw 0x0049b80dc0000000 0x00126e0370000000 0x0001c00e00000000 0x0000700380000000

def z550 : W := mkw 0x02dbf8001da68003 0x00b6fe000769a000 0xb9fde0001fc70003 0x2e7f780007f1c000

def z551 : W := mkw 0xa19e917489e89389 0x2867a45d227a24e2 0x421e107081f8c18c 0x1087841c207e3063

def z552 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xda1dd30e11c4f801 0x368774c384713e00

def z553 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c00008000000603 0x4b00002000000180

def z554 : W := mkw 0x0249fc001497c003 0x80927f000525f000 0xb9e1fc001e07c003 0x2e787f000781f000

def z555 : W := mkw 0xd0004412361f6ef6 0xf40011048d87dbbd 0x070000001e3fffff 0x01c00000078fffff

def z556 : W := mkw 0x12dbfc003db7c017 0x84b6ff000f6df005 0xfbfffc01ffffc07f 0xbeffff007ffff01f

def z557 : W := mkw 0xc061629b160e2ee2 0x701858a6c5838bb8 0xffe3e3ff1e3f3ff3 0xfff8f8ffc78fcffc

def z558 : W := mkw 0x02fbfe891db7c003 0x80beffa2476df000 0xfbffff8f1fffc003 0xfeffffe3c7fff000

def z559 : W := mkw 0x6004014680401948 0x18010051a0100652 0x0000030e00003800 0x000000c380000e00

def z560 : W := mkw 0x839e9d7009f9d381 0xa0e7a75c027e74e0 0x421e1c7001f8c180 0x1087871c007e3060

def z561 : W := mkw 0x81f72bf94b683780 0x607dcafe52da0de0 0x7ffe2ff17ff83f83 0x5fff8bfc5ffe0fe0

def z562 : W := mkw 0x00b202800b202400 0x402c80a002c80900 0x7ffe03801ff83e03 0x5fff80e007fe0f80

def z563 : W := mkw 0x90ffbffde0194294 0xa43fefff780650a5 0xfaffffffe038c18c 0xfebffffff80e3063

def z564 : W := mkw 0x8004015000481380 0x20010054001204e0 0x7e1e03f011f83f83 0x5f8780fc047e0fe0

def z565 : W := mkw 0x0092082040000000 0x0024820810000000 0x00020c3060000000 0x0000830c18000000

def z566 : W := mkw 0x83fffbf01feeb783 0x60fffefc07fbade0 0x7fffc3f01ff83f83 0x5ffff0fc07fe0fe0

def z567 : W := mkw 0x91b607f02b797794 0xe46d81fc0ade5de5 0x7ffe1ff0fff8ff8f 0x5fff87fc3ffe3fe3

def z568 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0x91e1e30f1e073870 0xa47878c3c781ce1c

def z569 : W := mkw 0x024164001db7c003 0x80905900076df000 0xbbe1e0001fffc003 0x2ef8780007fff000

def z570 : W := mkw 0x029a980009a08001 0x00a6a60002682000 0x001c000001c00000 0x0007000000700000

def z571 : W := mkw 0x02fffbeddda68003 0x00bffefb7769a000 0x11fdc30e1fc00000 0x047f70c387f00000

def z572 : W := mkw 0x00ffbfedc0114000 0x803feffb70045000 0xfaffffffe03fc003 0xfebffffff80ff000

def z573 : W := mkw 0x02fffbeddda68003 0x00bffefb7769a000 0xf9ffffffffc00000 0xfe7ffffffff00000

def z574 : W := mkw 0x00b603e000000000 0x002d80f800000000 0x10fc030000000000 0x043f00c000000000

def z575 : W := mkw 0x01b202a00b202400 0x406c80a802c80900 0x01e000000e000000 0x0078000003800000

def z576 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfffffc409fffc1cf 0xffffff1027fff073

def z577 : W := mkw 0x6004414690c4994b 0x18011051a4312652 0x0600034e91c4f9cd 0xc18000d3a4713e73

def z578 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400008100000670 0xc10000204000019c

def z579 : W := mkw 0x0000040000114000 0x8000010000045000 0x20022c00003b0002 0x08008b00000ec000

def z580 : W := mkw 0x00b603edc0000000 0x002d80fb70000000 0x78fe03ffe0000000 0xde3f80fff8000000

def z581 : W := mkw 0x0008900000000000 0x0002240000000000 0xd81dd00000000000 0x3607740000000000

def z582 : W := mkw 0x4000400210040842 0x1000100084010210 0x1001c30e10003800 0x040070c384000e00

def z583 : W := mkw 0x0041200000000000 0x0010480000000000 0xb8e1e00000000000 0x2e38780000000000

def z584 : W := mkw 0x020004000d334000 0x80800100034cd000 0x010000000e3b0002 0x00400000038ec000

def z585 : W := mkw 0x0000000000000000 0x0000000000000000 0x9801c30e00000000 0xe60070c380000000

def z586 : W := mkw 0x0000040000114000 0x8000010000045000 0xee023c40803fc1cf 0xfb808f10200ff073

def z587 : W := mkw 0x42dbfc021fb7ec63 0xd0b6ff0087edfb18 0xfffffc001ffffe73 0x3fffff0007ffff9c

def z588 : W := mkw 0x406df3cf96062c62 0x501b7cf3e5818b18 0xfdfdf3cf9e073e73 0xff7f7cf3e781cf9c

def z589 : W := mkw 0xe1b643f21becbfcb 0x786d90fc86fb2ff2 0x7ffe03f01ffcffcf 0x5fff80fc07ff3ff3

def z590 : W := mkw 0x03ffffe01ff7f503 0xc0fffff807fdfd40 0xfbffff001ffff803 0x3effffc007fffe00

def z591 : W := mkw 0x0200040009b1c001 0x80800100026c7000 0x0200000001f8c000 0x00800000007e3000

def z592 : W := mkw 0x000c914480000000 0x0003245120000000 0x401c104080000000 0x1007041020000000

def z593 : W := mkw 0x02ffbfedc9b1c001 0x80bfeffb726c7000 0xfaffffffe1f8c000 0xfebffffff87e3000

def z594 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0x8401e38f00073e70 0xe10078e3c001cf9c

def z595 : W := mkw 0x0004014480000000 0x0001005120000000 0x0000034e80000000 0xc00000d3a0000000

def z596 : W := mkw 0xc1f362bb1f2e2ee2 0x707cd8aec7cb8bb8 0xbde3e3bf1e3f3e73 0xef78f8efc78fcf9c

def z597 : W := mkw 0x600040021084884b 0x1800100084212212 0x000000000004c04c 0x0000000000013013

def z598 : W := mkw 0x9000041020194294 0xa4000104080650a5 0x46021cf1e038c7fc 0xd180873c780e31ff

def z599 : W := mkw 0x00f723e900000000 0x003dc8fa40000000 0xf8ffe3ff00000000 0xfe3ff8ffc0000000

def z600 : W := mkw 0x60dff94690c4994b 0x1837fe51a4312652 0xfeffff4e91c4f9cd 0xffbfffd3a4713e73

def z601 : W := mkw 0x010000000b603500 0x4040000002d80d40 0x010000001fc03800 0x0040000007f00e00

def z602 : W := mkw 0x0061228902002400 0x401848a240800900 0xbde1e38f1e003e03 0xef7878e3c7800f80

def z603 : W := mkw 0x900c9554a0194294 0xa4032555280650a5 0xfe1fffffe03fc7ff 0xff87fffff80ff1ff

def z604 : W := mkw 0x4249fc0b1497c863 0x90927f02c525f218 0x8001fc0f0007c070 0xa0007f03c001f01c

def z605 : W := mkw 0x02fbfe801fb7e403 0xc0beffa007edf900 0xffffff801ffffe03 0x7fffffe007ffff80

def z606 : W := mkw 0x40fbfa8b16062c62 0x503efea2c5818b18 0xfdffff8f1e073e73 0xff7fffe3c781cf9c

def z607 : W := mkw 0x600c914680401948 0x18032451a0100652 0xdc1dd34e800039cc 0xf70774d3a0000e73

def z608 : W := mkw 0x92dbfc103dbfc297 0xa4b6ff040f6ff0a5 0xfbfffc70ffffc18f 0x3effff1c3ffff063

def z609 : W := mkw 0x62dffd469df7d94b 0x98b7ff51a77df652 0xfbffff0e1ffff803 0x3effffc387fffe00

def z610 : W := mkw 0x4061228b02002c60 0x501848a2c0800b18 0xbce1e38f00003e70 0xef3878e3c0000f9c

def z611 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0x13fdc0001fffc003 0x04ff700007fff000

def z612 : W := mkw 0x020044001db7c003 0x80801100076df000 0xeb023c001fffc003 0x3ac08f0007fff000

def z613 : W := mkw 0x9000041020194294 0xa4000104080650a5 0x24022cf1e03b07fe 0xc9008b3c780ec1ff

def z614 : W := mkw 0xe00cd15690cc9bcb 0x38033455a43326f2 0xfe1fd3fe91fcffcf 0xff87f4ffa47f3ff3

def z615 : W := mkw 0x9000001020080294 0x24000004080200a5 0xec023cf1e00007fc 0xfb008f3c780001ff

def z616 : W := mkw 0x02dffd401df7d103 0x80b7ff50077df440 0xffffff401ffff983 0x7fffffd007fffe60

def z617 : W := mkw 0x9000041020194294 0xa4000104080650a5 0x6e022cf1603b07b3 0x5b808b3c580ec1ec

def z618 : W := mkw 0x9000041020194294 0xa4000104080650a5 0x46021c70e03fc7ff 0x1180871c380ff1ff

def z619 : W := mkw 0x9049bc1de0194294 0xa4126f07780650a5 0xee03fcffe03fc7ff 0xfb80ff3ff80ff1ff

def z620 : W := mkw 0x4000400216062c62 0x5000100085818b18 0x9d01c30e1e073e73 0xe74070c38781cf9c

def z621 : W := mkw 0x9249fc10349fc297 0xa4927f040d27f0a5 0xee03fcf1e03fc7ff 0xfb80ff3c780ff1ff

def z622 : W := mkw 0x4000000202002c60 0x5000000080800b18 0x0400000000003e70 0x0100000000000f9c

def z623 : W := mkw 0x81bed3f01becb783 0x606fb4fc06fb2de0 0xffffd3f01ffcff83 0x7ffff4fc07ff3fe0

def z624 : W := mkw 0x6061628b16c6bd6b 0x581858a2c5b1af5a 0xbfe1e38f1fc7ffff 0xeff878e3c7f1ffff

def z625 : W := mkw 0x02920c0009314000 0x80a48300024c5000 0x00020c0000380000 0x00008300000e0000

def z626 : W := mkw 0x83be9ff00bf9f781 0xe0efa7fc02fe7de0 0x7ffe1ff01ff8ff83 0x5fff87fc07fe3fe0

def z627 : W := mkw 0x002403edc0000000 0x000900fb70000000 0xe8023fffe0000000 0xfa008ffff8000000

def z628 : W := mkw 0x9000041020194294 0xa4000104080650a5 0xce021c70e03cc1cd 0xf380871c380f3073

def z629 : W := mkw 0x8020029002082680 0x600800a4008209a0 0x7fe203f01e383f83 0x5ff880fc078e0fe0

def z630 : W := mkw 0x0000000006022420 0x4000000001808908 0x010000000e030632 0x004000000380c18c

def z631 : W := mkw 0x4061228b06022c60 0x501848a2c1808b18 0x25e0238f0e033e72 0xc97808e3c380cf9c

def z632 : W := mkw 0x029e9d64c9b1c001 0x80a7a759326c7000 0x421e1c70e1f8c000 0x1087871c387e3000

def z633 : W := mkw 0xc1b643f21f6e3fe2 0x706d90fc87db8ff8 0x7ffe03f01fff3ff3 0x5fff80fc07ffcffc

def z634 : W := mkw 0x810000100b683780 0x6040000402da0de0 0x6f0200f01ff83f83 0x5bc0803c07fe0fe0

def z635 : W := mkw 0x4020028b02002c60 0x500800a2c0800b18 0x3de0038f1e003e73 0xcf7800e3c7800f9c

def z636 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfffffc811fffc673 0xffffff2047fff19c

def z637 : W := mkw 0x8100001009681380 0x20400004025a04e0 0x0200000001f80180 0x00800000007e0060

def z638 : W := mkw 0x80b603f000080280 0x202d80fc000200a0 0x7efe03f000380783 0x5fbf80fc000e01e0

def z639 : W := mkw 0x02f32ea94d334000 0x80bccbaa534cd000 0x21e22cb16e3b0002 0x08788b2c5b8ec000

def z640 : W := mkw 0x40f763eb16062c62 0x503dd8fac5818b18 0xfdffe3ff1e073e73 0xff7ff8ffc781cf9c

def z641 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xd81dd34e91c03800 0xf60774d3a4700e00

def z642 : W := mkw 0x8196017009681380 0x2065805c025a04e0 0x6e1e00f001f80783 0x5b87803c007e01e0

def z643 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0x60fe3cf1e0000000 0x183f8f3c78000000

def z644 : W := mkw 0x92fffffdfdbfc297 0xa4bfffff7f6ff0a5 0xffffffffffffc7ff 0xfffffffffffff1ff

def z645 : W := mkw 0x029adc001db7c003 0x80a6b700076df000 0x431e1c001fffc003 0x10c7870007fff000

def z646 : W := mkw 0x0004014000000000 0x0001005000000000 0x581c034000000000 0x560700d000000000

def z647 : W := mkw 0xd020069b22196ef4 0xf40801a6c8865bbd 0xee023fffe03fffff 0xfb808ffff80fffff

def z648 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x63fe00f00ff80782 0x18ff803c03fe01e0

def z649 : W := mkw 0xd0004412301d4ad6 0xb40011048c0752b5 0xfe03fffff03fffff 0xff80fffffc0fffff

def z650 : W := mkw 0x0000040000114000 0x8000010000045000 0xea023cf1e03fc003 0xfa808f3c780ff000

def z651 : W := mkw 0x629edd4699f5d94b 0x98a7b751a67d7652 0xde1fdf4e91fcf9cd 0xf787f7d3a47f3e73

def z652 : W := mkw 0x4041600214060842 0x1010580085018210 0xbde1e30e1e073843 0xef7878c38781ce10

def z653 : W := mkw 0x0061628916062422 0x401858a245818908 0xb9e1e0811e070633 0x2e7878204781c18c

def z654 : W := mkw 0x0000000000000000 0x0000000000000000 0x04000040800001cc 0xc100001020000073

def z655 : W := mkw 0x0061228900000000 0x001848a240000000 0x10e1c30e00000000 0x043870c380000000

def z656 : W := mkw 0x00dbf80014060002 0x0036fe0005018000 0xf9fffc001e070003 0x3e7fff000781c000

def z657 : W := mkw 0x6000400210c4994b 0x1800100084312652 0xce00104091c4f9cd 0xf380041024713e73

def z658 : W := mkw 0x0000040000114000 0x8000010000045000 0x42021c000038c000 0x10808700000e3000

def z659 : W := mkw 0x1249fc003497c017 0x84927f000d25f005 0x8001fc01e007c07c 0xa0007f007801f01f

def z660 : W := mkw 0x006db3cd80000000 0x001b6cf360000000 0xf8fdf3cf80000000 0xfe3f7cf3e0000000

def z661 : W := mkw 0x81b603f002483780 0x606d80fc00920de0 0x7cfe03f000003f80 0x5f3f80fc00000fe0

def z662 : W := mkw 0x0004014000401100 0x0001005000100440 0x421c004001c00180 0x1087001000700060

def z663 : W := mkw 0x01b603e00b603500 0x406d80f802d80d40 0x79fe03f01fc03800 0x5e7f80fc07f00e00

def z664 : W := mkw 0x4020428b12042c62 0x500810a2c4810b18 0x9c01c38f10043e71 0xe70070e3c4010f9c

def z665 : W := mkw 0x8000001000080280 0x20000004000200a0 0x200200b000380602 0x0800802c000e0180

def z666 : W := mkw 0x0061228906022420 0x401848a241808908 0xade020810e070673 0xeb7808204381c19c

def z667 : W := mkw 0x0249f80014868003 0x00927e000521a000 0x0001c00000000000 0x0000700000000000

def z668 : W := mkw 0x00f32aa940000000 0x003ccaaa50000000 0xe8e23cf1e0000000 0xfa388f3c78000000

def z669 : W := mkw 0x0020028002002400 0x400800a000800900 0xbde023811e073e73 0xef7808e04781cf9c

def z670 : W := mkw 0x602403efc0401948 0x180900fbf0100652 0x040003ffe00039cc 0xc10000fff8000e73

def z671 : W := mkw 0x0000000000000000 0x0000000000000000 0x420010408000c18c 0x1080041020003063

def z672 : W := mkw 0x4041600b14060862 0x10105802c5018218 0x0001c00e00000000 0x0000700380000000

def z673 : W := mkw 0x0196016009601100 0x0065805802580440 0x001c000001c00000 0x0007000000700000

def z674 : W := mkw 0x910004102b797794 0xe44001040ade5de5 0x070000001fffffff 0x01c0000007ffffff

def z675 : W := mkw 0x00be93e480000000 0x002fa4f920000000 0xf8ffd3fe80000000 0xfe3ff4ffa0000000

def z676 : W := mkw 0x4020428b16062c62 0x500810a2c5818b18 0x0500038f1e073e73 0xc14000e3c781cf9c

def z677 : W := mkw 0x00f32aa946022420 0x403ccaaa51808908 0x21e22cb16e030632 0x08788b2c5b80c18c

def z678 : W := mkw 0x00b603e000401100 0x002d80f800100440 0x7efe03f011c03981 0x5fbf80fc04700e60

def z679 : W := mkw 0x81ffbbfdcb683780 0x607feeff72da0de0 0x7fffc3fe1ff83f83 0x5ffff0ff87fe0fe0

def z680 : W := mkw 0xf0040156a0481bdc 0x3c010055a81206f7 0x040003ffe0003ffc 0xc10000fff8000fff

def z681 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xd8fdd34e80000000 0xf63f74d3a0000000

def z682 : W := mkw 0x0000000000000000 0x0000000000000000 0x40021c70e0000000 0x1000871c38000000

def z683 : W := mkw 0x2004014480401108 0x0801005120100442 0x000000408000018c 0x0000001020000063

def z684 : W := mkw 0x8000001000080280 0x20000004000200a0 0xee023cf1e0380783 0xfb808f3c780e01e0

def z685 : W := mkw 0xc1f763fb1f6e3fe2 0x707dd8fec7db8ff8 0x7fffc3fe1ff83f83 0x5ffff0ff87fe0fe0

def z686 : W := mkw 0x4061628b10040842 0x101858a2c4010210 0xbce1e38f10043841 0xef3878e3c4010e10

def z687 : W := mkw 0x0061228906022420 0x401848a241808908 0xb9e1e38f0e030632 0xee7878e3c380c18c

def z688 : W := mkw 0x1000040020114014 0x8400010008045005 0xac003c81e007c67f 0xeb000f207801f19f

def z689 : W := mkw 0x01b603e00b603500 0x406d80f802d80d40 0x3dfc03801fc03e03 0x4f7f00e007f00f80

def z690 : W := mkw 0x420044021fb7ec63 0xd080110087edfb18 0x070000001ffffe73 0x01c0000007ffff9c

def z691 : W := mkw 0x00f72be940000000 0x003dcafa50000000 0x78fe2ff160000000 0x5e3f8bfc58000000

def z692 : W := mkw 0x81b202b00b282680 0x606c80ac02ca09a0 0x6fe200f00e380783 0x5bf8803c038e01e0

def z693 : W := mkw 0x02dffd449db7c003 0x80b7ff51276df000 0xfbffff4e9fffc003 0xfeffffd3a7fff000

def z694 : W := mkw 0x9000001020080294 0x24000004080200a5 0x00000070e000018c 0x0000001c38000063

def z695 : W := mkw 0x620044021df7d94b 0x98801100877df652 0x070000001ffff9cf 0x01c0000007fffe73

def z696 : W := mkw 0x6069f28f9686ac6b 0x581a7ca3e5a1ab1a 0xbde1f38f9e07fe7f 0xef787ce3e781ff9f

def z697 : W := mkw 0x9000041020194294 0xa4000104080650a5 0x060000f1e03fc7ff 0xc180003c780ff1ff

def z698 : W := mkw 0x0000040000114000 0x8000010000045000 0x02000000003fc003 0x00800000000ff000

def z699 : W := mkw 0x4000400210040842 0x1000100084010210 0x0400000010043841 0x0100000004010e10

def z700 : W := mkw 0x909e9d74e0194294 0xa427a75d380650a5 0x421e1c70e038c18c 0x1087871c380e3063

def z701 : W := mkw 0x600c914680c09949 0x18032451a0302652 0x461c134e81c0f9cc 0xd18704d3a0703e73

def z702 : W := mkw 0x2000000000c09109 0x0800000000302442 0x0200000001c0c18c 0x0080000000703063

def z703 : W := mkw 0x200cd14490c4910b 0x0803345124312442 0xda1dd04091c4c18d 0x3687741024713063

def z704 : W := mkw 0x83b647f01ffff783 0xe0ed91fc07fffde0 0x7ffe03f01fffff83 0x5fff80fc07ffffe0

def z705 : W := mkw 0x920044103dbfc297 0xa48011040f6ff0a5 0xef023cf1ffffc7ff 0xfbc08f3c7ffff1ff

def z706 : W := mkw 0x6004014680401948 0x18010051a0100652 0x5e1c034e91c039cd 0xd78700d3a4700e73

def z707 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xb9e1e38f1e033e32 0xee7878e3c780cf8c

def z708 : W := mkw 0x5249fc0b3497c877 0x94927f02cd25f21d 0x8001fc0fe007c07c 0xa0007f03f801f01f

def z709 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xf8ffff7ee0000000 0x3e3fffdfb8000000

def z710 : W := mkw 0x912407f022597794 0xe44901fc08965de5 0x84003ff1e007fffc 0xe1000ffc7801ffff

def z711 : W := mkw 0x812403f002483780 0x604900fc00920de0 0x0000037000003980 0x000000dc00000e60

def z712 : W := mkw 0x81b202b00b282680 0x606c80ac02ca09a0 0x7ffe03b01ff83e03 0x5fff80ec07fe0f80

def z713 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xf9fffffffe000003 0xfe7fffffff800000

def z714 : W := mkw 0x006dbbedc0000000 0x001b6efb70000000 0xe803ffffe0000000 0xfa00fffff8000000

def z715 : W := mkw 0x20ffbbedc0808009 0x083feefb70202002 0xf8ffffffe000c00c 0xfe3ffffff8003003

def z716 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xb8ffefbf60000000 0xee3ffbefd8000000

def z717 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xfe1ffffff1c7ffff 0xff87fffffc71ffff

def z718 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xb9e1e38f1e073e33 0x2e7878e3c781cf8c

def z719 : W := mkw 0x900c9554a0194294 0xa4032555280650a5 0xde1dd34e803fc7ff 0xf78774d3a00ff1ff

def z720 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xfcffffffe0040041 0xff3ffffff8010010

def z721 : W := mkw 0x600cd946d0c4994b 0x18033651b4312652 0xde1ddf4ef1c4f9cd 0xf78777d3bc713e73

def z722 : W := mkw 0x00dbb80dc9200000 0x0036ee0372480000 0xfbfffc0ffff80003 0xbeffff03fffe0000

def z723 : W := mkw 0x004db96dc0000000 0x00136e5b70000000 0x8001fc7fe0000000 0xa0007f1ff8000000

def z724 : W := mkw 0x206db3cd86c2b529 0x481b6cf361b0ad4a 0x63fc30c18fc3c7be 0x18ff0c3063f0f1ef

def z725 : W := mkw 0xd061669b361f6ef6 0xf41859a6cd87dbbd 0x53e3df7efe38f98c 0x14f8f7dfbf8e3e63

def z726 : W := mkw 0x01ffbbedcb603500 0x407feefb72d80d40 0xffffffffffc03981 0xfffffffffff00e60

def z727 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xfffde38f1fc73e73 0xffff78e3c7f1cf9c

def z728 : W := mkw 0x00dfb94480000000 0x0037ee5120000000 0xf8ffffffe0000000 0xfe3ffffff8000000

def z729 : W := mkw 0xe1bad2b69bacaecb 0x786eb4ada6eb2bb2 0xa1e3d0be8e3cc64e 0xa878f42fa38f3193

def z730 : W := mkw 0x6000400210c4994b 0x1800100084312652 0xee023cf1f1c4f9cd 0xfb808f3c7c713e73

def z731 : W := mkw 0xc12403ffc2483fe0 0x704900fff0920ff8 0x040003ffe0003ff0 0xc10000fff8000ffc

def z732 : W := mkw 0x01ffbbedcb603500 0x407feefb72d80d40 0xfbfffffffff83803 0xfefffffffffe0e00

def z733 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0xfffe13f09ff83f83 0xffff84fc27fe0fe0

def z734 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xbde1ff8ffe073e73 0xef787fe3ff81cf9c

def z735 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0x561dd34e91c0f9cc 0xd58774d3a4703e73

def z736 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfffffc001fffc043 0xffffff0007fff010

def z737 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0xfffe33f19fffffff 0xffff8cfc67ffffff

def z738 : W := mkw 0x812403f902483780 0x604900fe40920de0 0x040003ff00003f80 0xc10000ffc0000fe0

def z739 : W := mkw 0x0092000009200000 0x0024800002480000 0x13fc00001ff80003 0x04ff000007fe0000

def z740 : W := mkw 0x0061228906022420 0x401848a241808908 0xbde1e38f1e033e33 0xef7878e3c780cf8c

def z741 : W := mkw 0x816dbbfdc2483780 0x605b6eff70920de0 0x8401ffffe0003f80 0xe1007ffff8000fe0

def z742 : W := mkw 0x42ba9e8b0bb1ec61 0xd0aea7a2c2ec7b18 0x461e1f8f01f8fe70 0xd18787e3c07e3f9c

def z743 : W := mkw 0x00ffbbedc0401100 0x003feefb70100440 0xf8fffffff1c03800 0xfe3ffffffc700e00

def z744 : W := mkw 0x4020428216062c62 0x500810a085818b18 0xbde1c38e1e073e73 0xef7870e38781cf9c

def z745 : W := mkw 0x02dbf8001da68003 0x00b6fe000769a000 0x53ffc0001ff80000 0x14fff00007fe0000

def z746 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x67fe00f01ff83f83 0x19ff803c07fe0fe0

def z747 : W := mkw 0x812403f002483780 0x604900fc00920de0 0xec023ff1e0003f80 0xfb008ffc78000fe0

def z748 : W := mkw 0xc12403f202483fc0 0x704900fc80920ff0 0x040003fe00003fc0 0xc10000ff80000ff0

def z749 : W := mkw 0x11b607e02b717514 0xc46d81f80adc5d45 0x91fc3f01ffc7f87c 0xa47f0fc07ff1fe1f

def z750 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xbde1e3cf9e073fff 0xef7878f3e781cfff

def z751 : W := mkw 0x0092000009200000 0x0024800002480000 0xfbfe3cf1fff80003 0xfeff8f3c7ffe0000

def z752 : W := mkw 0x0092000009200000 0x0024800002480000 0x63fe00000ff80002 0x18ff800003fe0000

def z753 : W := mkw 0x6249fc069497c84b 0x98927f01a525f212 0x8001fc0e0007c000 0x20007f038001f000

def z754 : W := mkw 0x81b202b00b683780 0x606c80ac02da0de0 0x7ffe00b01ff83f83 0x1fff802c07fe0fe0

def z755 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x5ffe03701ff83981 0x57ff80dc07fe0e60

def z756 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xffe1e3cf1e073ff3 0xfff878f3c781cffc

def z757 : W := mkw 0x8149b81dcb683780 0x60526e0772da0de0 0x8701fc0ffff83f83 0xa1c07f03fffe0fe0

def z758 : W := mkw 0x029a9c0009b1c001 0x80a6a700026c7000 0xfbfe3c001fffc003 0x3eff8f0007fff000

def z759 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfbfffc009fffc04f 0xbeffff0027fff013

def z760 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xf9fffc001ffb0002 0x3e7fff0007fec000

def z761 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xf8ffffbf60000000 0x3e3fffefd8000000

def z762 : W := mkw 0x836dfff016dff783 0xe0db7ffc05b7fde0 0x8401fff00007ff80 0x61007ffc0001ffe0

def z763 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x11fe03301ff83800 0x047f80cc07fe0e00

def z764 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xfe1dd3ce91c4ffcf 0xff8774f3a4713ff3

def z765 : W := mkw 0x409ed966d6062c62 0x5027b659b5818b18 0x451e1c70fe073e73 0x1147871c3f81cf9c

def z766 : W := mkw 0x62dbfc0fddb7c84b 0x98b6ff03f76df212 0xfbfffc0fffffc04f 0xbeffff03fffff013

def z767 : W := mkw 0x00fbbaadc0000000 0x003eeeab70000000 0xf8fffcbfe0000000 0xbe3fff2ff8000000

def z768 : W := mkw 0x42dbfc021db7c843 0x90b6ff00876df210 0xfbffff0e1ffff803 0x3effffc387fffe00

def z769 : W := mkw 0x00f723e900000000 0x003dc8fa40000000 0xf8ffffffe0000000 0xfe3ffffff8000000

def z770 : W := mkw 0x02d32c000d334000 0x80b4cb00034cd000 0x63fe2c000ffb0002 0x18ff8b0003fec000

def z771 : W := mkw 0x009ad40019b5c003 0x8026b500066d7000 0xfbfffc001fffc003 0x3effff0007fff000

def z772 : W := mkw 0xf00cd556b0dddbdf 0xbc033555ac3776f7 0x301fefbf71fb3e32 0x0c07fbefdc7ecf8c

def z773 : W := mkw 0x00d3280009200000 0x0034ca0002480000 0x7bfe2c001ff80003 0x1eff8b0007fe0000

def z774 : W := mkw 0x812403f002483780 0x604900fc00920de0 0x1c0003f010003f81 0x470000fc04000fe0

def z775 : W := mkw 0x00ffbbedc9200000 0x003feefb72480000 0xfaffffffe1f80000 0xfebffffff87e0000

def z776 : W := mkw 0x02920c0009314000 0x80a48300024c5000 0x7bfe0c001ff80003 0x1eff830007fe0000

def z777 : W := mkw 0x029244001db7c003 0x80a49100076df000 0xfbfe3c001fffc003 0x3eff8f0007fff000

def z778 : W := mkw 0x0096014009601100 0x0025805002580440 0x7bfe03001ff83803 0x1eff80c007fe0e00

def z779 : W := mkw 0x00ffbbedc6022420 0x403feefb71808908 0xfdffffffee070673 0xff7ffffffb81c19c

def z780 : W := mkw 0x81b603f90b683780 0x606d80fe42da0de0 0x7ffe03ff1ff83f83 0xdfff80ffc7fe0fe0

def z781 : W := mkw 0x0049b80dc0000000 0x00126e0370000000 0xc003fc7fe0000000 0xb000ff1ff8000000

def z782 : W := mkw 0xd10044123f7f7ff6 0xf44011048fdfdffd 0x070000001fffffff 0x01c0000007ffffff

def z783 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x57fe03701ff83f83 0x15ff80dc07fe0fe0

def z784 : W := mkw 0x02dbfc049db7c003 0x80b6ff01276df000 0xfbfffc0e9fffc003 0xbeffff03a7fff000

def z785 : W := mkw 0x0092000009200000 0x0024800002480000 0x7ffe03001ff83803 0x5fff80c007fe0e00

def z786 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xfe1df3cf91c4f9cd 0xff877cf3e4713e73

def z787 : W := mkw 0x01ffbbedcb202400 0x407feefb72c80900 0xf9ffffffee000000 0xfe7ffffffb800000

def z788 : W := mkw 0x12dbfc003db7c017 0x84b6ff000f6df005 0xfbfffc001fffc07f 0x3effff0007fff01f

def z789 : W := mkw 0x91b603f02b683794 0x646d80fc0ada0de5 0xfffe23f1ffff3fff 0xffff88fc7fffcfff

def z790 : W := mkw 0x42dbfc021db7c843 0x90b6ff00876df210 0xfffffc001ffff843 0x3fffff0007fffe10

def z791 : W := mkw 0xe12403ffc2483fc8 0x784900fff0920ff2 0x040003ffe0003fcc 0xc10000fff8000ff3

def z792 : W := mkw 0x812403f002483780 0x604900fc00920de0 0x6c0203f000003f80 0x5b0080fc00000fe0

def z793 : W := mkw 0x00ffbbedc2002400 0x403feefb70800900 0xfcffffffe0003e00 0xff3ffffff8000f80

def z794 : W := mkw 0x4249fc021497c863 0x90927f008525f218 0x8001fc000007c070 0x20007f000001f01c

def z795 : W := mkw 0x919e9d74e9795394 0xa467a75d3a5e54e5 0x421e1c70e1f8c18c 0x1087871c387e3063

def z796 : W := mkw 0x00ffbbedc9200000 0x003feefb72480000 0xf9ffffffffc00000 0xfe7ffffffff00000

def z797 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0x121dc30e11c0f98c 0x048770c384703e63

def z798 : W := mkw 0x02dbfc0dddb7c003 0x80b6ff03776df000 0xfbfffc0e1fffc003 0x3effff0387fff000

def z799 : W := mkw 0x812403f002483780 0x604900fc00920de0 0x0400030000003f80 0x010000c000000fe0

def z800 : W := mkw 0x4249fc021497c843 0x90927f008525f210 0x8001fc0e0007c040 0xa0007f038001f010

def z801 : W := mkw 0x00ffbbedc0401100 0x003feefb70100440 0xfaffffffe1c00180 0xfebffffff8700060

def z802 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfbfffc811fffc003 0xfeffff2047fff000

def z803 : W := mkw 0x00dbf80019a48003 0x0036fe0006692000 0xfbfffc001ffcc003 0x3effff0007ff3000

def z804 : W := mkw 0x62d72d468d735948 0x98b5cb51a35cd652 0x25e22f4e8e3b39ce 0xc9788bd3a38ece73

def z805 : W := mkw 0x609ad00699a4884b 0x1826b401a6692212 0xfbffd00e9ffcc04f 0xbefff403a7ff3013

def z806 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xfe1fd34e91fcf9cf 0xff87f4d3a47f3e73

def z807 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xfcfffffff0003801 0xff3ffffffc000e00

def z808 : W := mkw 0x00ffbbedc2403500 0x403feefb70900d40 0xffffffffffc03f83 0xfffffffffff00fe0

def z809 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xfaffffffe000c18c 0xfebffffff8003063

def z810 : W := mkw 0x0069ba8dc0000000 0x001a6ea370000000 0xf8e3ffffe0000000 0xfe38fffff8000000

def z811 : W := mkw 0x02dbbc0009b1c001 0x80b6ef00026c7000 0xfbfffc001ff8c003 0x3effff0007fe3000

def z812 : W := mkw 0x029204000d334000 0x80a48100034cd000 0x7bfe00001ffb0003 0x1eff800007fec000

def z813 : W := mkw 0x00dfb96dc0000000 0x0037ee5b70000000 0xd81fff7fe0000000 0xf607ffdff8000000

def z814 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfbfffc011fffc073 0xbeffff0047fff01c

def z815 : W := mkw 0x42dbfc021db7c843 0x90b6ff00876df210 0xffffff4e9ffff9cf 0xffffffd3a7fffe73

def z816 : W := mkw 0x812403f002483780 0x604900fc00920de0 0x040003f080003fcc 0xc10000fc20000ff3

def z817 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xfe1df34e91c7f9cf 0xff877cd3a471fe73

def z818 : W := mkw 0x02ffbbedc9a08001 0x00bfeefb72682000 0xf8ffffffe1c00000 0xfe3ffffff8700000

def z819 : W := mkw 0x029adc001db7c003 0x80a6b700076df000 0x7bfe1c001fffc003 0x1eff870007fff000

def z820 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0xfffe3ff1ffff3ff3 0xffff8ffc7fffcffc

def z821 : W := mkw 0x60f36aab50c4994b 0x183cdaaad4312652 0x26e22cb171c4f9cd 0x09b88b2c5c713e73

def z822 : W := mkw 0x02ffbbedcd220000 0x00bfeefb73488000 0xf9ffffffee000000 0xfe7ffffffb800000

def z823 : W := mkw 0x42dbfc021db7c843 0x90b6ff00876df210 0xffffff8f1ffffe73 0xffffffe3c7ffff9c

def z824 : W := mkw 0x819200100b683780 0x6064800402da0de0 0x7ffe00f01ff83f83 0x5fff803c07fe0fe0

def z825 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x79fe03f01ff83e02 0x5e7f80fc07fe0f80

def z826 : W := mkw 0x802403d002483780 0x600900f400920de0 0x7ffe03f01ff83f83 0x5fff80fc07fe0fe0

def z827 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x17fc03f01ff83f83 0x45ff00fc07fe0fe0

def z828 : W := mkw 0x00ffbbedc0401100 0x003feefb70100440 0xfcffffffe0003980 0xff3ffffff8000e60

def z829 : W := mkw 0x02dbbc000db3c001 0x80b6ef00036cf000 0x43fe1c000ff8c000 0x10ff870003fe3000

def z830 : W := mkw 0x4041600214060842 0x1010580085018210 0xbde1e38f1e073e73 0xef7878e3c781cf9c

def z831 : W := mkw 0x200c914480c09109 0x0803245120302442 0xde1dd34e91c0f98d 0xf78774d3a4703e63

def z832 : W := mkw 0x0092000009601100 0x0024800002580440 0x7ffe00001ff83983 0x1fff800007fe0e60

def z833 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xfffdd34e9fc4f9cf 0xffff74d3a7f13e73

def z834 : W := mkw 0x9000041020194294 0xa4000104080650a5 0xa4023cf1e03fc7fe 0xe9008f3c780ff1ff

def z835 : W := mkw 0x02d36c001d374002 0x80b4db00074dd000 0xfbffec001fff0003 0x3efffb0007ffc000

def z836 : W := mkw 0x62dbfc069db7c84b 0x98b6ff01a76df212 0xffffff0e9ffff84f 0xffffffc3a7fffe13

def z837 : W := mkw 0x00dbb80dc0000000 0x0036ee0370000000 0xf8fffcffe0000000 0xfe3fff3ff8000000

def z838 : W := mkw 0x92dbf8103dae8297 0x24b6fe040f6ba0a5 0x15fdc0f1ffc007fc 0xc57f703c7ff001ff

def z839 : W := mkw 0x01b603e00b603500 0x406d80f802d80d40 0x7bfe03f01ff83803 0x5eff80fc07fe0e00

def z840 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x7ffe03f09ff83fcf 0xdfff80fc27fe0ff3

def z841 : W := mkw 0x00dbb82dc0000000 0x0036ee0b70000000 0x8003fc3fe0000000 0xa000ff0ff8000000

def z842 : W := mkw 0x91f32eb96b396694 0xe47ccbae5ace59a5 0x21e22cb16e3b0632 0x08788b2c5b8ec18c

def z843 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xfaffffffe004c001 0xfebffffff8013000

def z844 : W := mkw 0x006dbbedc0000000 0x001b6efb70000000 0xd81dffffe0000000 0xf6077ffff8000000

def z845 : W := mkw 0x00d364001d374002 0x8034d900074dd000 0xfbfffc001fffc003 0x3effff0007fff000

def z846 : W := mkw 0x81b603f94b683780 0x606d80fe52da0de0 0x7ffe03f17ff83f83 0x5fff80fc5ffe0fe0

def z847 : W := mkw 0x0092040009314000 0x80248100024c5000 0x7bfe00001fffc003 0x1eff800007fff000

def z848 : W := mkw 0x812403f002483780 0x604900fc00920de0 0x040003f100003ff0 0xc10000fc40000ffc

def z849 : W := mkw 0x00b603e00b202400 0x402d80f802c80900 0x7ffe03f01ff83e03 0x5fff80fc07fe0f80

def z850 : W := mkw 0x00ffbbedc9601100 0x003feefb72580440 0xfffffffffff83983 0xfffffffffffe0e60

def z851 : W := mkw 0x00be9bedc0000000 0x002fa6fb70000000 0xd81fdfffe0000000 0xf607f7fff8000000

def z852 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xffe1f38f1e07fe73 0xfff87ce3c781ff9c

def z853 : W := mkw 0x02dbbc000db3c001 0x80b6ef00036cf000 0x21fe2c000ffb0002 0x087f8b0003fec000

def z854 : W := mkw 0x9000041020194294 0xa4000104080650a5 0xfe023ff1f03fffff 0xff808ffc7c0fffff

def z855 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x37fe03b01ff83f83 0x0dff80ec07fe0fe0

def z856 : W := mkw 0x009a900009a08001 0x0026a40002682000 0x7bfe10001ff8c003 0x1eff840007fe3000

def z857 : W := mkw 0x00ffbbedc4020020 0x003feefb71008008 0xf8ffffffe0030030 0xfe3ffffff800c00c

def z858 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xfeffffffe0000181 0xffbffffff8000060

def z859 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xda1dd34e91c0f98c 0xf68774d3a4703e63

def z860 : W := mkw 0x0092400019a48003 0x0024900006692000 0x7bfe00001ffcc003 0x1eff800007ff3000

def z861 : W := mkw 0x812403f002483780 0x604900fc00920de0 0x000003b000003e00 0x000000ec00000f80

def z862 : W := mkw 0x62dbfc069db7c84b 0x98b6ff01a76df212 0xfffffc4e9fffc1cf 0xffffff13a7fff073

def z863 : W := mkw 0x0069baadc0000000 0x001a6eab70000000 0x8001fcbfe0000000 0xa0007f2ff8000000

def z864 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xfaffffffe0380003 0xfebffffff80e0000

def z865 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x13fc03001ff83980 0x04ff00c007fe0e60

def z866 : W := mkw 0x029244001db7c003 0x80a49100076df000 0x13fc00001fffc003 0x04ff000007fff000

def z867 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xdbffdc001ffcc001 0x36fff70007ff3000

def z868 : W := mkw 0x022447edddb7c003 0x808911fb776df000 0x030003ffffffc003 0xc0c000fffffff000

def z869 : W := mkw 0x42dbfc0b1db7c863 0x90b6ff02c76df218 0xffffff0f1ffff873 0xffffffc3c7fffe1c

def z870 : W := mkw 0x40d3600b1d260862 0x1034d802c7498218 0xfbffe00f1fff0073 0xbefff803c7ffc01c

def z871 : W := mkw 0xc12403fb02483fe0 0x704900fec0920ff8 0x040003fe00003f80 0x410000ff80000fe0

def z872 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0x10ffcf3e60000000 0x043ff3cf98000000

def z873 : W := mkw 0x02dbf8001da68003 0x00b6fe000769a000 0x31ffc0001ff80002 0x0c7ff00007fe0000

def z874 : W := mkw 0x81b60bf04b683780 0x606d82fc12da0de0 0x7ffe0ff07ff83f83 0x5fff83fc1ffe0fe0

def z875 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xfcffffffe0000603 0xff3ffffff8000180

def z876 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x57fe03f01ff83f80 0x55ff80fc07fe0fe0

def z877 : W := mkw 0xf000441236dfffff 0xfc0011048db7ffff 0x070000001fffffff 0x01c0000007ffffff

def z878 : W := mkw 0xd20044123fbfeef7 0xf48011048feffbbd 0x070000001fffffff 0x01c0000007ffffff

def z879 : W := mkw 0x0092000009200000 0x0024800002480000 0xfffe20811fff0673 0xffff882047ffc19c

def z880 : W := mkw 0x02dbfc0dddb7c003 0x80b6ff03776df000 0xfbfffcffffffc003 0xfeffff3ffffff000

def z881 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xbde1e3fffe073e73 0xef7878ffff81cf9c

def z882 : W := mkw 0x019200000b603500 0x4064800002d80d40 0x7bfe00001ff83803 0x1eff800007fe0e00

def z883 : W := mkw 0xf10044123bfdffdf 0xfc4011048eff7ff7 0x070000001fffffff 0x01c0000007ffffff

def z884 : W := mkw 0x029a9c0009b1c001 0x80a6a700026c7000 0x63fe1c000ff8c002 0x18ff870003fe3000

def z885 : W := mkw 0x00ffbbedcb202400 0x403feefb72c80900 0xfffffffffff83e03 0xfffffffffffe0f80

def z886 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xb9ffec001fff0003 0x2e7ffb0007ffc000

def z887 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xd0ffff7fe0000000 0xb43fffdff8000000

def z888 : W := mkw 0x819601700b683780 0x6065805c02da0de0 0x7ffe00701ff83f83 0x1fff801c07fe0fe0

def z889 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfffffc001fffc1cf 0x3fffff0007fff073

def z890 : W := mkw 0x00ffbbedc4020000 0x003feefb71008000 0xf9ffffffee030002 0xfe7ffffffb80c000

def z891 : W := mkw 0x91b603f02b683794 0x646d80fc0ada0de5 0x7ffe03f01ff83fff 0x5fff80fc07fe0fff

def z892 : W := mkw 0x0092040009314000 0x80248100024c5000 0x7bfe2c001ffb0003 0x1eff8b0007fec000

def z893 : W := mkw 0x4249fc0fd497c863 0x90927f03f525f218 0x8001fc0fe007c070 0xa0007f03f801f01c

def z894 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xa5e1e38f0e073e72 0xe97878e3c381cf9c

def z895 : W := mkw 0x00dfb96dc0000000 0x0037ee5b70000000 0xe81ffcffe0000000 0xfa07ff3ff8000000

def z896 : W := mkw 0x00dfb96dc0000000 0x0037ee5b70000000 0x401fdc7ee0000000 0x1007f71fb8000000

def z897 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xffe3e38f1e3f3e73 0xfff8f8e3c78fcf9c

def z898 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0x7bffec001ffb0003 0x1efffb0007fec000

def z899 : W := mkw 0x62dbfc069db7c84b 0x98b6ff01a76df212 0xfbfffc0e1fffc003 0x3effff0387fff000

def z900 : W := mkw 0x0092000009200000 0x0024800002480000 0xfbfe20001fff0003 0x3eff880007ffc000

def z901 : W := mkw 0x0092000009200000 0x0024800002480000 0x53fe00001ff80000 0x14ff800007fe0000

def z902 : W := mkw 0x00f32aa940000000 0x003ccaaa50000000 0xf8e3ffffe0000000 0xfe38fffff8000000

def z903 : W := mkw 0x0092000009200000 0x0024800002480000 0x7bfe00f01ff80003 0x5eff803c07fe0000

def z904 : W := mkw 0x01ffbbedc2403500 0x407feefb70900d40 0xf8ffffffe0003800 0xfe3ffffff8000e00

def z905 : W := mkw 0x812403f002483780 0x604900fc00920de0 0x4e0003f000003f81 0x538000fc00000fe0

def z906 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfbfffc409fffc003 0xfeffff1027fff000

def z907 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xf8ffffffe0070003 0xfe3ffffff801c000

def z908 : W := mkw 0x01b603e00b603500 0x406d80f802d80d40 0x7ffe03801ff83e03 0x5fff80e007fe0f80

def z909 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x7ffe03f11ff83ff3 0xdfff80fc47fe0ffc

def z910 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0x78ffdffee0000000 0x5e3ff7ffb8000000

def z911 : W := mkw 0x02dbf8001da68003 0x00b6fe000769a000 0xfbfffc001ff80003 0x3effff0007fe0000

def z912 : W := mkw 0x0092000009200000 0x0024800002480000 0xfbfe3c001ff80003 0x3eff8f0007fe0000

def z913 : W := mkw 0x91b603f02b683794 0x646d80fc0ada0de5 0x7ffe03f0fff83f8f 0x5fff80fc3ffe0fe3

def z914 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xde1fdf7ef1c4f9cd 0xf787f7dfbc713e73

def z915 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xd21dd34e91c4f9cc 0xb48774d3a4713e73

def z916 : W := mkw 0x4249fc0b1497c863 0x90927f02c525f218 0x8001fc0e0007c000 0x20007f038001f000

def z917 : W := mkw 0x12dbfc0dfdb7c017 0x84b6ff037f6df005 0xfbfffc0fffffc07f 0xbeffff03fffff01f

def z918 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xe3fffc000fffc002 0x38ffff0003fff000

def z919 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xfde1f3cf9e073e73 0xff787cf3e781cf9c

def z920 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfbfffcb17fffc003 0x3effff2c5ffff000

def z921 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0x95e1e30f1e073e73 0xa57878c3c781cf9c

def z922 : W := mkw 0x00ffbbedc9200000 0x003feefb72480000 0xf9ffffffee380002 0xfe7ffffffb8e0000

def z923 : W := mkw 0x0000000000000000 0x0000000000000000 0xf803ffffe0000000 0xfe00fffff8000000

def z924 : W := mkw 0x00f72be940000000 0x003dcafa50000000 0xf8ffefff60000000 0xfe3ffbffd8000000

def z925 : W := mkw 0x00ffbbedc2002400 0x403feefb70800900 0xf9fffffffe003800 0xfe7fffffff800e00

def z926 : W := mkw 0x029adc0019b5c003 0x80a6b700066d7000 0xfbffdc001ffcc003 0x3efff70007ff3000

def z927 : W := mkw 0x22dbfc049db7c00b 0x88b6ff01276df002 0xfbfffc009fffc00f 0x3effff0027fff003

def z928 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0xfffe3ff01ff83f83 0x7fff8ffc07fe0fe0

def z929 : W := mkw 0x02dbfc091db7c023 0x80b6ff02476df008 0xfbfffc011fffc033 0x3effff0047fff00c

def z930 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0x63fe3c001fffc003 0x18ff8f0007fff000

def z931 : W := mkw 0x4004414210441942 0x1001105084110650 0xde1dd34e91c4f9cd 0xf78774d3a4713e73

def z932 : W := mkw 0x812403f002483780 0x604900fc00920de0 0x2c0003f000003f83 0x4b0000fc00000fe0

def z933 : W := mkw 0x600c914680c09949 0x18032451a0302652 0xde1dd34e81c0f9cc 0xf78774d3a0703e73

def z934 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xffe3fffffe07ffff 0xfff8ffffff81ffff

def z935 : W := mkw 0x9000041020194294 0xa4000104080650a5 0xfe1e3cf1f1ffc7ff 0xff878f3c7c7ff1ff

def z936 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0x15e1c38f1e073e73 0xc57870e3c781cf9c

def z937 : W := mkw 0x4008d00210848843 0x1002340084212210 0xde1dd34e91c4f9cd 0xf78774d3a4713e73

def z938 : W := mkw 0x002c93edc0000000 0x000b24fb70000000 0xf81fffffe0000000 0xfe07fffff8000000

def z939 : W := mkw 0x02d32c000d334000 0x80b4cb00034cd000 0x31fe2c001ffb0002 0x0c7f8b0007fec000

def z940 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0x5e1dd34e91c0f98d 0x578774d3a4703e63

def z941 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x7ffe13f09ff8ff8f 0x5fff84fc27fe3fe3

def z942 : W := mkw 0x0092000009200000 0x0024800002480000 0x31fe00001ff80002 0x0c7f800007fe0000

def z943 : W := mkw 0xf000441230dddbdf 0xbc0011048c3776f7 0x0600000011fcf9cd 0x01800000047f3e73

def z944 : W := mkw 0x00f32aa940000000 0x003ccaaa50000000 0xa0e3ecbf60000000 0xa838fb2fd8000000

def z945 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0x11fdc0001ffb0002 0x047f700007fec000

def z946 : W := mkw 0x029ad4001db7c003 0x80a6b500076df000 0xfbffd0001fffc003 0x3efff40007fff000

def z947 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0x35e1e38f1e033e72 0xcd7878e3c780cf9c

def z948 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x7ffe23f11ffb3fb3 0x5fff88fc47fecfec

def z949 : W := mkw 0x02dbf8001da68003 0x00b6fe000769a000 0x13fdc0001ff80003 0x04ff700007fe0000

def z950 : W := mkw 0x01b603e00b603500 0x406d80f802d80d40 0x53fe03001ff83800 0x14ff80c007fe0e00

def z951 : W := mkw 0x00ffbbedc2002420 0x403feefb70800908 0xf8ffffffe0000630 0xfe3ffffff800018c

def z952 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfbfffc001ff8c000 0x3effff0007fe3000

def z953 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0x35e1e38f1e073e73 0x0d7878e3c781cf9c

def z954 : W := mkw 0x0049b80dc0000000 0x00126e0370000000 0x8001fcffe0000000 0xe0007f3ff8000000

def z955 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x35fe03f01ff83f82 0x4d7f80fc07fe0fe0

def z956 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0x941dd34e91c4f9cc 0xe50774d3a4713e73

def z957 : W := mkw 0x90ffbffde0194294 0xa43fefff780650a5 0x16fdc30e003fc7ff 0x05bf70c3800ff1ff

def z958 : W := mkw 0xd0004412301d4ad6 0xb40011048c0752b5 0x06000000103fffff 0x01800000040fffff

def z959 : W := mkw 0x81b603fdcb683780 0x606d80ff72da0de0 0xfffe3ffffff83f83 0xffff8ffffffe0fe0

def z960 : W := mkw 0xa1b603f48b683788 0x686d80fd22da0de2 0x7ffe03f09ff83f8f 0x5fff80fc27fe0fe3

def z961 : W := mkw 0x12dbfc003db7c017 0x84b6ff000f6df005 0xfbfffcf1ffffc07f 0xfeffff3c7ffff01f

def z962 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xe0fffcffe0000000 0xb83fff3ff8000000

def z963 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xd3fffc001fffc000 0x34ffff0007fff000

def z964 : W := mkw 0x12dbfc003db7c017 0x84b6ff000f6df005 0xfbfffc00ffffc00f 0x3effff003ffff003

def z965 : W := mkw 0x00dfb96dc0000000 0x0037ee5b70000000 0xf8fffc7fe0000000 0xbe3fff1ff8000000

def z966 : W := mkw 0x91b603f02b683794 0x646d80fc0ada0de5 0x7ffe03f17ff83fb3 0x5fff80fc5ffe0fec

def z967 : W := mkw 0xc16563fb164e3fe2 0x705958fec5938ff8 0x8401e3ff00073ff0 0xe10078ffc001cffc

def z968 : W := mkw 0xe12403ff82483fe8 0x784900ffe0920ffa 0x040003ff80003ffc 0xc10000ffe0000fff

def z969 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0xfffe23f11ff83f83 0xffff88fc47fe0fe0

def z970 : W := mkw 0x91b603fdeb683794 0x646d80ff7ada0de5 0x7ffe03fffff83fff 0xdfff80fffffe0fff

def z971 : W := mkw 0x812403f9024837a0 0x604900fe40920de8 0x040003f100003fb0 0x410000fc40000fec

def z972 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0x7bffdc001ff8c003 0x1efff70007fe3000

def z973 : W := mkw 0x6249fc021497c84b 0x98927f008525f212 0x8001fc000007c04c 0x20007f000001f013

def z974 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfbfffc01ffffc003 0xbeffff007ffff000

def z975 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfbfffcf01fffc003 0x7effff3c07fff000

def z976 : W := mkw 0x80b202900b282680 0x602c80a402ca09a0 0x7ffe03f01ff83f83 0x5fff80fc07fe0fe0

def z977 : W := mkw 0x62dbfc0f9db7c86b 0x98b6ff03e76df21a 0xfbfffc0f9fffc07f 0xbeffff03e7fff01f

def z978 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfbfffc811fffc633 0x3effff2047fff18c

def z979 : W := mkw 0x00ffbbedc6022420 0x403feefb71808908 0xfdfffffffe033e33 0xff7fffffff80cf8c

def z980 : W := mkw 0x406162ab56062c62 0x501858aad5818b18 0xbde1e3bf7e073e73 0xef7878efdf81cf9c

def z981 : W := mkw 0x00d3200009200000 0x0034c80002480000 0xfbffe0001ff80003 0x3efff80007fe0000

def z982 : W := mkw 0x9000041020194294 0xa4000104080650a5 0xc6023cf1e03fc7fc 0xf1808f3c780ff1ff

def z983 : W := mkw 0x9000041020194294 0xa4000104080650a5 0xfe03ffffe03fc7ff 0xff80fffff80ff1ff

def z984 : W := mkw 0x0061228902002400 0x401848a240800900 0xbde1e38f1e073e73 0xef7878e3c781cf9c

def z985 : W := mkw 0x00ffbbedc2002400 0x403feefb70800900 0xf9ffffffee000602 0xfe7ffffffb800180

def z986 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0x13fdc0001ff8c000 0x04ff700007fe3000

def z987 : W := mkw 0x02dbfc095db7c003 0x80b6ff02576df000 0xfbfffc017fffc003 0x3effff005ffff000

def z988 : W := mkw 0xc1d7617b1d6e1be2 0x3075d85ec75b86f8 0xc21fe07f01ff01f0 0xb087f81fc07fc07c

def z989 : W := mkw 0x4020428212042c42 0x500810a084810b10 0xbde1e38f1e073e73 0xef7878e3c781cf9c

def z990 : W := mkw 0x000c914480401100 0x0003245120100440 0xde1dd34e91c4f9cd 0xf78774d3a4713e73

def z991 : W := mkw 0x81b603f48b683780 0x606d80fd22da0de0 0x7ffe03fe9ff83f83 0xdfff80ffa7fe0fe0

def z992 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x7ffe1ff0fff83f83 0x5fff87fc3ffe0fe0

def z993 : W := mkw 0x9000041020194294 0xa4000104080650a5 0x66023cf1e03fc7ff 0x19808f3c780ff1ff

def z994 : W := mkw 0x42dbfc021db7c863 0x90b6ff00876df218 0xfbfffc001fffc073 0x3effff0007fff01c

def z995 : W := mkw 0x00b603c00b603500 0x402d80f002d80d40 0x7ffe03c01ff83f83 0x5fff80f007fe0fe0

def z996 : W := mkw 0x00dfb964c0000000 0x0037ee5930000000 0xf8ffff7ee0000000 0xfe3fffdfb8000000

def z997 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xfafffffff1c00001 0xfebffffffc700000

def z998 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfbffff0e1fffc003 0xfeffffc387fff000

def z999 : W := mkw 0x01b603e00b603500 0x406d80f802d80d40 0x7ffe03401ff83983 0x5fff80d007fe0e60

def z1000 : W := mkw 0x12dbfc003db7c017 0x84b6ff000f6df005 0xfbfffc017fffc033 0x3effff005ffff00c

def z1001 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0xffffc3fe1ff83f83 0xfffff0ff87fe0fe0

def z1002 : W := mkw 0x02dbbc000d334000 0x80b6ef00034cd000 0xfbfffc001ffb0003 0x3effff0007fec000

def z1003 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xde1dd3fff1c4f9cd 0xf78774fffc713e73

def z1004 : W := mkw 0x006dbbedc0000000 0x001b6efb70000000 0xb8e1ffffe0000000 0xee387ffff8000000

def z1005 : W := mkw 0x009a980009200000 0x0026a60002480000 0x7bfe1c001ff80003 0x1eff870007fe0000

def z1006 : W := mkw 0x812403f002483780 0x604900fc00920de0 0x000000f000000780 0x0000003c000001e0

def z1007 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x7ffe03f01fff3ff3 0x5fff80fc07ffcffc

def z1008 : W := mkw 0x6249fc0f9497c86b 0x98927f03e525f21a 0x8001fc0f8007c07c 0xa0007f03e001f01f

def z1009 : W := mkw 0x819200100b683780 0x6064800402da0de0 0x17fc00001ff83f83 0x05ff000007fe0fe0

def z1010 : W := mkw 0x009e9964c0000000 0x0027a65930000000 0xc01fdc7ee0000000 0xb007f71fb8000000

def z1011 : W := mkw 0x91b603f02b683794 0x646d80fc0ada0de5 0xfffe3ff1fff83fff 0xffff8ffc7ffe0fff

def z1012 : W := mkw 0x00dbf0001da68003 0x0036fc000769a000 0xfbfff0001fffc003 0x3efffc0007fff000

def z1013 : W := mkw 0x0049f4001497c003 0x80127d000525f000 0xfbfffc001fffc003 0x3effff0007fff000

def z1014 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0x3de1e38f1e033e33 0x4f7878e3c780cf8c

def z1015 : W := mkw 0x812403f002483780 0x604900fc00920de0 0x040003f1e0003f80 0xc10000fc78000fe0

def z1016 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfffffc401fffc183 0x7fffff1007fff060

def z1017 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0x90fdffffe0000000 0xe43f7ffff8000000

def z1018 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xfde3ff8f1e073e73 0xff78ffe3c781cf9c

def z1019 : W := mkw 0x02d36c001db7c003 0x80b4db00076df000 0x7bfe2c001fffc003 0x1eff8b0007fff000

def z1020 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0xfffe3ff1fffcffcf 0xffff8ffc7fff3ff3

def z1021 : W := mkw 0x00ffbbedc0808001 0x003feefb70202000 0xfaffffffe1c0c000 0xfebffffff8703000

def z1022 : W := mkw 0x91b603f02b683794 0x646d80fc0ada0de5 0xfffe13f1fffcffff 0xffff84fc7fff3fff

def z1023 : W := mkw 0x00fbbaadc0000000 0x003eeeab70000000 0xe8e3fcffe0000000 0xfa38ff3ff8000000

def z1024 : W := mkw 0x00ffbbedc0401100 0x003feefb70100440 0xfefffffff1c4f9cd 0xffbffffffc713e73

def z1025 : W := mkw 0x00b603e009601100 0x002d80f802580440 0x7ffe03f01ff83983 0x5fff80fc07fe0e60

def z1026 : W := mkw 0x812403f4c2483780 0x604900fd30920de0 0x040003f0e0003f80 0x410000fc38000fe0

def z1027 : W := mkw 0x006523edc0000000 0x001948fb70000000 0xf8e3ffffe0000000 0xfe38fffff8000000

def z1028 : W := mkw 0x00be9be4c0000000 0x002fa6f930000000 0xf8ffdffee0000000 0xfe3ff7ffb8000000

def z1029 : W := mkw 0x20ffbbedc0c09109 0x083feefb70302442 0xfefffffff1c0f98d 0xffbffffffc703e63

def z1030 : W := mkw 0x600cd166d0c4994b 0x18033459b4312652 0xde1dd37ef1c4f9cd 0xf78774dfbc713e73

def z1031 : W := mkw 0xf20044123dffdbdf 0xbc8011048f7ff6f7 0x070000001fffffff 0x01c0000007ffffff

def z1032 : W := mkw 0x9061269920194294 0xa41849a6480650a5 0xbee1e38f003fc7ff 0xefb878e3c00ff1ff

def z1033 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xfcffffffe0000670 0xff3ffffff800019c

def z1034 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0xfffe03f01ffc3fc3 0xffff80fc07ff0ff0

def z1035 : W := mkw 0x0061228900000000 0x001848a240000000 0xb8e3efbf60000000 0xee38fbefd8000000

def z1036 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0x9de1c30e1e073e73 0xe77870c38781cf9c

def z1037 : W := mkw 0x02dbbc000db3c001 0x80b6ef00036cf000 0xebfe3c000fffc003 0x3aff8f0003fff000

def z1038 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfbfffc409fffc18f 0x3effff1027fff063

def z1039 : W := mkw 0x81b603f4cb683780 0x606d80fd32da0de0 0x7ffe03f0fff83f83 0x5fff80fc3ffe0fe0

def z1040 : W := mkw 0x0092000009200000 0x0024800002480000 0xfbfe10001ffcc003 0x3eff840007ff3000

def z1041 : W := mkw 0x9000041020194294 0xa4000104080650a5 0xffe23cf1fe3fc7ff 0xfff88f3c7f8ff1ff

def z1042 : W := mkw 0x12dbfc003db7c017 0x84b6ff000f6df005 0xfffffc81ffffc67f 0xffffff207ffff19f

def z1043 : W := mkw 0x0008900480000000 0x0002240120000000 0xe803fcffe0000000 0xfa00ff3ff8000000

def z1044 : W := mkw 0x004db94dc0000000 0x00136e5370000000 0xf81fffffe0000000 0xfe07fffff8000000

def z1045 : W := mkw 0x00f72bedc0000000 0x003dcafb70000000 0xb8e3efffe0000000 0xee38fbfff8000000

def z1046 : W := mkw 0x20ffbbedc0c09109 0x083feefb70302442 0xfeffffffe1c4c1cd 0xffbffffff8713073

def z1047 : W := mkw 0x4041600216062c62 0x5010580085818b18 0xbde1e30e1e073e73 0xef7878c38781cf9c

def z1048 : W := mkw 0xd12403fb22483ff4 0x744900fec8920ffd 0x040003ffe0003ffc 0xc10000fff8000fff

def z1049 : W := mkw 0x01b603e00b603500 0x406d80f802d80d40 0x31fe03001ff83802 0x0c7f80c007fe0e00

def z1050 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfffffcf1ffffc1cf 0xffffff3c7ffff073

def z1051 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xbde1e30e1e073e73 0x2f7878c38781cf9c

def z1052 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0x50ffdfffe0000000 0xd43ff7fff8000000

def z1053 : W := mkw 0x00f32aa940000000 0x003ccaaa50000000 0x30e3efbf60000000 0x0c38fbefd8000000

def z1054 : W := mkw 0x62dbfc021db7c84b 0x98b6ff00876df212 0xfbfffc001fffc04f 0x3effff0007fff013

def z1055 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x73fe03f01ff83f82 0x1cff80fc07fe0fe0

def z1056 : W := mkw 0x006db3cd80000000 0x001b6cf360000000 0xf8ffffffe0000000 0xfe3ffffff8000000

def z1057 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfffffc801fffc603 0x7fffff2007fff180

def z1058 : W := mkw 0x029a9c0009b1c001 0x80a6a700026c7000 0x53fe1c001ff8c000 0x14ff870007fe3000

def z1059 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfffffc001fffc673 0x3fffff0007fff19c

def z1060 : W := mkw 0xe12cd3f692ccbfcb 0x784b34fda4b32ff2 0x8401d3fe8004ffcc 0xe10074ffa0013ff3

def z1061 : W := mkw 0x02d328000d220000 0x00b4ca0003488000 0x7bfe00001ff80003 0x1eff800007fe0000

def z1062 : W := mkw 0x00fbba8900000000 0x003eeea240000000 0xf8ffffffe0000000 0xfe3ffffff8000000

def z1063 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0x11e1c30e1e033e32 0x047870c38780cf8c

def z1064 : W := mkw 0x0049b80dc0000000 0x00126e0370000000 0xa003fcbfe0000000 0xa800ff2ff8000000

def z1065 : W := mkw 0x4061628b1686ac63 0x501858a2c5a1ab18 0xbfe1e38f1fc7fe73 0xeff878e3c7f1ff9c

def z1066 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0x3de1c38e1e073e73 0x4f7870e38781cf9c

def z1067 : W := mkw 0x812403f002483780 0x604900fc00920de0 0xac0023f100073ff3 0xeb0008fc4001cffc

def z1068 : W := mkw 0x20ffbbedc0c09109 0x083feefb70302442 0xf8ffffffe1c00000 0xfe3ffffff8700000

def z1069 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xf8ffffffe0070070 0xfe3ffffff801c01c

def z1070 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xb1fffc001fffc002 0x2c7fff0007fff000

def z1071 : W := mkw 0x40616a8b56062c62 0x50185aa2d5818b18 0xbde1ef8f7e073e73 0xef787be3df81cf9c

def z1072 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0xfffe23f01fff3f83 0x7fff88fc07ffcfe0

def z1073 : W := mkw 0x20ffbbedc0401108 0x083feefb70100442 0xf8ffffffe000018c 0xfe3ffffff8000063

def z1074 : W := mkw 0x812403fdc2483780 0x604900ff70920de0 0x040003fe00003f80 0x410000ff80000fe0

def z1075 : W := mkw 0xa12403f482483788 0x684900fd20920de2 0x040003f080003f8c 0x410000fc20000fe3

def z1076 : W := mkw 0x029a980009a08001 0x00a6a60002682000 0x7bfe00001ff80003 0x1eff800007fe0000

def z1077 : W := mkw 0x4000400216062c62 0x5000100085818b18 0xed023cf1fe073e73 0xfb408f3c7f81cf9c

def z1078 : W := mkw 0x009a900009200000 0x0026a40002480000 0xfbffd0001ff80003 0x3efff40007fe0000

def z1079 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xde1dff4ff1c4f9cd 0xf7877fd3fc713e73

def z1080 : W := mkw 0x00dbb80009200000 0x0036ee0002480000 0x7bffc0001ff80003 0x1efff00007fe0000

def z1081 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xc61dd34e81c4f9cc 0xf18774d3a0713e73

def z1082 : W := mkw 0x0092400019240002 0x0024900006490000 0xfbffc0001ffc0003 0x3efff00007ff0000

def z1083 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0x70ffffffe0000000 0x1c3ffffff8000000

def z1084 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0x73fffc001ffbc002 0x1cffff0007fef000

def z1085 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xde1df34f91c7f9fd 0xf7877cd3e471fe7f

def z1086 : W := mkw 0x912403f022483794 0x644900fc08920de5 0x040003f160003fb0 0x410000fc58000fec

def z1087 : W := mkw 0x6004414210c4994b 0x1801105084312652 0xde1dc34e11c4f9cd 0xf78770d384713e73

def z1088 : W := mkw 0x0092000009200000 0x0024800002480000 0x7ffe00801ff80603 0x5fff802007fe0180

def z1089 : W := mkw 0x4061228b06022c60 0x501848a2c1808b18 0xbde1e38f0e033e72 0xef7878e3c380cf9c

def z1090 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x7ffe03f01ffcffcf 0x5fff80fc07ff3ff3

def z1091 : W := mkw 0x029240001da68003 0x00a490000769a000 0x7bfe00001ff80003 0x1eff800007fe0000

def z1092 : W := mkw 0x42dbfc0fddb7c863 0x90b6ff03f76df218 0xfbfffc0fffffc073 0xbeffff03fffff01c

def z1093 : W := mkw 0x912403fde2483794 0x644900ff78920de5 0x040003ffe0003ffc 0xc10000fff8000fff

def z1094 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x7bfe03701ff83983 0x1eff80dc07fe0e60

def z1095 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xfeffffffe007c7ff 0xffbffffff801f1ff

def z1096 : W := mkw 0x81b202900b683780 0x606c80a402da0de0 0x7ffe03801ff83f83 0x5fff80e007fe0fe0

def z1097 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xde1dd30e11c4f9cd 0x378774c384713e73

def z1098 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xda1dd34e91c4f98d 0x368774d3a4713e63

def z1099 : W := mkw 0x0249f4001db7c003 0x80927d00076df000 0xfbfdf0001fffc003 0x3eff7c0007fff000

def z1100 : W := mkw 0x000c914480000000 0x0003245120000000 0xd81fdf7ee0000000 0xf607f7dfb8000000

def z1101 : W := mkw 0x6061628b1686ac6b 0x581858a2c5a1ab1a 0xbde1e38f1e07fe7f 0xef7878e3c781ff9f

def z1102 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xa0e3ffffe0000000 0xe838fffff8000000

def z1103 : W := mkw 0x6008d00210c4994b 0x1802340084312652 0xde1dd30e11c4f9cd 0xf78774c384713e73

def z1104 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x3dfe03b01ff83e03 0x4f7f80ec07fe0f80

def z1105 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0x5e1dc34e11c4f9cd 0x578770d384713e73

def z1106 : W := mkw 0x812403f002483780 0x604900fc00920de0 0xce0013f08004ffcd 0xf38004fc20013ff3

def z1107 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xbde3efbf7e073e73 0xef78fbefdf81cf9c

def z1108 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0x9e1dc30e11c4f9cd 0xe78770c384713e73

def z1109 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfffffcc19fffc7ff 0xffffff3067fff1ff

def z1110 : W := mkw 0x02dbf8001da68003 0x00b6fe000769a000 0xfbffe0001fff0003 0x3efff80007ffc000

def z1111 : W := mkw 0x42dbfc0b1db7c863 0x90b6ff02c76df218 0xfbfffc0e1fffc003 0x3effff0387fff000

def z1112 : W := mkw 0x0292040009b1c001 0x80a48100026c7000 0x7bfe00001ff8c003 0x1eff800007fe3000

def z1113 : W := mkw 0x00b202800b202400 0x402c80a002c80900 0x7bfe03001ff83803 0x1eff80c007fe0e00

def z1114 : W := mkw 0x00d320000d220000 0x0034c80003488000 0x7bfe20001ffb0003 0x1eff880007fec000

def z1115 : W := mkw 0xd0004412341f4af6 0xb40011048d07d2bd 0x06000000003fc7ff 0x01800000000ff1ff

def z1116 : W := mkw 0x7049f40fb497c87f 0x9c127d03ed25f21f 0x8001fc0fe007c07c 0xa0007f03f801f01f

def z1117 : W := mkw 0x00d360001d260002 0x0034d80007498000 0x7bffc0001ff80003 0x1efff00007fe0000

def z1118 : W := mkw 0x0092000009200000 0x0024800002480000 0x7ffe00401ff80183 0x5fff801007fe0060

def z1119 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0x53ffdc001fffc003 0x14fff70007fff000

def z1120 : W := mkw 0x009e9964c0000000 0x0027a65930000000 0xf81fffffe0000000 0xfe07fffff8000000

def z1121 : W := mkw 0x009e9964c0000000 0x0027a65930000000 0x501fdf7ee0000000 0x1407f7dfb8000000

def z1122 : W := mkw 0x01b603e00b603500 0x406d80f802d80d40 0x13fc03001ff83803 0x04ff00c007fe0e00

def z1123 : W := mkw 0x912403f022483794 0x644900fc08920de5 0x040003f000003ffc 0x410000fc00000fff

def z1124 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0x561dd34e91c4f9cd 0x158774d3a4713e73

def z1125 : W := mkw 0x02d32c000d334000 0x80b4cb00034cd000 0xfbfe3c001fffc003 0x3eff8f0007fff000

def z1126 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xfe1fd3fe91c4f9cd 0xff87f4ffa4713e73

def z1127 : W := mkw 0x12dbfc003db7c017 0x84b6ff000f6df005 0xfffffc41ffffc1ff 0xffffff107ffff07f

def z1128 : W := mkw 0x00ffbbedc6022420 0x403feefb71808908 0xf9ffffffee000000 0xfe7ffffffb800000

def z1129 : W := mkw 0x009200000b202400 0x4024800002c80900 0x7ffe00001ff83e03 0x1fff800007fe0f80

def z1130 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x5ffc03401ff83f83 0x57ff00d007fe0fe0

def z1131 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0x961dd30e91c4f9cd 0xa58774c3a4713e73

def z1132 : W := mkw 0x1092040029314014 0x842481000a4c5005 0xfbfe3c01ffffc07f 0xbeff8f007ffff01f

def z1133 : W := mkw 0xc12443f2124c3fc2 0x704910fc84930ff0 0x9c01c3fe10043fc1 0xe70070ff84010ff0

def z1134 : W := mkw 0x00be93e480000000 0x002fa4f920000000 0xf8ffffffe0000000 0xfe3ffffff8000000

def z1135 : W := mkw 0x01ffbbedc9601100 0x007feefb72580440 0xf8ffffffe1c00000 0xfe3ffffff8700000

def z1136 : W := mkw 0x600cd14694c6994b 0x18033451a531a652 0xdf1dd34e9fc7f9cf 0xf7c774d3a7f1fe73

def z1137 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x11fc03001ff83e02 0x047f00c007fe0f80

def z1138 : W := mkw 0x01ffbbedcb603500 0x407feefb72d80d40 0xfdffffffffc03e03 0xff7ffffffff00f80

def z1139 : W := mkw 0x812403f482483780 0x604900fd20920de0 0x040003fe80003f80 0xc10000ffa0000fe0

def z1140 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xdbfdd0001fffc003 0x36ff740007fff000

def z1141 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0xfffe13f01ffcff83 0x7fff84fc07ff3fe0

def z1142 : W := mkw 0x42dbfc021db7c843 0x90b6ff00876df210 0xfbfffc0e1fffc043 0xbeffff0387fff010

def z1143 : W := mkw 0x91f326b92f3b66b4 0xe47cc9ae4bced9ad 0x21e22cb16e3b0632 0x08788b2c5b8ec18c

def z1144 : W := mkw 0x812403f942483780 0x604900fe50920de0 0x040003f160003f80 0x410000fc58000fe0

def z1145 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xfde3e3ff1e073e73 0xff78f8ffc781cf9c

def z1146 : W := mkw 0x6249fc0fd497c84b 0x98927f03f525f212 0x8001fc0fe007c04c 0xa0007f03f801f013

def z1147 : W := mkw 0x42dbfc0b1db7c863 0x90b6ff02c76df218 0xfffffc8f1fffc673 0xffffff23c7fff19c

def z1148 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0x93fdfc001fffc003 0x24ff7f0007fff000

def z1149 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0x161dc34e91c4f9cd 0xc58770d3a4713e73

def z1150 : W := mkw 0xd0004412361f6ef6 0xf40011048d87dbbd 0x050000001e3f3e73 0x01400000078fcf9c

def z1151 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfbfffc70ffffc003 0x3effff1c3ffff000

def z1152 : W := mkw 0x02d364001db7c003 0x80b4d900076df000 0xfbffe0001fffc003 0x3efff80007fff000

def z1153 : W := mkw 0x9000041020194294 0xa4000104080650a5 0xe2023cf1e03fc7fe 0xb8808f3c780ff1ff

def z1154 : W := mkw 0x912403f022483794 0x644900fc08920de5 0x040003f0e0003f8c 0x410000fc38000fe3

def z1155 : W := mkw 0x81b603fdcb683780 0x606d80ff72da0de0 0x7ffe03fe1ff83f83 0x5fff80ff87fe0fe0

def z1156 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0x78ffefff60000000 0x5e3ffbffd8000000

def z1157 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xb0ffffbfe0000000 0xac3fffeff8000000

def z1158 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x7ffe03001ff83f83 0x1fff80c007fe0fe0

def z1159 : W := mkw 0x00dbbc0009314000 0x8036ef00024c5000 0xfbfffc001fffc003 0x3effff0007fff000

def z1160 : W := mkw 0xc12403f202483fe0 0x704900fc80920ff8 0x040003f000003ff0 0x410000fc00000ffc

def z1161 : W := mkw 0x0092000009200000 0x0024800002480000 0xfffe10409ffcc1cf 0xffff841027ff3073

def z1162 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0x11ffcc001ff80000 0x047ff30007fe0000

def z1163 : W := mkw 0xf02403dfa2483ffc 0x7c0900f7e8920fff 0x040003ffe0003ffc 0xc10000fff8000fff

def z1164 : W := mkw 0x92f32e992f3b66b4 0xe4bccba64bced9ad 0x21e22cb16e3b0632 0x08788b2c5b8ec18c

def z1165 : W := mkw 0x00dbf8001d260002 0x0036fe0007498000 0xfbfffc001fff0003 0x3effff0007ffc000

def z1166 : W := mkw 0x812403d00b683780 0x604900f402da0de0 0x7ffc03c01ff83f83 0x5fff00f007fe0fe0

def z1167 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x7bfe03f01ff83980 0x5eff80fc07fe0e60

def z1168 : W := mkw 0x0092040009314000 0x80248100024c5000 0x7bfe1c001ff8c003 0x1eff870007fe3000

def z1169 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x7ffe03f1fff83f83 0xdfff80fc7ffe0fe0

def z1170 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0x30ffefffe0000000 0xcc3ffbfff8000000

def z1171 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xb1e1e38f1e073e72 0xac7878e3c781cf9c

def z1172 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xc01fffffe0000000 0xf007fffff8000000

def z1173 : W := mkw 0x52dbfc0b3db7c877 0x94b6ff02cf6df21d 0xfbfffc0fffffc07f 0xbeffff03fffff01f

def z1174 : W := mkw 0xe12403f682483fc8 0x784900fda0920ff2 0x040003fe00003f80 0x410000ff80000fe0

def z1175 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xde1dd3cf91c4fffd 0xf78774f3e4713fff

def z1176 : W := mkw 0x7249fc06b497c85f 0x9c927f01ad25f217 0x8001fc0fe007c07c 0xa0007f03f801f01f

def z1177 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0x7bffc0001fffc003 0x1efff00007fff000

def z1178 : W := mkw 0x00fbbaadc0000000 0x003eeeab70000000 0x20e3ecbf60000000 0x0838fb2fd8000000

def z1179 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0x95e1e38f1e073e70 0xe57878e3c781cf9c

def z1180 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0x33ffec001fffc003 0x0cfffb0007fff000

def z1181 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xffffff001ffff803 0x7fffffc007fffe00

def z1182 : W := mkw 0x0041200900000000 0x0010480240000000 0xe803fcffe0000000 0xfa00ff3ff8000000

def z1183 : W := mkw 0x609ed966d0c4994b 0x1827b659b4312652 0x461e1c70f1c4f9cd 0x1187871c3c713e73

def z1184 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x3ffc03801ff83f83 0x4fff00e007fe0fe0

def z1185 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xbfe1e38f1e07ffff 0xeff878e3c781ffff

def z1186 : W := mkw 0x02dbbc000db3c001 0x80b6ef00036cf000 0xfbfffc000ffbc002 0x3effff0003fef000

def z1187 : W := mkw 0x02dbfc091db7c003 0x80b6ff02476df000 0xfbfffc0f1fffc003 0xbeffff03c7fff000

def z1188 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xde1dd34e91c7ffff 0xf78774d3a471ffff

def z1189 : W := mkw 0x81b603f90b6837a0 0x606d80fe42da0de8 0x7ffe03f11ff83fb3 0x5fff80fc47fe0fec

def z1190 : W := mkw 0xb19e9574a9f9d39d 0xac67a55d2a7e74e7 0x421e1c70e1f8c18c 0x1087871c387e3063

def z1191 : W := mkw 0x02dbf8001da68003 0x00b6fe000769a000 0xfbffd0001ffcc003 0x3efff40007ff3000

def z1192 : W := mkw 0x02dbbc000db3c001 0x80b6ef00036cf000 0x7bfe3c001ffbc003 0x1eff8f0007fef000

def z1193 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xf8ffffffe0030632 0xfe3ffffff800c18c

def z1194 : W := mkw 0x009ad00019a48003 0x0026b40006692000 0x7bffc0001ff80003 0x1efff00007fe0000

def z1195 : W := mkw 0x600cd14694c6996b 0x18033451a531a65a 0xde1dd34e91c7f9fd 0xf78774d3a471fe7f

def z1196 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xf8ffffffe004c04c 0xfe3ffffff8013013

def z1197 : W := mkw 0x00ffbbedc2002400 0x403feefb70800900 0xfdfffffffe073e73 0xff7fffffff81cf9c

def z1198 : W := mkw 0x600cd14690c4994b 0x18033451a4312652 0xfe1fff4e91c4f9cd 0xff87ffd3a4713e73

def z1199 : W := mkw 0x819601500b683780 0x6065805402da0de0 0x7ffe03401ff83f83 0x5fff80d007fe0fe0

def z1200 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xbbfde0001fffc003 0x2eff780007fff000

def z1201 : W := mkw 0x4061628b16062c62 0x501858a2c5818b18 0xbde1f38f9e07fe7f 0xef787ce3e781ff9f

def z1202 : W := mkw 0xf0004412309dcadf 0xbc0011048c2772b7 0x06000000003fc7ff 0x01800000000ff1ff

def z1203 : W := mkw 0x02dbfc205db7c003 0x80b6ff08176df000 0xfbfffc307fffc003 0x3effff0c1ffff000

def z1204 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x7bfe03b01ff83e03 0x1eff80ec07fe0f80

def z1205 : W := mkw 0x40f36aab56062c62 0x503cdaaad5818b18 0x25e22cb17e073e73 0x09788b2c5f81cf9c

def z1206 : W := mkw 0x81b603f00b683780 0x606d80fc02da0de0 0x7ffe2ff17ff83f83 0x5fff8bfc5ffe0fe0

def z1207 : W := mkw 0xe12403f202483fc8 0x784900fc80920ff2 0x040003f000003fcc 0x410000fc00000ff3

def z1208 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xd8ffdf7ee0000000 0xf63ff7dfb8000000

def z1209 : W := mkw 0x72dbfc06bdb7c85f 0x9cb6ff01af6df217 0xfbfffc0fffffc07f 0xbeffff03fffff01f

def z1210 : W := mkw 0x009240001d260002 0x0024900007498000 0x7bfe00001fff0003 0x1eff800007ffc000

def z1211 : W := mkw 0x4092400219240842 0x1024900086490210 0xffffc30e1ffc3843 0xfffff0c387ff0e10

def z1212 : W := mkw 0x00ffbbedc0000000 0x003feefb70000000 0xfcffffffe00001cc 0xff3ffffff8000073

def z1213 : W := mkw 0x00fbbaadc0000000 0x003eeeab70000000 0xb8e3ffbfe0000000 0xee38ffeff8000000

def z1214 : W := mkw 0x02dbfc04ddb7c003 0x80b6ff01376df000 0xfbfffc00ffffc003 0x3effff003ffff000

def z1215 : W := mkw 0x00fbbaa940000000 0x003eeeaa50000000 0xf8ffffbf60000000 0xfe3fffefd8000000

def z1216 : W := mkw 0xb29e9d54a9f9d39d 0xaca7a7552a7e74e7 0x421e1c70e1f8c18c 0x1087871c387e3063

def z1217 : W := mkw 0x8096015009681380 0x20258054025a04e0 0x7ffe03f01ff83f83 0x5fff80fc07fe0fe0

def z1218 : W := mkw 0xf12403f6a2483fdc 0x7c4900fda8920ff7 0x040003ffe0003ffc 0xc10000fff8000fff

def z1219 : W := mkw 0x02dbfc001db7c003 0x80b6ff00076df000 0xfffffcf1ffffc673 0xffffff3c7ffff19c

def z1220 : W := mkw 0x8196017009681380 0x2065805c025a04e0 0x7ffe03701ff83983 0x5fff80dc07fe0e60

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z7,z5,z6]),(0,[z1,z2,z3,z8,z4,z5,z9])],[(0,[z1,z2,z3,z4,z10,z5,z6])],[(0,[z11,z2,z3,z12,z4,z5,z6]),(0,[z13,z1,z14,z3,z4,z5,z6]),(0,[z1,z2,z4,z10,z5,z6,z15]),(0,[z1,z16,z2,z3,z4,z5,z6]),(0,[z17,z1,z2,z4,z5,z6,z15])],[(0,[z1,z2,z3,z4,z5,z18,z6]),(0,[z19,z1,z2,z3,z4,z5,z6]),(0,[z13,z1,z20,z3,z4,z5,z6]),(0,[z13,z1,z2,z3,z4,z21,z6]),(0,[z1,z2,z3,z22,z4,z5,z6]),(0,[z17,z16,z2,z3,z4,z5,z6]),(0,[z17,z1,z23,z3,z4,z5,z6]),(0,[z24,z1,z2,z3,z5,z6,z25]),(0,[z1,z2,z3,z4,z5,z6,z26]),(0,[z1,z2,z27,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z28]),(0,[z1,z2,z3,z4,z5,z6,z29]),(0,[z30,z13,z1,z3,z4,z5,z6]),(0,[z31,z1,z2,z32,z4,z5,z6])],[(0,[z1,z2,z33,z3,z4,z5,z6])],[(0,[z34,z1,z2,z3,z4,z5,z6]),(0,[z1,z35,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z36]),(0,[z1,z2,z3,z4,z37,z5,z6])],[(0,[z1,z38,z2,z3,z4,z5,z6]),(0,[z24,z1,z3,z4,z21,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z39,z5,z6]),(0,[z40,z1,z41,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z42]),(0,[z13,z1,z3,z43,z4,z5,z6]),(0,[z1,z2,z3,z4,z44,z5,z6]),(0,[z1,z2,z3,z4,z5,z45,z6])],[(0,[z1,z2,z3,z46,z4,z5,z6]),(0,[z1,z2,z47,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z48]),(0,[z13,z1,z3,z49,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z50]),(0,[z1,z2,z51,z3,z4,z5,z6]),(0,[z52,z1,z2,z3,z4,z5,z6])],[(0,[z53,z54,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z55,z4,z5,z6]),(0,[z24,z1,z2,z3,z49,z5,z6])],[(0,[z1,z2,z3,z4,z5,z56,z6]),(0,[z1,z2,z3,z4,z5,z6,z57]),(0,[z1,z2,z58,z3,z4,z5,z6])],[(0,[z59,z2,z3,z4,z5,z60,z6]),(0,[z1,z3,z4,z21,z5,z6,z61]),(0,[z62,z1,z2,z20,z4,z5,z6]),(0,[z1,z2,z63,z20,z3,z5,z6]),(0,[z1,z64,z2,z3,z4,z5,z6]),(0,[z17,z1,z2,z3,z4,z65,z6])],[(0,[z1,z66,z2,z3,z4,z5,z6]),(0,[z59,z1,z2,z3,z4,z60,z6]),(0,[z1,z67,z2,z3,z4,z5,z6]),(0,[z68,z1,z2,z3,z4,z5,z6]),(0,[z31,z1,z69,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z70])],[(0,[z1,z71,z2,z3,z4,z5,z6]),(0,[z1,z72,z3,z73,z4,z5,z6]),(0,[z1,z14,z2,z3,z4,z74,z6])]],
   [[(0,[z75,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z76,z5,z6]),(1,[z59,z2,z3,z4,z60,z6]),(0,[z1,z2,z77,z3,z4,z5,z6]),(0,[z78,z2,z3,z4,z5,z79,z6]),(0,[z80,z1,z2,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z5,z6,z25]),(0,[z1,z3,z4,z81,z21,z5,z6]),(0,[z1,z3,z82,z4,z21,z5,z6]),(0,[z1,z2,z3,z4,z5,z83,z6])],[(0,[z53,z2,z3,z4,z5,z79,z6]),(0,[z1,z2,z3,z84,z4,z5,z6])],[(0,[z1,z2,z3,z4,z85,z5,z6]),(0,[z1,z86,z3,z4,z5,z6,z50]),(0,[z87,z2,z63,z3,z4,z5,z6]),(1,[z31,z1,z2,z4,z6,z88]),(0,[z1,z2,z3,z4,z5,z6,z89])],[(0,[z1,z3,z90,z4,z21,z5,z6]),(0,[z1,z2,z91,z3,z4,z5,z6]),(0,[z92,z1,z2,z3,z4,z5,z6]),(0,[z93,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z94])],[(0,[z1,z2,z3,z4,z5,z6,z95]),(0,[z1,z2,z96,z3,z4,z5,z6]),(0,[z1,z2,z97,z3,z4,z5,z6]),(0,[z98,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z21,z5,z5,z6]),(0,[z1,z2,z3,z10,z5,z6,z9]),(0,[z1,z2,z3,z4,z5,z99,z6])],[(0,[z1,z100,z2,z3,z4,z5,z6]),(0,[z30,z1,z2,z73,z4,z5,z6])],[(0,[z17,z1,z2,z3,z101,z5,z6]),(0,[z17,z1,z2,z3,z4,z99,z6])],[(0,[z1,z2,z3,z4,z5,z6,z102]),(0,[z13,z59,z1,z3,z4,z5,z6]),(0,[z1,z3,z103,z4,z21,z5,z6]),(0,[z104,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z105,z3,z4,z5,z6]),(1,[z17,z1,z2,z4,z5,z15]),(0,[z1,z2,z3,z4,z106,z5,z6])]],
   [[(0,[z1,z2,z107,z3,z4,z5,z6]),(1,[z108,z2,z3,z4,z5,z6]),(0,[z1,z14,z69,z2,z3,z4,z6]),(0,[z109,z1,z3,z4,z21,z5,z6]),(0,[z1,z2,z3,z4,z110,z5,z6])],[(0,[z111,z1,z2,z3,z4,z5,z6]),(0,[z1,z112,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z113,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z114]),(0,[z115,z1,z3,z4,z21,z5,z6]),(0,[z62,z1,z2,z3,z10,z5,z6])],[(0,[z1,z14,z2,z3,z4,z60,z6]),(0,[z1,z58,z3,z4,z21,z5,z6]),(0,[z17,z1,z2,z3,z116,z5,z6]),(1,[z1,z2,z3,z8,z5,z117]),(0,[z1,z2,z3,z4,z5,z6,z118])],[(0,[z1,z2,z3,z4,z119,z5,z6]),(0,[z1,z2,z3,z4,z120,z5,z6]),(1,[z16,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z121,z6]),(0,[z1,z3,z4,z122,z21,z5,z6]),(0,[z123,z1,z2,z3,z4,z5,z6]),(0,[z124,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z125,z5,z6]),(0,[z1,z2,z3,z4,z37,z6,z126])],[(0,[z127,z2,z3,z90,z4,z5,z6]),(0,[z13,z1,z3,z90,z4,z5,z6]),(0,[z1,z2,z3,z128,z4,z5,z6]),(0,[z31,z1,z2,z3,z4,z129,z6])],[(0,[z1,z130,z3,z4,z5,z6,z50]),(0,[z1,z3,z4,z131,z5,z60,z6]),(0,[z1,z86,z72,z3,z4,z5,z6]),(0,[z1,z63,z3,z4,z21,z5,z6]),(0,[z1,z2,z3,z132,z4,z5,z6]),(0,[z40,z1,z3,z4,z5,z6,z50]),(0,[z1,z2,z3,z4,z133,z5,z6]),(0,[z1,z2,z3,z134,z4,z5,z6]),(1,[z135,z2,z3,z4,z5,z6])],[(0,[z136,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z137,z4,z5,z6]),(0,[z1,z138,z2,z3,z4,z5,z6]),(1,[z1,z2,z105,z4,z5,z139]),(1,[z2,z3,z4,z5,z6,z36])]],
   [[(0,[z140,z1,z2,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z5,z6,z15]),(0,[z1,z2,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z141,z5,z6])],[(0,[z1,z2,z142,z3,z4,z5,z6]),(0,[z143,z1,z2,z3,z4,z5,z6]),(0,[z13,z13,z1,z3,z4,z5,z6]),(0,[z1,z69,z2,z3,z49,z4,z6]),(0,[z1,z2,z144,z3,z4,z5,z6])],[(0,[z11,z2,z130,z3,z4,z5,z6]),(0,[z1,z2,z3,z145,z4,z5,z6]),(1,[z146,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z147,z4,z5,z6]),(0,[z1,z148,z2,z3,z4,z5,z6])],[(0,[z149,z1,z130,z3,z4,z5,z6]),(0,[z150,z1,z2,z3,z90,z5,z6]),(0,[z150,z2,z3,z4,z5,z79,z6]),(0,[z1,z151,z2,z3,z4,z5,z6]),(1,[z1,z152,z3,z4,z5,z6]),(0,[z153,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z154,z6]),(0,[z1,z2,z105,z3,z4,z5,z15]),(0,[z155,z1,z2,z3,z4,z5,z6])],[(0,[z1,z156,z2,z3,z4,z5,z6]),(0,[z157,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z158,z5,z6]),(0,[z1,z2,z159,z3,z4,z5,z6])],[(0,[z149,z11,z2,z3,z4,z5,z6]),(0,[z13,z1,z3,z12,z4,z5,z6]),(0,[z1,z2,z3,z8,z160,z5,z6]),(0,[z1,z105,z3,z4,z21,z5,z6]),(1,[z1,z2,z3,z4,z65,z6]),(1,[z1,z161,z3,z4,z5,z6]),(0,[z162,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z163,z4,z5,z6])],[(0,[z1,z2,z3,z4,z164,z5,z6]),(0,[z1,z2,z3,z4,z129,z5,z6]),(0,[z1,z2,z3,z165,z4,z5,z6])],[(0,[z166,z1,z2,z3,z4,z5,z6]),(0,[z13,z1,z156,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z167,z5,z6]),(0,[z1,z2,z3,z4,z168,z5,z6]),(1,[z1,z169,z3,z4,z5,z6]),(0,[z170,z1,z2,z3,z4,z5,z6]),(0,[z1,z171,z2,z3,z103,z5,z6]),(0,[z1,z2,z3,z49,z4,z5,z6])]],
   [[(0,[z172,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z173,z4,z5,z6]),(0,[z1,z2,z3,z4,z174,z5,z6]),(0,[z40,z1,z2,z3,z4,z5,z175]),(0,[z176,z1,z2,z3,z4,z5,z6]),(1,[z1,z3,z134,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z139,z6]),(0,[z1,z2,z105,z3,z4,z5,z139])],[(1,[z1,z2,z3,z4,z177,z6])],[(0,[z1,z2,z3,z4,z5,z6,z178]),(0,[z13,z1,z2,z3,z49,z4,z6]),(0,[z1,z2,z3,z4,z5,z179,z6]),(0,[z1,z2,z3,z4,z5,z6,z180]),(1,[z1,z2,z3,z4,z83,z6]),(0,[z181,z1,z2,z3,z5,z6,z9])],[(0,[z53,z1,z2,z182,z4,z5,z6]),(0,[z1,z2,z183,z3,z4,z5,z6]),(0,[z184,z1,z2,z3,z4,z5,z6]),(1,[z13,z1,z3,z4,z21,z6]),(0,[z1,z2,z3,z4,z5,z6,z185]),(0,[z1,z41,z3,z4,z21,z5,z6]),(0,[z1,z2,z63,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z186,z6]),(0,[z1,z2,z3,z4,z5,z187,z6]),(0,[z188,z1,z2,z3,z4,z5,z6]),(0,[z1,z189,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z190])],[(1,[z1,z2,z3,z4,z191,z6]),(0,[z1,z2,z192,z3,z4,z5,z6]),(0,[z31,z193,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z25]),(0,[z1,z2,z3,z4,z194,z5,z6]),(0,[z1,z161,z2,z3,z4,z5,z6]),(0,[z195,z14,z2,z3,z4,z5,z6])],[(0,[z2,z3,z12,z90,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z196]),(0,[z1,z2,z3,z4,z116,z5,z6]),(1,[z1,z2,z3,z101,z5,z6]),(1,[z1,z2,z3,z4,z99,z6])],[(1,[z1,z2,z3,z4,z197,z6]),(0,[z1,z2,z198,z3,z4,z5,z6])]],
   [[(0,[z199,z1,z2,z3,z4,z5,z6]),(0,[z54,z1,z3,z4,z21,z5,z6]),(0,[z1,z2,z200,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z201,z5,z6]),(0,[z108,z1,z2,z3,z4,z5,z6]),(0,[z1,z20,z3,z4,z21,z5,z6]),(0,[z1,z3,z4,z5,z6,z202,z88]),(0,[z1,z203,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z204,z4,z5,z6]),(0,[z11,z1,z2,z3,z4,z5,z6]),(0,[z205,z1,z152,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z78,z1,z2,z3,z4,z5,z79]),(0,[z206,z1,z3,z4,z21,z5,z6]),(0,[z1,z2,z207,z3,z4,z5,z6])],[(0,[z1,z2,z208,z3,z4,z5,z6]),(0,[z11,z13,z1,z3,z4,z5,z6]),(0,[z209,z1,z3,z4,z210,z5,z6]),(1,[z1,z2,z3,z116,z5,z6])],[(1,[z1,z2,z211,z4,z5,z6]),(0,[z1,z86,z3,z4,z21,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z212]),(0,[z1,z2,z3,z4,z5,z6,z213]),(0,[z1,z2,z3,z4,z5,z214,z6])],[(0,[z215,z1,z2,z3,z4,z5,z6]),(0,[z59,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z216,z6]),(0,[z1,z2,z3,z8,z4,z5,z6])],[(0,[z156,z2,z130,z3,z4,z5,z6]),(0,[z78,z1,z3,z4,z21,z5,z6]),(0,[z1,z2,z3,z217,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z218,z6]),(1,[z1,z3,z4,z21,z5,z6]),(1,[z2,z219,z3,z4,z5,z6])],[(0,[z220,z1,z2,z3,z4,z5,z6]),(0,[z53,z1,z3,z4,z21,z5,z6]),(0,[z1,z2,z182,z105,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z221]),(0,[z1,z2,z3,z4,z222,z5,z6]),(0,[z223,z1,z2,z3,z4,z5,z6]),(0,[z1,z171,z3,z4,z5,z6,z50]),(0,[z224,z13,z1,z3,z4,z5,z6]),(0,[z13,z1,z2,z3,z4,z6,z126]),(0,[z31,z1,z2,z3,z4,z5,z6])],[(0,[z127,z1,z2,z182,z4,z5,z6]),(0,[z11,z2,z3,z4,z160,z5,z6]),(0,[z13,z1,z3,z225,z4,z5,z6]),(0,[z31,z226,z2,z3,z4,z5,z6]),(1,[z1,z3,z4,z194,z5,z6]),(0,[z227,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z228,z1,z2,z3,z4,z5,z6]),(0,[z13,z1,z32,z3,z4,z5,z6]),(0,[z1,z3,z4,z10,z21,z5,z6]),(0,[z1,z2,z3,z4,z229,z5,z6]),(0,[z14,z230,z2,z3,z4,z5,z6])],[(0,[z209,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z231,z5,z6]),(0,[z232,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z126,z25])],[(0,[z233,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z234]),(0,[z1,z2,z3,z90,z4,z5,z6]),(0,[z62,z64,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z235]),(0,[z1,z2,z3,z49,z74,z5,z6])],[(0,[z1,z2,z3,z4,z236,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z237]),(0,[z1,z2,z3,z4,z5,z238,z6])],[(0,[z1,z2,z3,z4,z5,z6,z239]),(0,[z2,z3,z4,z160,z5,z6,z95]),(0,[z1,z2,z63,z4,z10,z5,z6]),(0,[z1,z2,z3,z240,z4,z5,z6]),(0,[z1,z2,z3,z4,z129,z6,z126]),(0,[z1,z2,z3,z241,z4,z5,z6]),(0,[z242,z1,z3,z4,z5,z6,z25])],[(0,[z1,z2,z3,z4,z243,z5,z6]),(0,[z1,z2,z3,z4,z5,z244,z6]),(0,[z13,z1,z2,z3,z4,z60,z6]),(0,[z205,z1,z2,z3,z4,z197,z6]),(0,[z245,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z246,z3,z4,z5,z6]),(0,[z1,z3,z4,z21,z74,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z15]),(0,[z247,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z248,z4,z5,z6]),(0,[z249,z1,z2,z3,z4,z5,z6]),(0,[z245,z13,z1,z3,z4,z5,z6]),(1,[z31,z13,z1,z3,z4,z6]),(1,[z250,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z251,z21,z5,z6]),(0,[z1,z2,z252,z3,z4,z5,z6])],[(0,[z1,z130,z3,z4,z21,z5,z6]),(0,[z205,z1,z2,z3,z4,z5,z79]),(0,[z1,z2,z253,z3,z4,z5,z6]),(0,[z1,z86,z41,z3,z4,z5,z6])]],
   [[(0,[z1,z3,z73,z4,z210,z5,z6]),(0,[z1,z2,z3,z4,z5,z254,z6]),(0,[z1,z2,z3,z4,z5,z6,z255])],[(0,[z205,z1,z2,z211,z4,z5,z6]),(0,[z256,z13,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z257,z4,z5,z6]),(0,[z258,z1,z2,z3,z4,z5,z6]),(0,[z127,z1,z3,z4,z21,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z259]),(0,[z30,z1,z3,z73,z4,z5,z6]),(0,[z1,z2,z3,z260,z4,z5,z6]),(0,[z1,z2,z261,z3,z4,z5,z6]),(0,[z1,z2,z262,z3,z4,z5,z6]),(0,[z1,z263,z2,z3,z4,z5,z6])],[(0,[z205,z1,z3,z4,z21,z5,z6]),(0,[z264,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z265]),(0,[z31,z1,z2,z4,z5,z6,z88]),(0,[z1,z189,z32,z3,z4,z5,z6]),(1,[z1,z266,z3,z4,z5,z6]),(0,[z267,z1,z2,z3,z4,z5,z6])],[(0,[z13,z1,z130,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z268,z5,z6])],[(0,[z1,z2,z3,z4,z269,z5,z6]),(0,[z30,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z270,z6])],[(0,[z1,z2,z3,z4,z5,z6,z271]),(0,[z13,z78,z1,z3,z4,z5,z6]),(0,[z181,z135,z2,z3,z4,z5,z6])]],
   [[(0,[z150,z1,z3,z4,z21,z5,z6]),(1,[z1,z2,z173,z4,z5,z6]),(0,[z13,z1,z3,z4,z5,z6,z272]),(0,[z1,z14,z2,z3,z4,z6,z88])],[(0,[z273,z1,z130,z3,z4,z5,z6]),(0,[z274,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z79,z6,z95]),(0,[z62,z1,z3,z4,z21,z5,z6]),(0,[z1,z3,z4,z21,z21,z5,z6]),(0,[z1,z2,z275,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z276,z6]),(0,[z30,z1,z2,z72,z4,z5,z6]),(0,[z277,z1,z2,z3,z4,z5,z6])],[(1,[z228,z1,z2,z3,z4,z6]),(0,[z277,z13,z1,z3,z4,z5,z6])],[(0,[z1,z278,z2,z3,z4,z5,z6]),(0,[z24,z13,z1,z2,z3,z4,z6]),(0,[z1,z3,z49,z4,z21,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z279]),(0,[z1,z2,z3,z4,z280,z5,z6])],[(0,[z281,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z282,z3,z4,z5,z6]),(1,[z54,z2,z3,z90,z5,z6]),(0,[z1,z2,z3,z283,z4,z5,z6])],[(0,[z54,z1,z2,z3,z90,z5,z6]),(0,[z54,z2,z3,z90,z4,z5,z6]),(0,[z11,z1,z2,z3,z4,z60,z6]),(0,[z181,z1,z161,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z284,z5,z6])],[(0,[z1,z2,z285,z3,z4,z5,z6]),(0,[z1,z2,z211,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z286,z6]),(0,[z1,z2,z287,z3,z4,z5,z6]),(0,[z288,z1,z2,z3,z4,z5,z6]),(0,[z289,z13,z1,z3,z4,z5,z6]),(0,[z1,z2,z105,z4,z5,z139,z6])]],
   [[(0,[z290,z1,z3,z4,z5,z6,z88]),(0,[z1,z2,z3,z4,z291,z5,z6])],[(0,[z292,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z293,z4,z5,z6])],[(0,[z294,z1,z2,z3,z4,z5,z6]),(0,[z13,z1,z182,z3,z4,z5,z6]),(0,[z295,z1,z2,z3,z4,z5,z6]),(1,[z13,z1,z3,z49,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z296]),(1,[z297,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z298,z4,z5,z6]),(0,[z13,z1,z3,z4,z5,z5,z6]),(0,[z1,z2,z3,z4,z251,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z202]),(0,[z181,z1,z2,z3,z4,z83,z6])],[(0,[z149,z1,z2,z3,z4,z299,z6]),(0,[z1,z300,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z225,z4,z5,z6]),(0,[z1,z2,z3,z301,z4,z5,z6]),(1,[z242,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z302,z4,z5,z6])],[(0,[z1,z2,z3,z4,z81,z5,z6]),(0,[z1,z3,z4,z303,z21,z5,z6]),(0,[z205,z1,z2,z173,z4,z5,z6]),(0,[z304,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z305,z5,z6]),(0,[z146,z2,z3,z4,z5,z6,z15]),(0,[z1,z306,z2,z3,z4,z5,z6])],[(0,[z13,z273,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z307]),(0,[z1,z171,z3,z4,z21,z5,z6]),(0,[z1,z41,z2,z3,z4,z5,z175]),(0,[z62,z1,z2,z63,z3,z5,z6])]],
   [[(0,[z273,z2,z130,z3,z4,z5,z6]),(0,[z1,z308,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z21,z5,z79,z6]),(0,[z1,z2,z20,z3,z10,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z309]),(0,[z1,z310,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z311])],[(0,[z1,z2,z3,z312,z4,z5,z6]),(0,[z1,z2,z3,z4,z131,z5,z6]),(0,[z13,z1,z171,z3,z4,z5,z6]),(0,[z1,z313,z2,z3,z4,z5,z6])],[(0,[z13,z1,z3,z4,z160,z5,z6]),(0,[z314,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z315]),(1,[z13,z1,z14,z3,z4,z6]),(0,[z1,z69,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z316]),(0,[z1,z2,z3,z317,z4,z5,z6])],[(0,[z78,z2,z3,z12,z4,z5,z6]),(0,[z1,z2,z3,z318,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z319,z6]),(0,[z1,z2,z3,z4,z37,z5,z126]),(0,[z1,z2,z3,z320,z4,z5,z6])],[(0,[z53,z2,z3,z12,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z321]),(0,[z13,z1,z3,z4,z210,z5,z6]),(0,[z1,z32,z3,z134,z4,z5,z6]),(0,[z24,z1,z2,z3,z4,z6,z25])],[(1,[z1,z3,z4,z5,z6,z202]),(0,[z1,z2,z3,z4,z5,z6,z322]),(0,[z1,z2,z3,z4,z5,z6,z323]),(0,[z1,z324,z2,z3,z4,z5,z6])],[(0,[z181,z1,z3,z4,z21,z5,z6]),(0,[z1,z3,z4,z21,z5,z6,z9]),(0,[z1,z2,z325,z3,z4,z5,z6]),(0,[z62,z1,z2,z63,z4,z5,z6]),(1,[z1,z23,z3,z4,z5,z6]),(0,[z1,z266,z3,z49,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z326,z6]),(0,[z1,z2,z3,z4,z5,z6,z327]),(0,[z295,z1,z3,z4,z5,z60,z6]),(0,[z1,z2,z3,z4,z60,z6,z126]),(0,[z13,z1,z3,z73,z4,z5,z6]),(0,[z1,z3,z4,z21,z5,z6,z88]),(0,[z1,z2,z3,z4,z328,z5,z6]),(0,[z1,z2,z219,z3,z4,z5,z6]),(0,[z1,z2,z63,z3,z5,z6,z9])]],
   [[(0,[z1,z2,z12,z4,z5,z6,z15]),(0,[z1,z2,z3,z4,z329,z5,z6]),(0,[z330,z1,z3,z4,z21,z5,z6]),(0,[z1,z2,z3,z331,z4,z5,z6]),(0,[z1,z2,z3,z5,z117,z6,z9])],[(0,[z54,z78,z2,z3,z4,z5,z6]),(0,[z205,z2,z3,z90,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z332]),(0,[z1,z2,z3,z333,z4,z5,z6])],[(0,[z1,z2,z3,z334,z4,z5,z6]),(0,[z1,z2,z335,z3,z4,z5,z6])],[(0,[z53,z1,z2,z12,z4,z5,z6]),(0,[z1,z2,z3,z4,z336,z5,z6]),(1,[z1,z3,z4,z131,z5,z6]),(0,[z337,z1,z2,z3,z4,z5,z6]),(0,[z1,z171,z41,z3,z4,z5,z6]),(0,[z13,z1,z2,z3,z4,z5,z6])],[(1,[z205,z2,z3,z4,z5,z95]),(0,[z1,z2,z3,z4,z5,z6,z338])],[(0,[z1,z2,z3,z4,z339,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z272]),(0,[z1,z14,z3,z4,z21,z5,z6]),(0,[z340,z1,z2,z3,z4,z5,z6]),(0,[z62,z1,z2,z105,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z36,z9])],[(0,[z1,z2,z3,z4,z341,z5,z6]),(0,[z1,z2,z342,z3,z4,z5,z6]),(0,[z343,z1,z2,z3,z4,z5,z6]),(1,[z1,z306,z3,z4,z5,z6])],[(0,[z273,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z344,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z345]),(0,[z2,z3,z90,z4,z5,z79,z6]),(0,[z1,z250,z2,z3,z4,z5,z6]),(0,[z346,z1,z2,z3,z4,z5,z6])],[(0,[z1,z347,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z348,z6]),(1,[z1,z2,z3,z4,z286,z6]),(0,[z13,z1,z3,z4,z5,z6,z126]),(0,[z1,z2,z3,z43,z4,z5,z6]),(0,[z1,z32,z3,z4,z21,z5,z6]),(0,[z1,z349,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z350,z5,z6]),(0,[z1,z2,z3,z351,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z352]),(0,[z1,z2,z3,z4,z5,z6,z353]),(0,[z1,z3,z4,z21,z5,z45,z6]),(0,[z1,z354,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z355,z5,z6])],[(0,[z1,z156,z3,z4,z5,z6,z50]),(0,[z1,z2,z3,z4,z356,z5,z6]),(0,[z1,z3,z4,z21,z5,z6,z50]),(0,[z1,z2,z105,z4,z10,z5,z6]),(0,[z1,z2,z3,z357,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z358])],[(0,[z359,z1,z2,z3,z4,z5,z6]),(0,[z30,z1,z86,z3,z4,z5,z6]),(0,[z360,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z10,z5,z6]),(0,[z343,z1,z3,z4,z5,z6,z126])],[(0,[z109,z1,z2,z3,z4,z5,z6]),(0,[z78,z1,z2,z3,z4,z5,z95]),(0,[z13,z1,z3,z103,z4,z5,z6]),(0,[z40,z1,z2,z3,z4,z5,z50]),(0,[z361,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z362,z5,z6])],[(0,[z149,z156,z2,z3,z4,z5,z6]),(0,[z150,z2,z3,z12,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z363,z6]),(0,[z11,z54,z2,z3,z4,z5,z6]),(0,[z364,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z90,z5,z6,z9]),(0,[z1,z2,z3,z365,z4,z5,z6]),(0,[z1,z2,z3,z4,z366,z5,z6]),(0,[z24,z1,z2,z3,z4,z74,z6]),(0,[z1,z2,z3,z4,z5,z6,z367]),(0,[z1,z2,z3,z4,z5,z6,z368])],[(0,[z127,z1,z2,z12,z4,z5,z6]),(0,[z1,z2,z3,z4,z369,z5,z6]),(0,[z11,z1,z370,z3,z4,z5,z6]),(0,[z371,z1,z2,z3,z4,z5,z6]),(0,[z115,z13,z1,z3,z4,z5,z6]),(0,[z1,z2,z372,z3,z4,z5,z6])]],
   [[(0,[z1,z373,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z374]),(0,[z13,z1,z3,z4,z5,z60,z6]),(0,[z1,z69,z2,z3,z4,z6,z126]),(0,[z375,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z376,z4,z5,z6])],[(0,[z1,z377,z2,z3,z4,z5,z6]),(0,[z209,z1,z2,z3,z103,z5,z6]),(0,[z1,z2,z3,z4,z5,z378,z6]),(0,[z62,z1,z2,z4,z5,z6,z15]),(1,[z310,z2,z3,z4,z5,z6]),(0,[z1,z2,z379,z3,z4,z5,z6])],[(0,[z2,z182,z3,z12,z4,z5,z6]),(0,[z193,z1,z2,z3,z4,z5,z6]),(0,[z17,z1,z2,z3,z4,z5,z6]),(0,[z380,z1,z2,z3,z4,z5,z6]),(0,[z181,z1,z2,z3,z8,z5,z6])],[(0,[z127,z78,z2,z3,z4,z5,z6]),(0,[z381,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z382,z3,z4,z5,z6]),(0,[z1,z2,z383,z3,z4,z5,z6]),(0,[z17,z13,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z384,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z385]),(0,[z1,z2,z3,z4,z386,z5,z6])],[(0,[z205,z78,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z6,z316]),(0,[z1,z2,z20,z4,z10,z5,z6])],[(0,[z1,z2,z3,z4,z387,z5,z6]),(0,[z1,z2,z3,z4,z388,z5,z6]),(1,[z295,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z21,z5,z6,z95]),(0,[z1,z2,z389,z3,z4,z5,z6])],[(0,[z390,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z391]),(0,[z13,z1,z3,z4,z5,z117,z6])],[(0,[z1,z69,z2,z3,z4,z60,z6]),(0,[z205,z1,z2,z3,z4,z286,z6]),(0,[z1,z2,z3,z4,z5,z6,z392])]],
   [[(0,[z224,z1,z2,z3,z4,z5,z6]),(0,[z393,z1,z2,z3,z4,z5,z6]),(0,[z11,z1,z2,z3,z4,z303,z6]),(0,[z1,z2,z3,z4,z5,z6,z394]),(0,[z1,z2,z3,z4,z5,z395,z6])],[(0,[z1,z2,z3,z4,z5,z6,z396]),(0,[z1,z2,z3,z4,z397,z5,z6])],[(0,[z1,z2,z3,z4,z5,z398,z6]),(0,[z1,z2,z399,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z400,z5,z6]),(0,[z401,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z402,z6])],[(0,[z59,z1,z2,z3,z4,z303,z6]),(0,[z205,z1,z2,z3,z4,z5,z95]),(0,[z1,z72,z3,z4,z21,z5,z6]),(0,[z181,z297,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z403]),(0,[z1,z2,z3,z73,z4,z5,z6]),(0,[z1,z297,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z404]),(0,[z1,z2,z3,z405,z4,z5,z6])],[(0,[z1,z86,z171,z3,z4,z5,z6]),(0,[z17,z1,z2,z3,z4,z5,z15])],[(0,[z1,z2,z3,z4,z406,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z407]),(0,[z408,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z409]),(0,[z1,z2,z32,z3,z4,z129,z6]),(0,[z410,z1,z2,z3,z4,z5,z6]),(0,[z1,z411,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z412,z6]),(0,[z413,z1,z2,z3,z4,z5,z6]),(1,[z1,z414,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z415,z6]),(0,[z1,z230,z2,z3,z4,z5,z6])],[(0,[z2,z3,z12,z4,z5,z60,z6]),(0,[z2,z3,z4,z5,z60,z79,z6]),(0,[z13,z1,z3,z4,z5,z175,z6]),(0,[z31,z1,z2,z3,z4,z6,z88]),(0,[z1,z2,z58,z3,z4,z37,z5]),(0,[z1,z2,z3,z4,z416,z5,z6])],[(0,[z1,z2,z3,z4,z417,z5,z6]),(0,[z1,z418,z20,z3,z4,z5,z6]),(1,[z1,z2,z32,z4,z129,z6])],[(0,[z54,z2,z182,z3,z4,z5,z6]),(0,[z228,z1,z2,z3,z4,z210,z6]),(0,[z256,z1,z2,z3,z4,z5,z6]),(0,[z17,z1,z2,z3,z4,z5,z139]),(0,[z419,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z420,z4,z5,z6])],[(0,[z1,z2,z3,z4,z421,z5,z6]),(0,[z1,z2,z3,z4,z5,z422,z6]),(0,[z1,z2,z423,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z424,z25]),(0,[z181,z1,z2,z3,z4,z5,z117]),(0,[z1,z2,z3,z4,z5,z425,z6]),(0,[z1,z2,z3,z4,z5,z6,z426]),(0,[z1,z2,z427,z3,z4,z5,z6])],[(0,[z1,z2,z3,z12,z4,z5,z6]),(0,[z1,z2,z3,z4,z428,z5,z6]),(0,[z1,z429,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z430,z5,z6])],[(1,[z13,z250,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z5,z431,z6]),(0,[z1,z2,z432,z3,z4,z5,z6]),(0,[z24,z310,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z126])],[(0,[z1,z14,z2,z3,z4,z303,z6]),(0,[z1,z3,z4,z21,z129,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z433]),(0,[z1,z2,z3,z4,z5,z434,z6])]],
   [[(0,[z435,z13,z1,z3,z4,z5,z6]),(0,[z436,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z37,z126])],[(1,[z127,z2,z182,z4,z5,z6]),(0,[z1,z2,z437,z3,z4,z5,z6]),(0,[z13,z1,z86,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z438,z6]),(0,[z1,z3,z4,z21,z5,z139,z6]),(0,[z1,z2,z3,z4,z5,z439,z6]),(0,[z1,z2,z3,z4,z5,z440,z6])],[(0,[z441,z1,z2,z3,z4,z5,z6]),(0,[z78,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z442])],[(0,[z1,z2,z3,z4,z5,z6,z443]),(1,[z13,z1,z3,z4,z5,z6])],[(0,[z444,z1,z2,z3,z4,z5,z6]),(0,[z445,z1,z2,z3,z4,z5,z6]),(0,[z1,z156,z3,z4,z21,z5,z6]),(0,[z53,z13,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z446]),(0,[z1,z2,z3,z4,z5,z6,z447]),(0,[z1,z2,z3,z4,z5,z6,z448]),(1,[z1,z2,z3,z4,z449,z6])],[(0,[z1,z2,z3,z4,z5,z60,z6]),(0,[z1,z2,z3,z4,z5,z450,z6]),(0,[z1,z451,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z452,z6])],[(0,[z1,z2,z3,z453,z4,z5,z6]),(0,[z150,z1,z2,z3,z160,z5,z6]),(0,[z454,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z73,z4,z5,z6,z50]),(0,[z1,z2,z3,z4,z5,z6,z455]),(0,[z1,z3,z4,z21,z5,z6,z25])],[(0,[z1,z182,z3,z4,z21,z5,z6]),(0,[z1,z2,z3,z4,z5,z456,z6]),(0,[z1,z2,z3,z457,z4,z5,z6]),(0,[z13,z1,z69,z3,z4,z5,z6]),(0,[z135,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z11,z127,z2,z3,z4,z5,z6]),(0,[z78,z2,z3,z4,z160,z5,z6]),(0,[z1,z414,z2,z3,z4,z5,z6])],[(0,[z1,z458,z2,z3,z4,z5,z6]),(0,[z289,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z49,z4,z194,z5,z6]),(0,[z1,z2,z459,z3,z4,z5,z6])],[(1,[z1,z41,z3,z4,z5,z175])],[(1,[z53,z2,z12,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z460,z6]),(0,[z1,z2,z3,z376,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z117,z6])],[(0,[z461,z1,z2,z3,z4,z5,z6]),(0,[z40,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z462,z4,z5,z6])],[(0,[z127,z2,z182,z3,z4,z5,z6]),(0,[z1,z2,z3,z463,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z464,z6]),(0,[z461,z13,z1,z3,z4,z5,z6]),(0,[z40,z13,z1,z3,z4,z5,z6]),(1,[z465,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z466,z4,z5,z6]),(0,[z1,z14,z2,z3,z4,z5,z126])],[(0,[z1,z3,z12,z4,z21,z5,z6]),(0,[z1,z2,z3,z4,z5,z467,z6]),(0,[z205,z2,z182,z3,z4,z5,z6]),(0,[z1,z2,z468,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z449,z5,z6])],[(0,[z127,z1,z2,z3,z4,z5,z6]),(0,[z469,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z470,z3,z4,z5,z6])]],
   [[(0,[z1,z156,z41,z3,z4,z5,z6]),(0,[z471,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z472]),(0,[z2,z63,z219,z3,z4,z5,z6]),(0,[z1,z2,z32,z3,z4,z5,z6]),(0,[z473,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z474,z126])],[(0,[z1,z2,z3,z4,z5,z475,z6]),(0,[z476,z1,z2,z3,z4,z5,z6]),(0,[z477,z1,z2,z3,z4,z5,z6]),(0,[z11,z1,z3,z4,z21,z5,z6]),(0,[z205,z13,z1,z3,z4,z5,z6]),(1,[z1,z69,z3,z4,z21,z6]),(0,[z1,z2,z478,z3,z4,z5,z6]),(0,[z181,z1,z2,z376,z4,z5,z6]),(1,[z230,z2,z3,z4,z5,z6])],[(0,[z11,z59,z2,z3,z4,z5,z6]),(0,[z1,z86,z2,z73,z4,z5,z6]),(0,[z1,z2,z3,z479,z4,z5,z6]),(0,[z480,z1,z2,z3,z4,z5,z6])],[(1,[z273,z130,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z481,z5,z6]),(0,[z87,z1,z2,z3,z4,z5,z6])],[(0,[z482,z1,z2,z3,z4,z5,z6]),(0,[z59,z1,z3,z4,z21,z5,z6]),(0,[z1,z2,z3,z4,z122,z5,z6]),(0,[z1,z2,z3,z82,z4,z5,z6]),(0,[z1,z41,z2,z3,z4,z5,z50]),(0,[z1,z2,z483,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z484,z5,z6])],[(0,[z150,z1,z2,z3,z4,z5,z6]),(0,[z482,z13,z1,z3,z4,z5,z6]),(1,[z195,z2,z3,z4,z5,z6])],[(0,[z150,z13,z1,z3,z4,z5,z6]),(0,[z11,z2,z3,z4,z303,z5,z6]),(0,[z485,z1,z2,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z5,z6,z88]),(0,[z31,z1,z3,z4,z21,z5,z6]),(0,[z1,z3,z4,z21,z5,z6,z15]),(0,[z1,z2,z3,z4,z5,z175,z6])],[(0,[z486,z1,z2,z3,z4,z5,z6]),(0,[z1,z171,z2,z3,z210,z5,z6]),(0,[z24,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z487,z3,z4,z5,z6]),(0,[z1,z306,z58,z3,z4,z5,z6])]],
   [[(0,[z488,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z489,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z490]),(0,[z24,z13,z1,z3,z4,z5,z6])],[(0,[z149,z1,z2,z3,z4,z191,z6]),(0,[z54,z2,z3,z4,z5,z60,z6]),(0,[z1,z69,z2,z3,z4,z303,z6]),(0,[z1,z2,z3,z4,z491,z5,z6]),(0,[z1,z2,z3,z4,z5,z492,z6]),(0,[z493,z1,z2,z3,z4,z5,z6]),(0,[z209,z1,z3,z4,z21,z5,z6]),(1,[z13,z1,z3,z4,z6,z126]),(0,[z1,z2,z3,z49,z4,z6,z25])],[(0,[z1,z2,z3,z4,z494,z5,z6]),(0,[z1,z2,z3,z4,z495,z5,z6]),(0,[z1,z2,z3,z4,z5,z496,z6]),(0,[z1,z2,z3,z4,z5,z497,z6]),(0,[z465,z1,z2,z3,z4,z5,z6])],[(0,[z150,z2,z3,z4,z160,z5,z6]),(1,[z1,z2,z3,z498,z5,z6]),(0,[z1,z2,z3,z4,z499,z5,z6]),(0,[z108,z13,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z500,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z474])],[],[(0,[z1,z2,z130,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z177,z5,z6]),(0,[z501,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z502,z3,z4,z5,z6]),(0,[z503,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z160,z5,z6,z9]),(0,[z1,z2,z3,z4,z5,z6,z504]),(0,[z1,z14,z2,z3,z4,z37,z6])],[(0,[z2,z182,z3,z4,z160,z5,z6]),(0,[z505,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z63,z3,z8,z5,z6])]],
   [[(0,[z13,z54,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z506,z6]),(1,[z13,z1,z3,z4,z60,z6]),(0,[z507,z1,z2,z3,z4,z5,z6])],[(0,[z149,z1,z3,z4,z21,z5,z6]),(0,[z13,z1,z250,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z5,z45,z6])],[(0,[z13,z1,z2,z3,z4,z303,z6]),(0,[z13,z1,z3,z4,z5,z6,z50]),(0,[z1,z2,z508,z3,z4,z5,z6]),(0,[z24,z419,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z509,z5,z6]),(0,[z1,z510,z2,z3,z4,z5,z6])],[(0,[z511,z1,z2,z3,z4,z5,z6]),(0,[z512,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z105,z12,z4,z5,z6]),(0,[z1,z2,z513,z3,z4,z5,z6]),(0,[z13,z1,z58,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z61]),(0,[z1,z2,z514,z3,z4,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z515,z1,z2,z3,z4,z5,z6]),(0,[z1,z207,z3,z4,z21,z5,z6]),(0,[z516,z1,z2,z3,z4,z5,z6]),(0,[z517,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z518,z4,z5,z6]),(0,[z30,z1,z3,z4,z21,z5,z6]),(0,[z1,z2,z519,z3,z4,z5,z6])],[(0,[z520,z1,z2,z3,z4,z5,z6]),(0,[z521,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z73,z4,z21,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z522]),(0,[z523,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z524,z3,z4,z5,z6])]],
   [[(0,[z1,z69,z2,z3,z4,z45,z6])],[(0,[z115,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z525,z3,z4,z5,z6]),(0,[z526,z1,z2,z3,z4,z5,z6]),(0,[z205,z1,z2,z3,z498,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z527])],[(0,[z1,z2,z182,z3,z4,z5,z6]),(0,[z1,z14,z2,z58,z3,z4,z6])],[(0,[z1,z2,z3,z4,z528,z5,z6]),(0,[z127,z2,z3,z4,z5,z60,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z3,z4,z21,z5,z6,z296]),(0,[z181,z1,z2,z3,z4,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z529,z1,z2,z3,z4,z5,z6]),(0,[z205,z2,z3,z4,z5,z60,z6]),(0,[z13,z1,z3,z4,z5,z6,z95]),(0,[z530,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z531,z5,z6]),(0,[z181,z13,z1,z3,z4,z5,z6]),(0,[z532,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z533,z5,z6]),(0,[z1,z2,z534,z3,z4,z5,z6])],[(0,[z2,z3,z4,z160,z5,z60,z6]),(1,[z1,z2,z3,z128,z5,z6]),(0,[z1,z2,z3,z4,z197,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z535]),(0,[z1,z226,z2,z3,z4,z5,z6]),(0,[z17,z536,z2,z3,z4,z5,z6]),(0,[z181,z1,z2,z3,z4,z449,z6]),(1,[z343,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z537,z5,z6]),(0,[z1,z2,z3,z90,z8,z5,z6]),(0,[z13,z1,z72,z3,z4,z5,z6]),(0,[z538,z1,z2,z3,z4,z5,z6]),(0,[z539,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z65,z5,z6]),(1,[z181,z1,z2,z3,z5,z9])],[(0,[z11,z2,z3,z4,z5,z79,z6]),(1,[z1,z418,z3,z4,z5,z6]),(0,[z1,z266,z2,z3,z4,z5,z6])]],
   [[(0,[z540,z1,z2,z3,z4,z5,z6]),(0,[z541,z1,z2,z3,z4,z5,z6]),(0,[z542,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z543,z6]),(1,[z40,z1,z3,z4,z5,z50]),(0,[z1,z3,z4,z5,z175,z6,z50]),(0,[z1,z544,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z545,z4,z5,z6])],[(0,[z1,z2,z546,z3,z4,z5,z6]),(0,[z1,z2,z547,z3,z4,z5,z6]),(0,[z54,z1,z2,z3,z160,z5,z6]),(0,[z13,z1,z2,z3,z4,z45,z6]),(0,[z548,z1,z2,z3,z4,z5,z6]),(1,[z1,z189,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z160,z5,z6]),(0,[z549,z1,z2,z3,z4,z5,z6]),(0,[z24,z1,z69,z2,z3,z4,z6]),(0,[z1,z550,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z551]),(0,[z1,z14,z2,z3,z4,z6,z25])],[(0,[z80,z1,z3,z4,z21,z5,z6]),(0,[z1,z3,z8,z4,z21,z5,z6]),(0,[z1,z2,z3,z552,z4,z5,z6]),(0,[z553,z1,z2,z3,z4,z5,z6]),(0,[z1,z554,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z555]),(0,[z1,z2,z556,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z210,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z557])],[(0,[z1,z2,z3,z74,z5,z6,z25])],[(0,[z1,z2,z370,z3,z4,z5,z6]),(0,[z1,z414,z2,z3,z4,z175,z6])],[(0,[z1,z2,z558,z3,z4,z5,z6]),(0,[z205,z11,z2,z3,z4,z5,z6]),(0,[z1,z41,z3,z73,z4,z5,z6]),(0,[z1,z2,z3,z559,z4,z5,z6]),(0,[z13,z1,z3,z4,z74,z5,z6]),(0,[z1,z2,z3,z4,z5,z560,z6]),(0,[z1,z69,z2,z32,z3,z4,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z561,z6]),(0,[z562,z1,z2,z3,z73,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z563]),(0,[z1,z2,z3,z4,z564,z5,z6])],[(0,[z565,z1,z2,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z303,z5,z6]),(0,[z1,z2,z3,z4,z5,z566,z6]),(1,[z87,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z567]),(0,[z181,z1,z2,z468,z4,z5,z6]),(0,[z1,z2,z568,z3,z4,z5,z6]),(0,[z1,z14,z2,z58,z3,z4,z5])],[(0,[z149,z1,z156,z3,z4,z5,z6]),(0,[z1,z569,z2,z3,z4,z5,z6]),(0,[z562,z1,z2,z3,z4,z5,z6]),(0,[z1,z570,z2,z3,z4,z5,z6]),(0,[z1,z69,z3,z4,z21,z5,z6]),(0,[z181,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z8,z4,z5,z117])],[(0,[z1,z2,z571,z3,z4,z5,z6]),(0,[z205,z1,z2,z3,z128,z5,z6]),(0,[z1,z572,z2,z3,z4,z5,z6]),(0,[z1,z41,z2,z3,z4,z5,z6]),(0,[z1,z2,z573,z3,z4,z5,z6])],[(0,[z574,z1,z2,z3,z4,z5,z6]),(0,[z1,z86,z3,z4,z210,z5,z6]),(1,[z193,z2,z3,z4,z5,z6]),(0,[z1,z575,z2,z3,z4,z5,z6]),(0,[z1,z2,z576,z3,z4,z5,z6])],[(0,[z1,z2,z3,z577,z4,z5,z6]),(0,[z2,z3,z12,z4,z5,z6,z95]),(0,[z578,z1,z2,z3,z4,z5,z6]),(0,[z579,z1,z2,z3,z4,z5,z6]),(0,[z580,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z21,z5,z6,z338]),(1,[z1,z2,z3,z49,z74,z6]),(1,[z1,z556,z3,z4,z5,z6])],[(0,[z581,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z299,z6]),(0,[z13,z1,z3,z4,z129,z5,z6]),(0,[z1,z2,z582,z3,z4,z5,z6])],[(0,[z583,z1,z2,z3,z4,z5,z6]),(0,[z1,z584,z2,z3,z4,z5,z6]),(0,[z585,z1,z2,z3,z4,z5,z6]),(0,[z586,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z126,z88])]],
   [[(0,[z1,z2,z3,z587,z4,z5,z6]),(0,[z54,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z588,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z589]),(1,[z1,z370,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z5,z139,z6]),(0,[z13,z1,z2,z32,z3,z4,z6])],[(0,[z205,z53,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z206,z1,z2,z3,z4,z5,z6]),(1,[z24,z1,z2,z3,z6,z25]),(0,[z1,z2,z590,z3,z4,z5,z6])],[(0,[z1,z591,z2,z3,z4,z5,z6]),(0,[z592,z1,z2,z3,z4,z5,z6]),(0,[z13,z127,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z160,z21,z5,z6]),(1,[z78,z2,z3,z4,z5,z79]),(0,[z1,z2,z593,z3,z4,z5,z6]),(0,[z435,z1,z2,z3,z4,z5,z6]),(0,[z13,z1,z594,z3,z4,z5,z6]),(0,[z1,z325,z3,z4,z21,z5,z6])],[(0,[z595,z1,z2,z3,z4,z5,z6]),(0,[z1,z86,z2,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z21,z5,z6]),(0,[z13,z1,z63,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z596])],[(0,[z1,z2,z3,z597,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z598,z6]),(0,[z599,z1,z2,z3,z4,z5,z6]),(0,[z536,z1,z2,z3,z4,z5,z6]),(0,[z1,z23,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z600,z5,z6]),(0,[z1,z601,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z103,z4,z5,z6]),(1,[z24,z13,z1,z3,z4,z6]),(1,[z536,z2,z3,z4,z5,z6]),(0,[z146,z1,z2,z3,z4,z5,z6])],[(0,[z53,z1,z2,z3,z4,z5,z6]),(1,[z150,z2,z3,z160,z5,z6]),(0,[z602,z1,z2,z3,z4,z5,z6]),(0,[z11,z1,z169,z3,z4,z5,z6]),(1,[z226,z2,z3,z4,z5,z6]),(0,[z1,z2,z32,z4,z129,z5,z6]),(0,[z1,z2,z4,z5,z139,z6,z15]),(1,[z1,z576,z3,z4,z5,z6])],[(0,[z273,z1,z3,z4,z21,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z603]),(0,[z1,z2,z3,z604,z73,z4,z6]),(0,[z1,z86,z2,z72,z4,z5,z6]),(0,[z1,z3,z4,z210,z5,z6,z50]),(0,[z1,z2,z605,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z606,z4,z5,z6])],[(0,[z1,z2,z3,z607,z4,z5,z6]),(0,[z1,z2,z3,z604,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z608]),(0,[z1,z2,z3,z4,z609,z5,z6])],[(0,[z1,z2,z610,z3,z4,z5,z6]),(1,[z13,z1,z3,z4,z303,z6]),(0,[z1,z611,z2,z3,z4,z5,z6]),(0,[z1,z612,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z613,z6]),(0,[z1,z354,z3,z4,z21,z5,z6]),(0,[z290,z1,z2,z3,z4,z5,z6]),(0,[z242,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z614])],[(0,[z1,z2,z3,z4,z5,z615,z6]),(0,[z1,z2,z72,z3,z4,z5,z6])],[(0,[z53,z2,z3,z4,z160,z5,z6]),(0,[z13,z1,z3,z8,z4,z5,z6]),(0,[z13,z250,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z6,z555]),(0,[z1,z2,z616,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z424]),(0,[z1,z2,z3,z4,z5,z617,z6])],[(0,[z1,z2,z3,z4,z5,z618,z6]),(0,[z1,z2,z3,z4,z5,z6,z619])],[(0,[z1,z2,z620,z3,z4,z5,z6]),(0,[z1,z2,z152,z3,z4,z5,z6]),(1,[z108,z13,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z621])],[(0,[z1,z2,z622,z3,z4,z5,z6]),(0,[z149,z2,z3,z4,z5,z60,z6]),(0,[z1,z2,z3,z4,z5,z623,z6]),(0,[z13,z1,z41,z3,z4,z5,z6]),(0,[z1,z2,z3,z101,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z624,z5,z6]),(0,[z1,z625,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z626,z6]),(1,[z419,z2,z3,z4,z5,z6])],[(0,[z1,z169,z2,z3,z4,z5,z6]),(0,[z627,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z628,z6]),(0,[z1,z2,z3,z4,z629,z5,z6])],[(0,[z630,z1,z2,z3,z4,z5,z6]),(0,[z150,z54,z2,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z5,z79,z6]),(0,[z1,z2,z631,z3,z4,z5,z6]),(0,[z17,z1,z3,z4,z21,z5,z6])],[(0,[z205,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z468,z4,z5,z6])],[(0,[z1,z632,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z633]),(0,[z1,z2,z3,z4,z634,z5,z6]),(0,[z1,z2,z635,z3,z4,z5,z6]),(0,[z1,z20,z3,z462,z4,z5,z6]),(0,[z17,z1,z636,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z74,z5,z6])],[(0,[z1,z2,z3,z4,z637,z5,z6]),(0,[z1,z2,z3,z4,z638,z5,z6])],[(0,[z1,z2,z639,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z191,z5,z6]),(0,[z1,z2,z3,z4,z303,z5,z6]),(1,[z1,z3,z4,z5,z6,z424])],[(0,[z1,z2,z3,z640,z4,z5,z6]),(1,[z290,z1,z3,z4,z5,z6]),(0,[z1,z2,z58,z3,z4,z6,z126])]],
   [[(1,[z1,z2,z3,z4,z299,z6]),(1,[z1,z611,z3,z4,z5,z6]),(0,[z1,z2,z3,z641,z4,z5,z6]),(1,[z562,z1,z2,z3,z4,z6]),(0,[z13,z1,z3,z4,z5,z6,z9]),(0,[z1,z2,z3,z4,z175,z6,z316]),(0,[z1,z2,z3,z4,z642,z5,z6])],[(1,[z13,z1,z3,z4,z45,z6]),(0,[z1,z41,z3,z4,z5,z175,z6]),(0,[z643,z1,z2,z3,z4,z5,z6]),(1,[z1,z3,z462,z4,z5,z6]),(0,[z62,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z644]),(0,[z1,z645,z2,z3,z4,z5,z6]),(0,[z646,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z498,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z647]),(0,[z62,z13,z1,z3,z4,z5,z6]),(0,[z1,z418,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z648,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z649])],[(0,[z650,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z651,z5,z6]),(0,[z31,z13,z1,z2,z3,z4,z6]),(1,[z64,z2,z3,z4,z5,z6]),(1,[z516,z2,z3,z4,z5,z6]),(0,[z1,z2,z32,z3,z4,z6,z88])],[(0,[z2,z182,z3,z4,z5,z79,z6]),(0,[z1,z2,z652,z3,z4,z5,z6]),(0,[z653,z1,z2,z3,z4,z5,z6]),(0,[z654,z1,z2,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z10,z5,z6]),(0,[z1,z14,z2,z3,z4,z129,z6]),(0,[z195,z1,z2,z3,z4,z5,z6])],[(0,[z54,z2,z3,z4,z5,z6,z95])],[(0,[z655,z1,z2,z3,z4,z5,z6]),(0,[z656,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z657,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z431,z6]),(1,[z1,z14,z2,z58,z3,z4])],[(0,[z2,z130,z3,z4,z5,z60,z6]),(0,[z658,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z594,z3,z4,z5,z6]),(0,[z1,z3,z4,z21,z5,z6,z126]),(0,[z1,z2,z659,z3,z4,z5,z6]),(0,[z660,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z273,z1,z156,z3,z4,z5,z6]),(0,[z1,z41,z130,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z661,z5,z6]),(0,[z2,z3,z90,z4,z160,z5,z6]),(0,[z1,z2,z3,z4,z21,z5,z6]),(0,[z662,z1,z2,z3,z4,z5,z6])],[(0,[z1,z663,z2,z3,z4,z5,z6]),(1,[z30,z1,z73,z4,z5,z6]),(1,[z209,z1,z3,z210,z5,z6]),(0,[z209,z1,z2,z3,z210,z5,z6]),(0,[z1,z2,z664,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z37,z5,z6]),(0,[z1,z2,z3,z4,z665,z5,z6]),(0,[z666,z1,z2,z3,z4,z5,z6])],[(0,[z149,z273,z2,z3,z4,z5,z6]),(0,[z53,z127,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z21,z5,z439,z6]),(0,[z1,z2,z636,z3,z4,z5,z6])],[(0,[z205,z150,z2,z3,z4,z5,z6]),(0,[z1,z171,z3,z73,z4,z5,z6]),(0,[z1,z3,z103,z4,z210,z5,z6]),(0,[z1,z3,z4,z120,z21,z5,z6]),(0,[z1,z3,z4,z37,z21,z5,z6]),(0,[z465,z2,z3,z4,z5,z6,z9])],[(0,[z209,z1,z171,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z44,z5,z6])],[(0,[z1,z667,z2,z3,z4,z5,z6]),(0,[z668,z1,z2,z3,z4,z5,z6]),(0,[z669,z1,z2,z3,z4,z5,z6]),(0,[z1,z58,z556,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z670,z5,z6]),(0,[z1,z3,z4,z21,z5,z60,z6]),(0,[z205,z1,z611,z3,z4,z5,z6]),(0,[z108,z13,z1,z3,z4,z5,z6]),(1,[z1,z2,z20,z10,z5,z6]),(0,[z671,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z672,z3,z4,z5,z6]),(0,[z1,z673,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z674])],[(0,[z1,z171,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z129,z5,z6,z88]),(0,[z675,z1,z2,z3,z4,z5,z6])]],
   [[(1,[z1,z2,z3,z604,z4,z6]),(0,[z1,z3,z4,z210,z21,z5,z6]),(0,[z1,z2,z3,z4,z177,z210,z6]),(1,[z13,z1,z32,z3,z4,z6]),(1,[z1,z3,z4,z5,z6,z474])],[(0,[z1,z2,z676,z3,z4,z5,z6]),(0,[z677,z1,z2,z3,z4,z5,z6]),(0,[z678,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z679,z6]),(0,[z13,z1,z14,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z680])],[(1,[z149,z156,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z74,z6,z126]),(0,[z681,z1,z2,z3,z4,z5,z6])],[(0,[z682,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z303,z6,z126]),(0,[z1,z2,z683,z3,z4,z5,z6]),(0,[z31,z13,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z21,z5,z117,z6]),(1,[z1,z636,z3,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z684,z5,z6]),(1,[z62,z1,z2,z63,z5,z6]),(0,[z17,z1,z2,z105,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z685]),(0,[z1,z2,z3,z49,z4,z74,z6])],[(0,[z127,z2,z3,z4,z5,z6,z95]),(0,[z1,z2,z686,z3,z4,z5,z6]),(0,[z687,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z79,z6]),(0,[z209,z13,z1,z3,z4,z5,z6]),(0,[z62,z516,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z555,z15]),(0,[z181,z1,z576,z3,z4,z5,z6])]],
   [[(1,[z11,z2,z3,z4,z303,z6]),(0,[z205,z2,z3,z4,z5,z6,z95]),(0,[z330,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z688,z3,z4,z5,z6]),(0,[z1,z689,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z690,z4,z5,z6]),(0,[z1,z171,z3,z103,z4,z5,z6]),(0,[z691,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z692,z5,z6])],[(0,[z1,z2,z693,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z694,z6]),(0,[z13,z1,z105,z3,z4,z5,z6]),(0,[z1,z69,z2,z3,z4,z21,z6])],[(0,[z1,z2,z3,z4,z695,z5,z6]),(1,[z1,z171,z3,z103,z5,z6]),(0,[z1,z2,z3,z4,z696,z5,z6])],[(0,[z1,z2,z3,z4,z5,z697,z6]),(0,[z698,z1,z2,z3,z4,z5,z6]),(0,[z150,z127,z2,z3,z4,z5,z6]),(0,[z1,z2,z699,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z700]),(0,[z1,z2,z3,z701,z4,z5,z6]),(0,[z40,z1,z3,z4,z21,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z9]),(0,[z1,z14,z2,z3,z4,z5,z6])],[(0,[z149,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z702,z3,z4,z5,z6]),(0,[z2,z3,z4,z303,z5,z60,z6]),(0,[z1,z2,z703,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z88]),(0,[z1,z2,z3,z8,z5,z117,z6])],[(0,[z149,z13,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z704,z6]),(0,[z1,z2,z3,z4,z5,z6,z705]),(0,[z1,z2,z182,z4,z5,z6,z15]),(0,[z1,z41,z3,z4,z210,z5,z6]),(0,[z1,z2,z3,z706,z4,z5,z6]),(0,[z1,z3,z4,z21,z5,z175,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z707,z4,z5,z6]),(0,[z1,z2,z3,z708,z4,z6]),(0,[z709,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z710]),(0,[z310,z3,z4,z21,z5,z6]),(0,[z1,z3,z4,z711,z65,z6])],[(0,[z108,z13,z3,z4,z303,z6]),(0,[z1,z2,z3,z4,z712,z6]),(0,[z24,z1,z3,z21,z6,z25])],[(0,[z13,z1,z3,z4,z18,z6]),(0,[z135,z2,z3,z4,z5,z6]),(0,[z13,z713,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z6,z26]),(0,[z714,z2,z3,z4,z5,z6]),(0,[z2,z715,z3,z4,z5,z6]),(0,[z716,z2,z3,z4,z5,z6])],[(0,[z205,z2,z3,z4,z5,z603]),(0,[z2,z3,z4,z5,z6,z36]),(0,[z663,z2,z3,z4,z60,z6]),(0,[z13,z219,z3,z4,z5,z6]),(0,[z13,z250,z3,z4,z45,z6]),(0,[z1,z3,z4,z21,z6,z316]),(0,[z62,z516,z2,z63,z5,z6]),(0,[z1,z576,z468,z4,z5,z6])],[(0,[z1,z2,z3,z717,z5,z6]),(0,[z1,z2,z718,z4,z5,z6]),(0,[z13,z1,z105,z4,z5,z139]),(0,[z13,z310,z3,z4,z5,z6]),(0,[z135,z2,z3,z4,z449,z6])],[(0,[z2,z3,z4,z5,z6,z719]),(0,[z1,z3,z4,z5,z6,z424]),(0,[z720,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z721,z5,z6]),(0,[z722,z1,z3,z4,z5,z6]),(0,[z205,z13,z3,z4,z5,z95]),(0,[z290,z1,z3,z4,z5,z6]),(0,[z723,z2,z3,z4,z5,z6]),(0,[z1,z2,z724,z20,z5,z6]),(0,[z1,z2,z4,z5,z139,z725]),(0,[z726,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z299,z6]),(0,[z1,z611,z3,z4,z5,z6]),(0,[z1,z152,z3,z4,z5,z6]),(0,[z127,z2,z77,z4,z5,z6]),(0,[z562,z1,z2,z3,z4,z6]),(0,[z1,z2,z727,z4,z5,z6]),(0,[z728,z2,z3,z4,z5,z6]),(0,[z146,z13,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z729]),(0,[z162,z1,z2,z3,z6,z25])]],
   [[(0,[z505,z2,z12,z4,z5,z6]),(0,[z13,z1,z3,z4,z45,z6])],[(0,[z2,z3,z730,z4,z5,z6]),(0,[z205,z2,z3,z4,z5,z619]),(0,[z1,z2,z3,z4,z65,z6]),(0,[z1,z2,z3,z320,z74,z6])],[(0,[z64,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z731]),(0,[z13,z1,z3,z4,z65,z6]),(0,[z473,z13,z1,z3,z4,z6]),(0,[z732,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z733,z6]),(0,[z1,z2,z734,z4,z5,z6]),(0,[z1,z2,z3,z735,z5,z6]),(0,[z562,z1,z171,z3,z4,z6]),(0,[z162,z13,z1,z3,z4,z6]),(0,[z1,z736,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z737,z6]),(0,[z17,z1,z636,z4,z5,z15]),(0,[z17,z1,z2,z4,z5,z725]),(0,[z1,z2,z3,z4,z362,z126])],[],[(0,[z1,z3,z4,z738,z5,z6]),(0,[z739,z1,z3,z4,z197,z6]),(0,[z13,z1,z3,z4,z177,z6]),(0,[z195,z13,z14,z3,z4,z6]),(1,[z1,z2,z3,z6,z729])],[(0,[z740,z1,z2,z4,z5,z6]),(0,[z1,z3,z4,z741,z60,z6]),(0,[z1,z742,z73,z4,z5,z6]),(0,[z24,z13,z1,z3,z225,z6]),(0,[z13,z1,z3,z4,z83,z6]),(0,[z1,z414,z3,z4,z6,z50]),(0,[z1,z2,z4,z5,z6,z725]),(0,[z743,z2,z3,z4,z5,z6])]],
   [[(0,[z542,z2,z3,z4,z5,z95]),(0,[z1,z2,z744,z4,z5,z6]),(0,[z11,z2,z173,z4,z5,z6]),(0,[z80,z562,z1,z3,z4,z6]),(0,[z289,z1,z3,z4,z5,z272]),(0,[z108,z13,z3,z4,z45,z6]),(0,[z1,z69,z3,z4,z6,z474]),(0,[z193,z3,z4,z21,z5,z6]),(0,[z1,z745,z3,z4,z5,z6]),(0,[z135,z2,z468,z4,z5,z6]),(0,[z1,z14,z306,z3,z4,z6])],[(0,[z1,z2,z3,z4,z746,z6]),(0,[z1,z3,z4,z747,z5,z6]),(0,[z13,z536,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z748]),(0,[z1,z2,z749,z3,z4,z6])],[(0,[z13,z1,z3,z4,z191,z6]),(0,[z1,z2,z750,z4,z5,z6]),(0,[z13,z250,z32,z3,z4,z6]),(0,[z13,z1,z3,z420,z4,z6]),(0,[z1,z3,z8,z21,z5,z117]),(0,[z1,z354,z207,z3,z4,z5]),(0,[z1,z2,z3,z101,z5,z6])],[(0,[z751,z1,z3,z4,z5,z6]),(0,[z752,z1,z3,z4,z5,z6]),(0,[z13,z1,z3,z101,z5,z6]),(0,[z13,z1,z3,z4,z99,z6]),(0,[z1,z2,z376,z8,z5,z6]),(0,[z1,z2,z3,z4,z753,z6])],[(0,[z1,z2,z3,z4,z754,z6]),(0,[z13,z127,z182,z4,z5,z6]),(0,[z13,z1,z3,z4,z197,z6]),(0,[z30,z1,z742,z4,z5,z6]),(0,[z31,z13,z193,z3,z4,z6]),(0,[z1,z2,z3,z4,z755,z6]),(0,[z1,z2,z756,z4,z5,z6]),(0,[z297,z161,z3,z4,z5,z6]),(0,[z181,z297,z2,z3,z5,z9])],[(0,[z1,z2,z3,z4,z757,z6]),(0,[z1,z2,z20,z10,z5,z6]),(0,[z1,z758,z3,z4,z5,z6]),(0,[z1,z759,z3,z4,z5,z6])],[(0,[z1,z760,z3,z4,z5,z6]),(0,[z13,z78,z3,z4,z5,z79]),(0,[z761,z2,z3,z4,z5,z6]),(0,[z1,z69,z3,z4,z762,z6]),(0,[z1,z2,z3,z116,z5,z6]),(0,[z1,z2,z3,z4,z763,z6]),(0,[z1,z2,z3,z764,z5,z6]),(0,[z24,z242,z1,z3,z6,z25])],[(0,[z53,z2,z765,z4,z5,z6]),(0,[z1,z3,z4,z766,z5,z6]),(0,[z1,z2,z3,z604,z4,z6]),(0,[z13,z1,z32,z3,z4,z6]),(0,[z13,z1,z3,z116,z5,z6])]],
   [[(0,[z1,z156,z3,z4,z191,z6]),(0,[z13,z1,z211,z4,z5,z6]),(0,[z767,z3,z4,z21,z5,z6]),(0,[z1,z3,z768,z4,z5,z6]),(0,[z769,z2,z3,z4,z5,z6]),(0,[z1,z770,z3,z4,z5,z6]),(0,[z771,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z117,z772])],[(0,[z1,z3,z4,z21,z5,z6]),(0,[z149,z156,z3,z4,z5,z6]),(0,[z773,z1,z3,z4,z5,z6]),(0,[z108,z2,z3,z4,z60,z6]),(0,[z3,z4,z21,z5,z6,z555]),(0,[z1,z3,z4,z774,z5,z6])],[(0,[z2,z3,z4,z5,z79,z307]),(0,[z256,z250,z3,z4,z5,z6]),(0,[z13,z775,z3,z4,z5,z6]),(1,[z1,z2,z724,z5,z6]),(0,[z1,z776,z3,z4,z5,z6])],[(0,[z13,z1,z3,z4,z121,z6]),(0,[z1,z777,z3,z4,z5,z6]),(0,[z1,z3,z4,z21,z449,z6]),(0,[z536,z636,z3,z4,z5,z6]),(0,[z778,z1,z2,z3,z4,z6]),(0,[z779,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z780,z6]),(0,[z13,z1,z3,z4,z355,z6]),(0,[z1,z414,z41,z3,z4,z175]),(0,[z781,z2,z3,z4,z5,z6]),(0,[z297,z2,z376,z4,z5,z6]),(0,[z1,z2,z468,z4,z83,z6])],[(0,[z2,z3,z4,z5,z6,z782]),(0,[z1,z2,z3,z4,z6,z729])],[(0,[z1,z2,z3,z4,z783,z6]),(0,[z1,z784,z3,z4,z5,z6]),(0,[z785,z1,z3,z462,z4,z6]),(0,[z523,z1,z2,z4,z5,z15])],[(0,[z1,z2,z3,z786,z5,z6]),(0,[z11,z2,z3,z4,z303,z6]),(0,[z787,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z788,z3,z4,z5,z6]),(0,[z1,z152,z3,z498,z5,z6]),(0,[z1,z611,z3,z498,z5,z6]),(0,[z30,z1,z604,z73,z4,z6]),(0,[z1,z2,z3,z4,z6,z789]),(0,[z1,z2,z749,z3,z4,z5])],[(0,[z108,z130,z3,z4,z5,z6]),(0,[z1,z3,z790,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z791]),(0,[z1,z3,z4,z792,z5,z6]),(0,[z793,z2,z3,z4,z5,z6])],[(0,[z2,z3,z765,z4,z5,z6]),(0,[z1,z2,z3,z794,z4,z6]),(0,[z1,z2,z4,z5,z6,z795]),(0,[z31,z13,z1,z3,z4,z6]),(0,[z13,z796,z3,z4,z5,z6])],[(0,[z1,z2,z3,z797,z5,z6]),(0,[z668,z2,z3,z90,z5,z6]),(0,[z1,z798,z3,z4,z5,z6]),(0,[z343,z1,z3,z4,z303,z6]),(0,[z1,z3,z4,z799,z5,z6]),(0,[z228,z1,z3,z4,z21,z6]),(0,[z1,z3,z800,z462,z4,z6]),(0,[z1,z2,z582,z10,z5,z6])],[(0,[z1,z2,z105,z4,z5,z422]),(0,[z482,z108,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z7,z6]),(0,[z419,z3,z4,z21,z5,z6]),(0,[z465,z3,z4,z21,z5,z6]),(0,[z801,z2,z3,z4,z5,z6])],[(0,[z1,z802,z3,z4,z5,z6]),(0,[z803,z1,z3,z4,z5,z6]),(0,[z13,z1,z91,z3,z4,z6]),(0,[z1,z3,z4,z804,z5,z6]),(0,[z1,z3,z49,z4,z805,z6]),(0,[z1,z2,z3,z806,z5,z6]),(0,[z807,z2,z3,z4,z5,z6]),(0,[z808,z2,z3,z4,z5,z6]),(0,[z809,z2,z3,z4,z5,z6]),(0,[z810,z2,z3,z4,z5,z6])],[(0,[z1,z811,z3,z4,z5,z6]),(0,[z1,z812,z3,z4,z5,z6]),(0,[z195,z2,z3,z4,z197,z6]),(0,[z13,z1,z3,z806,z5,z6]),(0,[z813,z2,z3,z4,z5,z6]),(0,[z1,z814,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z725,z15]),(0,[z1,z3,z815,z4,z5,z6]),(0,[z1,z3,z4,z816,z5,z6])],[(0,[z1,z2,z3,z817,z5,z6]),(0,[z2,z818,z3,z4,z5,z6]),(0,[z1,z3,z101,z21,z5,z6])]],
   [[(0,[z1,z819,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z820,z6]),(0,[z1,z2,z3,z821,z5,z6]),(0,[z1,z169,z3,z4,z60,z6]),(0,[z295,z1,z14,z3,z4,z6]),(0,[z2,z822,z3,z4,z5,z6]),(0,[z62,z1,z63,z21,z5,z6]),(0,[z31,z1,z4,z6,z202,z88])],[(0,[z13,z1,z3,z4,z6,z178]),(0,[z1,z3,z103,z804,z5,z6]),(0,[z13,z1,z3,z4,z6,z180]),(0,[z1,z3,z823,z4,z5,z6])],[(0,[z1,z2,z3,z4,z824,z6]),(0,[z2,z182,z173,z4,z5,z6]),(0,[z13,z1,z3,z4,z6,z367]),(0,[z13,z1,z3,z4,z6,z185])],[(0,[z1,z2,z3,z4,z825,z6]),(0,[z562,z1,z41,z3,z4,z6]),(0,[z1,z2,z3,z4,z826,z6])],[(0,[z1,z2,z3,z4,z827,z6]),(0,[z149,z156,z3,z4,z299,z6]),(0,[z1,z2,z173,z4,z5,z6]),(0,[z13,z1,z3,z4,z428,z6]),(0,[z2,z173,z4,z5,z60,z6]),(0,[z13,z1,z3,z4,z741,z6]),(0,[z1,z2,z3,z498,z197,z6]),(0,[z828,z3,z4,z21,z5,z6]),(0,[z1,z829,z3,z4,z5,z6])],[(0,[z1,z2,z830,z4,z5,z6])],[(0,[z1,z2,z831,z3,z5,z6]),(0,[z832,z1,z2,z3,z4,z6]),(0,[z11,z152,z3,z4,z5,z6]),(0,[z1,z2,z3,z833,z5,z6]),(0,[z1,z2,z3,z4,z5,z834]),(0,[z1,z835,z3,z4,z5,z6]),(0,[z666,z1,z2,z63,z5,z6])],[(0,[z228,z1,z2,z3,z4,z6]),(0,[z13,z1,z3,z833,z5,z6]),(0,[z13,z1,z3,z4,z5,z834]),(0,[z516,z3,z4,z21,z5,z6]),(0,[z1,z3,z4,z836,z5,z6])]],
   [[(0,[z837,z2,z3,z4,z5,z6]),(0,[z40,z1,z3,z4,z5,z838]),(0,[z1,z2,z3,z74,z6,z729])],[(0,[z1,z839,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z840,z6]),(0,[z841,z2,z3,z4,z5,z6])],[(0,[z1,z152,z3,z128,z5,z6]),(0,[z1,z611,z3,z128,z5,z6]),(0,[z1,z3,z4,z6,z474,z316]),(0,[z24,z1,z3,z6,z424,z25])],[(0,[z295,z130,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z842]),(0,[z843,z2,z3,z4,z5,z6]),(0,[z844,z2,z3,z4,z5,z6]),(0,[z845,z1,z3,z4,z5,z6]),(0,[z17,z16,z2,z4,z5,z15])],[(0,[z1,z2,z3,z4,z846,z6]),(0,[z847,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z21,z6,z443]),(0,[z13,z1,z3,z4,z533,z6]),(0,[z1,z3,z4,z848,z99,z6]),(0,[z1,z14,z2,z749,z3,z4])],[(0,[z849,z1,z2,z3,z4,z6]),(0,[z53,z13,z12,z4,z5,z6]),(0,[z850,z2,z3,z4,z5,z6]),(1,[z1,z2,z749,z3,z4])],[(0,[z851,z2,z3,z4,z5,z6]),(0,[z1,z2,z852,z4,z5,z6]),(0,[z31,z290,z1,z3,z4,z6]),(0,[z1,z853,z3,z4,z5,z6])],[(0,[z2,z12,z4,z5,z6,z102]),(0,[z59,z2,z3,z4,z60,z6]),(0,[z2,z3,z498,z5,z6,z95]),(0,[z465,z13,z3,z4,z5,z6])]],
   [[(0,[z538,z130,z3,z4,z5,z6]),(0,[z11,z2,z3,z4,z191,z6]),(0,[z215,z2,z3,z4,z60,z6]),(0,[z1,z97,z3,z210,z5,z6]),(0,[z250,z2,z3,z4,z6,z126]),(0,[z1,z2,z3,z4,z5,z854])],[(0,[z1,z2,z3,z4,z855,z6]),(0,[z13,z1,z3,z4,z6,z235]),(0,[z13,z1,z310,z3,z4,z6]),(0,[z62,z2,z63,z219,z5,z6]),(0,[z856,z1,z3,z4,z5,z6])],[(0,[z127,z182,z4,z21,z5,z6]),(0,[z11,z2,z3,z4,z197,z6]),(0,[z40,z1,z3,z4,z5,z272]),(0,[z857,z2,z3,z4,z5,z6]),(0,[z858,z2,z3,z4,z5,z6]),(0,[z24,z242,z1,z3,z4,z6]),(0,[z181,z1,z2,z3,z83,z9])],[(0,[z1,z2,z3,z859,z5,z6]),(0,[z13,z54,z3,z4,z60,z6]),(0,[z860,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z861,z5,z6])],[(0,[z13,z1,z3,z4,z244,z6]),(0,[z13,z1,z3,z4,z805,z6]),(0,[z1,z3,z4,z862,z5,z6])],[(0,[z2,z285,z3,z160,z5,z6]),(0,[z2,z3,z4,z821,z5,z6]),(0,[z206,z228,z1,z3,z4,z6]),(0,[z1,z3,z4,z861,z449,z6])],[(0,[z1,z2,z3,z128,z197,z6]),(0,[z228,z1,z3,z73,z4,z6]),(0,[z863,z2,z3,z4,z5,z6]),(0,[z864,z2,z3,z4,z5,z6]),(0,[z1,z2,z724,z3,z5,z6]),(0,[z181,z1,z2,z468,z5,z9])],[(0,[z108,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z303,z757,z6]),(0,[z1,z3,z498,z21,z5,z6]),(0,[z195,z13,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z772]),(0,[z1,z3,z4,z37,z474,z126])]],
   [[(0,[z205,z13,z3,z4,z60,z6]),(0,[z209,z228,z1,z3,z4,z6]),(0,[z13,z14,z230,z3,z4,z6]),(0,[z13,z230,z2,z3,z4,z6]),(0,[z206,z1,z3,z5,z6,z61])],[(0,[z1,z2,z3,z4,z865,z6]),(1,[z13,z230,z3,z4,z6]),(0,[z195,z866,z3,z4,z5,z6])],[(0,[z16,z2,z3,z4,z5,z6]),(0,[z465,z2,z3,z90,z5,z6]),(0,[z1,z23,z3,z4,z5,z6]),(0,[z108,z250,z3,z4,z5,z6]),(0,[z1,z867,z3,z4,z5,z6]),(0,[z536,z23,z3,z4,z5,z6]),(0,[z24,z310,z2,z3,z6,z25]),(0,[z242,z1,z3,z49,z4,z6])],[(0,[z273,z868,z3,z4,z5,z6]),(0,[z152,z3,z4,z5,z60,z6]),(0,[z13,z1,z3,z4,z6,z265]),(0,[z1,z3,z869,z4,z5,z6])],[(0,[z209,z1,z3,z177,z210,z6]),(1,[z13,z226,z3,z4,z6]),(0,[z13,z1,z3,z870,z4,z6]),(0,[z1,z3,z4,z5,z6,z871])],[(0,[z127,z2,z765,z4,z5,z6]),(0,[z1,z2,z173,z498,z5,z6]),(0,[z1,z2,z724,z4,z5,z6]),(0,[z872,z2,z3,z4,z5,z6]),(0,[z1,z873,z3,z4,z5,z6])],[(0,[z13,z3,z12,z4,z60,z6]),(0,[z1,z2,z3,z4,z874,z6]),(0,[z393,z2,z3,z160,z5,z6]),(0,[z13,z1,z3,z4,z6,z271]),(0,[z31,z13,z226,z3,z4,z6]),(0,[z1,z2,z105,z4,z5,z139]),(0,[z1,z2,z3,z49,z6,z729]),(0,[z135,z576,z3,z4,z5,z6])],[(0,[z875,z2,z3,z4,z5,z6])]],
   [[(0,[z205,z2,z3,z4,z5,z95]),(0,[z1,z2,z3,z4,z876,z6]),(0,[z209,z1,z3,z804,z5,z6]),(0,[z2,z3,z4,z5,z6,z877])],[(0,[z146,z2,z3,z4,z5,z6]),(0,[z54,z2,z3,z657,z5,z6]),(0,[z2,z3,z4,z5,z6,z878]),(0,[z879,z1,z3,z4,z5,z6]),(0,[z195,z880,z3,z4,z5,z6])],[(0,[z1,z2,z881,z4,z5,z6]),(0,[z1,z882,z2,z3,z4,z6]),(0,[z250,z3,z4,z5,z6,z272]),(0,[z1,z306,z3,z4,z5,z6]),(0,[z242,z1,z14,z3,z4,z6]),(0,[z2,z3,z4,z5,z6,z883]),(0,[z1,z884,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z684,z126]),(0,[z13,z1,z3,z4,z564,z6])],[(0,[z562,z885,z2,z3,z4,z6]),(0,[z1,z161,z3,z4,z5,z6]),(0,[z13,z226,z3,z4,z5,z6]),(0,[z1,z886,z3,z4,z5,z6]),(0,[z887,z2,z3,z4,z5,z6]),(0,[z536,z2,z3,z4,z65,z6])],[(0,[z1,z2,z3,z4,z888,z6]),(0,[z1,z889,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z286,z6]),(0,[z890,z2,z3,z4,z5,z6]),(0,[z13,z250,z3,z4,z21,z6]),(0,[z31,z1,z2,z43,z4,z6])],[(0,[z1,z169,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z891]),(0,[z13,z127,z3,z4,z60,z6]),(0,[z13,z1,z3,z4,z286,z6]),(0,[z13,z1,z3,z147,z4,z6]),(0,[z242,z1,z3,z4,z6,z126]),(0,[z1,z161,z3,z4,z449,z6]),(0,[z1,z2,z3,z4,z5,z772])],[(0,[z1,z3,z134,z4,z5,z6]),(0,[z361,z13,z1,z3,z4,z6]),(0,[z1,z41,z3,z4,z5,z838]),(0,[z892,z1,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z893,z4,z6]),(0,[z2,z3,z90,z498,z5,z6]),(0,[z1,z2,z3,z4,z177,z6]),(0,[z13,z1,z894,z4,z5,z6]),(0,[z87,z3,z4,z21,z5,z6]),(0,[z895,z2,z3,z4,z5,z6]),(0,[z896,z2,z3,z4,z5,z6])],[(0,[z13,z1,z3,z4,z6,z296]),(0,[z13,z1,z897,z4,z5,z6]),(0,[z13,z230,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z83,z6]),(0,[z1,z898,z3,z4,z5,z6]),(0,[z1,z3,z4,z899,z5,z6])],[(0,[z13,z1,z3,z4,z21,z6]),(0,[z1,z3,z4,z21,z762,z6]),(0,[z1,z2,z105,z4,z5,z725]),(0,[z1,z576,z3,z4,z83,z6])],[(0,[z228,z1,z41,z3,z4,z6]),(0,[z1,z2,z3,z4,z291,z126]),(0,[z900,z1,z3,z4,z99,z6]),(0,[z901,z1,z3,z4,z65,z6]),(0,[z17,z1,z2,z4,z65,z15])],[(0,[z1,z2,z3,z4,z191,z6]),(0,[z295,z250,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z634,z6]),(0,[z1,z2,z376,z4,z5,z6]),(0,[z902,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z6,z729,z25])],[(0,[z310,z2,z3,z4,z5,z6]),(0,[z903,z1,z3,z4,z5,z6]),(0,[z13,z1,z376,z4,z5,z6]),(0,[z62,z1,z2,z724,z5,z6]),(0,[z1,z2,z3,z4,z99,z6]),(0,[z536,z2,z3,z101,z5,z6]),(0,[z536,z2,z3,z4,z99,z6])],[(0,[z13,z1,z3,z4,z528,z6]),(0,[z1,z2,z3,z4,z197,z6]),(0,[z904,z2,z3,z4,z5,z6]),(0,[z181,z1,z161,z3,z5,z9]),(0,[z1,z2,z376,z4,z449,z6])],[(0,[z1,z868,z3,z4,z5,z6]),(0,[z1,z2,z173,z128,z5,z6]),(0,[z64,z2,z4,z5,z6,z15])]],
   [[(0,[z59,z295,z3,z4,z60,z6]),(0,[z1,z414,z3,z4,z21,z6]),(0,[z1,z3,z4,z905,z5,z6])],[(0,[z295,z1,z3,z4,z5,z6]),(0,[z1,z906,z3,z4,z5,z6]),(0,[z78,z3,z4,z21,z5,z79]),(0,[z907,z2,z3,z4,z5,z6]),(0,[z1,z908,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z909,z6]),(0,[z228,z1,z3,z103,z4,z6]),(0,[z13,z1,z3,z4,z6,z316]),(0,[z910,z2,z3,z4,z5,z6]),(0,[z536,z2,z3,z116,z5,z6])],[(0,[z868,z130,z3,z4,z5,z6]),(0,[z1,z2,z211,z4,z5,z6]),(0,[z1,z911,z3,z4,z5,z6]),(0,[z912,z1,z3,z4,z5,z6]),(0,[z1,z171,z3,z479,z5,z6]),(0,[z13,z1,z3,z4,z319,z6]),(0,[z1,z161,z468,z4,z5,z6])],[(0,[z1,z2,z3,z4,z6,z913]),(0,[z1,z32,z3,z870,z4,z6]),(0,[z181,z465,z2,z3,z5,z9]),(0,[z1,z2,z58,z749,z3,z4])],[(0,[z53,z2,z351,z4,z5,z6]),(0,[z2,z219,z3,z4,z5,z6]),(0,[z1,z2,z3,z914,z5,z6]),(0,[z526,z13,z1,z3,z4,z6]),(0,[z536,z3,z4,z21,z5,z6]),(0,[z1,z2,z3,z915,z5,z6]),(0,[z17,z1,z2,z101,z5,z15])],[(0,[z53,z2,z173,z4,z5,z6]),(0,[z11,z370,z3,z4,z303,z6]),(0,[z209,z1,z3,z44,z5,z6]),(0,[z108,z13,z3,z4,z191,z6]),(0,[z13,z1,z3,z134,z4,z6]),(0,[z226,z3,z4,z21,z5,z6]),(0,[z1,z3,z82,z122,z5,z6]),(0,[z1,z2,z3,z916,z4,z6])],[(0,[z149,z3,z4,z5,z439,z6]),(0,[z1,z917,z3,z4,z5,z6]),(0,[z1,z325,z73,z4,z5,z6]),(0,[z1,z3,z4,z194,z5,z6]),(0,[z1,z918,z3,z4,z5,z6]),(0,[z14,z230,z2,z58,z3,z4])],[(0,[z1,z2,z919,z4,z5,z6]),(0,[z1,z920,z3,z4,z5,z6]),(0,[z1,z2,z921,z4,z5,z6]),(0,[z30,z562,z1,z3,z4,z6]),(0,[z1,z171,z3,z225,z5,z6]),(0,[z13,z922,z3,z4,z5,z6]),(0,[z277,z1,z3,z225,z5,z6]),(0,[z1,z3,z4,z762,z45,z6]),(0,[z923,z2,z3,z4,z5,z6]),(0,[z924,z2,z3,z4,z5,z6]),(0,[z925,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z20,z10,z21,z5,z6]),(0,[z1,z354,z414,z3,z4,z6]),(0,[z1,z926,z3,z4,z5,z6]),(0,[z1,z927,z3,z4,z5,z6]),(0,[z17,z1,z2,z116,z5,z15]),(0,[z1,z306,z3,z4,z6,z126])],[(0,[z1,z2,z3,z4,z928,z6]),(0,[z205,z2,z3,z498,z5,z95]),(0,[z1,z929,z3,z4,z5,z6])],[(0,[z1,z930,z3,z4,z5,z6]),(0,[z529,z1,z2,z4,z5,z15]),(0,[z108,z13,z32,z3,z4,z6]),(0,[z24,z13,z310,z3,z4,z6]),(0,[z1,z2,z931,z3,z5,z6]),(0,[z1,z3,z4,z932,z5,z6])],[(0,[z78,z2,z3,z498,z5,z6]),(0,[z562,z1,z3,z4,z210,z6]),(0,[z1,z3,z4,z6,z710,z126])],[(0,[z1,z2,z3,z933,z5,z6]),(0,[z1,z2,z934,z4,z5,z6]),(0,[z3,z4,z21,z5,z6,z36])],[(0,[z250,z2,z3,z4,z5,z6]),(0,[z54,z2,z3,z821,z5,z6]),(0,[z2,z3,z4,z5,z79,z327]),(0,[z13,z1,z3,z4,z131,z6]),(0,[z13,z1,z3,z4,z5,z935])],[(0,[z1,z2,z936,z4,z5,z6]),(0,[z13,z130,z3,z4,z60,z6]),(0,[z1,z2,z3,z498,z286,z6]),(0,[z1,z2,z937,z3,z5,z6]),(0,[z938,z2,z3,z4,z5,z6]),(0,[z461,z1,z43,z4,z5,z6]),(0,[z13,z1,z427,z3,z4,z6]),(0,[z1,z2,z749,z3,z4,z126]),(0,[z1,z939,z3,z4,z5,z6])],[(0,[z2,z765,z12,z4,z5,z6]),(0,[z104,z1,z73,z4,z5,z6]),(0,[z13,z1,z32,z4,z129,z6]),(0,[z1,z2,z3,z940,z5,z6])]],
   [[(0,[z13,z1,z3,z4,z348,z6]),(0,[z31,z13,z250,z3,z4,z6]),(0,[z13,z64,z3,z4,z5,z6]),(0,[z1,z376,z4,z21,z5,z6]),(0,[z1,z2,z3,z4,z941,z6]),(0,[z942,z1,z3,z4,z449,z6])],[(0,[z1,z611,z3,z4,z197,z6]),(0,[z13,z1,z590,z3,z4,z6]),(0,[z16,z636,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z943])],[(0,[z188,z13,z1,z3,z4,z6]),(0,[z13,z1,z3,z4,z6,z358]),(0,[z135,z3,z4,z21,z5,z6]),(0,[z944,z2,z3,z4,z5,z6])],[(0,[z13,z1,z3,z4,z661,z6]),(0,[z1,z266,z3,z4,z5,z6]),(0,[z290,z1,z32,z3,z4,z6]),(0,[z181,z135,z2,z3,z5,z9]),(0,[z181,z1,z2,z3,z5,z772])],[(0,[z1,z945,z3,z4,z5,z6]),(0,[z1,z946,z3,z4,z5,z6]),(0,[z1,z2,z947,z4,z5,z6]),(0,[z1,z2,z3,z4,z948,z6])],[(0,[z53,z12,z4,z21,z5,z6]),(0,[z410,z2,z182,z4,z5,z6]),(0,[z1,z949,z3,z4,z5,z6]),(0,[z1,z3,z128,z21,z5,z6]),(0,[z1,z950,z2,z3,z4,z6]),(0,[z13,z1,z3,z4,z37,z126]),(0,[z24,z419,z2,z3,z6,z25])],[(0,[z951,z2,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z194,z6]),(0,[z109,z3,z4,z5,z439,z6])],[(0,[z13,z1,z3,z4,z5,z6]),(0,[z330,z130,z3,z4,z5,z6]),(0,[z1,z3,z4,z21,z299,z6]),(0,[z1,z952,z3,z4,z5,z6]),(0,[z295,z1,z3,z4,z6,z126]),(0,[z562,z1,z3,z4,z6,z50]),(0,[z1,z41,z3,z4,z5,z270]),(0,[z24,z13,z1,z3,z44,z6]),(0,[z1,z3,z4,z37,z21,z126])]],
   [[(0,[z1,z2,z953,z4,z5,z6]),(0,[z150,z13,z3,z160,z5,z6]),(0,[z31,z13,z1,z43,z4,z6]),(0,[z310,z69,z2,z3,z4,z6]),(0,[z1,z20,z462,z10,z5,z6])],[(0,[z228,z850,z2,z3,z4,z6]),(0,[z13,z1,z3,z4,z449,z6]),(0,[z954,z414,z2,z3,z4,z6]),(0,[z1,z866,z3,z4,z5,z6])],[(0,[z1,z41,z3,z4,z5,z615]),(0,[z1,z2,z3,z4,z955,z6]),(0,[z13,z1,z324,z3,z4,z6]),(0,[z1,z2,z3,z956,z5,z6]),(0,[z1,z2,z32,z22,z4,z6]),(0,[z64,z3,z4,z21,z5,z6])],[(0,[z1,z2,z211,z498,z5,z6]),(0,[z205,z2,z3,z128,z5,z95]),(0,[z2,z3,z4,z5,z957,z95]),(0,[z13,z1,z3,z956,z5,z6]),(0,[z2,z3,z4,z5,z6,z958]),(0,[z1,z636,z3,z4,z65,z6]),(0,[z17,z2,z4,z5,z555,z15])],[(0,[z54,z2,z3,z90,z5,z6]),(0,[z13,z250,z3,z49,z4,z6]),(0,[z1,z2,z3,z4,z959,z6])],[(0,[z2,z3,z160,z5,z6,z603]),(0,[z2,z3,z4,z5,z6,z957]),(0,[z1,z2,z3,z4,z6,z960])],[(0,[z149,z295,z3,z4,z5,z6]),(0,[z1,z961,z3,z4,z5,z6]),(0,[z228,z1,z86,z3,z4,z6]),(0,[z1,z3,z4,z177,z21,z6]),(0,[z501,z13,z1,z3,z4,z6]),(0,[z1,z41,z3,z4,z5,z175]),(0,[z962,z2,z3,z4,z5,z6])],[(0,[z53,z2,z12,z4,z5,z6]),(0,[z655,z2,z12,z4,z5,z6]),(0,[z1,z963,z3,z4,z5,z6]),(0,[z1,z964,z3,z4,z5,z6])]],
   [[(0,[z868,z2,z3,z4,z5,z6]),(0,[z150,z2,z3,z243,z5,z6]),(0,[z1,z2,z3,z128,z286,z6]),(0,[z965,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z966]),(0,[z1,z171,z3,z301,z5,z6]),(0,[z1,z3,z4,z5,z6,z967]),(0,[z1,z3,z4,z5,z6,z968])],[(0,[z13,z1,z3,z4,z398,z6]),(0,[z1,z130,z3,z4,z191,z6]),(0,[z297,z2,z3,z4,z5,z6]),(0,[z11,z169,z3,z4,z303,z6]),(0,[z507,z1,z3,z4,z5,z50]),(0,[z13,z1,z3,z49,z4,z6]),(0,[z62,z1,z2,z262,z5,z6]),(0,[z1,z880,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z969,z6]),(0,[z13,z1,z547,z3,z4,z6]),(0,[z401,z2,z3,z160,z5,z6]),(0,[z24,z108,z13,z3,z4,z6]),(0,[z17,z146,z2,z4,z5,z15])],[(0,[z150,z2,z3,z821,z5,z6]),(0,[z13,z3,z4,z160,z60,z6]),(0,[z242,z1,z3,z4,z5,z6]),(0,[z954,z2,z3,z4,z5,z6]),(0,[z31,z193,z2,z4,z6,z88]),(0,[z297,z2,z3,z4,z449,z6])],[(0,[z13,z1,z3,z4,z561,z6]),(0,[z1,z2,z3,z4,z6,z970]),(0,[z13,z250,z14,z3,z4,z6]),(0,[z1,z41,z3,z4,z175,z316]),(0,[z1,z3,z4,z971,z5,z6]),(0,[z1,z972,z3,z4,z5,z6]),(0,[z1,z636,z3,z101,z5,z6]),(0,[z1,z636,z3,z4,z99,z6])],[(0,[z1,z2,z3,z4,z973,z6]),(0,[z230,z2,z3,z4,z5,z6]),(0,[z1,z974,z3,z4,z5,z6]),(0,[z1,z3,z804,z210,z5,z6]),(0,[z1,z3,z82,z210,z5,z6]),(0,[z13,z1,z468,z4,z5,z6]),(0,[z1,z69,z3,z4,z21,z6]),(0,[z1,z2,z724,z10,z5,z6])],[(1,[z2,z765,z4,z5,z6]),(0,[z1,z975,z3,z4,z5,z6]),(0,[z59,z2,z3,z4,z757,z6]),(0,[z2,z3,z4,z5,z79,z957]),(0,[z1,z2,z3,z4,z976,z6]),(0,[z1,z3,z4,z977,z5,z6]),(0,[z1,z978,z3,z4,z5,z6]),(0,[z979,z2,z3,z4,z5,z6])],[(0,[z273,z130,z3,z4,z5,z6]),(0,[z1,z2,z980,z4,z5,z6]),(0,[z13,z1,z3,z4,z412,z6]),(0,[z150,z2,z173,z4,z5,z6]),(0,[z13,z1,z3,z384,z4,z6]),(0,[z1,z2,z3,z4,z187,z126])]],
   [[(0,[z981,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z982]),(0,[z13,z250,z3,z4,z6,z126]),(0,[z1,z636,z3,z116,z5,z6])],[(0,[z1,z2,z3,z4,z5,z983]),(0,[z2,z182,z4,z5,z6,z407]),(0,[z195,z2,z3,z4,z5,z6]),(0,[z984,z1,z2,z4,z5,z6]),(0,[z828,z2,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z5,z982]),(0,[z13,z1,z14,z3,z4,z6]),(0,[z985,z2,z3,z4,z5,z6])],[(0,[z1,z986,z3,z4,z5,z6]),(0,[z1,z987,z3,z4,z5,z6]),(0,[z1,z152,z173,z4,z5,z6]),(0,[z1,z611,z173,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z988]),(0,[z1,z2,z989,z4,z5,z6])],[(0,[z78,z2,z3,z4,z5,z56]),(0,[z990,z1,z2,z3,z5,z6]),(0,[z30,z562,z1,z73,z4,z6]),(0,[z16,z2,z105,z4,z5,z6]),(0,[z1,z3,z4,z816,z83,z6])],[(0,[z1,z2,z3,z4,z991,z6]),(0,[z1,z2,z3,z4,z992,z6]),(0,[z1,z2,z742,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z202]),(0,[z1,z14,z2,z688,z3,z4])],[(0,[z1,z2,z3,z4,z5,z993]),(0,[z1,z3,z994,z4,z5,z6]),(0,[z1,z2,z211,z128,z5,z6]),(0,[z713,z2,z3,z4,z5,z6]),(0,[z995,z1,z2,z3,z4,z6]),(0,[z996,z2,z3,z4,z5,z6]),(0,[z997,z2,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z6,z126]),(0,[z13,z87,z3,z4,z5,z6]),(0,[z785,z1,z20,z3,z4,z6])],[(0,[z1,z998,z3,z4,z5,z6]),(0,[z108,z2,z3,z4,z303,z6])],[(0,[z13,z250,z3,z4,z60,z6]),(0,[z1,z999,z2,z3,z4,z6]),(0,[z297,z2,z468,z4,z5,z6])]],
   [[(0,[z13,z1,z3,z498,z5,z6]),(0,[z13,z1,z3,z4,z439,z6]),(0,[z13,z1,z3,z4,z438,z6]),(0,[z1,z1000,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1001,z6]),(0,[z1,z1002,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z6,z442]),(0,[z13,z1,z3,z4,z629,z6]),(0,[z793,z3,z4,z21,z5,z6]),(0,[z1,z3,z49,z21,z74,z6])],[(0,[z1,z3,z4,z131,z5,z6]),(0,[z1,z2,z3,z1003,z5,z6]),(0,[z1004,z13,z3,z4,z5,z6]),(1,[z1,z3,z4,z762,z6])],[(0,[z1005,z1,z3,z4,z5,z6]),(0,[z13,z1,z616,z3,z4,z6]),(0,[z1,z3,z4,z1006,z5,z6]),(0,[z1,z3,z49,z194,z74,z6])],[(0,[z1,z2,z3,z4,z1007,z6]),(0,[z13,z1,z3,z4,z60,z6]),(0,[z2,z3,z4,z197,z60,z6]),(0,[z1,z2,z3,z4,z1008,z6]),(0,[z1,z3,z4,z5,z6,z838]),(0,[z1,z2,z3,z4,z1009,z6]),(0,[z669,z1,z2,z4,z6,z88]),(0,[z1010,z2,z3,z4,z5,z6]),(0,[z1,z14,z58,z556,z3,z4])],[(0,[z1,z2,z3,z4,z6,z1011]),(0,[z13,z1,z246,z3,z4,z6]),(0,[z1012,z1,z3,z4,z5,z6]),(0,[z1,z2,z32,z4,z6,z988])],[(0,[z205,z2,z3,z4,z5,z102]),(0,[z64,z2,z105,z4,z5,z6])],[(0,[z24,z1,z2,z3,z44,z6]),(0,[z1013,z1,z3,z4,z5,z6]),(0,[z16,z2,z4,z5,z6,z15])]],
   [[(0,[z1,z2,z3,z8,z5,z506]),(1,[z2,z3,z4,z5,z957]),(0,[z2,z219,z3,z5,z6,z9]),(0,[z31,z226,z2,z4,z6,z88]),(0,[z17,z1,z23,z4,z5,z15]),(0,[z1,z2,z1014,z4,z5,z6])],[(0,[z1,z3,z4,z1015,z286,z6]),(0,[z78,z2,z3,z4,z5,z957]),(0,[z775,z2,z3,z4,z5,z6]),(0,[z922,z2,z3,z4,z5,z6]),(0,[z1,z1016,z3,z4,z5,z6])],[(0,[z465,z2,z3,z498,z5,z6]),(0,[z1,z2,z894,z4,z5,z6]),(0,[z13,z228,z1,z3,z4,z6]),(0,[z1,z3,z4,z177,z194,z6]),(0,[z13,z1017,z3,z4,z5,z6])],[(0,[z1,z2,z1018,z4,z5,z6]),(0,[z1,z1019,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1020,z6]),(0,[z1021,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z1022]),(0,[z1,z2,z897,z4,z5,z6]),(0,[z1023,z2,z3,z4,z5,z6])],[(0,[z435,z1,z3,z44,z5,z6]),(0,[z155,z13,z1,z3,z4,z6]),(0,[z1,z105,z4,z21,z5,z139]),(0,[z1024,z2,z3,z4,z5,z6])],[(0,[z1025,z1,z2,z3,z4,z6]),(0,[z1,z3,z4,z1026,z5,z6]),(0,[z542,z1,z2,z3,z5,z9]),(0,[z1,z169,z3,z4,z303,z6]),(0,[z1027,z2,z3,z4,z5,z6]),(0,[z1028,z2,z3,z4,z5,z6]),(0,[z1,z189,z32,z4,z129,z6])],[(0,[z529,z2,z3,z4,z5,z95]),(0,[z13,z1,z3,z320,z4,z6])],[(0,[z13,z1,z3,z4,z406,z6]),(0,[z13,z1,z3,z4,z509,z6]),(0,[z2,z1029,z3,z4,z5,z6])]],
   [[(0,[z650,z1,z3,z4,z5,z50]),(0,[z1,z2,z3,z1030,z5,z6]),(0,[z2,z3,z4,z5,z6,z1031]),(0,[z13,z516,z3,z4,z5,z6]),(0,[z230,z69,z2,z3,z4,z6]),(0,[z837,z3,z4,z21,z5,z6]),(0,[z1,z576,z376,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z1032]),(0,[z314,z2,z3,z160,z5,z6]),(0,[z108,z169,z3,z4,z5,z6]),(1,[z785,z1,z3,z4,z6]),(0,[z1,z2,z3,z5,z772,z9])],[(0,[z11,z13,z3,z4,z303,z6]),(0,[z13,z1,z3,z128,z5,z6]),(0,[z1033,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1034,z6]),(0,[z16,z2,z3,z4,z65,z6]),(0,[z1,z23,z3,z4,z65,z6]),(0,[z1,z2,z105,z116,z5,z6]),(0,[z1035,z2,z3,z4,z5,z6]),(0,[z195,z14,z2,z58,z3,z4])],[(0,[z149,z250,z3,z4,z5,z6]),(0,[z1,z2,z1036,z4,z5,z6]),(0,[z1,z418,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z316]),(0,[z1,z1037,z3,z4,z5,z6]),(0,[z1,z1038,z3,z4,z5,z6]),(0,[z1,z14,z306,z58,z3,z4])],[(0,[z1,z2,z3,z4,z1039,z6]),(0,[z127,z2,z437,z4,z5,z6]),(0,[z256,z1,z3,z4,z5,z431]),(0,[z1040,z1,z3,z4,z83,z6])],[(0,[z1,z3,z4,z131,z299,z6]),(0,[z54,z2,z3,z302,z5,z6]),(0,[z1,z189,z3,z4,z5,z6]),(0,[z108,z13,z3,z4,z21,z6]),(0,[z13,z1,z3,z4,z481,z6]),(0,[z17,z536,z2,z4,z5,z15]),(0,[z135,z161,z3,z4,z5,z6])],[(0,[z195,z2,z3,z4,z60,z6]),(0,[z205,z152,z3,z4,z5,z95]),(0,[z205,z611,z3,z4,z5,z95]),(0,[z13,z1,z3,z4,z5,z1041]),(0,[z1,z1042,z3,z4,z5,z6]),(0,[z1043,z2,z3,z4,z5,z6])],[(0,[z108,z2,z3,z4,z191,z6]),(0,[z59,z3,z4,z21,z60,z6]),(0,[z13,z3,z4,z303,z60,z6]),(0,[z1,z2,z487,z10,z5,z6]),(0,[z17,z1,z2,z4,z99,z15]),(0,[z24,z1,z2,z3,z6,z729]),(0,[z1044,z2,z3,z4,z5,z6])]],
   [[(0,[z13,z1,z3,z4,z492,z6]),(0,[z1045,z2,z3,z4,z5,z6]),(0,[z1,z14,z58,z3,z4,z21]),(0,[z2,z1046,z3,z4,z5,z6])],[(0,[z1,z2,z1047,z4,z5,z6]),(0,[z13,z1,z3,z4,z497,z6]),(0,[z1,z2,z3,z8,z5,z434]),(0,[z1,z3,z4,z5,z6,z1048])],[(0,[z1,z1049,z2,z3,z4,z6]),(0,[z13,z1,z3,z333,z4,z6]),(0,[z13,z3,z4,z5,z6,z555]),(0,[z13,z1,z3,z4,z106,z6]),(0,[z1,z41,z3,z4,z5,z431]),(0,[z13,z1,z3,z4,z6,z474]),(0,[z135,z2,z3,z4,z83,z6])],[(0,[z1,z1050,z3,z4,z5,z6]),(0,[z1,z152,z3,z4,z286,z6]),(0,[z1,z611,z3,z4,z286,z6]),(0,[z1,z3,z116,z21,z5,z6]),(0,[z16,z2,z3,z101,z5,z6]),(0,[z16,z2,z3,z4,z99,z6]),(0,[z1,z23,z3,z101,z5,z6])],[(0,[z2,z3,z90,z5,z6,z221])],[(0,[z1,z2,z1051,z4,z5,z6]),(0,[z87,z2,z3,z4,z5,z6]),(0,[z1052,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z251,z5,z296]),(0,[z1053,z2,z3,z4,z5,z6]),(0,[z135,z2,z376,z4,z5,z6])],[(0,[z1,z3,z4,z1054,z5,z6]),(0,[z13,z297,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1055,z6]),(0,[z1056,z2,z3,z4,z5,z6]),(0,[z1,z1057,z3,z4,z5,z6]),(0,[z1,z266,z3,z49,z74,z6]),(0,[z1,z1058,z3,z4,z5,z6])],[(0,[z1,z1059,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z935]),(0,[z108,z3,z4,z21,z5,z6]),(0,[z1,z3,z4,z5,z6,z1060]),(0,[z1,z414,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z762,z6]),(0,[z16,z2,z3,z116,z5,z6]),(0,[z1,z23,z3,z116,z5,z6]),(0,[z1,z1061,z3,z4,z5,z6])]],
   [[(0,[z136,z2,z3,z4,z60,z6]),(0,[z193,z2,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z167,z6]),(0,[z54,z2,z3,z365,z5,z6]),(0,[z1062,z2,z3,z4,z5,z6]),(0,[z13,z1,z325,z3,z4,z6]),(0,[z13,z1,z3,z4,z762,z6]),(0,[z1,z3,z4,z711,z5,z6])],[(0,[z1,z2,z1063,z4,z5,z6]),(0,[z942,z1,z3,z4,z5,z6]),(0,[z13,z1,z230,z3,z4,z6]),(0,[z1,z2,z32,z4,z129,z6]),(0,[z1,z161,z3,z4,z83,z6])],[(0,[z205,z2,z3,z4,z197,z95]),(0,[z13,z1,z3,z49,z74,z6]),(0,[z1,z2,z3,z49,z231,z6]),(0,[z16,z3,z4,z21,z5,z6]),(0,[z1064,z2,z3,z4,z5,z6])],[(0,[z1,z3,z4,z805,z5,z6]),(0,[z1017,z2,z3,z4,z5,z6]),(0,[z181,z2,z3,z5,z36,z9])],[(0,[z1,z2,z1065,z4,z5,z6]),(0,[z1,z2,z1066,z4,z5,z6]),(0,[z1,z152,z3,z4,z197,z6]),(0,[z739,z1,z3,z4,z5,z6]),(0,[z13,z1,z423,z3,z4,z6]),(0,[z250,z3,z4,z5,z6,z50]),(0,[z1,z3,z4,z1067,z5,z6]),(0,[z2,z1068,z3,z4,z5,z6]),(0,[z1069,z2,z3,z4,z5,z6]),(0,[z1,z1070,z3,z4,z5,z6])],[(0,[z465,z2,z3,z160,z5,z6]),(0,[z1,z2,z1071,z4,z5,z6]),(1,[z2,z3,z4,z757,z6]),(0,[z13,z1,z3,z318,z4,z6]),(0,[z1,z2,z3,z4,z1072,z6]),(0,[z2,z1073,z3,z4,z5,z6]),(0,[z13,z250,z3,z4,z5,z6]),(0,[z1,z2,z3,z101,z65,z6]),(0,[z297,z2,z3,z5,z6,z9])],[(0,[z2,z3,z90,z821,z5,z6]),(0,[z11,z2,z3,z498,z5,z6]),(0,[z1,z3,z4,z1074,z5,z6]),(0,[z360,z1,z3,z210,z5,z6]),(0,[z414,z732,z2,z3,z4,z6]),(0,[z1,z3,z4,z5,z6,z1075]),(0,[z1,z1076,z3,z4,z5,z6])],[(0,[z149,z169,z3,z4,z5,z6]),(0,[z2,z1077,z3,z4,z5,z6]),(0,[z1078,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z1079,z5,z6]),(0,[z900,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z37,z126])]],
   [[(0,[z127,z2,z182,z4,z5,z6]),(0,[z2,z3,z498,z5,z60,z6]),(0,[z1,z152,z211,z4,z5,z6]),(0,[z1,z611,z211,z4,z5,z6]),(0,[z205,z3,z4,z21,z5,z95]),(0,[z767,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z536,z2,z3,z4,z5,z6]),(0,[z1080,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z1081,z5,z6]),(0,[z146,z3,z4,z21,z5,z6]),(0,[z785,z1,z2,z3,z4,z6]),(0,[z1082,z1,z3,z4,z5,z6]),(0,[z1083,z2,z3,z4,z5,z6]),(0,[z1,z1084,z3,z4,z5,z6]),(0,[z1,z2,z3,z1085,z5,z6]),(0,[z1,z2,z3,z116,z65,z6]),(0,[z1,z3,z4,z5,z6,z1086])],[(0,[z1,z2,z3,z1087,z5,z6]),(0,[z512,z2,z3,z4,z60,z6]),(0,[z13,z1,z3,z1081,z5,z6])],[(0,[z2,z173,z4,z5,z6,z95]),(0,[z1,z3,z4,z21,z6,z48]),(0,[z1088,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z449,z6])],[(0,[z1,z2,z1089,z4,z5,z6]),(0,[z1,z2,z3,z4,z1090,z6]),(0,[z2,z3,z4,z757,z5,z6]),(0,[z13,z1,z601,z3,z4,z6]),(0,[z1,z1091,z3,z4,z5,z6]),(0,[z1,z3,z4,z21,z65,z6]),(0,[z1,z2,z3,z800,z4,z6])],[(0,[z2,z3,z4,z191,z60,z6]),(0,[z1,z3,z1092,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1093]),(0,[z1,z3,z4,z21,z286,z6]),(0,[z1,z2,z3,z4,z1094,z6]),(0,[z13,z1,z14,z3,z4,z272])],[(0,[z1095,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z101,z99,z6]),(0,[z1,z2,z3,z5,z6,z772])],[(0,[z13,z3,z4,z60,z79,z6]),(0,[z13,z1,z3,z4,z543,z6]),(1,[z1,z2,z4,z6,z988])]],
   [[(0,[z169,z130,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1096,z6]),(0,[z1,z2,z3,z1097,z5,z6]),(0,[z2,z3,z4,z5,z6,z555]),(0,[z562,z1,z3,z4,z21,z6]),(0,[z1,z2,z3,z1098,z5,z6]),(0,[z669,z13,z1,z3,z4,z6]),(0,[z1,z659,z3,z4,z21,z6]),(0,[z1,z2,z372,z10,z5,z6])],[(0,[z136,z1,z3,z4,z21,z6]),(0,[z1,z1099,z3,z4,z5,z6]),(0,[z1,z3,z4,z21,z83,z6]),(0,[z31,z1,z2,z4,z6,z988])],[(0,[z30,z1,z43,z4,z5,z6]),(0,[z108,z13,z3,z4,z5,z6]),(0,[z1,z325,z4,z120,z5,z6]),(0,[z1,z2,z10,z5,z6,z649]),(0,[z1,z2,z3,z116,z99,z6])],[(0,[z1,z38,z3,z4,z21,z6]),(0,[z602,z2,z12,z4,z5,z6]),(0,[z1,z173,z4,z21,z5,z6]),(0,[z1,z211,z4,z21,z5,z6]),(0,[z1,z2,z4,z6,z988,z88])],[(0,[z149,z156,z3,z4,z191,z6]),(0,[z1,z3,z4,z21,z191,z6]),(0,[z419,z2,z3,z4,z5,z6]),(0,[z465,z2,z3,z4,z5,z6]),(0,[z1,z2,z211,z4,z197,z6]),(0,[z13,z1,z3,z8,z5,z117]),(0,[z1100,z2,z3,z4,z5,z6])],[(0,[z1,z2,z4,z1101,z5,z6]),(0,[z112,z2,z3,z4,z5,z79]),(0,[z1102,z2,z3,z4,z5,z6]),(0,[z13,z997,z3,z4,z5,z6]),(0,[z181,z13,z1,z3,z5,z9]),(0,[z68,z13,z1,z3,z4,z6]),(0,[z1,z3,z4,z21,z99,z6]),(0,[z297,z576,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1103,z5,z6]),(0,[z127,z2,z192,z4,z5,z6]),(0,[z2,z142,z182,z4,z5,z6]),(0,[z1,z3,z4,z21,z197,z6]),(0,[z904,z3,z4,z21,z5,z6]),(1,[z1,z3,z4,z5,z838]),(0,[z1,z2,z3,z4,z1104,z6])],[(0,[z13,z678,z1,z3,z4,z6]),(0,[z1,z2,z3,z1105,z5,z6]),(0,[z723,z562,z2,z3,z4,z6]),(1,[z1,z3,z804,z5,z6]),(0,[z1,z468,z4,z21,z5,z6]),(0,[z1,z3,z4,z1106,z5,z6]),(0,[z1,z2,z468,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z988])]],
   [[(0,[z108,z156,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z350,z6]),(1,[z2,z3,z821,z5,z6]),(0,[z586,z1,z3,z4,z5,z50]),(0,[z714,z13,z3,z4,z5,z6]),(0,[z13,z1,z3,z4,z6,z567]),(0,[z24,z13,z419,z3,z4,z6]),(0,[z13,z1,z3,z4,z566,z6])],[(0,[z1,z2,z1107,z4,z5,z6]),(0,[z80,z13,z1,z3,z4,z6]),(0,[z13,z1,z3,z82,z4,z6]),(0,[z1,z2,z468,z4,z449,z6])],[(0,[z1,z2,z3,z1108,z5,z6]),(0,[z314,z13,z1,z3,z4,z6]),(0,[z219,z3,z4,z21,z5,z6]),(0,[z785,z1,z3,z4,z5,z6]),(0,[z1,z1109,z3,z4,z5,z6]),(0,[z1,z1110,z3,z4,z5,z6]),(0,[z1,z3,z1111,z4,z5,z6]),(0,[z181,z1,z2,z376,z5,z9])],[(0,[z1,z1112,z3,z4,z5,z6]),(0,[z205,z2,z173,z4,z5,z95]),(0,[z24,z13,z1,z3,z49,z6]),(0,[z1113,z1,z2,z3,z4,z6])],[(0,[z13,z215,z1,z3,z4,z6]),(0,[z146,z2,z173,z4,z5,z6]),(0,[z108,z13,z3,z49,z4,z6]),(0,[z1114,z1,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1115])],[(0,[z13,z1,z3,z4,z299,z6]),(0,[z13,z1,z107,z3,z4,z6]),(0,[z78,z2,z173,z4,z5,z6]),(0,[z1,z3,z462,z4,z5,z6]),(0,[z13,z1,z727,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1116,z6]),(1,[z1,z2,z4,z5,z725]),(0,[z1117,z1,z3,z4,z5,z6]),(0,[z1118,z1,z3,z4,z5,z6])],[(0,[z156,z868,z3,z4,z5,z6]),(0,[z627,z156,z3,z4,z5,z6]),(0,[z516,z2,z3,z4,z5,z6]),(0,[z1,z1119,z3,z4,z5,z6]),(0,[z54,z3,z90,z21,z5,z6]),(0,[z346,z13,z1,z3,z4,z6]),(0,[z13,z1,z3,z4,z366,z6]),(0,[z1120,z2,z3,z4,z5,z6]),(0,[z1121,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z182,z3,z498,z5,z6]),(0,[z1,z14,z2,z383,z3,z4]),(0,[z195,z2,z3,z4,z303,z6]),(0,[z1,z2,z173,z4,z286,z6]),(0,[z1,z3,z4,z799,z197,z6])],[(0,[z13,z1,z14,z58,z3,z4])],[(0,[z1,z1122,z2,z3,z4,z6]),(0,[z1,z2,z3,z498,z5,z6]),(0,[z1,z3,z4,z5,z6,z1123]),(0,[z1,z2,z3,z8,z5,z772]),(0,[z1,z14,z2,z58,z3,z4])],[(0,[z1,z2,z3,z1124,z5,z6]),(0,[z1,z3,z4,z21,z499,z6]),(0,[z1,z69,z3,z134,z4,z6]),(0,[z1,z3,z4,z5,z838,z50]),(0,[z1,z414,z41,z3,z4,z6]),(0,[z1,z2,z116,z5,z6,z15]),(0,[z1,z1125,z3,z4,z5,z6]),(0,[z1,z2,z376,z5,z6,z9]),(0,[z1,z2,z749,z3,z4,z37])],[(0,[z1,z2,z3,z1126,z5,z6]),(0,[z1004,z2,z3,z4,z5,z6]),(0,[z108,z13,z14,z3,z4,z6]),(0,[z1,z1127,z3,z4,z5,z6])],[(0,[z677,z2,z3,z90,z5,z6]),(0,[z59,z3,z4,z131,z60,z6]),(0,[z30,z1,z73,z4,z5,z6]),(0,[z209,z1,z3,z210,z5,z6]),(0,[z13,z1,z3,z4,z356,z6]),(0,[z1,z3,z4,z21,z158,z6]),(0,[z250,z3,z4,z21,z5,z6]),(0,[z226,z69,z2,z3,z4,z6]),(0,[z1128,z2,z3,z4,z5,z6])],[(0,[z11,z2,z3,z4,z167,z6]),(0,[z1129,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1130,z6]),(0,[z1,z2,z3,z1131,z5,z6]),(0,[z13,z1,z3,z4,z6,z710]),(0,[z1,z1132,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1133]),(0,[z1,z2,z3,z4,z5,z725]),(0,[z1134,z2,z3,z4,z5,z6])],[(0,[z78,z2,z3,z4,z5,z467]),(0,[z1135,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z1136,z5,z6]),(0,[z687,z2,z12,z4,z5,z6]),(0,[z1,z2,z3,z4,z1137,z6]),(0,[z13,z562,z1,z3,z4,z6]),(0,[z108,z13,z3,z4,z6,z126]),(0,[z13,z1,z689,z3,z4,z6]),(0,[z24,z13,z1,z3,z6,z25]),(0,[z1138,z2,z3,z4,z5,z6])],[(0,[z1,z3,z4,z1139,z5,z6]),(0,[z2,z3,z821,z160,z5,z6]),(0,[z13,z1,z3,z4,z85,z6]),(0,[z1,z1140,z3,z4,z5,z6]),(0,[z2,z3,z4,z757,z60,z6]),(0,[z1,z2,z173,z4,z197,z6]),(0,[z1,z2,z3,z4,z1141,z6]),(1,[z13,z310,z3,z4,z6]),(0,[z1,z3,z1142,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z1143])],[(0,[z150,z3,z160,z21,z5,z6]),(0,[z1,z3,z4,z1144,z5,z6]),(0,[z1,z2,z1145,z4,z5,z6]),(0,[z1,z171,z3,z804,z5,z6])],[(0,[z1,z2,z3,z4,z1146,z6]),(0,[z1,z69,z3,z4,z131,z6]),(0,[z13,z1,z20,z10,z5,z6]),(0,[z62,z64,z2,z63,z5,z6]),(0,[z16,z23,z3,z4,z5,z6]),(0,[z1,z3,z4,z848,z5,z6]),(0,[z1,z3,z1147,z4,z5,z6])],[(0,[z1,z1148,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z474])],[(0,[z1,z2,z3,z1149,z5,z6]),(0,[z13,z1,z3,z604,z4,z6]),(0,[z885,z2,z3,z4,z5,z6]),(0,[z290,z1,z14,z3,z4,z6]),(0,[z2,z3,z4,z5,z6,z1150])],[(0,[z1,z1151,z3,z4,z5,z6]),(0,[z11,z3,z4,z303,z21,z6]),(0,[z13,z1,z3,z4,z623,z6]),(0,[z31,z13,z1,z4,z6,z88]),(0,[z13,z1,z14,z3,z4,z126]),(0,[z297,z2,z3,z4,z83,z6])],[(0,[z1,z1152,z3,z4,z5,z6]),(0,[z108,z13,z3,z4,z60,z6]),(0,[z13,z1,z112,z3,z4,z6]),(0,[z13,z1,z3,z4,z626,z6]),(0,[z1,z2,z3,z4,z5,z1153]),(0,[z523,z1,z2,z3,z5,z9]),(0,[z1,z3,z4,z5,z6,z1154])]],
   [[(0,[z1,z2,z3,z4,z1155,z6]),(0,[z1,z636,z3,z4,z5,z6]),(0,[z31,z13,z1,z32,z4,z6]),(0,[z796,z2,z3,z4,z5,z6]),(0,[z2,z219,z3,z8,z5,z6])],[(0,[z2,z173,z90,z4,z5,z6]),(0,[z13,z1,z534,z3,z4,z6]),(0,[z250,z41,z3,z4,z5,z6]),(0,[z31,z1,z4,z21,z6,z88]),(0,[z290,z1,z3,z4,z6,z126]),(0,[z1156,z2,z3,z4,z5,z6])],[(0,[z150,z2,z3,z498,z5,z6]),(0,[z13,z1,z3,z4,z339,z6]),(0,[z228,z1,z3,z4,z6,z50]),(0,[z1,z3,z4,z5,z762,z6]),(0,[z62,z1,z2,z63,z5,z6]),(0,[z1157,z2,z3,z4,z5,z6]),(0,[z343,z1,z3,z4,z37,z126])],[(0,[z1,z2,z3,z4,z1158,z6]),(0,[z678,z2,z3,z4,z60,z6]),(0,[z1159,z1,z3,z4,z5,z6]),(0,[z17,z13,z1,z4,z5,z15]),(0,[z1,z2,z3,z4,z5,z838])],[(0,[z1,z3,z4,z5,z6,z1160]),(0,[z1,z2,z3,z128,z5,z6]),(0,[z1,z2,z3,z804,z5,z6]),(0,[z13,z1,z470,z3,z4,z6]),(0,[z343,z1,z3,z4,z5,z6]),(0,[z1,z69,z3,z4,z194,z6])],[(0,[z1161,z1,z3,z4,z5,z6]),(0,[z330,z3,z4,z81,z5,z6]),(0,[z1,z1162,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1163]),(0,[z181,z1,z2,z3,z5,z9])],[(0,[z146,z2,z12,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z1164]),(0,[z17,z1,z4,z21,z5,z15]),(0,[z1,z32,z134,z4,z129,z6])],[(0,[z1165,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1166,z6]),(0,[z1,z2,z3,z4,z1167,z6]),(0,[z1,z171,z3,z103,z5,z6]),(0,[z40,z1,z3,z4,z5,z50]),(0,[z1168,z1,z3,z4,z5,z6]),(0,[z181,z1,z2,z3,z449,z9])]],
   [[(0,[z1,z2,z3,z4,z1169,z6]),(0,[z1,z2,z3,z4,z5,z1041]),(0,[z1170,z2,z3,z4,z5,z6]),(0,[z965,z3,z4,z21,z5,z6]),(0,[z1,z2,z1171,z4,z5,z6])],[(0,[z1172,z2,z3,z4,z5,z6]),(0,[z1,z3,z103,z5,z6,z61]),(0,[z13,z1,z354,z3,z4,z6]),(0,[z297,z3,z4,z21,z5,z6]),(0,[z1,z3,z1173,z4,z5,z6])],[(0,[z1,z2,z63,z724,z5,z6]),(0,[z1,z3,z4,z5,z6,z1174])],[(0,[z273,z250,z3,z4,z5,z6]),(0,[z1,z2,z3,z1175,z5,z6]),(0,[z1,z2,z3,z4,z1176,z6])],[(0,[z2,z182,z765,z4,z5,z6]),(0,[z580,z2,z3,z4,z60,z6]),(0,[z1,z1177,z3,z4,z5,z6]),(0,[z205,z2,z3,z4,z286,z95]),(0,[z1,z652,z73,z4,z5,z6]),(0,[z1178,z2,z3,z4,z5,z6])],[(0,[z1,z3,z604,z4,z21,z6]),(0,[z230,z3,z4,z21,z5,z6])],[(0,[z1,z2,z765,z4,z5,z6]),(0,[z1,z2,z1179,z4,z5,z6]),(0,[z1,z23,z3,z4,z99,z6])],[(0,[z1,z3,z4,z81,z191,z6]),(0,[z1,z1180,z3,z4,z5,z6]),(0,[z13,z54,z3,z90,z5,z6]),(0,[z13,z1,z3,z4,z222,z6]),(0,[z13,z1,z1179,z4,z5,z6]),(0,[z1,z1181,z3,z4,z5,z6]),(0,[z1,z14,z2,z519,z3,z4])]],
   [[(0,[z31,z13,z1,z594,z4,z6]),(0,[z1182,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z1183,z5,z6]),(0,[z1,z2,z3,z4,z1184,z6]),(0,[z146,z2,z182,z4,z5,z6]),(0,[z1,z2,z1185,z4,z5,z6]),(0,[z206,z13,z1,z3,z4,z6]),(0,[z195,z3,z4,z21,z5,z6]),(0,[z1,z2,z105,z4,z5,z628])],[(0,[z1,z1186,z3,z4,z5,z6]),(0,[z13,z1,z173,z4,z5,z6]),(0,[z13,z1,z672,z3,z4,z6]),(0,[z13,z16,z3,z4,z5,z6]),(0,[z31,z290,z1,z4,z6,z88])],[(0,[z1,z1187,z3,z4,z5,z6]),(0,[z1,z2,z3,z1188,z5,z6]),(0,[z13,z59,z3,z4,z60,z6]),(0,[z31,z108,z13,z3,z4,z6]),(0,[z13,z1,z414,z3,z4,z6]),(0,[z1,z32,z4,z21,z129,z6]),(0,[z181,z1,z576,z3,z5,z9])],[(0,[z13,z419,z3,z4,z5,z6]),(0,[z1,z556,z3,z4,z5,z6]),(0,[z1,z2,z3,z49,z74,z6])],[(0,[z149,z13,z3,z4,z60,z6]),(0,[z1,z2,z3,z4,z1189,z6]),(0,[z209,z228,z1,z3,z210,z6]),(0,[z13,z3,z4,z5,z6,z36]),(0,[z13,z1,z3,z4,z6,z674]),(0,[z1,z2,z4,z5,z6,z1190]),(0,[z1,z1191,z3,z4,z5,z6])],[(0,[z181,z1,z3,z21,z5,z9]),(0,[z1,z1192,z3,z4,z5,z6]),(0,[z1193,z2,z3,z4,z5,z6]),(0,[z1194,z1,z3,z4,z5,z6])],[(1,[z868,z3,z4,z5,z6]),(0,[z1,z370,z3,z4,z5,z6]),(0,[z1,z2,z3,z1195,z5,z6]),(0,[z205,z2,z3,z4,z5,z957]),(0,[z13,z1,z226,z3,z4,z6]),(0,[z1,z3,z4,z133,z21,z6]),(0,[z1,z161,z376,z4,z5,z6])]],
   [[(0,[z13,z1,z3,z597,z4,z6]),(0,[z13,z1,z3,z4,z679,z6]),(0,[z1,z3,z604,z134,z4,z6]),(0,[z13,z250,z3,z4,z81,z6]),(0,[z1,z3,z4,z5,z175,z296]),(0,[z62,z87,z2,z63,z5,z6]),(0,[z24,z1,z2,z3,z6,z25]),(0,[z1196,z2,z3,z4,z5,z6]),(0,[z1197,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1198,z5,z6]),(0,[z1,z2,z3,z4,z1199,z6]),(0,[z1,z1200,z3,z4,z5,z6]),(0,[z78,z2,z3,z4,z5,z79]),(0,[z205,z2,z211,z4,z5,z95]),(0,[z1,z41,z3,z4,z5,z254]),(0,[z844,z13,z3,z4,z5,z6]),(0,[z1,z2,z1201,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1202])],[(0,[z1,z1203,z3,z4,z5,z6]),(0,[z1,z3,z4,z741,z5,z6]),(0,[z1,z2,z3,z4,z1204,z6])],[(0,[z2,z3,z1205,z4,z5,z6]),(0,[z1,z2,z3,z4,z1206,z6]),(0,[z1,z3,z4,z5,z6,z1207]),(0,[z13,z1,z159,z3,z4,z6]),(0,[z250,z14,z2,z3,z4,z6]),(0,[z13,z310,z2,z3,z4,z6])],[(0,[z13,z250,z3,z4,z303,z6]),(0,[z13,z1,z663,z3,z4,z6]),(0,[z1,z3,z742,z4,z5,z6]),(0,[z13,z1,z3,z4,z201,z6]),(0,[z24,z13,z1,z3,z4,z6]),(0,[z13,z193,z3,z4,z5,z6]),(0,[z1208,z2,z3,z4,z5,z6]),(0,[z1,z2,z376,z4,z83,z6]),(0,[z1,z3,z4,z1209,z5,z6])],[(0,[z13,z1,z3,z4,z81,z6]),(0,[z226,z2,z3,z4,z5,z6]),(0,[z1210,z1,z3,z4,z5,z6]),(0,[z150,z2,z3,z160,z5,z6]),(0,[z1,z3,z4,z1015,z5,z6]),(0,[z1,z576,z3,z4,z5,z6]),(0,[z1,z3,z1211,z4,z5,z6]),(0,[z1,z2,z4,z129,z6,z988]),(0,[z297,z2,z3,z8,z5,z6])],[(0,[z1,z2,z211,z4,z286,z6]),(0,[z912,z1,z3,z4,z286,z6]),(0,[z562,z1,z72,z3,z4,z6]),(0,[z31,z1,z2,z4,z6,z88])],[(0,[z11,z2,z3,z4,z85,z6]),(0,[z1212,z2,z3,z4,z5,z6]),(0,[z24,z13,z250,z3,z4,z6]),(0,[z1213,z2,z3,z4,z5,z6]),(0,[z1,z576,z3,z4,z449,z6])]],
   [[(0,[z1,z1214,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z957]),(0,[z13,z226,z2,z3,z4,z6]),(0,[z1,z207,z3,z4,z5,z50]),(0,[z1,z2,z427,z4,z129,z6])],[(0,[z13,z1,z3,z4,z303,z6]),(0,[z343,z1,z3,z4,z60,z6]),(0,[z11,z2,z3,z4,z757,z6]),(0,[z1215,z2,z3,z4,z5,z6]),(0,[z13,z1,z3,z489,z4,z6]),(0,[z224,z250,z3,z4,z5,z6]),(0,[z13,z1172,z3,z4,z5,z6]),(0,[z13,z1102,z3,z4,z5,z6]),(0,[z1,z3,z870,z4,z5,z6]),(0,[z1,z3,z4,z5,z175,z838])],[(0,[z1,z2,z4,z5,z6,z1216]),(0,[z13,z864,z3,z4,z5,z6])],[(0,[z149,z868,z3,z4,z5,z6]),(0,[z53,z2,z3,z498,z5,z6]),(0,[z901,z1,z3,z4,z5,z6]),(0,[z17,z1,z2,z4,z5,z15])],[(0,[z863,z228,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1217,z6]),(0,[z1,z3,z4,z5,z6,z1218]),(0,[z1040,z1,z3,z4,z5,z6])],[(0,[z1,z1219,z3,z4,z5,z6]),(0,[z602,z13,z1,z3,z4,z6]),(0,[z62,z13,z1,z63,z5,z6]),(0,[z13,z135,z3,z4,z5,z6])],[(0,[z13,z1,z3,z4,z704,z6]),(0,[z13,z1,z14,z3,z4,z431]),(0,[z1,z2,z3,z8,z5,z117])],[(0,[z364,z13,z1,z3,z4,z6]),(0,[z1,z2,z3,z4,z1220,z6]),(0,[z1,z14,z2,z3,z4,z431]),(0,[z13,z1,z605,z3,z4,z6]),(0,[z1,z418,z20,z10,z5,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 517) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 517).take 511) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1028).take 225) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1253)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [517, 511, 225] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 93).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 93).take 92).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 185).take 71).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [93, 92, 71] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_40213

theorem PEqualNP.Outside.L_meta_40213 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4272482472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4272482472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40213.solve
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40325

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
  Nat.testBit (4276808936 * 2 ^ 32 + 4276677832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x8010660d031a7228#64 ++ 0x340083306818d391#64 ++ 0x6033ee1f073ef27e#64 ++ 0xfb019f70f839f793#64 : BitVec 256),
   (0x004500a2084404d0#64 ++ 0x8802280510422026#64 ++ 0xe8cd13e318c71ffd#64 ++ 0xf746689f18c638ff#64 : BitVec 256),
   (0x030a185460a9a301#64 ++ 0x101850c2a3054d18#64 ++ 0xf70e1c7ce0f9e39b#64 ++ 0xefb870e3e707cf1c#64 : BitVec 256),
   (0x05b01f00b501d802#64 ++ 0x202d80f805a80ec0#64 ++ 0xdff01f80ff01fc17#64 ++ 0xdeff80fc07f80fe0#64 : BitVec 256),
   (0x0eefa000def60003#64 ++ 0xc0777d0006f7b000#64 ++ 0xdfffe000fffe000f#64 ++ 0xbeffff0007fff000#64 : BitVec 256),
   (0x27ffdffb0000001c#64 ++ 0x013ffeffd8000000#64 ++ 0xe7ffffff00000000#64 ++ 0x7f3ffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [9, 1]⟩, ⟨.and, [10, 2]⟩, ⟨.or, [10, 2]⟩, ⟨.and, [12, 6]⟩, ⟨.and, [13, 7]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xe8cd13e318c71ffd 0xf746689f18c638ff

def z1 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xf70e1c7ce0f9e39b 0xefb870e3e707cf1c

def z2 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xdff01f80ff01fc17 0xdeff80fc07f80fe0

def z3 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xdfffe000fffe000f 0xbeffff0007fff000

def z4 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffffff00000000 0x7f3ffffff8000000

def z5 : W := mkw 0x27ffdfff68eda7dd 0x993ffefffb476d3e 0xfffffffff8ffffff 0xffffffffffc7ffff

def z6 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x6033ee1f073ef27e 0xfb019f70f839f793

def z7 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0x1732e000e7380002 0x08b997000739c000

def z8 : W := mkw 0x8effe60ddffe722b 0xf477ff306efff391 0xffffee1ffffef27f 0xffffff70fffff793

def z9 : W := mkw 0x030a185000000000 0x001850c280000000 0x07020c1c00000000 0x08381060e0000000

def z10 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0x0732ec1c00000000 0x08399760e0000000

def z11 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffffff00c10399 0xff3ffffff806081c

def z12 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xfffff3e3ffff1fff 0xffffff9f1ffff8ff

def z13 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xefffffff18c71ffd 0xff7ffffff8c638ff

def z14 : W := mkw 0xa7ffffff0b5e76fc 0xbd3ffffff85af3b7 0xefffffff1fffffff 0xff7ffffff8ffffff

def z15 : W := mkw 0x805566ab0b5654f8 0xac02ab35585ab2a7 0x08f1e3831f061c64 0x10478f1c18f830e3

def z16 : W := mkw 0x0010060001005000 0x2000803000080280 0xc8f01f801f01fc17 0xde4780fc00f80fe0

def z17 : W := mkw 0x2ffffffffeffa31f 0xd17ffffffff7fd18 0xffffffffffffe39f 0xffffffffffffff1c

def z18 : W := mkw 0x8010660903125028 0x2400833048189281 0x6033ee1f07061064 0x7b019f70f8383083

def z19 : W := mkw 0x04b0070095005802 0x2025803804a802c0 0x08f003801f001c04 0x1047801c00f800e0

def z20 : W := mkw 0x234fd8fb0000001c 0x011a7ec7d8000000 0xe70ffc7f00000000 0x6f387fe3f8000000

def z21 : W := mkw 0x020a200042b20001 0x0010510002159000 0xd73fe000e7fe000f 0xbeb9ff00073ff000

def z22 : W := mkw 0x831a7e5d63bbf329 0x3418d3f2eb1ddf99 0xf73ffe7fe7fff3ff 0xffb9fff3ff3fff9f

def z23 : W := mkw 0x0000200002120000 0x0000010000109000 0x4033e000073e000e 0xba019f000039f000

def z24 : W := mkw 0x01101f002101d800 0x200880f801080ec0 0x00001f800001fc10 0x400000fc00000fe0

def z25 : W := mkw 0x0010460900000008 0x0000823048000000 0x6033ee1f00000000 0x7b019f70f8000000

def z26 : W := mkw 0x0fffbf00fff7d803 0xe07ffdf807ffbec0 0xdfffff80fffffc1f 0xfefffffc07ffffe0

def z27 : W := mkw 0x08002000def604c3 0xc840010006f7b026 0x18000000ffff1fff 0x80c0000007fff8ff

def z28 : W := mkw 0x0ce5a0009e560002 0xc0672d0004f2b000 0x08f1e0001f060004 0x10478f0000f83000

def z29 : W := mkw 0x0a4fa0004af60001 0xc0527d000257b000 0x000fe00000fe0008 0x20007f000007f000

def z30 : W := mkw 0x020a000040a00001 0x0010500002050000 0xd70e0000e0f8000b 0xaeb870000707c000

def z31 : W := mkw 0x05a01900b501d802 0x202d00c805a80ec0 0x9fc01180ff01fc17 0x84fe008c07f80fe0

def z32 : W := mkw 0x0100180020018000 0x000800c001000c00 0xd7001c00e001e013 0xceb800e007000f00

def z33 : W := mkw 0x27ffdffb2001801c 0x013ffeffd9000c00 0xf7ffffffe001e013 0xffbfffffff000f00

def z34 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8c1138318071e7d 0xf746089c18c038f3

def z35 : W := mkw 0x05f51fa2bd45dcd2 0xa82fa8fd15ea2ee6 0xfffd1fe3ffc7ffff 0xffffe8ff1ffe3fff

def z36 : W := mkw 0x80002004031a7220 0x340001002018d391 0x00000000073ef27e 0x800000000039f793

def z37 : W := mkw 0x0fefb850def60003 0xc07f7dc286f7b000 0xfffffc7cfffe000f 0xffffffe3e7fff000

def z38 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0x87fdf3e300000000 0x143fef9f18000000

def z39 : W := mkw 0x05b01f0000000000 0x002d80f800000000 0xc7f01f8000000000 0x5e3f80fc00000000

def z40 : W := mkw 0x27ffdffbb501d81e 0x213ffeffdda80ec0 0xffffffffff01fc17 0xfffffffffff80fe0

def z41 : W := mkw 0x010018042009a200 0x100800c021004d10 0xf7021c1ce039e21b 0xefb810e0e701cf10

def z42 : W := mkw 0x0045000000000000 0x0002280000000000 0xc0cd000000000000 0x3606680000000000

def z43 : W := mkw 0x030a185060a18101 0x001850c283050c08 0x970c1060e0c10181 0x04b860830706080c

def z44 : W := mkw 0x030a185000000000 0x001850c280000000 0xe70e1c7c00000000 0x6f3870e3e0000000

def z45 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x0032ec1c0738e002 0x08019760e039c700

def z46 : W := mkw 0x27ffdffb40a0001d 0x013ffeffda050000 0xf7ffffffe0f8000b 0xffbfffffff07c000

def z47 : W := mkw 0x04b00700b501d802 0x2025803805a80ec0 0x18f00380ff01fc17 0x90c7801c07f80fe0

def z48 : W := mkw 0x0010060001005000 0x2000803000080280 0x40300e000700f016 0xda01807000380780

def z49 : W := mkw 0x05a01900b4018802 0x002d00c805a00c40 0x9fc01180f8010c01 0x04fe008c07c00860

def z50 : W := mkw 0x0000000000000000 0x0000000000000000 0xc8c0138018011c15 0xd646009c00c008e0

def z51 : W := mkw 0x004500a2084404d0 0x8802280510422026 0x200d006300c603e8 0x210068031806301f

def z52 : W := mkw 0x224fc0fb0000001c 0x01127e07d8000000 0x200fe07f00000000 0x21007f03f8000000

def z53 : W := mkw 0x80102604031a7220 0x340081302018d391 0x40300e00073ef27e 0xda0180700039f793

def z54 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x1ff3e000ff3e0006 0x18ff9f0007f9f000

def z55 : W := mkw 0x24f5c7ab0000001c 0x0127ae3d58000000 0x60f3ef9f00000000 0x7b079f7cf8000000

def z56 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0x07f3ef9f00000000 0x183f9f7cf8000000

def z57 : W := mkw 0x010018542009a300 0x100800c2a1004d18 0x00000c1c0000e000 0x00000060e0000700

def z58 : W := mkw 0x27aa995000000004 0x013d54ca80000000 0x0700000000000000 0x0038000000000000

def z59 : W := mkw 0x0000000000000000 0x0000000000000000 0x600102030006127c 0xf300081018003093

def z60 : W := mkw 0x805566af0b5e76f8 0xbc02ab35785af3b7 0xe8ffffff1fffffff 0xff47fffff8ffffff

def z61 : W := mkw 0x27ffdfff60a9a31d 0x113ffefffb054d18 0xf7ffffffe0f9e39b 0xffbfffffff07cf1c

def z62 : W := mkw 0x21105f590000000c 0x010882fac8000000 0x00000c1c00000000 0x00000060e0000000

def z63 : W := mkw 0x04e500a29c4404d2 0x8827280514e22026 0xfffd13e3ffc71fff 0xffffe89f1ffe38ff

def z64 : W := mkw 0x8a5fe60d4bfe7229 0xf452ff306a5ff391 0x603fee1f07fef27e 0xfb01ff70f83ff793

def z65 : W := mkw 0x0045000008440000 0x8002280000422000 0xc8cd000018c6000d 0xb646680000c63000

def z66 : W := mkw 0x27ef99f200000014 0x013f7ccf90000000 0x87cc11e000000000 0x043e608f00000000

def z67 : W := mkw 0x27ffdffb000004dc 0x093ffeffd8000026 0xe7ffffff00011ff0 0x7f3ffffff80008ff

def z68 : W := mkw 0x0100180020018000 0x000800c001000c00 0x17000c00e000e002 0x08b8006007000700

def z69 : W := mkw 0x27ffdffb0844001c 0x813ffeffd8422000 0xefffffff18c6000d 0xff7ffffff8c63000

def z70 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x0033ee1f073ef066 0x18019f70f839f783

def z71 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0x17300c00e700e002 0x08b9806007380700

def z72 : W := mkw 0x85b07f0db71bfa2a 0x342d83f86db8dfd1 0xfff3ff9fff3ffe7f 0xffff9ffcfff9fff3

def z73 : W := mkw 0x020a000000000000 0x0010500000000000 0xc70e000000000000 0x2e38700000000000

def z74 : W := mkw 0x0000000094000002 0x0000000004a00000 0x18000000ff000007 0x80c0000007f80000

def z75 : W := mkw 0xa7baff5d031a722c 0x353dd7fae818d391 0x6733ee1f073ef27e 0xfb399f70f839f793

def z76 : W := mkw 0x05b01f00b4018802 0x002d80f805a00c40 0xdff01f80f8010c01 0x5eff80fc07c00860

def z77 : W := mkw 0x21105ffb000004dc 0x090882ffd8000026 0x20001fff00011ff0 0x410000fff80008ff

def z78 : W := mkw 0x8cf5e6099f56502a 0xe467af304cfab281 0x08f1e2031f061064 0x10478f1018f83083

def z79 : W := mkw 0x85f57fafbf5ffefa 0xbc2fabfd7dfafff7 0xffffffffffffffff 0xffffffffffffffff

def z80 : W := mkw 0x831a7e5d031a7228 0x3418d3f2e818d391 0xe73ffe7f073ef27e 0xff39fff3f839f793

def z81 : W := mkw 0x0fffbfa2fff7dcd3 0xe87ffdfd17ffbee6 0xffffffe3ffffffff 0xffffffff1fffffff

def z82 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xe7ffffff00c603e8 0x7f3ffffff806301f

def z83 : W := mkw 0x2ffffffbd6b2001f 0x417fffffdeb59000 0xf7ffffffe7380002 0x7fbfffffff39c000

def z84 : W := mkw 0x05f51fa2b501d812 0x202fa8fd15a80ec0 0xfffd1fe3ff01fc17 0xffffe8ff1ff80fe0

def z85 : W := mkw 0x0000000460a9a301 0x1000000023054d18 0xf00c1060e0f9e39b 0xe78060830707cf1c

def z86 : W := mkw 0x27ffdffb9500581e 0x213ffeffdca802c0 0xefffffff1f001c04 0x7f7ffffff8f800e0

def z87 : W := mkw 0x0000000095005802 0x2000000004a802c0 0x080000001f001c04 0x0040000000f800e0

def z88 : W := mkw 0x010018542009a300 0x100800c2a1004d18 0x20001c7c0001e390 0x410000e3e0000f1c

def z89 : W := mkw 0x8000600d031a7228 0x340003006818d391 0x2003e01f073ef27e 0xa1001f00f839f793

def z90 : W := mkw 0x034f18f668eda7d1 0x981a78c7b3476d3e 0xffcf1ffff8ffffff 0xfffe78ffffc7ffff

def z91 : W := mkw 0x07ba1f54f5a9fb03 0x303dd0faa7ad4fd8 0xfffe1ffcfff9ff9f 0xfffff0ffe7ffcffc

def z92 : W := mkw 0x0eefa0a2def60013 0xc0777d0516f7b000 0xfffff3e3fffe000f 0xffffff9f1ffff000

def z93 : W := mkw 0x8010460d01087228 0x3400823068084391 0x20000e1f0000f270 0x41000070f8000793

def z94 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8cc13e018c11f9d 0xf746609f00c608fc

def z95 : W := mkw 0x0a4fa0a24af604d1 0xc8527d051257b026 0x200fe06300fe03e8 0x21007f031807f01f

def z96 : W := mkw 0x26ffc7fb0000001c 0x0137fe3fd8000000 0x20ffe3ff00000000 0x3107ff1ff8000000

def z97 : W := mkw 0x08452000def60003 0xc042290006f7b000 0xd8cd0000fffe000f 0xb6c6680007fff000

def z98 : W := mkw 0x80002004031a7220 0x340001002018d391 0x4033e000073ef27e 0xba019f000039f793

def z99 : W := mkw 0x85b03f04b71bfa22 0x342d81f825b8dfd1 0xdff01f80ff3ffe7f 0xdeff80fc07f9fff3

def z100 : W := mkw 0x2045c0ab0000001c 0x01022e0558000000 0x0001e00300000000 0x00000f0018000000

def z101 : W := mkw 0x0eefa004defe2203 0xd0777d0026f7f110 0xffffec1cfffee21f 0xffffff60e7fff710

def z102 : W := mkw 0x00000000084404c0 0x8800000000422026 0x0800000018c71ffd 0x8040000000c638ff

def z103 : W := mkw 0x0eefa000d6b20003 0x40777d0006b59000 0xd7ffe000e7380002 0x3ebfff000739c000

def z104 : W := mkw 0x21105ffb0000001c 0x010882ffd8000000 0x20001fff00000000 0x410000fff8000000

def z105 : W := mkw 0x004500a2084404d0 0x8802280510422026 0x280d006318c71ffd 0xa140680318c638ff

def z106 : W := mkw 0xa7ffffff031a723c 0x353ffffff818d391 0xe7ffffff073ef27e 0xff3ffffff839f793

def z107 : W := mkw 0x000000a2000004d0 0x0800000510000026 0x200013e300011ff0 0x4100009f180008ff

def z108 : W := mkw 0x004500a200000010 0x0002280510000000 0xe8cd13e318011c15 0xf746689f18c008e0

def z109 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0x5733e000e73e000e 0xbab99f000739f000

def z110 : W := mkw 0x04a0000094000002 0x0025000004a00000 0xdff00000ff000007 0x9eff800007f80000

def z111 : W := mkw 0x27ef99f660a9a315 0x113f7ccfb3054d18 0xf7ce1dfce0f9e39b 0xefbe70efe707cf1c

def z112 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xd7301c00e701e013 0xceb980e007380f00

def z113 : W := mkw 0x07ba1f54f5a9fb03 0x303dd0faa7ad4fd8 0x17320c1ce738e002 0x08b99060e739c700

def z114 : W := mkw 0x01101f002101d800 0x200880f801080ec0 0xc8c01f801801fc15 0xd64600fc00c00fe0

def z115 : W := mkw 0x000000a2000004d0 0x0800000510000026 0x0000038300001c60 0x0000001c180000e3

def z116 : W := mkw 0x2ffffffbdef6001f 0xc17fffffdef7b000 0xfffffffffffe000f 0xfffffffffffff000

def z117 : W := mkw 0x04a0000094000002 0x0025000004a00000 0x08f000001f000004 0x1047800000f80000

def z118 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0x273fec7f00000000 0x2939ff63f8000000

def z119 : W := mkw 0x08002004feffa303 0xd040010027f7fd18 0x18000000ffffe39f 0x80c0000007ffff1c

def z120 : W := mkw 0x0fefb854feffa303 0xd07f7dc2a7f7fd18 0xfffffc7cffffe39f 0xffffffe3e7ffff1c

def z121 : W := mkw 0x06ef800094000002 0x00377c0004a00000 0xdfffe000ff000007 0xbeffff0007f80000

def z122 : W := mkw 0x020a000040a00001 0x0010500002050000 0xf70e1060e0f9039b 0xefb870830707c81c

def z123 : W := mkw 0x24b0c7090000000c 0x0125863848000000 0x0030e00000000000 0x0001870000000000

def z124 : W := mkw 0x005546ab00000018 0x0002aa3558000000 0xe0ffffff00000000 0x7f07fffff8000000

def z125 : W := mkw 0x201047ab0000001c 0x0100823d58000000 0x0000038300000000 0x0000001c18000000

def z126 : W := mkw 0x06ef800000000000 0x00377c0000000000 0xc7ffe00000000000 0x3e3fff0000000000

def z127 : W := mkw 0x0000000000000000 0x0000000000000000 0xe00c106000c10399 0xe70060830006081c

def z128 : W := mkw 0x800020040b5e76e0 0xbc000100205af3b7 0x080000001fffffff 0x8040000000ffffff

def z129 : W := mkw 0x030a185440a82301 0x101850c2a2054118 0xe70e1c7c00f80388 0x6f3870e3e007c01c

def z130 : W := mkw 0x831a5e5d61a9f329 0x3418d2f2eb0d4f99 0xf70e1e7fe0f9f3fb 0xefb870f3ff07cf9f

def z131 : W := mkw 0x8010460d01087228 0x3400823068084391 0x00000c1c0000e000 0x00000060e0000700

def z132 : W := mkw 0x031a5e5900000008 0x0018d2f2c8000000 0xe73ffe7f00000000 0x7f39fff3f8000000

def z133 : W := mkw 0x030a185060a18101 0x001850c283050c08 0xf70c1060e0c10399 0xe7b860830706081c

def z134 : W := mkw 0x04a0000094000002 0x0025000004a00000 0xdff01380ff011c17 0xdeff809c07f808e0

def z135 : W := mkw 0x81105f0d2109fa28 0x340882f869084fd1 0x20001f9f0001fe70 0x410000fcf8000ff3

def z136 : W := mkw 0x005546ab084404d8 0x8802aa3558422026 0xe8ffffff18c71ffd 0xff47fffff8c638ff

def z137 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00c000000c00009 0xa600600000060000

def z138 : W := mkw 0x0a4fa000def60003 0xc0527d0006f7b000 0x180fe000fffe000f 0xa0c07f0007fff000

def z139 : W := mkw 0xa25fe6ff031a723c 0x3512ff37f818d391 0x603fee7f073ef27e 0xfb01ff73f839f793

def z140 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x9fcc0000fffe000f 0x84fe600007fff000

def z141 : W := mkw 0x020a005440a82301 0x10105002a2054118 0x200e007c00f80388 0x21007003e007c01c

def z142 : W := mkw 0x0000000460a9a301 0x1000000023054d18 0x10000000e038e002 0x008000000701c700

def z143 : W := mkw 0x224fc0fb084404dc 0x89127e07d8422026 0x200fe07f00c603e8 0x21007f03f806301f

def z144 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x9ffee000fff80003 0x0cfff70007ffc000

def z145 : W := mkw 0x0fefb900fef78803 0xc07f7dc807f7bc40 0xdffff180ffff0c0f 0xbeffff8c07fff860

def z146 : W := mkw 0x0fbabf00f7b3d803 0x607dd5f807bd9ec0 0xdff2ff80ff39fc17 0xdeff97fc07f9cfe0

def z147 : W := mkw 0x030a185060a18101 0x001850c283050c08 0xd70c1c60e0c1e193 0xceb860e307060f0c

def z148 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0x970c1060e0f9e39b 0x84b860830707cf1c

def z149 : W := mkw 0x030a185400082200 0x101850c2a0004110 0xe70e1c7c0038e21a 0xef3870e3e001c710

def z150 : W := mkw 0x200040fb0000001c 0x01000207d8000000 0x2000007f00000000 0x01000003f8000000

def z151 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffffff0006127c 0xff3ffffff8003093

def z152 : W := mkw 0x0100180020018000 0x000800c001000c00 0x00001c000001e010 0x400000e000000f00

def z153 : W := mkw 0x024f00f648ec27d1 0x98127807b247613e 0xe8cf13ff18ff1ffd 0xf746789ff8c7f8ff

def z154 : W := mkw 0x85b07f0db71bfa2a 0x342d83f86db8dfd1 0x7733ee1fe73ef27e 0xfbb99f70ff39f793

def z155 : W := mkw 0x220ac0590000000c 0x01105602c8000000 0x0002e01c00000000 0x00001700e0000000

def z156 : W := mkw 0x0fffbf54fffffb03 0xf07ffdfaa7ffffd8 0xfffffffcffffff9f 0xffffffffe7fffffc

def z157 : W := mkw 0x08000000dce40003 0xc040000006e72000 0x18000000f8c00001 0x00c0000007c60000

def z158 : W := mkw 0x0000000460a9a301 0x1000000023054d18 0x10000000e0f9e39b 0x808000000707cf1c

def z159 : W := mkw 0x24f5c7ab0000001c 0x0127ae3d58000000 0x00f1e38300000000 0x10078f1c18000000

def z160 : W := mkw 0x010018542009a300 0x100800c2a1004d18 0x60021c7c0039e39a 0xeb0010e3e001cf1c

def z161 : W := mkw 0x0045000008440000 0x8002280000422000 0xc8cd138018c71c1d 0xf646689c00c638e0

def z162 : W := mkw 0x2eefe0fbdef6001f 0xc1777f07def7b000 0xffffe07ffffe000f 0xbfffff03fffff000

def z163 : W := mkw 0x8010660903125028 0x2400833048189281 0x0031e20307061064 0x10018f1018383083

def z164 : W := mkw 0x00000000b501d802 0x2000000005a80ec0 0xd8c01380ff01fc17 0xd6c6009c07f80fe0

def z165 : W := mkw 0x8000600d021a2228 0x140003006810d111 0x6033e01f073e026e 0xbb019f00f839f013

def z166 : W := mkw 0x00000000084404c0 0x8800000000422026 0x0800000018061c64 0x0040000000c030e3

def z167 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x2033ec1f073ee26a 0x29019f60f839f713

def z168 : W := mkw 0x27ffdffbb501d81e 0x213ffeffdda80ec0 0xf7ffffffe700e002 0x7fbfffffff380700

def z169 : W := mkw 0x06ef800008440000 0x80377c0000422000 0xcfffe00018c6000d 0xbe7fff0000c63000

def z170 : W := mkw 0x024f00a248e404d1 0x8812780512472026 0xffcf13e3f8ff1fff 0xfffe789f1fc7f8ff

def z171 : W := mkw 0x004500a200000010 0x0002280510000000 0x200d006300000000 0x2100680318000000

def z172 : W := mkw 0x8010660d0b5e76e8 0xbc008330685af3b7 0x6833ee1f1fffffff 0xfb419f70f8ffffff

def z173 : W := mkw 0x05b05f09b501d80a 0x202d82f84da80ec0 0xfff3ff9fff01fc17 0xffff9ffcfff80fe0

def z174 : W := mkw 0x05b01f0000000000 0x002d80f800000000 0x07300c0000000000 0x0839806000000000

def z175 : W := mkw 0x87ba7f5df7bbfb2b 0x343dd3faefbddfd9 0xffffffffffffffff 0xffffffffffffffff

def z176 : W := mkw 0x0fbabf00f7b3d803 0x607dd5f807bd9ec0 0x1732ec00e738e002 0x08b997600739c700

def z177 : W := mkw 0x05b05f0900000008 0x002d82f848000000 0xe7f3ff9f00000000 0x7f3f9ffcf8000000

def z178 : W := mkw 0x805546af094c76f8 0xbc02aa35784a63b7 0xe8cd1fff18c7fffd 0xf74668fff8c63fff

def z179 : W := mkw 0x0eef8000dce40003 0xc0777c0006e72000 0xdfffe000f8c00001 0x3effff0007c60000

def z180 : W := mkw 0x0045000008440000 0x8002280000422000 0x08c1000018060004 0x1046080000c03000

def z181 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x4032ee1c0738f016 0xda019770e039c780

def z182 : W := mkw 0x034f18f668eda7d1 0x981a78c7b3476d3e 0xffce1dfcf8f9ef9b 0xeffe70efe7c7cf7c

def z183 : W := mkw 0x04b0070095005802 0x2025803804a802c0 0x0030000007000000 0x0001800000380000

def z184 : W := mkw 0x030a185040a00001 0x001850c282050000 0xf70e1c7ce0f8000b 0xefb870e3e707c000

def z185 : W := mkw 0x0eef80a2dce404d3 0xc8777c0516e72026 0xffcd13e3f8c71ffd 0xf7fe689f1fc638ff

def z186 : W := mkw 0x24f5c7ab084404dc 0x8927ae3d58422026 0x08f1e38318061c64 0x10478f1c18c030e3

def z187 : W := mkw 0x0a0aa00042b20001 0x4050550002159000 0x0002e00000380000 0x000017000001c000

def z188 : W := mkw 0x24f5c7ab084404dc 0x8927ae3d58422026 0xe8fdf3e318c71ffd 0xf747ef9f18c638ff

def z189 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0xd73ee000e7f8000b 0xaeb9f700073fc000

def z190 : W := mkw 0x0ce5a0009e560002 0xc0672d0004f2b000 0xc8fde0001fc6000d 0xb647ef0000fe3000

def z191 : W := mkw 0x81107e5d231bf328 0x340883f2e918df99 0x6033fe7f073ff3fe 0xfb019ff3f839ff9f

def z192 : W := mkw 0x031a5e5d60a9a309 0x1018d2f2eb054d18 0xf73ffe7fe0f9e39b 0xffb9fff3ff07cf1c

def z193 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000c000000e012 0xca00006000000700

def z194 : W := mkw 0x07ef985000000000 0x003f7cc280000000 0xe7fffc7c00000000 0x7f3fffe3e0000000

def z195 : W := mkw 0x84b0670d971a7a2a 0x342583386cb8d3d1 0x68f3ef9f1f3efe7e 0xfb479f7cf8f9f7f3

def z196 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000100000010011 0xc600008000000800

def z197 : W := mkw 0x27ef99f2084404d4 0x893f7ccf90422026 0x8fcc11e018c10d81 0x047e608f00c6086c

def z198 : W := mkw 0x80002004021a2220 0x140001002010d111 0x00000000003e0268 0x000000000001f013

def z199 : W := mkw 0x004500a208440010 0x8002280510422000 0xe8cd13e318c6000d 0xf746689f18c63000

def z200 : W := mkw 0x004500a2084404d0 0x8802280510422026 0x88cd13e318c71de5 0x1446689f18c638ef

def z201 : W := mkw 0x235fdffb0000001c 0x011afeffd8000000 0x200fffff00000000 0x61007ffff8000000

def z202 : W := mkw 0x020a000460a9a301 0x1010500023054d18 0xd70e0000e0f9e39b 0xaeb870000707cf1c

def z203 : W := mkw 0x004520000a560000 0x800229000052b000 0xc8ffe0001ffe000f 0xbe47ff0000fff000

def z204 : W := mkw 0x80002004b71bfa22 0x3400010025b8dfd1 0x18000000ff3ffe7f 0x80c0000007f9fff3

def z205 : W := mkw 0x2effe7abdef6001f 0xc177ff3d5ef7b000 0xdfffe383fffe000f 0xbeffff1c1ffff000

def z206 : W := mkw 0x010018f62009a7d0 0x180800c7b1004d3e 0x20001fff0001fff0 0x410000fff8000fff

def z207 : W := mkw 0x0010060001005000 0x2000803000080280 0x00300c000700e002 0x0801806000380700

def z208 : W := mkw 0x05b01f0000000000 0x002d80f800000000 0xcff01f8018011c15 0xde7f80fc00c008e0

def z209 : W := mkw 0x0000000440a82301 0x1000000022054118 0x0000000000f80388 0x000000000007c01c

def z210 : W := mkw 0x0010460900000008 0x0000823048000000 0x6033ee1f0006127c 0xfb019f70f8003093

def z211 : W := mkw 0x27ffdffb60a1811d 0x013ffeffdb050c08 0xf7ffffffe0c10181 0x7fbfffffff06080c

def z212 : W := mkw 0xa7baff5d031a722c 0x353dd7fae818d391 0x0732ec1c0738e002 0x08399760e039c700

def z213 : W := mkw 0x04a00000b501d802 0x2025000005a80ec0 0xdff00000ff01fc17 0x9eff800007f80fe0

def z214 : W := mkw 0x004500a2084404d0 0x8802280510422026 0x08c1038318061c64 0x1046081c18c030e3

def z215 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xefffffff18061c64 0x7f7ffffff8c030e3

def z216 : W := mkw 0x05f51fa200000010 0x002fa8fd10000000 0xe7fd1fe300000000 0x7f3fe8ff18000000

def z217 : W := mkw 0x225fc6fb0000001c 0x0112fe37d8000000 0x603fee7f00000000 0x7b01ff73f8000000

def z218 : W := mkw 0x8000600d021a2228 0x140003006810d111 0x2003e01f003e0268 0x21001f00f801f013

def z219 : W := mkw 0x0010260003125000 0x2000813000189280 0x4033ee00073ef01e 0xfa019f700039f780

def z220 : W := mkw 0x0eef8000dce40003 0xc0777c0006e72000 0x9fcc0000f8c00001 0x04fe600007c60000

def z221 : W := mkw 0x21105ffb0000001c 0x010882ffd8000000 0x6033ffff00000000 0x7b019ffff8000000

def z222 : W := mkw 0x224fc0fb084404dc 0x89127e07d8422026 0xe8cff3ff18c71ffd 0xf7467f9ff8c638ff

def z223 : W := mkw 0x8000000401087220 0x3400000020084391 0x000000000000f270 0x0000000000000793

def z224 : W := mkw 0x06ffc60900000008 0x0037fe3048000000 0xe7ffee1f00000000 0x7f3fff70f8000000

def z225 : W := mkw 0x01101f00b501d802 0x200880f805a80ec0 0x18001f80ff01fc17 0xc0c000fc07f80fe0

def z226 : W := mkw 0x0fefb8f6feffa7d3 0xd87f7dc7b7f7fd3e 0xffffffffffffffff 0xffffffffffffffff

def z227 : W := mkw 0x801066af031a76f8 0x3c0083357818d3b7 0x6033ffff073ffffe 0xfb019ffff839ffff

def z228 : W := mkw 0x04e5800000000000 0x00272c0000000000 0x00f1e00000000000 0x10078f0000000000

def z229 : W := mkw 0x0100185460a9a301 0x100800c2a3054d18 0x30001c7ce0f9e39b 0xc18000e3e707cf1c

def z230 : W := mkw 0xa1105fff0108723c 0x350882fff8084391 0x20001fff0000f270 0x410000fff8000793

def z231 : W := mkw 0x020a005440a82301 0x10105002a2054118 0xe00e107c00f90399 0xe7007083e007c81c

def z232 : W := mkw 0x27ffdf590000000c 0x013ffefac8000000 0xc7ffec1c00000000 0x3e3fff60e0000000

def z233 : W := mkw 0x004500a200000010 0x0002280510000000 0xe0cd13e300000000 0x7706689f18000000

def z234 : W := mkw 0x0fef9850fce58103 0xc07f7cc287e72c08 0x9fcc1060f8c10181 0x04fe608307c6080c

def z235 : W := mkw 0x0effa600dff65003 0xe077fd3006ffb280 0xdfffee00fffef01f 0xfeffff7007fff780

def z236 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0x17020c1ce038e002 0x08b81060e701c700

def z237 : W := mkw 0x2fffdffbdce4001f 0xc17ffeffdee72000 0xfffffffff8c00001 0x7fffffffffc60000

def z238 : W := mkw 0x030a185060a18101 0x001850c283050c08 0xd70e1060e0f9018b 0xaeb870830707c80c

def z239 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xe8cd13e318061c64 0x7746689f18c030e3

def z240 : W := mkw 0x05b01f00bd45dcc2 0xa82d80f805ea2ee6 0xdff01f80ffc7ffff 0xdeff80fc07fe3fff

def z241 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xc8cd11e018c70d8d 0xb646688f00c6386c

def z242 : W := mkw 0x0010460900000008 0x0000823048000000 0x20000e1f00000000 0x41000070f8000000

def z243 : W := mkw 0x034f18f268e585d1 0x881a78c793472c2e 0x9fcc11e0f8c10d81 0x04fe608f07c6086c

def z244 : W := mkw 0x06aa0000d4a00003 0x0035500006a50000 0xdffe0000fff8000f 0xbefff00007ffc000

def z245 : W := mkw 0xafffffffdffe723f 0xf57ffffffefff391 0xfffffffffffef27f 0xfffffffffffff793

def z246 : W := mkw 0x831a7e5d63bbf329 0x3418d3f2eb1ddf99 0x1732ec1ce738e002 0x08b99760e739c700

def z247 : W := mkw 0x8010660903125028 0x2400833048189281 0x4031ee030706f076 0xda018f7018383783

def z248 : W := mkw 0x06ef800040a00001 0x00377c0002050000 0xd7ffe000e0f8000b 0xbebfff000707c000

def z249 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xffffe063fffe03ef 0xbfffff031ffff01f

def z250 : W := mkw 0x00000000b501d802 0x2000000005a80ec0 0x18000000ff01fc17 0x80c0000007f80fe0

def z251 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0x970e1c7ce0f9e183 0x0cb870e3e707cf0c

def z252 : W := mkw 0xa7fffffb0312503c 0x253fffffd8189281 0xe7ffffff07061064 0x7f3ffffff8383083

def z253 : W := mkw 0x01551fa22945dcd0 0xa80aa8fd114a2ee6 0xe8cd1fe318c7fffd 0xf74668ff18c63fff

def z254 : W := mkw 0x004500a2084404d0 0x8802280510422026 0x88cc11e018c71ffd 0x8446608f00c638ff

def z255 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0xc7f2ff9c00000000 0x5e3f97fce0000000

def z256 : W := mkw 0x0000000008440000 0x8000000000422000 0x0800000018c6000d 0x8040000000c63000

def z257 : W := mkw 0x020a005040a00101 0x0010500282050008 0x000c006000c00180 0x000060030006000c

def z258 : W := mkw 0x0010460901005008 0x2000823048080280 0x6033ee1f0700f016 0xfb019f70f8380780

def z259 : W := mkw 0x00000000bd45dcc2 0xa800000005ea2ee6 0x18000000ffc7ffff 0x80c0000007fe3fff

def z260 : W := mkw 0x0000200002120000 0x0000010000109000 0x6033e203073e127e 0xfb019f101839f093

def z261 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000020000001014 0xd200001000000080

def z262 : W := mkw 0x801046af010876f8 0x3c008235780843b7 0x20001fff0001fff0 0x410000fff8000fff

def z263 : W := mkw 0x01101e002101d000 0x200880f001080e80 0xd7301e00e701f017 0xdeb980f007380f80

def z264 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xd70e0c1ce0f8e00b 0xaeb87060e707c700

def z265 : W := mkw 0x0ce5a000def60003 0xc0672d0006f7b000 0x18f1e000fffe000f 0x90c78f0007fff000

def z266 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xfffc1fe0ffc1ff9f 0xffffe0ff07fe0ffc

def z267 : W := mkw 0x004500a2084404d0 0x8802280510422026 0x88cc11e018c10d81 0x0446608f00c6086c

def z268 : W := mkw 0x0010060001005000 0x2000803000080280 0x0030020007001004 0x1001801000380080

def z269 : W := mkw 0x020a000440a82201 0x1010500022054110 0xf70e0c1ce0f8e21b 0xefb87060e707c710

def z270 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xfffff060ffff039f 0xffffff8307fff81c

def z271 : W := mkw 0x08002000d6b20003 0x4040010006b59000 0x10000000e7380002 0x008000000739c000

def z272 : W := mkw 0x06ef800000000000 0x00377c0000000000 0x87cc000000000000 0x043e600000000000

def z273 : W := mkw 0x8000600d021a2228 0x140003006810d111 0x0002e01c00380000 0x00001700e001c000

def z274 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0xdff2e000ff380007 0x9eff970007f9c000

def z275 : W := mkw 0x85b07f0d031a7228 0x342d83f86818d391 0xe7f3ff9f073ef27e 0xff3f9ffcf839f793

def z276 : W := mkw 0x05b01f0094000002 0x002d80f804a00000 0xdff01f80ff000007 0xdeff80fc07f80000

def z277 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0x6733ee1f00000000 0x7b399f70f8000000

def z278 : W := mkw 0x26ffc7ab0000001c 0x0137fe3d58000000 0xc7ffe38300000000 0x3e3fff1c18000000

def z279 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z280 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xdffff380ffff1c1f 0xfeffff9c07fff8e0

def z281 : W := mkw 0x8fffff0dfffffa2b 0xf47ffff86fffffd1 0xffffff9ffffffe7f 0xfffffffcfffffff3

def z282 : W := mkw 0x27ff9ff2b501d816 0x213ffcff95a80ec0 0xdffc1fe0ff01fc17 0xdeffe0ff07f80fe0

def z283 : W := mkw 0x0010460900000008 0x0000823048000000 0x0032ec1c00000000 0x08019760e0000000

def z284 : W := mkw 0x0a4fa0004af60001 0xc0527d000257b000 0x403fe00007fe000e 0xba01ff00003ff000

def z285 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xffce1ffcf8f9ff9f 0xfffe70ffe7c7cffc

def z286 : W := mkw 0x031a1e5461a9f301 0x3018d0f2a30d4f98 0xf73e1e7ce7f9f39f 0xffb9f0f3e73fcf9c

def z287 : W := mkw 0x08002000def60003 0xc040010006f7b000 0x18000000fffe000f 0x80c0000007fff000

def z288 : W := mkw 0x004500a2084404d0 0x8802280510422026 0x600d026300c613fc 0xf30068131806309f

def z289 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x2031ee1f0706f274 0x51018f70f8383793

def z290 : W := mkw 0x00000004f5a9fb03 0x3000000027ad4fd8 0x18000000fff9ff9f 0x80c0000007ffcffc

def z291 : W := mkw 0x0000000020018000 0x0000000001000c00 0x10000000e001e013 0x8080000007000f00

def z292 : W := mkw 0x27ffdffbbd45dcde 0xa93ffeffddea2ee6 0xffffffffffc7ffff 0xfffffffffffe3fff

def z293 : W := mkw 0xa7ffffff63bbf33d 0x353ffffffb1ddf99 0xf7ffffffe7fff3ff 0xffbfffffff3fff9f

def z294 : W := mkw 0x27ffdfff40a8231d 0x113ffefffa054118 0xe7ffffff00f80388 0x7f3ffffff807c01c

def z295 : W := mkw 0x88002004dffe7223 0xf440010026fff391 0x18000000fffef27f 0x80c0000007fff793

def z296 : W := mkw 0x27ef99f200000014 0x013f7ccf90000000 0xe7ce1dfc00000000 0x6f3e70efe0000000

def z297 : W := mkw 0x0100180020018000 0x000800c001000c00 0xdfc01f80f801fc17 0xdefe00fc07c00fe0

def z298 : W := mkw 0x000000002101d800 0x2000000001080ec0 0x000000000001fc10 0x0000000000000fe0

def z299 : W := mkw 0x26efc0fb0000001c 0x01377e07d8000000 0xe7ffe07f00000000 0x3f3fff03f8000000

def z300 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xf70f1e7fe0fff3ff 0xffb878f3ff07ff9f

def z301 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0x17301f80e701fc12 0x48b980fc07380fe0

def z302 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xd7f01f80e700e002 0x5ebf80fc07380700

def z303 : W := mkw 0x030a185000000000 0x001850c280000000 0xe70e1c7c00c10399 0xef3870e3e006081c

def z304 : W := mkw 0x0000000400082200 0x1000000020004110 0x20000c1c0000e210 0x41000060e0000710

def z305 : W := mkw 0x01101f002101d800 0x200880f801080ec0 0xd7001f80e001fc13 0xceb800fc07000fe0

def z306 : W := mkw 0x8ebae60dd7ba722b 0x7475d7306ebdd391 0x1732ec1ce738e002 0x08b99760e739c700

def z307 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x173fe000e7fe000a 0x28b9ff00073ff000

def z308 : W := mkw 0x004500a200000010 0x0002280510000000 0x80cc11e000000000 0x0406608f00000000

def z309 : W := mkw 0x0045000008440000 0x8002280000422000 0x000d000000c60008 0x2000680000063000

def z310 : W := mkw 0x210019f200000014 0x010800cf90000000 0x000011e000000000 0x0000008f00000000

def z311 : W := mkw 0x00000000b501d802 0x2000000005a80ec0 0x10000000e700e002 0x0080000007380700

def z312 : W := mkw 0x07ba1f5460a9a301 0x103dd0faa3054d18 0xf7fe1ffce0f9e39b 0xffbff0ffe707cf1c

def z313 : W := mkw 0x04a0200096120002 0x0025010004b09000 0xdff3e000ff3e000f 0xbeff9f0007f9f000

def z314 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0x9ff01d80ff01ec03 0x0cff80ec07f80f60

def z315 : W := mkw 0xa4f5e7af031a723c 0x3527af3d7818d391 0x60f3ef9f073ef27e 0xfb079f7cf839f793

def z316 : W := mkw 0x2ffffffbdef604df 0xc97fffffdef7b026 0xffffffffffff1fff 0xfffffffffffff8ff

def z317 : W := mkw 0x804520a60b5e76f0 0xbc022905305af3b7 0xe8cd13e31fffffff 0xf746689f18ffffff

def z318 : W := mkw 0x0000000000000000 0x0000000000000000 0x2001000300060268 0x2100080018003013

def z319 : W := mkw 0x0eefa000def604c3 0xc8777d0006f7b026 0xdfffe000ffff1fff 0xbeffff0007fff8ff

def z320 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xc8cd038318c61c6d 0xb646681c18c630e3

def z321 : W := mkw 0x0000200002120000 0x0000010000109000 0x00000000073e000e 0x800000000039f000

def z322 : W := mkw 0x0ca0a00096120002 0x4065050004b09000 0x0030e00007000000 0x0001870000380000

def z323 : W := mkw 0x04a0010094000802 0x0025000804a00040 0x08c0018018000c00 0x0046000c00c00060

def z324 : W := mkw 0xa7ffffffb71bfa3e 0x353ffffffdb8dfd1 0xffffffffff3ffe7f 0xfffffffffff9fff3

def z325 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0x9fc01f80f801fc11 0x44fe00fc07c00fe0

def z326 : W := mkw 0x8000600902120028 0x0400030048109001 0x0001e00300060060 0x00000f0018003003

def z327 : W := mkw 0x0eefa000fff7d803 0xe0777d0007ffbec0 0xdfffe000fffffc1f 0xbeffff0007ffffe0

def z328 : W := mkw 0x004520a20a5604d0 0x880229051052b026 0xe8fff3e31fff1fff 0xff47ff9f18fff8ff

def z329 : W := mkw 0x85b05f0db509fa2a 0x342d82f86da84fd1 0xfff01f9fff01fe77 0xdfff80fcfff80ff3

def z330 : W := mkw 0x05f51f00bd45d802 0xa02fa8f805ea2ec0 0xdffd1f80ffc7fc1f 0xfeffe8fc07fe3fe0

def z331 : W := mkw 0x0ce5a0009e560002 0xc0672d0004f2b000 0x48f3e0001f3e000e 0xba479f0000f9f000

def z332 : W := mkw 0x030a185060a18101 0x001850c283050c08 0xf70e1c7ce0c10181 0x6fb870e3e706080c

def z333 : W := mkw 0x05b01f0095005802 0x202d80f804a802c0 0xcff01f801f001c04 0x5e7f80fc00f800e0

def z334 : W := mkw 0x030a180060a18001 0x001850c003050c00 0xd70e1c00e0f9e01b 0xeeb870e00707cf00

def z335 : W := mkw 0x0000000400082200 0x1000000020004110 0x000000000038e21a 0x800000000001c710

def z336 : W := mkw 0x05b01f04b509fa02 0x302d80f825a84fd0 0xfff21f9cff39fe1f 0xffff90fce7f9cff0

def z337 : W := mkw 0x2ffffffb4af6001d 0xc17fffffda57b000 0xe7ffffff00fe0008 0x7f3ffffff807f000

def z338 : W := mkw 0x8000600d021a2228 0x140003006810d111 0x6003ec1f003ee27a 0xeb001f60f801f713

def z339 : W := mkw 0x27ef99f260a18115 0x013f7ccf93050c08 0x97cc11e0e0c10181 0x04be608f0706080c

def z340 : W := mkw 0x234fd8ff60a9a31d 0x111a7ec7fb054d18 0xf70ffc7fe0f9e39b 0xefb87fe3ff07cf1c

def z341 : W := mkw 0x030a385462bba301 0x101851c2a315dd18 0xf73ffc7ce7ffe39f 0xffb9ffe3e73fff1c

def z342 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xe00d106300c703f9 0xe70068831806381f

def z343 : W := mkw 0x0100180000000000 0x000800c000000000 0xc7001c0000000000 0x4e3800e000000000

def z344 : W := mkw 0x0fefb854feffa303 0xd07f7dc2a7f7fd18 0xdfffec1cfffee00f 0xbeffff60e7fff700

def z345 : W := mkw 0x830a385463bbf321 0x341851c2a31ddf99 0xf70e1c7ce7fff3ff 0xefb870e3e73fff9f

def z346 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xefffffff18011c15 0xff7ffffff8c008e0

def z347 : W := mkw 0x024f800000000000 0x00127c0000000000 0x000fe00000000000 0x20007f0000000000

def z348 : W := mkw 0x0000000000000000 0x0000000000000000 0x200c006000c00388 0x210060030006001c

def z349 : W := mkw 0x0045000008440000 0x8002280000422000 0x88cc000018c00001 0x0446600000c60000

def z350 : W := mkw 0x80002004031a7220 0x340001002018d391 0x000000000738e002 0x000000000039c700

def z351 : W := mkw 0x231a5fff60a9a31d 0x1118d2fffb054d18 0xf70e1fffe0f9e39b 0xefb870ffff07cf1c

def z352 : W := mkw 0x0100190020018800 0x000800c801000c40 0x0000118000010c00 0x0000008c00000860

def z353 : W := mkw 0x27ffdffff5a9fb1f 0x313ffeffffad4fd8 0xfffffffffff9ff9f 0xffffffffffffcffc

def z354 : W := mkw 0x80002004031a7220 0x340001002018d391 0x60010203073ef27e 0xf30008101839f793

def z355 : W := mkw 0x05a01900b4018802 0x002d00c805a00c40 0xdfc01d80f801ec13 0xcefe00ec07c00f60

def z356 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xb70e107ce0f90389 0x25b87083e707c81c

def z357 : W := mkw 0x84b0660d971a722a 0x342583306cb8d391 0xfff3ee1fff3ef27f 0xffff9f70fff9f793

def z358 : W := mkw 0x0eef80a2dce404d3 0xc8777c0516e72026 0x9fcc11e0f8c10d81 0x04fe608f07c6086c

def z359 : W := mkw 0x004500a2084404d0 0x8802280510422026 0x08c0018018000c00 0x0046000c00c00060

def z360 : W := mkw 0x0010060401087200 0x3000803020084390 0x60320e1c0738f21e 0xfb019070e039c790

def z361 : W := mkw 0x000000a2000004d0 0x0800000510000026 0x600113e300071ffc 0xf300089f180038ff

def z362 : W := mkw 0x07ba1f50b501d802 0x203dd0fa85a80ec0 0xfffe1ffcff01fc17 0xfffff0ffe7f80fe0

def z363 : W := mkw 0x00000000b4018802 0x0000000005a00c40 0x18000000f8010c01 0x00c0000007c00860

def z364 : W := mkw 0x27badf5d60a9a30d 0x113dd6faeb054d18 0x1732ec1ce038e002 0x08b99760e701c700

def z365 : W := mkw 0x224fc0ff40a8231d 0x11127e07fa054118 0x200fe07f00f80388 0x21007f03f807c01c

def z366 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xfff11f83ff07fe7f 0xffff88fc1ff83ff3

def z367 : W := mkw 0x2a4fe0fb4af6001d 0xc1527f07da57b000 0x200fe07f00fe0008 0x21007f03f807f000

def z368 : W := mkw 0x07aa1854f4a9a303 0x103d50c2a7a54d18 0xfffe1c7cfff9e39f 0xfffff0e3e7ffcf1c

def z369 : W := mkw 0x0000000400082200 0x1000000020004110 0x60020c1c0038e21a 0xeb001060e001c710

def z370 : W := mkw 0x0eaaa000def60003 0xc075550006f7b000 0x1f32e000fffe000f 0x88f9970007fff000

def z371 : W := mkw 0x07ef985460a9a301 0x103f7cc2a3054d18 0xf7fffc7ce0f9e39b 0xffbfffe3e707cf1c

def z372 : W := mkw 0x8eefa004dffe7223 0xf4777d0026fff391 0xdfffe000fffef27f 0xbeffff0007fff793

def z373 : W := mkw 0x8010660903125028 0x2400833048189281 0x0030e00007000000 0x0001870000380000

def z374 : W := mkw 0x8010660d031a7228 0x340083306818d391 0xe8f3ff9f1f3ffe7f 0xff479ffcf8f9fff3

def z375 : W := mkw 0x0000000000000000 0x0000000000000000 0xd7000000e0000003 0x8eb8000007000000

def z376 : W := mkw 0x0effa700dff65803 0xe077fd3806ffb2c0 0xdfffe380fffe1c0f 0xbeffff1c07fff0e0

def z377 : W := mkw 0x27ff9ff200000014 0x013ffcff90000000 0xc7fc1fe000000000 0x5e3fe0ff00000000

def z378 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x6032ec1c0738e21a 0xeb019760e039c710

def z379 : W := mkw 0x21105ffb2101d81c 0x210882ffd9080ec0 0x20001fff0001fc10 0x410000fff8000fe0

def z380 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xb70c1c7ce0c1e391 0x45b860e3e7060f1c

def z381 : W := mkw 0x81105e5d2109f328 0x340882f2e9084f99 0x20001e7f0001f3f0 0x410000f3f8000f9f

def z382 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xffffe203fffe127f 0xffffff101ffff093

def z383 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0x87fefdfc00000000 0x0c3ff7efe0000000

def z384 : W := mkw 0x2ffffffbfff7d81f 0xe17fffffdfffbec0 0xfffffffffffffc1f 0xffffffffffffffe0

def z385 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000106000010390 0x410000830000081c

def z386 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0x17020c1ce0f9e39b 0x88b81060e707cf1c

def z387 : W := mkw 0x06ef80a2084404d0 0x88377c0510422026 0xeffff3e318c71ffd 0xff7fff9f18c638ff

def z388 : W := mkw 0x8010460d01087228 0x3400823068084391 0x60300e1f0700f276 0xdb018070f8380793

def z389 : W := mkw 0x04b0070095005802 0x2025803804a802c0 0xdff00380ff001c07 0x9eff801c07f800e0

def z390 : W := mkw 0x0000000400082200 0x1000000020004110 0x00020c1c0038e002 0x08001060e001c700

def z391 : W := mkw 0x0eef8000dce40003 0xc0777c0006e72000 0xdfcd0000f8c6000d 0xb6fe680007c63000

def z392 : W := mkw 0x000000a2000004d0 0x0800000510000026 0xe8c013e318011ff5 0xd746009f18c008ff

def z393 : W := mkw 0x020a000040a00001 0x0010500002050000 0x000e000000f80008 0x200070000007c000

def z394 : W := mkw 0x27ffdfff2009a31c 0x113ffefff9004d18 0xe7ffffff0001e390 0x7f3ffffff8000f1c

def z395 : W := mkw 0x8effe6afdffe76fb 0xfc77ff357efff3b7 0xffffffffffffffff 0xffffffffffffffff

def z396 : W := mkw 0x830a785d62bba329 0x141853c2eb15dd19 0xf70ffc7fe0ffe3fb 0xefb87fe3ff07ff1f

def z397 : W := mkw 0x05a01900b4018802 0x002d00c805a00c40 0x17000000e0000000 0x00b8000007000000

def z398 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xefffffff18c10d81 0x7f7ffffff8c6086c

def z399 : W := mkw 0x27badf59b501d80e 0x213dd6facda80ec0 0xdff2ff9cff01fc17 0xdeff97fce7f80fe0

def z400 : W := mkw 0x27ffdfff60a9a31d 0x113ffefffb054d18 0xf7ffffffe038e002 0x7fbfffffff01c700

def z401 : W := mkw 0x04a0000094000002 0x0025000004a00000 0x17300000e7000002 0x08b9800007380000

def z402 : W := mkw 0x85b07f09b713d82a 0x242d83f84db89ec1 0xdff1ff83ff07fc77 0xdeff8ffc1ff83fe3

def z403 : W := mkw 0x27ffdffb2101d81c 0x213ffeffd9080ec0 0xe7ffffff0001fc10 0x7f3ffffff8000fe0

def z404 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x20000e1f073ef27e 0xc1000070f839f793

def z405 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xdffff1e0ffff0d8f 0xbeffff8f07fff86c

def z406 : W := mkw 0x0010060000000000 0x0000803000000000 0x40300e0000000000 0x5a01807000000000

def z407 : W := mkw 0x030a18542009a300 0x101850c2a1004d18 0xe70e1c7c0001e390 0x6f3870e3e0000f1c

def z408 : W := mkw 0x805566ab0b5654f8 0xac02ab35585ab2a7 0xe8fdf3e31fc71ffd 0xf747ef9f18fe38ff

def z409 : W := mkw 0x0eaa8000d4a00003 0x4075540006a50000 0x17000000e0000000 0x00b8000007000000

def z410 : W := mkw 0x27ef99f200000014 0x013f7ccf90000000 0xc7fff1e000000000 0x3e3fff8f00000000

def z411 : W := mkw 0x0000000000000000 0x0000000000000000 0x88c0118018010c01 0x0446008c00c00860

def z412 : W := mkw 0x04b0070095005802 0x2025803804a802c0 0x48f00f801f00fc16 0xda47807c00f807e0

def z413 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0x57300e00e700f016 0xdab9807007380780

def z414 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x2032ee1f0738f272 0x49019770f839c793

def z415 : W := mkw 0x27ffdffb9400001e 0x013ffeffdca00000 0xffffffffff000007 0xfffffffffff80000

def z416 : W := mkw 0x27ffdffb0100501c 0x213ffeffd8080280 0xe7ffffff0700f016 0xff3ffffff8380780

def z417 : W := mkw 0x020a005440a82301 0x10105002a2054118 0x600e0c7c00f8e39a 0xeb007063e007c71c

def z418 : W := mkw 0x0000000468eda7c1 0x9800000023476d3e 0x18000000f8ffffff 0x80c0000007c7ffff

def z419 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xdff00c00ff00e007 0x9eff806007f80700

def z420 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0x1f300c00ff01fc17 0x88f9806007f80fe0

def z421 : W := mkw 0x07ff9f00b501d802 0x203ffcf805a80ec0 0xdfffff80ff01fc17 0xfefffffc07f80fe0

def z422 : W := mkw 0x07ba1f00f5a1d803 0x203dd0f807ad0ec0 0xdffe1f80fff9fc1f 0xfefff0fc07ffcfe0

def z423 : W := mkw 0x04a0000094000002 0x0025000004a00000 0x9fc00000f8000001 0x04fe000007c00000

def z424 : W := mkw 0x84b067099712582a 0x242583384cb892c1 0x08f1e3831f061c64 0x10478f1c18f830e3

def z425 : W := mkw 0x07ff9f0000000000 0x003ffcf800000000 0xc7ffff8000000000 0x7e3ffffc00000000

def z426 : W := mkw 0x0000000000000000 0x0000000000000000 0xe00d126300c713fd 0xf70068931806389f

def z427 : W := mkw 0x0fff9f00fde5d803 0xe07ffcf807ef2ec0 0xdffc1f80ffc1fc17 0xdeffe0fc07fe0fe0

def z428 : W := mkw 0x0ce5a0a29e5604d2 0xc8672d0514f2b026 0x08f1e3831f061c64 0x10478f1c18f830e3

def z429 : W := mkw 0x25f5dfabb501d81e 0x212faefd5da80ec0 0xdff1ff83ff01fc17 0xdeff8ffc1ff80fe0

def z430 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0x370e0c7ce0f8e38a 0x29b87063e707c71c

def z431 : W := mkw 0x0000000000000000 0x0000000000000000 0x60020c1c00000000 0x6b001060e0000000

def z432 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xd7021c1ce039e013 0xceb810e0e701cf00

def z433 : W := mkw 0x25f5dfab0000001c 0x012faefd58000000 0xc7f1ff8300000000 0x5e3f8ffc18000000

def z434 : W := mkw 0x031a1f5461a9fb01 0x3018d0faa30d4fd8 0xf70e1ffce0f9ff9b 0xefb870ffe707cffc

def z435 : W := mkw 0x030a185060a18101 0x001850c283050c08 0x17000000e0000000 0x00b8000007000000

def z436 : W := mkw 0x04b0060095005002 0x2025803004a80280 0xdff00e00ff00f017 0xdeff807007f80780

def z437 : W := mkw 0x804560af0a5e26f8 0x9c022b057852f137 0x200fe07f00fe03e8 0x21007f03f807f01f

def z438 : W := mkw 0x01101f0000000000 0x000880f800000000 0x00001f8000000000 0x400000fc00000000

def z439 : W := mkw 0x07ba1f5000000000 0x003dd0fa80000000 0xe7fe1ffc00000000 0x7f3ff0ffe0000000

def z440 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xc8c1138318071c75 0xd646089c18c038e3

def z441 : W := mkw 0x805566af031a7238 0x3402ab357818d391 0xe0ffffff073ef27e 0xff07fffff839f793

def z442 : W := mkw 0x27badf5d60a9a30d 0x113dd6faeb054d18 0xf73efc7ce0f9e39b 0xefb9f7e3e707cf1c

def z443 : W := mkw 0x0000000000000000 0x0000000000000000 0x6001020300000000 0x7300081018000000

def z444 : W := mkw 0x0000000040a00001 0x0000000002050000 0x10000000e0f8000b 0x808000000707c000

def z445 : W := mkw 0x014518f6284da7d0 0x980a28c7b1426d3e 0xe8cd1fff18c7fffd 0xf74668fff8c63fff

def z446 : W := mkw 0x030a185020018000 0x001850c281000c00 0xf70e1c7ce001e013 0xefb870e3e7000f00

def z447 : W := mkw 0x8010660d031a7228 0x340083306818d391 0xe03ffe7f07fff3ff 0xff01fff3f83fff9f

def z448 : W := mkw 0x27ef99f2b4018816 0x013f7ccf95a00c40 0x9fcc11e0f8010c01 0x04fe608f07c00860

def z449 : W := mkw 0x0000000000000000 0x0000000000000000 0x08c0038018001c04 0x1046001c00c000e0

def z450 : W := mkw 0x8000600d021a2228 0x140003006810d111 0x6003e21f003e127c 0xf3001f10f801f093

def z451 : W := mkw 0x8000400d00082228 0x1400020068004111 0x2000001f00000260 0x01000000f8000013

def z452 : W := mkw 0x014518a2284584d0 0x880a28c511422c26 0xffcd1fe3f8c7ffff 0xfffe68ff1fc63fff

def z453 : W := mkw 0x0000005400082300 0x10000002a0004118 0x2000007c00000380 0x01000003e000001c

def z454 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xdfffe383fffe1c6f 0xbeffff1c1ffff0e3

def z455 : W := mkw 0x224fc0fb0000001c 0x01127e07d8000000 0xe0cff3ff00000000 0x77067f9ff8000000

def z456 : W := mkw 0x831a7e5d63bbf329 0x3418d3f2eb1ddf99 0xf73efc7ce7f9e39b 0xefb9f7e3e73fcf1c

def z457 : W := mkw 0x0fefb850fef78103 0xc07f7dc287f7bc08 0xdffff060ffff018f 0xbeffff8307fff80c

def z458 : W := mkw 0x05a0190000000000 0x002d00c800000000 0x87c0118000000000 0x043e008c00000000

def z459 : W := mkw 0x24f5c7ab9500581e 0x2127ae3d5ca802c0 0x08f1e3831f001c04 0x10478f1c18f800e0

def z460 : W := mkw 0x25b05ffbb501d81e 0x212d82ffdda80ec0 0xfff01fffff01fc17 0xdfff80fffff80fe0

def z461 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xc8cc13e018c11d95 0xd646609f00c608ec

def z462 : W := mkw 0x034f18f200000010 0x001a78c790000000 0xe7cf1fff00000000 0x7f3e78fff8000000

def z463 : W := mkw 0x0eef8000dce40003 0xc0777c0006e72000 0xdfce0000f8f8000b 0xaefe700007c7c000

def z464 : W := mkw 0x004500a2bd45dcd2 0xa802280515ea2ee6 0xf8cd13e3ffc7ffff 0xf7c6689f1ffe3fff

def z465 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000000000000218 0xe300000000000010

def z466 : W := mkw 0x07ba1f54f5a9fb03 0x303dd0faa7ad4fd8 0xf73e1c7ce7f9e39b 0xefb9f0e3e73fcf1c

def z467 : W := mkw 0x27badf59b501d80e 0x213dd6facda80ec0 0x1732ec1ce700e002 0x08b99760e7380700

def z468 : W := mkw 0x004500a2084404d0 0x8802280510422026 0x28cd03e318c61fec 0x3146681f18c630ff

def z469 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x6033ee1f0738e002 0x7b019f70f839c700

def z470 : W := mkw 0x27ffdffbb401881e 0x013ffeffdda00c40 0xfffffffff8010c01 0x7fffffffffc00860

def z471 : W := mkw 0x05b03f00b713d802 0x202d81f805b89ec0 0xdff3ff80ff3ffc1f 0xfeff9ffc07f9ffe0

def z472 : W := mkw 0x00000000084404c0 0x8800000000422026 0x6801020318c71ffd 0xf340081018c638ff

def z473 : W := mkw 0x0faab854f6bba303 0x507d55c2a7b5dd18 0x1732ec1ce738e002 0x08b99760e739c700

def z474 : W := mkw 0x0faab854f6bba303 0x507d55c2a7b5dd18 0xf73efc7ce7f9e39b 0xefb9f7e3e73fcf1c

def z475 : W := mkw 0x0000000000000000 0x0000000000000000 0x400200000038000a 0xaa0010000001c000

def z476 : W := mkw 0x8effe609dff6502b 0xe477ff304effb281 0xdfffe203fffe106f 0xbeffff101ffff083

def z477 : W := mkw 0x2fefb9f2def60017 0xc17f7dcf96f7b000 0xdffff1e0fffe000f 0xbeffff8f07fff000

def z478 : W := mkw 0x8010660903125028 0x2400833048189281 0x4033e203073e106e 0xba019f101839f083

def z479 : W := mkw 0x0a0a2000def60003 0xc050510006f7b000 0xdf0e0000fffe000f 0xaef8700007fff000

def z480 : W := mkw 0x0ce5a0009e560002 0xc0672d0004f2b000 0xdff1e000ff060007 0x9eff8f0007f83000

def z481 : W := mkw 0x0a4fa0004af60001 0xc0527d000257b000 0xd70fe000e0fe000b 0xaeb87f000707f000

def z482 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0xe73efc7c00000000 0x6f39f7e3e0000000

def z483 : W := mkw 0x8055660d0b5e7228 0xb402ab30685af391 0xe8ffee1f1ffef27f 0xff47ff70f8fff793

def z484 : W := mkw 0x06aa800000000000 0x0035540000000000 0x0732e00000000000 0x0839970000000000

def z485 : W := mkw 0x27efd9fb0000001c 0x013f7ecfd8000000 0xa7cff1ff00000000 0x253e7f8ff8000000

def z486 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x08ffe0001ffe000c 0x3047ff0000fff000

def z487 : W := mkw 0x0a4fa0a24af604d1 0xc8527d051257b026 0xe8cff3e318ff1ffd 0xf7467f9f18c7f8ff

def z488 : W := mkw 0x05b01f0020018000 0x002d80f801000c00 0xd7f01f80e001e013 0xdebf80fc07000f00

def z489 : W := mkw 0x8000200463bbf321 0x34000100231ddf99 0x10000000e7fff3ff 0x80800000073fff9f

def z490 : W := mkw 0x0100180460a9a301 0x100800c023054d18 0xd7001c00e0f9e39b 0xceb800e00707cf1c

def z491 : W := mkw 0x85b07f0db71bfa2a 0x342d83f86db8dfd1 0x1732ec1ce738e002 0x08b99760e739c700

def z492 : W := mkw 0x004500a200000010 0x0002280510000000 0xe0cd13e300c10399 0xf706689f1806081c

def z493 : W := mkw 0x010018542009a300 0x100800c2a1004d18 0xe00c1c7c00c1e399 0xe70060e3e0060f1c

def z494 : W := mkw 0x820a605d42ba2329 0x14105302ea15d119 0x200fe07f00fe03e8 0x21007f03f807f01f

def z495 : W := mkw 0x05e519a2bc458cd2 0x882f28cd15e22c66 0xffcd13e3f8c71ffd 0xf7fe689f1fc638ff

def z496 : W := mkw 0x020a005440a82301 0x10105002a2054118 0x0002001c00380000 0x00001000e001c000

def z497 : W := mkw 0x0100180020018000 0x000800c001000c00 0xf70c1c60e0c1e39b 0xefb860e307060f1c

def z498 : W := mkw 0x0010060001005000 0x2000803000080280 0x00000e000000f010 0x4000007000000780

def z499 : W := mkw 0xa4f5e7ab0312503c 0x2527af3d58189281 0x00f1e38307061064 0x10078f1c18383083

def z500 : W := mkw 0x034f18f660a9a311 0x101a78c7b3054d18 0xf7cf1fffe0f9e39b 0xffbe78ffff07cf1c

def z501 : W := mkw 0x020a000040a00001 0x0010500002050000 0x17020000e0380002 0x08b810000701c000

def z502 : W := mkw 0x0fef9900fce58803 0xc07f7cc807e72c40 0x9fcc1180f8c10c01 0x04fe608c07c60860

def z503 : W := mkw 0x0eef8000dce40003 0xc0777c0006e72000 0xdffc0000ffc00007 0x9effe00007fe0000

def z504 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x2033e21f073e126c 0x31019f10f839f093

def z505 : W := mkw 0x04b0070095005802 0x2025803804a802c0 0xc8f013801f011c15 0xd647809c00f808e0

def z506 : W := mkw 0x020a005000000000 0x0010500280000000 0x200e007c00000000 0x21007003e0000000

def z507 : W := mkw 0x004500a2084404d0 0x8802280510422026 0x28c113e318071ff4 0x5146089f18c038ff

def z508 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xa8cd11e318c70fe9 0x2546688f18c6387f

def z509 : W := mkw 0x0010070001005800 0x20008038000802c0 0x0000038000001c00 0x0000001c000000e0

def z510 : W := mkw 0x004500a2000004d0 0x0802280510000026 0xe0cd13e300011ff0 0x7706689f180008ff

def z511 : W := mkw 0x004500a6084c26d0 0x9802280530426136 0xe8cf1fff18ffffff 0xff4678fff8c7ffff

def z512 : W := mkw 0x25f5dffb0000001c 0x012faeffd8000000 0x20f1ffff00000000 0x51078ffff8000000

def z513 : W := mkw 0x0000200002120000 0x0000010000109000 0x0003e000003e0008 0x20001f000001f000

def z514 : W := mkw 0x0010460900000008 0x0000823048000000 0x0031e20300000000 0x10018f1018000000

def z515 : W := mkw 0x835f7eff6bfff7f9 0xbc1afbf7fb5fffbf 0xffffffffffffffff 0xffffffffffffffff

def z516 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000020300001270 0x4100001018000093

def z517 : W := mkw 0x8010660d63bbf329 0x340083306b1ddf99 0x7033ee1fe7fff3ff 0xfb819f70ff3fff9f

def z518 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000c10399 0x800000000006081c

def z519 : W := mkw 0x05f51fa2bd45dcd2 0xa82fa8fd15ea2ee6 0xdffc1fe0ffc1fd97 0xdeffe0ff07fe0fec

def z520 : W := mkw 0x00000000084404c0 0x8800000000422026 0xc8c0138018c71ffd 0xd646009c00c638ff

def z521 : W := mkw 0x06ef80a200000010 0x00377c0510000000 0xe7fff3e300000000 0x7f3fff9f18000000

def z522 : W := mkw 0x0045000008440000 0x8002280000422000 0xe8cd106018c7039d 0xf746688300c6381c

def z523 : W := mkw 0x0a4f800048e40001 0xc0527c0002472000 0x000c000000c00000 0x0000600000060000

def z524 : W := mkw 0x05b01f002101d800 0x202d80f801080ec0 0xc7f01f800001fc10 0x5e3f80fc00000fe0

def z525 : W := mkw 0x27badffb0000001c 0x013dd6ffd8000000 0x2732ffff00000000 0x493997fff8000000

def z526 : W := mkw 0x04b0070000000000 0x0025803800000000 0x00f0038000000000 0x1007801c00000000

def z527 : W := mkw 0x80002004031a7220 0x340001002018d391 0x60020c1c073ef27e 0xeb001060e039f793

def z528 : W := mkw 0xa1107fff031a723c 0x350883fff818d391 0x6033ffff073ef27e 0xfb019ffff839f793

def z529 : W := mkw 0x86ffe60d031a7228 0x3437ff306818d391 0xe7ffee1f073ef27e 0xff3fff70f839f793

def z530 : W := mkw 0x27ef99f200000014 0x013f7ccf90000000 0xe7cd13e300000000 0x773e689f18000000

def z531 : W := mkw 0x821a660d43ba7229 0x3410d3306a1dd391 0xf73fee1fe7fef27f 0xffb9ff70ff3ff793

def z532 : W := mkw 0x805566af0b5e76f8 0xbc02ab35785af3b7 0x68f3ef9f1f3efe7e 0xfb479f7cf8f9f7f3

def z533 : W := mkw 0x21555ffb0000001c 0x010aaaffd8000000 0xe0cd1fff00000000 0x770668fff8000000

def z534 : W := mkw 0x0000200002120000 0x0000010000109000 0x0032e00007380002 0x080197000039c000

def z535 : W := mkw 0x0a4fa0544afe2301 0xd0527d02a257f118 0x200fe07c00fe0388 0x21007f03e007f01c

def z536 : W := mkw 0x004500a2084404d0 0x8802280510422026 0x0001000300060060 0x0000080018003003

def z537 : W := mkw 0x27ffdfff0008221c 0x113ffefff8004110 0xe7ffffff0038e21a 0xff3ffffff801c710

def z538 : W := mkw 0x25b05ffb0000001c 0x012d82ffd8000000 0xe7f01fff00000000 0x5f3f80fff8000000

def z539 : W := mkw 0x0000400900000008 0x0000020048000000 0x2003e01f00000000 0x21001f00f8000000

def z540 : W := mkw 0x000000042009a300 0x1000000021004d18 0x000000000001e390 0x0000000000000f1c

def z541 : W := mkw 0x8ffffe5dfffff32b 0xf47ffff2efffff99 0xfffffe7ffffff3ff 0xfffffff3ffffff9f

def z542 : W := mkw 0x05b01f0001005000 0x202d80f800080280 0xc7f01f800700f016 0xde3f80fc00380780

def z543 : W := mkw 0x00000000000004c0 0x0800000000000026 0x0000000000011ff0 0x00000000000008ff

def z544 : W := mkw 0x231a5ffb0000001c 0x0118d2ffd8000000 0xe70e1fff00000000 0x6f3870fff8000000

def z545 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0x1ff00f80ff00fc06 0x18ff807c07f807e0

def z546 : W := mkw 0x05e519a2bc458cd2 0x882f28cd15e22c66 0x9fcc11e0f8c10d81 0x04fe608f07c6086c

def z547 : W := mkw 0x05b01f54b509fb02 0x302d80faa5a84fd8 0xfff01ffcff01ff97 0xdfff80ffe7f80ffc

def z548 : W := mkw 0x0000000060a18101 0x0000000003050c08 0x10000000e0c10181 0x008000000706080c

def z549 : W := mkw 0x034f18f2084404d0 0x881a78c790422026 0xefcf1fff18c71ffd 0xff7e78fff8c638ff

def z550 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000006127c 0x8000000000003093

def z551 : W := mkw 0x0010060001005000 0x2000803000080280 0x60310e030706f27e 0xfb01887018383793

def z552 : W := mkw 0x04f507a29d445cd2 0xa827a83d14ea22e6 0xe8fd13e31fc71ffd 0xf747e89f18fe38ff

def z553 : W := mkw 0x81107f0d231bfa28 0x340883f86918dfd1 0x6033ff9f073ffe7e 0xfb019ffcf839fff3

def z554 : W := mkw 0x08002000def60003 0xc040010006f7b000 0x5833e000fffe000f 0xbac19f0007fff000

def z555 : W := mkw 0x01101f002101d800 0x200880f801080ec0 0x00000c000000e000 0x0000006000000700

def z556 : W := mkw 0x0ca02000def60003 0xc065010006f7b000 0xdff00000fffe000f 0x9eff800007fff000

def z557 : W := mkw 0x0000000460a9a301 0x1000000023054d18 0x70020c1ce0f9e39b 0xeb801060e707cf1c

def z558 : W := mkw 0x8cf5e60d9f5e722a 0xf467af306cfaf391 0x68f3ee1f1f3ef27e 0xfb479f70f8f9f793

def z559 : W := mkw 0x0eefa004feffa303 0xd0777d0027f7fd18 0xdfffe000ffffe39f 0xbeffff0007ffff1c

def z560 : W := mkw 0x000000a2084404d0 0x8800000510422026 0x280013e318c71ffd 0xc140009f18c638ff

def z561 : W := mkw 0x004500a2084404d0 0x8802280510422026 0x000c006000c00180 0x000060030006000c

def z562 : W := mkw 0x000000a2000004d0 0x0800000510000026 0xe00c13e300c11ff9 0xe700609f180608ff

def z563 : W := mkw 0x8810660ddffe722b 0xf44083306efff391 0x7833ee1ffffef27f 0xfbc19f70fffff793

def z564 : W := mkw 0x8a4fe00d4afe2229 0xd4527f006a57f111 0x200fe01f00fe0268 0x21007f00f807f013

def z565 : W := mkw 0x0ce580009c440002 0xc0672c0004e22000 0x08c0000018000000 0x0046000000c00000

def z566 : W := mkw 0x831a7e5d63bbf329 0x3418d3f2eb1ddf99 0x7733ee1fe73ef27e 0xfbb99f70ff39f793

def z567 : W := mkw 0x04e500009c440002 0x8027280004e22000 0xdffd0000ffc6000f 0xbeffe80007fe3000

def z568 : W := mkw 0x01101fa22101dcd0 0x280880fd11080ee6 0x20001fe30001fff0 0x410000ff18000fff

def z569 : W := mkw 0x000000a2000004d0 0x0800000510000026 0x20000063000003e0 0x010000031800001f

def z570 : W := mkw 0x07ff1ff6fdedffd3 0xb83ff8ffb7ef6ffe 0xffff1fffffffffff 0xfffff8ffffffffff

def z571 : W := mkw 0x080020009e560002 0xc040010004f2b000 0x080000001f060004 0x0040000000f83000

def z572 : W := mkw 0x030a18f660a9a7d1 0x181850c7b3054d3e 0xf70e1fffe0f9fffb 0xefb870ffff07cfff

def z573 : W := mkw 0x2fffff59def6000f 0xc17ffffacef7b000 0xdfffec1cfffe000f 0xbeffff60e7fff000

def z574 : W := mkw 0x08002000fff7d803 0xe040010007ffbec0 0x18000000fffffc1f 0x80c0000007ffffe0

def z575 : W := mkw 0x0a4fa0004af60001 0xc0527d000257b000 0xc8cfe00018fe000d 0xb6467f0000c7f000

def z576 : W := mkw 0x0845a0000a560000 0xc0422d000052b000 0x0001e00000060000 0x00000f0000003000

def z577 : W := mkw 0x07ba1f54f5a9fb03 0x303dd0faa7ad4fd8 0xdff21f9cff39fc17 0xdeff90fce7f9cfe0

def z578 : W := mkw 0x080020004af60001 0xc04001000257b000 0x0000000000fe0008 0x000000000007f000

def z579 : W := mkw 0x0100180020018000 0x000800c001000c00 0x97001000e0010001 0x04b8008007000800

def z580 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000138000011c10 0x4000009c000008e0

def z581 : W := mkw 0x0b0a3854feffa303 0xd05851c2a7f7fd18 0xff0e1c7cffffe39f 0xeff870e3e7ffff1c

def z582 : W := mkw 0x0000000001005000 0x2000000000080280 0x000000000700f016 0x8000000000380780

def z583 : W := mkw 0x0b4fb8546affa301 0xd05a7dc2a357fd18 0xf70ffc7ce0ffe39b 0xefb87fe3e707ff1c

def z584 : W := mkw 0x020a005460a9a301 0x10105002a3054d18 0x300e007ce0f9e39b 0xa1807003e707cf1c

def z585 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0x77020c1ce038e21a 0xebb81060e701c710

def z586 : W := mkw 0x804560af0a5e26f8 0x9c022b057852f137 0xe8cff3ff18ff1ffd 0xf7467f9ff8c7f8ff

def z587 : W := mkw 0x0010660902120008 0x0000833048109000 0x6033ee1f073e000e 0xfb019f70f839f000

def z588 : W := mkw 0x0cf5a7009f565802 0xe067ad3804fab2c0 0x08f1e3801f061c04 0x10478f1c00f830e0

def z589 : W := mkw 0x0000000000000000 0x0000000000000000 0x4030000007000006 0x9a01800000380000

def z590 : W := mkw 0x00000000084404c0 0x8800000000422026 0xe80c106018c71ffd 0xe740608300c638ff

def z591 : W := mkw 0x8010660d021a2228 0x140083306810d111 0x6033ee1f003e0268 0x7b019f70f801f013

def z592 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x9fcfe000f8fe0009 0x24fe7f0007c7f000

def z593 : W := mkw 0x00100600b501d802 0x2000803005a80ec0 0x58300e00ff01fc17 0xdac1807007f80fe0

def z594 : W := mkw 0x0010460d00082208 0x1000823068004110 0x6033ee1f0038e21a 0xfb019f70f801c710

def z595 : W := mkw 0x8000200003125020 0x2400010000189281 0x0000000007061064 0x0000000000383083

def z596 : W := mkw 0x24e581a200000014 0x01272c0d10000000 0x00c0018000000000 0x0006000c00000000

def z597 : W := mkw 0x8010460d01087228 0x3400823068084391 0x60010e1f0006f27c 0xf3000870f8003793

def z598 : W := mkw 0x000000a200000010 0x0000000510000000 0x200013e300000000 0x4100009f18000000

def z599 : W := mkw 0x81107e0d231bf228 0x340883f06918df91 0xf733fe1fe73ff27f 0xffb99ff0ff39ff93

def z600 : W := mkw 0x010018542009a300 0x100800c2a1004d18 0xf7001c7ce001e393 0xcfb800e3e7000f1c

def z601 : W := mkw 0xa24fe0ff021a223c 0x15127f07f810d111 0x200fe07f003e0268 0x21007f03f801f013

def z602 : W := mkw 0x2ffffffb9e56001e 0xc17fffffdcf2b000 0xefffffff1f060004 0x7f7ffffff8f83000

def z603 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xe8cd13e318c10d81 0x7746689f18c6086c

def z604 : W := mkw 0xa7ffffff031a723c 0x353ffffff818d391 0xe7ffffff0738e002 0x7f3ffffff839c700

def z605 : W := mkw 0x0effe609def6000b 0xc077ff304ef7b000 0xffffee1ffffe000f 0xffffff70fffff000

def z606 : W := mkw 0x0fef9854fceda303 0xd07f7cc2a7e76d18 0xffce1c7cf8f9e39b 0xeffe70e3e7c7cf1c

def z607 : W := mkw 0x21105fff2009a31c 0x110882fff9004d18 0x20001fff0001e390 0x410000fff8000f1c

def z608 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0c0138000000000 0x5606009c00000000

def z609 : W := mkw 0x8eefe00ddefe222b 0xd4777f006ef7f111 0xffffe01ffffe026f 0xbfffff00fffff013

def z610 : W := mkw 0x8010460d01087228 0x3400823068084391 0x6033ee1f0000f270 0x7b019f70f8000793

def z611 : W := mkw 0x8010660903125028 0x2400833048189281 0x6031e2030706127c 0xf3018f1018383093

def z612 : W := mkw 0x034f185468eda301 0x901a78c2a3476d18 0xffcf1c7cf8ffe39f 0xfffe78e3e7c7ff1c

def z613 : W := mkw 0x05f51fa2bd45dcd2 0xa82fa8fd15ea2ee6 0xdff11f83ff07fc77 0xdeff88fc1ff83fe3

def z614 : W := mkw 0x8ebae60dd7ba722b 0x7475d7306ebdd391 0x7733ee1fe73ef27e 0xfbb99f70ff39f793

def z615 : W := mkw 0x805566af0b5e76f8 0xbc02ab35785af3b7 0x603fee7f07fef3fe 0xfb01ff73f83ff79f

def z616 : W := mkw 0x05b01f04f5a9fb03 0x302d80f827ad4fd8 0xdff01f80fff9ff9f 0xdeff80fc07ffcffc

def z617 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xa7cc1fff00000000 0x453e60fff8000000

def z618 : W := mkw 0x0eefa054defe2303 0xd0777d02a6f7f118 0xffffe07cfffe038f 0xbfffff03e7fff01c

def z619 : W := mkw 0x034f18f268e585d1 0x881a78c793472c2e 0xffcd13e3f8c71ffd 0xf7fe689f1fc638ff

def z620 : W := mkw 0x01101f542109fb00 0x300880faa1084fd8 0x20001ffc0001ff90 0x410000ffe0000ffc

def z621 : W := mkw 0x04f507a29d445cd2 0xa827a83d14ea22e6 0x08f103831f061c64 0x1047881c18f830e3

def z622 : W := mkw 0x04a0000000000000 0x0025000000000000 0xc7f0000000000000 0x1e3f800000000000

def z623 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x2003ee1f003ef278 0x61001f70f801f793

def z624 : W := mkw 0x004500a200000010 0x0002280510000000 0xe0cd13e30006127c 0xf706689f18003093

def z625 : W := mkw 0x000000a2000004d0 0x0800000510000026 0x000011e000010d80 0x0000008f0000086c

def z626 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001020300061064 0x1000081018003083

def z627 : W := mkw 0x8010660db71bfa2a 0x340083306db8dfd1 0x7833ee1fff3ffe7f 0xfbc19f70fff9fff3

def z628 : W := mkw 0x01101f002101d800 0x200880f801080ec0 0x40301f800701fc16 0xda0180fc00380fe0

def z629 : W := mkw 0x06efa00002120000 0x00377d0000109000 0xc7ffe000073e000e 0xbe3fff000039f000

def z630 : W := mkw 0x8effe60ddffe722b 0xf477ff306efff391 0xdfffec1cfffee00f 0xbeffff60e7fff700

def z631 : W := mkw 0x0000000400082200 0x1000000020004110 0x2002001c00380208 0x21001000e001c010

def z632 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x0031e203073ef27e 0x90018f101839f793

def z633 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xe0cd13e300c603e8 0x7706689f1806301f

def z634 : W := mkw 0x030a185000000000 0x001850c280000000 0x870c106000000000 0x0438608300000000

def z635 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x9ffde000ffc60005 0x14ffef0007fe3000

def z636 : W := mkw 0x0000200002120000 0x0000010000109000 0x0031e00007060004 0x10018f0000383000

def z637 : W := mkw 0x005506a2094454d0 0xa802a835104a22a6 0xe8fd1fe31fc7ffff 0xff47e8ff18fe3fff

def z638 : W := mkw 0x0000000000000000 0x0000000000000000 0xe00c106000000000 0x6700608300000000

def z639 : W := mkw 0x85b07f0db71bfa2a 0x342d83f86db8dfd1 0xdff2ff9cff39fc17 0xdeff97fce7f9cfe0

def z640 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xf70e1c7ce038e002 0x6fb870e3e701c700

def z641 : W := mkw 0x07ba1f50f5a1d903 0x203dd0fa87ad0ec8 0xdffc1fe0ffc1fd97 0xdeffe0ff07fe0fec

def z642 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0x200e1c7c00f9e398 0x610070e3e007cf1c

def z643 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0x9ff01380ff011c05 0x14ff809c07f808e0

def z644 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x0032ec1c073ef27e 0x88019760e039f793

def z645 : W := mkw 0x024f00f648ec27d1 0x98127807b247613e 0x200f007f00fe03e8 0x21007803f807f01f

def z646 : W := mkw 0x004500a2084404d0 0x8802280510422026 0x08c1038318c71ffd 0x9046081c18c638ff

def z647 : W := mkw 0x0000000000000000 0x0000000000000000 0x400100000006000c 0xb200080000003000

def z648 : W := mkw 0x224f80f200000014 0x01127c0790000000 0x000c006000000000 0x0000600300000000

def z649 : W := mkw 0x27fffffb0212001c 0x013fffffd8109000 0xe7ffffff073e000e 0xff3ffffff839f000

def z650 : W := mkw 0x01001800b501d802 0x200800c005a80ec0 0xdf001c00ff01fc17 0xcef800e007f80fe0

def z651 : W := mkw 0x2fbaff59d6b2000f 0x417dd7faceb59000 0x1732ec1ce7380002 0x08b99760e739c000

def z652 : W := mkw 0x0000000000000000 0x0000000000000000 0x0800000018011c15 0x8040000000c008e0

def z653 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xe8cc11e018c10f99 0xe746608f00c6087c

def z654 : W := mkw 0x24f5c7ab0000001c 0x0127ae3d58000000 0xe0fdf3e300000000 0x7707ef9f18000000

def z655 : W := mkw 0x0045000008440000 0x8002280000422000 0xe8cd020318c6127d 0xf746681018c63093

def z656 : W := mkw 0x0fffbf00fff7d803 0xe07ffdf807ffbec0 0xdfffec00fffee00f 0xbeffff6007fff700

def z657 : W := mkw 0x00000000084404c0 0x8800000000422026 0x0800000018c10d81 0x0040000000c6086c

def z658 : W := mkw 0x00000000084404c0 0x8800000000422026 0x0000000000c603e8 0x000000000006301f

def z659 : W := mkw 0x0fefb800fef78003 0xc07f7dc007f7bc00 0xdffffc00ffffe01f 0xfeffffe007ffff00

def z660 : W := mkw 0x821a665d43ba7329 0x3410d332ea1dd399 0x603fee7f07fef3fe 0xfb01ff73f83ff79f

def z661 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0x08f01f801f01fc14 0x504780fc00f80fe0

def z662 : W := mkw 0x030a1854f5a9fb03 0x301850c2a7ad4fd8 0xff0e1c7cfff9ff9f 0xeff870e3e7ffcffc

def z663 : W := mkw 0xa7ffdfff0108723c 0x353ffefff8084391 0xe7ffffff0000f270 0x7f3ffffff8000793

def z664 : W := mkw 0xa7ffffff021a223c 0x153ffffff810d111 0xe7ffffff003e0268 0x7f3ffffff801f013

def z665 : W := mkw 0x07aa1950f4a18903 0x003d50ca87a50c48 0x9fcc11e0f8c10d81 0x04fe608f07c6086c

def z666 : W := mkw 0x2cf5e7ab9e56001e 0xc167af3d5cf2b000 0x08f1e3831f060004 0x10478f1c18f83000

def z667 : W := mkw 0x004500a2084404d0 0x8802280510422026 0x68c1038318061e7c 0xf346081c18c030f3

def z668 : W := mkw 0x05a01900b4018802 0x002d00c805a00c40 0xdff01180ff010c07 0x9eff808c07f80860

def z669 : W := mkw 0x084520a2def604d3 0xc842290516f7b026 0xf8cd13e3ffff1fff 0xf7c6689f1ffff8ff

def z670 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0x37021c7ce039e392 0x49b810e3e701cf1c

def z671 : W := mkw 0x004500a2084404d0 0x8802280510422026 0x200d13e300c71ff8 0x6100689f180638ff

def z672 : W := mkw 0x030a185468eda7c1 0x981850c2a3476d3e 0xff0e1c7cf8ffffff 0xeff870e3e7c7ffff

def z673 : W := mkw 0x27ef99f2084404d4 0x893f7ccf90422026 0xefcd13e318c71ffd 0xf77e689f18c638ff

def z674 : W := mkw 0x05b01fa2b501dcd2 0x282d80fd15a80ee6 0xfff01fe3ff01fff7 0xdfff80ff1ff80fff

def z675 : W := mkw 0x21555ffb084404dc 0x890aaaffd8422026 0xe8cd1fff18c71ffd 0xf74668fff8c638ff

def z676 : W := mkw 0x0100185000000000 0x000800c280000000 0x20001c7c00000000 0x410000e3e0000000

def z677 : W := mkw 0x05a01900b4018802 0x002d00c805a00c40 0xdfc01380f8011c15 0xd6fe009c07c008e0

def z678 : W := mkw 0x0000000000000000 0x0000000000000000 0xc8c0000018000005 0x9646000000c00000

def z679 : W := mkw 0x0000000000000000 0x0000000000000000 0x4033e00000000000 0x3a019f0000000000

def z680 : W := mkw 0x00450000084404c0 0x8802280000422026 0xc8cd000018c71ffd 0xb646680000c638ff

def z681 : W := mkw 0x0eefa0009e560002 0xc0777d0004f2b000 0xcfffe0001f060004 0x3e7fff0000f83000

def z682 : W := mkw 0x05f51fa2084404d0 0x882fa8fd10422026 0xeffd1fe318c71ffd 0xff7fe8ff18c638ff

def z683 : W := mkw 0x0000000000000000 0x0000000000000000 0x800c106000c10181 0x040060830006080c

def z684 : W := mkw 0x0eefa0004af60001 0xc0777d000257b000 0xc7ffe00000fe0008 0x3e3fff000007f000

def z685 : W := mkw 0x004500a200000010 0x0002280510000000 0x00c1038300000000 0x1006081c18000000

def z686 : W := mkw 0x0000000400082200 0x1000000020004110 0xe00e1c7c00f9e39b 0xef0070e3e007cf1c

def z687 : W := mkw 0x07aa1954f4a9ab03 0x103d50caa7a54d58 0xffce1dfcf8f9ef9b 0xeffe70efe7c7cf7c

def z688 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x4033ec1c073ee00e 0xba019f60e039f700

def z689 : W := mkw 0x0000000400082200 0x1000000020004110 0x60030e1f003ef27e 0xfb001870f801f793

def z690 : W := mkw 0x024f000048e40001 0x8012780002472000 0xdfcf0000f8fe000f 0xbefe780007c7f000

def z691 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xe8cd006318c603ed 0xb746680318c6301f

def z692 : W := mkw 0x020a000040a00001 0x0010500002050000 0x970c0000e0c00001 0x04b8600007060000

def z693 : W := mkw 0x0fffbf00def60003 0xc07ffdf806f7b000 0xdfffff80fffe000f 0xfefffffc07fff000

def z694 : W := mkw 0x020a005440a82301 0x10105002a2054118 0xf70e007ce0f8038b 0xafb87003e707c01c

def z695 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xa8cc13e318c11ff1 0x4546609f18c608ff

def z696 : W := mkw 0x2fef99f2dce40017 0xc17f7ccf96e72000 0x9fcc11e0f8c00001 0x04fe608f07c60000

def z697 : W := mkw 0x00002004021a2200 0x100001002010d110 0x6033ec1c073ee21e 0xfb019f60e039f710

def z698 : W := mkw 0x8010460901005028 0x2400823048080281 0x0000020300001060 0x0000001018000083

def z699 : W := mkw 0x0df5bf00bf57d802 0xe06fadf805fabec0 0xdff1ff80ff07fc17 0xdeff8ffc07f83fe0

def z700 : W := mkw 0x0db03f00fff7d803 0xe06d81f807ffbec0 0xdff01f80fffffc1f 0xdeff80fc07ffffe0

def z701 : W := mkw 0x034f18f668eda7d1 0x981a78c7b3476d3e 0xf70f1c7fe0ffe3fb 0xefb878e3ff07ff1f

def z702 : W := mkw 0x0100185020018100 0x000800c281000c08 0x0000106000010180 0x000000830000080c

def z703 : W := mkw 0x0ce5a0a29e5604d2 0xc8672d0514f2b026 0xe8fdf3e31fc71ffd 0xf747ef9f18fe38ff

def z704 : W := mkw 0x004500a668eda7d1 0x9802280533476d3e 0xf8cd13e3f8ffffff 0xf7c6689f1fc7ffff

def z705 : W := mkw 0x05a01800b4018002 0x002d00c005a00c00 0xdff01c00ff01e017 0xdeff80e007f80f00

def z706 : W := mkw 0x8010460d01087228 0x3400823068084391 0x60020e1f0038f27a 0xeb001070f801c793

def z707 : W := mkw 0x231adffb0000001c 0x0118d6ffd8000000 0x2002ffff00000000 0x410017fff8000000

def z708 : W := mkw 0x031a5e5900000008 0x0018d2f2c8000000 0x0732ec1c00000000 0x08399760e0000000

def z709 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xe8cd1fe318c7ffff 0xff4668ff18c63fff

def z710 : W := mkw 0x21105fff2109fb1c 0x310882fff9084fd8 0x20001fff0001ff90 0x410000fff8000ffc

def z711 : W := mkw 0xa7efb9f6031a7234 0x353f7dcfb018d391 0x87cc11e0073ef27e 0x843e608f0039f793

def z712 : W := mkw 0x224fc0fb0000001c 0x01127e07d8000000 0x0003e01f00000000 0x00001f00f8000000

def z713 : W := mkw 0x27ffdffb000004dc 0x093ffeffd8000026 0xe7ffffff00001c60 0x7f3ffffff80000e3

def z714 : W := mkw 0x0eaaa0a2d6b204d3 0x4875550516b59026 0x3732f3e3e7391ff2 0x49b9979f1f39c8ff

def z715 : W := mkw 0x27ffdffb284584dc 0x893ffeffd9422c26 0xfffffffff8c7ffff 0xffffffffffc63fff

def z716 : W := mkw 0x07ba5f5df5a9fb0b 0x303dd2faefad4fd8 0xfffffffffff9ff9f 0xffffffffffffcffc

def z717 : W := mkw 0x25b0dffb0000001c 0x012d86ffd8000000 0x2030ffff00000000 0x410187fff8000000

def z718 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x6033ff9f073ffe7e 0xfb019ffcf839fff3

def z719 : W := mkw 0x80102604031a7220 0x340081302018d391 0x00300200073ef27e 0x900180100039f793

def z720 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffffff07000006 0xff3ffffff8380000

def z721 : W := mkw 0x225fc6fb0100501c 0x2112fe37d8080280 0x603fee7f0700f016 0xfb01ff73f8380780

def z722 : W := mkw 0x06efa00096120002 0x00377d0004b09000 0xdfffe000ff3e000f 0xbeffff0007f9f000

def z723 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xefffffff18071e7d 0xff7ffffff8c038f3

def z724 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xf70e1c7ce0f8e38a 0x6fb870e3e707c71c

def z725 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0x673fee7f00000000 0x7b39ff73f8000000

def z726 : W := mkw 0x27ffdffb9c44001e 0x813ffeffdce22000 0xffffffffffc6000f 0xfffffffffffe3000

def z727 : W := mkw 0x27ffdf590000000c 0x013ffefac8000000 0x073fec1c00000000 0x2839ff60e0000000

def z728 : W := mkw 0x24b0c7090000000c 0x0125863848000000 0x6033ee1f00000000 0x7b019f70f8000000

def z729 : W := mkw 0x0eefa000d6b20003 0x40777d0006b59000 0xd7ffe000e73e000e 0xbebfff000739f000

def z730 : W := mkw 0x26ffc7fb0000001c 0x0137fe3fd8000000 0xe7ffe3ff00000000 0x3f3fff1ff8000000

def z731 : W := mkw 0x27ffdf59b501d80e 0x213ffefacda80ec0 0xdfffff9cff01fc17 0xfefffffce7f80fe0

def z732 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xdff01d80ff01ec07 0x9eff80ec07f80f60

def z733 : W := mkw 0x81105f0d2109fa28 0x340882f869084fd1 0xe8c11f9f1807fe7d 0xf74608fcf8c03ff3

def z734 : W := mkw 0x8effc60dddec722b 0xf477fe306eef6391 0xbfcc0e1ff8c0f271 0x45fe6070ffc60793

def z735 : W := mkw 0x27ffdffbb501d81e 0x213ffeffdda80ec0 0xffffffffff01ec03 0x7ffffffffff80f60

def z736 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x6033fe7f073ff3fe 0xfb019ff3f839ff9f

def z737 : W := mkw 0x0010460900000008 0x0000823048000000 0x6033ee1f0006000c 0xfb019f70f8003000

def z738 : W := mkw 0x805566af0b5e76f8 0xbc02ab35785af3b7 0x88fefdfc1ff9ed83 0x0c47f7efe0ffcf6c

def z739 : W := mkw 0x021a465900000008 0x0010d232c8000000 0x603fee7f00000000 0x7b01ff73f8000000

def z740 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0x9ff01d80ff01fc17 0x8cff80ec07f80fe0

def z741 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8c1138318011c15 0xf746089c18c008e0

def z742 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xb70c1c7ce0f9e39b 0xc5b860e3e707cf1c

def z743 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xefffffff18071ff4 0x7f7ffffff8c038ff

def z744 : W := mkw 0x024fc00900000008 0x00127e0048000000 0x200fe01f00000000 0x21007f00f8000000

def z745 : W := mkw 0x80002004031a7220 0x340001002018d391 0x000000000738f016 0x800000000039c780

def z746 : W := mkw 0x2155dffb0000001c 0x010aaeffd8000000 0x2001ffff00000000 0x41000ffff8000000

def z747 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xdfffe383ffff1fff 0xbeffff1c1ffff8ff

def z748 : W := mkw 0x85a0790db61baa2a 0x142d03c86db0dd51 0xbfc3f19ff83f0e69 0x25fe1f8cffc1f873

def z749 : W := mkw 0x24f5c7ab084404dc 0x8927ae3d58422026 0xe8ffffff18c71ffd 0xff47fffff8c638ff

def z750 : W := mkw 0x224fc0fb084404dc 0x89127e07d8422026 0x280fe07f18c71ffd 0xa1407f03f8c638ff

def z751 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xdff3ff80ff01fc17 0xfeff9ffc07f80fe0

def z752 : W := mkw 0x27badffb0000001c 0x013dd6ffd8000000 0x6733ffff00000000 0x7b399ffff8000000

def z753 : W := mkw 0x224fc0fb40a0001d 0x01127e07da050000 0xf70fe07fe0f8000b 0xafb87f03ff07c000

def z754 : W := mkw 0x05a01900b501d802 0x202d00c805a80ec0 0x9fc01180ff01ec03 0x04fe008c07f80f60

def z755 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0x20ffffff00000000 0x7107fffff8000000

def z756 : W := mkw 0x224fc0fbb501d81e 0x21127e07dda80ec0 0x380fe07fff01fc17 0xa1c07f03fff80fe0

def z757 : W := mkw 0x27ffdffb9400001e 0x013ffeffdca00000 0xefffffff1f000004 0x7f7ffffff8f80000

def z758 : W := mkw 0x0eefa000d6b20003 0x40777d0006b59000 0xdfffe000ff380007 0xbeffff0007f9c000

def z759 : W := mkw 0x804520a6031a7230 0x340229053018d391 0xe0cd13e3073ef27e 0xf706689f1839f793

def z760 : W := mkw 0x004500a2084404d0 0x8802280510422026 0x28cd13e318c71ffc 0x7146689f18c638ff

def z761 : W := mkw 0x0eefa000def604c3 0xc8777d0006f7b026 0xffffe203ffff1fff 0xffffff101ffff8ff

def z762 : W := mkw 0x8cf5e6ab9f5654fa 0xec67af355cfab2a7 0x08f1e3831f061c64 0x10478f1c18f830e3

def z763 : W := mkw 0x235fdefb0000001c 0x011afef7d8000000 0xe73ffe7f00000000 0x7f39fff3f8000000

def z764 : W := mkw 0x0010460901005008 0x2000823048080280 0x6033ee1f0706f27e 0xfb019f70f8383793

def z765 : W := mkw 0x0fef98f2fce585d3 0xc87f7cc797e72c2e 0x9fcc11e0f8c10d81 0x04fe608f07c6086c

def z766 : W := mkw 0x0000400900000008 0x0000020048000000 0x6003e21f00000000 0x73001f10f8000000

def z767 : W := mkw 0x001046ab00000018 0x0000823558000000 0x6033ffff00000000 0x7b019ffff8000000

def z768 : W := mkw 0x27ffdffb48e404dd 0x893ffeffda472026 0xfffffffff8ff1fff 0xffffffffffc7f8ff

def z769 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xdffff3e0ffff1d9f 0xfeffff9f07fff8ec

def z770 : W := mkw 0x29107ffbdef6001f 0xc14883ffdef7b000 0x38001ffffffe000f 0xc1c000fffffff000

def z771 : W := mkw 0x27badf5940a0000d 0x013dd6faca050000 0xd73eec1ce0f8000b 0xaeb9f760e707c000

def z772 : W := mkw 0x021a460940a00009 0x0010d2304a050000 0xf73fee1fe0f8000b 0xffb9ff70ff07c000

def z773 : W := mkw 0x005546ab094454d8 0xa802aa35584a22a6 0xe8ffffff1fc7ffff 0xff47fffff8fe3fff

def z774 : W := mkw 0x04b0460900000008 0x0025823048000000 0xe7f3ee1f00000000 0x7f3f9f70f8000000

def z775 : W := mkw 0x21105ffb0000001c 0x010882ffd8000000 0x2003ffff00000000 0x61001ffff8000000

def z776 : W := mkw 0x0de5b854be5fa302 0xd06f2dc2a5f2fd18 0x28f1fc7c1f07e394 0x51478fe3e0f83f1c

def z777 : W := mkw 0x07ef9850b4018002 0x003f7cc285a00c00 0xfffffc7cff01e017 0xffffffe3e7f80f00

def z778 : W := mkw 0x800020040a5e26e0 0x9c0001002052f137 0x0800000018ff1ffd 0x8040000000c7f8ff

def z779 : W := mkw 0x05b05f09b501d80a 0x202d82f84da80ec0 0xdff2ff9cff01fc17 0xdeff97fce7f80fe0

def z780 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xdffc1fe0ffc1fd97 0xdeffe0ff07fe0fec

def z781 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffffff00001014 0xff3ffffff8000080

def z782 : W := mkw 0x25f5dffb0000001c 0x012faeffd8000000 0xe0fdffff00000000 0x7707effff8000000

def z783 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xa8cd13e318c71fed 0x3546689f18c638ff

def z784 : W := mkw 0x05b05f09b501d80a 0x202d82f84da80ec0 0xdff1ff83ff01fc17 0xdeff8ffc1ff80fe0

def z785 : W := mkw 0x26efc0fb0000001c 0x01377e07d8000000 0x273fe07f00000000 0x2939ff03f8000000

def z786 : W := mkw 0x8000200463bbf321 0x34000100231ddf99 0x10000000e738e002 0x008000000739c700

def z787 : W := mkw 0x27badf592001800c 0x013dd6fac9000c00 0xd732fc1ce001e013 0xceb997e0e7000f00

def z788 : W := mkw 0x07ffdf09b501d80a 0x203ffef84da80ec0 0xffffff9fff01fc17 0xfffffffcfff80fe0

def z789 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0x67f3ef9f00000000 0x7b3f9f7cf8000000

def z790 : W := mkw 0x8000200463bbf321 0x34000100231ddf99 0xf00d1263e7fff3ff 0xf78068931f3fff9f

def z791 : W := mkw 0x0eefa050def60003 0xc0777d0286f7b000 0xffffe07cfffe000f 0xbfffff03e7fff000

def z792 : W := mkw 0x80002004031a7220 0x340001002018d391 0x00000000073e126c 0x000000000039f093

def z793 : W := mkw 0x27ffdffbb501d81e 0x213ffeffdda80ec0 0xfffffffff801fc11 0x7fffffffffc00fe0

def z794 : W := mkw 0x235fdffb0000001c 0x011afeffd8000000 0xe0cfffff00000000 0x77067ffff8000000

def z795 : W := mkw 0x00002004021a2200 0x100001002010d110 0x00000000073ee21e 0x800000000039f710

def z796 : W := mkw 0x05a01900b501d802 0x202d00c805a80ec0 0xdff01180ff01fc17 0x9eff808c07f80fe0

def z797 : W := mkw 0x0eaaa000def60003 0xc075550006f7b000 0x1f32e000fff80003 0x08f9970007ffc000

def z798 : W := mkw 0x0010460900000008 0x0000823048000000 0xe0f3ff9f00000000 0x7f079ffcf8000000

def z799 : W := mkw 0x0000200002120000 0x0000010000109000 0xd733e000e73e000f 0xbeb99f000739f000

def z800 : W := mkw 0x27efd9fb084404dc 0x893f7ecfd8422026 0xefcff3ff18c71ffd 0xf77e7f9ff8c638ff

def z801 : W := mkw 0x01105f092101d808 0x200882f849080ec0 0x20001f9f0001fc10 0x410000fcf8000fe0

def z802 : W := mkw 0x00002004021a2200 0x100001002010d110 0x6033ee1f073ef27e 0xfb019f70f839f793

def z803 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0x273fffff00000000 0x6939fffff8000000

def z804 : W := mkw 0x81105f0d2109fa28 0x340882f869084fd1 0x20000e1f0000f270 0x41000070f8000793

def z805 : W := mkw 0x8000200463bbf321 0x34000100231ddf99 0x10000000e7f9e39b 0x80800000073fcf1c

def z806 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0x1ff00d80ff00ec02 0x08ff806c07f80760

def z807 : W := mkw 0x05a01900b501d802 0x202d00c805a80ec0 0xdfc01d80ff01fc17 0xcefe00ec07f80fe0

def z808 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xc7ffef9f00000000 0x3e3fff7cf8000000

def z809 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xffffe203fffe000f 0xffffff101ffff000

def z810 : W := mkw 0x8eefa004dffe7223 0xf4777d0026fff391 0x9fcc0000fffef27f 0x84fe600007fff793

def z811 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xf70e1c7ce0fff3ff 0xefb870e3e707ff9f

def z812 : W := mkw 0x0000400900000008 0x0000020048000000 0x6003ec1f00000000 0x6b001f60f8000000

def z813 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffffff00011c10 0x7f3ffffff80008e0

def z814 : W := mkw 0x2fffdffbd4a0001f 0x417ffeffdea50000 0xf7ffffffe0000000 0x7fbfffffff000000

def z815 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xffffe263fffe13ff 0xffffff131ffff09f

def z816 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xb70e1c7ce0f9e38b 0x2db870e3e707cf1c

def z817 : W := mkw 0x06ffc60900000008 0x0037fe3048000000 0xc7ffec1c00000000 0x3e3fff60e0000000

def z818 : W := mkw 0x0b5fbf006bf7d801 0xe05afdf8035fbec0 0x000fff8000fffc18 0x60007ffc0007ffe0

def z819 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xdff01f80ff07fe7f 0xdeff80fc07f83ff3

def z820 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xdff01f80ff00fc06 0x5eff80fc07f807e0

def z821 : W := mkw 0x05a01900b501d802 0x202d00c805a80ec0 0xdfc01380ff01fc17 0xd6fe009c07f80fe0

def z822 : W := mkw 0x2eefc0fbdce4001f 0xc1777e07dee72000 0xbfcfe07ff8c00001 0x25fe7f03ffc60000

def z823 : W := mkw 0x0010460900000008 0x0000823048000000 0x6033ee1f00000218 0xfb019f70f8000010

def z824 : W := mkw 0x27badffb0000001c 0x013dd6ffd8000000 0xe73effff00000000 0x6f39f7fff8000000

def z825 : W := mkw 0x26ffc7fb0000001c 0x0137fe3fd8000000 0xe0fff3ff00000000 0x7707ff9ff8000000

def z826 : W := mkw 0x07aa985000000000 0x003d54c280000000 0xe73efc7c00000000 0x6f39f7e3e0000000

def z827 : W := mkw 0x884520a6dffe76f3 0xfc42290536fff3b7 0xf8cd13e3ffffffff 0xf7c6689f1fffffff

def z828 : W := mkw 0x27ffdffb60a1811d 0x013ffeffdb050c08 0xf7ffffffe0000000 0x7fbfffffff000000

def z829 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0xdff3e000ff3e000f 0xbeff9f0007f9f000

def z830 : W := mkw 0x0ce5a0009e560002 0xc0672d0004f2b000 0xdff3e000ff3e000f 0xbeff9f0007f9f000

def z831 : W := mkw 0x25b05f59b501d80e 0x212d82facda80ec0 0xdff01f9cff01fc17 0xdeff80fce7f80fe0

def z832 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xfff11f83ff01fc17 0xffff88fc1ff80fe0

def z833 : W := mkw 0x005546ab00000018 0x0002aa3558000000 0x603fee7f00000000 0x7b01ff73f8000000

def z834 : W := mkw 0x80002004b71bfa22 0x3400010025b8dfd1 0x10000000e73ef27e 0x808000000739f793

def z835 : W := mkw 0x0055460900000008 0x0002aa3048000000 0xe0ffee1f00000000 0x7f07ff70f8000000

def z836 : W := mkw 0x84b02704971a7a22 0x3425813824b8d3d1 0x08f003801f3efe7e 0x9047801c00f9f7f3

def z837 : W := mkw 0x27badffb000004dc 0x093dd6ffd8000026 0x2732ffff00011ff0 0x493997fff80008ff

def z838 : W := mkw 0x04b046099400000a 0x002582304ca00000 0xfff3ee1fff000007 0xffff9f70fff80000

def z839 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xefffffff18000005 0xff7ffffff8c00000

def z840 : W := mkw 0x27badf59084404cc 0x893dd6fac8422026 0x0f32ec1c18c71ffd 0x88799760e0c638ff

def z841 : W := mkw 0x26ffc7fb0000001c 0x0137fe3fd8000000 0x60ffefff00000000 0x7b07ff7ff8000000

def z842 : W := mkw 0x27ffdffb9500501e 0x213ffeffdca80280 0xffffffffff00f017 0xfffffffffff80780

def z843 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xd70e1c7ce0f9e193 0xceb870e3e707cf0c

def z844 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xffffe3e3fffe1fef 0xbfffff1f1ffff0ff

def z845 : W := mkw 0x27ffdffb60a1811d 0x013ffeffdb050c08 0xf7ffffffe0c10399 0xffbfffffff06081c

def z846 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0xd732e000e7380003 0x8eb997000739c000

def z847 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xefffffff18071c75 0xff7ffffff8c038e3

def z848 : W := mkw 0x27ffdf590844000c 0x813ffefac8422000 0xcfffec1c18c6000d 0xbe7fff60e0c63000

def z849 : W := mkw 0x221ac6590000000c 0x0110d632c8000000 0x0032ec1c00000000 0x08019760e0000000

def z850 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xdff00f80ff00fc07 0x9eff807c07f807e0

def z851 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe73ffc7f00000000 0x6f39ffe3f8000000

def z852 : W := mkw 0x235fdffb0000001c 0x011afeffd8000000 0xe70fffff00000000 0x6f387ffff8000000

def z853 : W := mkw 0x27ffdffb2101dcdc 0x293ffeffd9080ee6 0xe7ffffff0001fff0 0x7f3ffffff8000fff

def z854 : W := mkw 0x234fd8fb084404dc 0x891a7ec7d8422026 0xefcfffff18c71ffd 0xff7e7ffff8c638ff

def z855 : W := mkw 0x26ffc7fb0000001c 0x0137fe3fd8000000 0x00f3e39f00000000 0x10079f1cf8000000

def z856 : W := mkw 0x25f5dffb0000001c 0x012faeffd8000000 0x00f1ef9f00000000 0x10078f7cf8000000

def z857 : W := mkw 0x06ffc6ab00000018 0x0037fe3558000000 0xe7ffffff00000000 0x7f3ffffff8000000

def z858 : W := mkw 0x27badffb0000001c 0x013dd6ffd8000000 0x0732ef9f00000000 0x0839977cf8000000

def z859 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xdff3e000ff3e0007 0x9eff9f0007f9f000

def z860 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xdfffe000ffff039f 0xbeffff0007fff81c

def z861 : W := mkw 0x27ffdffb9500581e 0x213ffeffdca802c0 0xe7ffffff07000000 0x7f3ffffff8380000

def z862 : W := mkw 0x80102604031a7220 0x340081302018d391 0x00300c00073ef27e 0x880180600039f793

def z863 : W := mkw 0x21105f590000000c 0x010882fac8000000 0x6033ee1f00000000 0x7b019f70f8000000

def z864 : W := mkw 0x08002004defe2303 0xd040010026f7f118 0x18000000fffe038f 0x80c0000007fff01c

def z865 : W := mkw 0x8000200443ba7321 0x34000100221dd399 0x0000000007fef3fe 0x80000000003ff79f

def z866 : W := mkw 0x21555ffb084404dc 0x890aaaffd8422026 0xe8ffffff18c71ffd 0xff47fffff8c638ff

def z867 : W := mkw 0x0eefa000d6b20003 0x40777d0006b59000 0x97fee000e7380002 0x0cbff7000739c000

def z868 : W := mkw 0x024f20004af60001 0x801279000257b000 0xdfffe000fffe000f 0xbeffff0007fff000

def z869 : W := mkw 0x031a5e5900000008 0x0018d2f2c8000000 0x6733ee1f00000000 0x7b399f70f8000000

def z870 : W := mkw 0x8010460901005028 0x2400823048080281 0x6033ee1f00001060 0x7b019f70f8000083

def z871 : W := mkw 0x031a5e5960a18109 0x0018d2f2cb050c08 0xf73ffe7fe0c10181 0x7fb9fff3ff06080c

def z872 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xefffffff18010c01 0x7f7ffffff8c00860

def z873 : W := mkw 0x27ffdffb000004dc 0x093ffeffd8000026 0xe7ffffff00c11ff9 0xff3ffffff80608ff

def z874 : W := mkw 0x06ba0754d5a87b03 0x3035d03aa6ad43d8 0x28fe03fc1ff81f8c 0x3147f01fe0ffc0fc

def z875 : W := mkw 0x05b05f09b501d80a 0x202d82f84da80ec0 0xfff3ff9fff07fe7f 0xffff9ffcfff83ff3

def z876 : W := mkw 0x0eaaa000def60003 0xc075550006f7b000 0x1732e000e7fe000a 0x08b99700073ff000

def z877 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffffff0038000a 0xff3ffffff801c000

def z878 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xe7ffffff00c71ff8 0x7f3ffffff80638ff

def z879 : W := mkw 0x80002004031a7220 0x340001002018d391 0x0000000007fff3ff 0x80000000003fff9f

def z880 : W := mkw 0x225fc6fb0000001c 0x0112fe37d8000000 0xe0ffffff00000000 0x7f07fffff8000000

def z881 : W := mkw 0x01105e5900000008 0x000882f2c8000000 0x6033fe7f00000000 0x7b019ff3f8000000

def z882 : W := mkw 0x26efc0fb0000001c 0x01377e07d8000000 0xa7cfe07f00000000 0x253e7f03f8000000

def z883 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xdfffe000fffe127f 0xbeffff0007fff093

def z884 : W := mkw 0x27ffdffb0100501c 0x213ffeffd8080280 0xe7ffffff0706f27e 0xff3ffffff8383793

def z885 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0x0733ec1f00000000 0x08399f60f8000000

def z886 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xfff01f80ff01fe1f 0xffff80fc07f80ff0

def z887 : W := mkw 0x235fdffb0000001c 0x011afeffd8000000 0x200fec7f00000000 0x21007f63f8000000

def z888 : W := mkw 0x27ffdffbb501d81e 0x213ffeffdda80ec0 0xdff3ff9fff01fc17 0xdeff9ffcfff80fe0

def z889 : W := mkw 0x85f53fa6bf5ffef2 0xbc2fa9fd35fafff7 0xfffd1fe3ffffffff 0xffffe8ff1fffffff

def z890 : W := mkw 0x0010460900000008 0x0000823048000000 0x2031ee1f00000000 0x51018f70f8000000

def z891 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0xe73ffe7f00000000 0x7f39fff3f8000000

def z892 : W := mkw 0x005546ab084404d8 0x8802aa3558422026 0xe8ffffff18c10d81 0x7f47fffff8c6086c

def z893 : W := mkw 0x004500a2084404d0 0x8802280510422026 0x88cd13e318c71ffd 0x9446689f18c638ff

def z894 : W := mkw 0x030a195460a9ab01 0x101850caa3054d58 0xf70e1dfce0f9ef9b 0xefb870efe707cf7c

def z895 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xffffe063ffff1fff 0xbfffff031ffff8ff

def z896 : W := mkw 0x05b01f50b501d802 0x202d80fa85a80ec0 0xfff01ffcff01fc17 0xdfff80ffe7f80fe0

def z897 : W := mkw 0x80002004021a2220 0x140001002010d111 0x00000000073e026e 0x800000000039f013

def z898 : W := mkw 0x26efc0fb084404dc 0x89377e07d8422026 0xefffe07f18c603ed 0xbf7fff03f8c6301f

def z899 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0x5732e000e738000a 0xaab997000739c000

def z900 : W := mkw 0x0010460900000008 0x0000823048000000 0x0033ee1f00000000 0x18019f70f8000000

def z901 : W := mkw 0x201046fb0000001c 0x01008237d8000000 0x6033ee7f00000000 0x7b019f73f8000000

def z902 : W := mkw 0x06ef8000d4a00003 0x00377c0006a50000 0xdfffe000fff8000f 0xbeffff0007ffc000

def z903 : W := mkw 0x26ffc7fb0000001c 0x0137fe3fd8000000 0x203fe07f00000000 0x2101ff03f8000000

def z904 : W := mkw 0x225fc7fb0000001c 0x0112fe3fd8000000 0x200fe3ff00000000 0x21007f1ff8000000

def z905 : W := mkw 0x27efd9fb0000001c 0x013f7ecfd8000000 0xe7fff1ff00000000 0x3f3fff8ff8000000

def z906 : W := mkw 0x80002004031a7220 0x340001002018d391 0x00010203073ef27e 0x900008101839f793

def z907 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xefffffff18c71de5 0x7f7ffffff8c638ef

def z908 : W := mkw 0x27ffdffbd4a0001f 0x013ffeffdea50000 0xfffffffffff8000f 0xffffffffffffc000

def z909 : W := mkw 0x0010460900000008 0x0000823048000000 0xe03ffe7f00000000 0x7f01fff3f8000000

def z910 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xdfffe180fffe0c0f 0xbeffff0c07fff060

def z911 : W := mkw 0x0010460900000008 0x0000823048000000 0x6033ee1f0038000a 0xfb019f70f801c000

def z912 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x5ff3e000ff3e000e 0xbaff9f0007f9f000

def z913 : W := mkw 0x27ef99f200000014 0x013f7ccf90000000 0xe7fffdfc00000000 0x7f3fffefe0000000

def z914 : W := mkw 0x0eefa0a2def60013 0xc0777d0516f7b000 0xfffff3e3ffff039f 0xffffff9f1ffff81c

def z915 : W := mkw 0x27badf599400000e 0x013dd6facca00000 0x1732ec1ce7000002 0x08b99760e7380000

def z916 : W := mkw 0x025fc60900000008 0x0012fe3048000000 0x603fee1f00000000 0x7b01ff70f8000000

def z917 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffffff00000218 0xff3ffffff8000010

def z918 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xdff01d80ff01ec13 0xceff80ec07f80f60

def z919 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xdffee000fff8000b 0xaefff70007ffc000

def z920 : W := mkw 0x07ef98f200000010 0x003f7cc790000000 0xe7ffffff00000000 0x7f3ffffff8000000

def z921 : W := mkw 0x235fdffb2101d81c 0x211afeffd9080ec0 0x200fffff0001fc10 0x61007ffff8000fe0

def z922 : W := mkw 0x0010460900000008 0x0000823048000000 0x6033ee1f00061064 0x7b019f70f8003083

def z923 : W := mkw 0x07ffdf0900000008 0x003ffef848000000 0xe7ffff9f00000000 0x7f3ffffcf8000000

def z924 : W := mkw 0x27ffdffb9500581e 0x213ffeffdca802c0 0xffffffffff001c07 0xfffffffffff800e0

def z925 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xdff11f83ff07fc77 0xdeff88fc1ff83fe3

def z926 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x6033ec1f073ee26e 0xbb019f60f839f713

def z927 : W := mkw 0x800020040b5e76e0 0xbc000100205af3b7 0x0000000007fef3fe 0x80000000003ff79f

def z928 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xfffff383ffff1e7f 0xffffff9c1ffff8f3

def z929 : W := mkw 0xa7ffdffb0100503c 0x253ffeffd8080281 0xe7ffffff00001060 0x7f3ffffff8000083

def z930 : W := mkw 0x24f5c7af60a9a31d 0x1127ae3d7b054d18 0x10f1e383e0f9e39b 0x90878f1c1f07cf1c

def z931 : W := mkw 0x0eefa0a2def60013 0xc0777d0516f7b000 0xffffe063fffe000f 0xbfffff031ffff000

def z932 : W := mkw 0x8010660d031a7228 0x340083306818d391 0xe8ffffff1fffffff 0xff47fffff8ffffff

def z933 : W := mkw 0x034f18f668eda7d1 0x981a78c7b3476d3e 0x1fc30f9ff83efc66 0x18fe187cffc1f7e3

def z934 : W := mkw 0x27ffdffb9400001e 0x013ffeffdca00000 0xf7ffffffe7000002 0x7fbfffffff380000

def z935 : W := mkw 0x27badf599400000e 0x013dd6facca00000 0xdff2ec1cff000007 0x9eff9760e7f80000

def z936 : W := mkw 0x06efc00900000008 0x00377e0048000000 0xe7ffe01f00000000 0x3f3fff00f8000000

def z937 : W := mkw 0x005546ab00000018 0x0002aa3558000000 0x60f3ef9f00000000 0x7b079f7cf8000000

def z938 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xf73ffc7ce0f9e39b 0xffb9ffe3e707cf1c

def z939 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xdfffe003fffe006f 0xbeffff001ffff003

def z940 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0x9ff2e000ff380003 0x0cff970007f9c000

def z941 : W := mkw 0x21105ffb000004dc 0x090882ffd8000026 0x6033ffff00071ffc 0xfb019ffff80038ff

def z942 : W := mkw 0x81105e0d2109f228 0x340882f069084f91 0x20001e1f0001f270 0x410000f0f8000f93

def z943 : W := mkw 0x04f5c60900000008 0x0027ae3048000000 0x60f3ee1f00000000 0x7b079f70f8000000

def z944 : W := mkw 0x225fc6fb0000001c 0x0112fe37d8000000 0x203fe27f00000000 0x3101ff13f8000000

def z945 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0x1732e000e73e000e 0x88b997000739f000

def z946 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0xe7f3ff9f00000000 0x7f3f9ffcf8000000

def z947 : W := mkw 0x80002004031a7220 0x340001002018d391 0x20000203073ef27e 0xc10000101839f793

def z948 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0xd73ee000e7380002 0x2eb9f7000739c000

def z949 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xdffff3e3ffff1def 0xbeffff9f1ffff8ef

def z950 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0xe73efc7c00c10399 0xef39f7e3e006081c

def z951 : W := mkw 0x820a200443ba7221 0x34105100221dd391 0xd70e0000e7fef27f 0xaeb87000073ff793

def z952 : W := mkw 0x27ffdffb0844001c 0x813ffeffd8422000 0xefffffff18060004 0x7f7ffffff8c03000

def z953 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xe7ffffff00c613fc 0xff3ffffff806309f

def z954 : W := mkw 0x880020044afe2221 0xd44001002257f111 0x0000000000fe0268 0x000000000007f013

def z955 : W := mkw 0x21105ffb2101d81c 0x210882ffd9080ec0 0x6033ffff0701fc16 0xfb019ffff8380fe0

def z956 : W := mkw 0x880020044bfe7221 0xf4400100225ff391 0x0000000007fef27e 0x80000000003ff793

def z957 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0x9ffef1e0fff90d83 0x0cfff78f07ffc86c

def z958 : W := mkw 0x27badf59b401880e 0x013dd6facda00c40 0x1732ec1ce0000000 0x08b99760e7000000

def z959 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xdfffe000ff3e0006 0x3effff0007f9f000

def z960 : W := mkw 0x05f55fabb501d81a 0x202faafd5da80ec0 0xffffffffff01fc17 0xfffffffffff80fe0

def z961 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0x770e0c7ce0f8e39a 0xebb87063e707c71c

def z962 : W := mkw 0x05b05f0900000008 0x002d82f848000000 0x6733ee1f00000000 0x7b399f70f8000000

def z963 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0x5733e000e7380002 0x3ab99f000739c000

def z964 : W := mkw 0x27badf59b501d80e 0x213dd6facda80ec0 0xf73efc7ce701e013 0xefb9f7e3e7380f00

def z965 : W := mkw 0x27ffdffb0844001c 0x813ffeffd8422000 0xefffffff18c7039d 0xff7ffffff8c6381c

def z966 : W := mkw 0x020a200042b20001 0x0010510002159000 0x5733e000e73e000e 0xbab99f000739f000

def z967 : W := mkw 0x27badf59b401880e 0x013dd6facda00c40 0x9ff2fd9cf8010c01 0x0cff97ece7c00860

def z968 : W := mkw 0x80002004231bf220 0x340001002118df91 0x10000000e73ff27f 0x808000000739ff93

def z969 : W := mkw 0x81105eff2109f7f8 0x3c0882f7f9084fbf 0x20001fff0001fff0 0x410000fff8000fff

def z970 : W := mkw 0x0eefa050def60103 0xc0777d0286f7b008 0xdfffe060fffe018f 0xbeffff0307fff00c

def z971 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0x9ff01f80ff01fc07 0x1cff80fc07f80fe0

def z972 : W := mkw 0x8a4fe0af4afe26f9 0xdc527f057a57f137 0x200fe07f00fe03e8 0x21007f03f807f01f

def z973 : W := mkw 0x27badf590100500c 0x213dd6fac8080280 0x0732ec1c0700e002 0x08399760e0380700

def z974 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xa8cc13e318c71ffd 0xc546609f18c638ff

def z975 : W := mkw 0x0000200462bba301 0x100001002315dd18 0x10000000e7ffe39f 0x80800000073fff1c

def z976 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xe8fff3e318c71ffd 0xff47ff9f18c638ff

def z977 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffffff00c00388 0x7f3ffffff806001c

def z978 : W := mkw 0x27ffdffbb501d81e 0x213ffeffdda80ec0 0xffffffffff07fe7f 0xfffffffffff83ff3

def z979 : W := mkw 0x0010460901005008 0x2000823048080280 0x4032ee1c0700f016 0xda019770e0380780

def z980 : W := mkw 0x0010460900000008 0x0000823048000000 0x2032ee1f00000000 0x49019770f8000000

def z981 : W := mkw 0x06bac60900000008 0x0035d63048000000 0x6733ee1f00000000 0x7b399f70f8000000

def z982 : W := mkw 0x80102604031a7220 0x340081302018d391 0x00300c000738e002 0x080180600039c700

def z983 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0x9ff01380ff01fc17 0x94ff809c07f80fe0

def z984 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xdffff1e0ffff1fff 0xbeffff8f07fff8ff

def z985 : W := mkw 0x27ffdffbb401881e 0x013ffeffdda00c40 0xf7ffffffe0000000 0x7fbfffffff000000

def z986 : W := mkw 0x26efc0fb084404dc 0x89377e07d8422026 0xeffff3ff18c71ffd 0xff7fff9ff8c638ff

def z987 : W := mkw 0x0eefa000d6b20003 0x40777d0006b59000 0xd7ffe000e7f8000b 0xbebfff00073fc000

def z988 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xf70e1c7ce0f9e183 0x6fb870e3e707cf0c

def z989 : W := mkw 0x0010460900000008 0x0000823048000000 0x6033ee1f00001270 0x7b019f70f8000093

def z990 : W := mkw 0x80002004971a7222 0x3400010024b8d391 0x18000000ff3ef27f 0x80c0000007f9f793

def z991 : W := mkw 0x07ef985000000000 0x003f7cc280000000 0xc7ffec1c00000000 0x3e3fff60e0000000

def z992 : W := mkw 0x80002004031a7220 0x340001002018d391 0x000000000738e21a 0x800000000039c710

def z993 : W := mkw 0x220ac0590000000c 0x01105602c8000000 0x2003e01f00000000 0x21001f00f8000000

def z994 : W := mkw 0x020a005440a82301 0x10105002a2054118 0x000c006000f80388 0x000060030007c01c

def z995 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xefffffff18c603ed 0xff7ffffff8c6301f

def z996 : W := mkw 0x004540ab084404d8 0x88022a0558422026 0x200fe07f00c603e8 0x21007f03f806301f

def z997 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xf7ffffffe0000003 0xffbfffffff000000

def z998 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x9ffee000fffe000f 0x8cfff70007fff000

def z999 : W := mkw 0x27ffdffbb401881e 0x013ffeffdda00c40 0xfffffffff801ec13 0xffffffffffc00f60

def z1000 : W := mkw 0x224fc0fb084404dc 0x89127e07d8422026 0x28cfe3ff18061c64 0x31467f1ff8c030e3

def z1001 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x2033ee1f073ef27c 0x71019f70f839f793

def z1002 : W := mkw 0x0a0a2000def60003 0xc050510006f7b000 0xdf3fe000fffe000f 0xbef9ff0007fff000

def z1003 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8cd13e318c71ffd 0xf746689f18c638ff

def z1004 : W := mkw 0x0ca02000def60003 0xc065010006f7b000 0xdff3e000fffe000f 0xbeff9f0007fff000

def z1005 : W := mkw 0x0eefa0a2d6b20013 0x40777d0516b59000 0xf7fff3e3e7380002 0x7fbfff9f1f39c000

def z1006 : W := mkw 0x27ffdffb40a0011d 0x013ffeffda050008 0xe7ffffff00c00180 0x7f3ffffff806000c

def z1007 : W := mkw 0x2fffdffb48e4001d 0xc17ffeffda472000 0xe7ffffff00c00000 0x7f3ffffff8060000

def z1008 : W := mkw 0x804520a60b5e76f0 0xbc022905305af3b7 0x08c103831f3efe7e 0x9046081c18f9f7f3

def z1009 : W := mkw 0x04a00000b501d802 0x2025000005a80ec0 0xdff01380ff01fc17 0xdeff809c07f80fe0

def z1010 : W := mkw 0x27badf59b501d80e 0x213dd6facda80ec0 0x7733ee1fe700f016 0xfbb99f70ff380780

def z1011 : W := mkw 0x27badf592101d80c 0x213dd6fac9080ec0 0x0732ec1c0000e000 0x08399760e0000700

def z1012 : W := mkw 0x224fc0fb0000001c 0x01127e07d8000000 0x200fe07f00c00388 0x21007f03f806001c

def z1013 : W := mkw 0x24f5c7ab9500581e 0x2127ae3d5ca802c0 0x68f3ef9f1f00fc16 0xfb479f7cf8f807e0

def z1014 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xefffffff18c70fe9 0x7f7ffffff8c6387f

def z1015 : W := mkw 0x0010460900000008 0x0000823048000000 0x4033ec1c00000000 0x3a019f60e0000000

def z1016 : W := mkw 0x88452004dffe7223 0xf442290026fff391 0xf8cd0203fffef27f 0xf7c668101ffff793

def z1017 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0x0733ee1f00000000 0x18399f70f8000000

def z1018 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xd73fe000e7fe000b 0xaeb9ff00073ff000

def z1019 : W := mkw 0x0a4fa0004af60001 0xc0527d000257b000 0x000c000000fe0008 0x000060000007f000

def z1020 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x4033ee1f073ef06e 0xba019f70f839f783

def z1021 : W := mkw 0x27ffdf590000000c 0x013ffefac8000000 0xe7ffee1f00000000 0x7f3fff70f8000000

def z1022 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0x1f32e000ff380007 0x88f9970007f9c000

def z1023 : W := mkw 0x04b047099500580a 0x202582384ca802c0 0x08f1e3831f001c04 0x10478f1c18f800e0

def z1024 : W := mkw 0x804520040b5e7220 0xb4022900205af391 0xc8cd00001ffef27f 0xb646680000fff793

def z1025 : W := mkw 0x06aa2000d6b20003 0x0035510006b59000 0xdfffe000fffe000f 0xbeffff0007fff000

def z1026 : W := mkw 0x88002004dffe7223 0xf440010026fff391 0x18000000fffee00f 0x80c0000007fff700

def z1027 : W := mkw 0x805526a60b5e76f0 0xbc02a935305af3b7 0xe8fd1fe31fffffff 0xff47e8ff18ffffff

def z1028 : W := mkw 0x27ffdffbb501d81e 0x213ffeffdda80ec0 0xffffffffff011c05 0x7ffffffffff808e0

def z1029 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0x370e0c7ce0f9e39b 0xa9b87063e707cf1c

def z1030 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xdffff060ffff018f 0xbeffff8307fff80c

def z1031 : W := mkw 0x0010460901005008 0x2000823048080280 0x0032ec1c0700e002 0x08019760e0380700

def z1032 : W := mkw 0x06ef800000000000 0x00377c0000000000 0xe7ffec1c00000000 0x7f3fff60e0000000

def z1033 : W := mkw 0x05a01800b4018002 0x002d00c005a00c00 0xdff01f80ff01fc17 0xdeff80fc07f80fe0

def z1034 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xc7fefffc00000000 0x5e3ff7ffe0000000

def z1035 : W := mkw 0x001046ab000004d8 0x0800823558000026 0x6033ffff00011ff0 0x7b019ffff80008ff

def z1036 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xffffe060fffe038f 0xbfffff0307fff01c

def z1037 : W := mkw 0x27ffdffb2101d81c 0x213ffeffd9080ec0 0xe7ffffff0000e000 0x7f3ffffff8000700

def z1038 : W := mkw 0x27ffdffbb401801e 0x013ffeffdda00c00 0xffffffffff01e017 0xfffffffffff80f00

def z1039 : W := mkw 0x831a7e5963b3d129 0x2418d3f2cb1d9e89 0x973df263e7c711e5 0x14b9ef931f3e388f

def z1040 : W := mkw 0x27ffdffbb501d81e 0x213ffeffdda80ec0 0xffffffffff00fc06 0x7ffffffffff807e0

def z1041 : W := mkw 0x2eefa1a2def60017 0xc1777d0d16f7b000 0xdfffe180fffe000f 0xbeffff0c07fff000

def z1042 : W := mkw 0x80002004021a2220 0x140001002010d111 0x00000000003e127c 0x800000000001f093

def z1043 : W := mkw 0x25f5dffb084404dc 0x892faeffd8422026 0xe8fdffff18c71ffd 0xf747effff8c638ff

def z1044 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xdfffe380fffe1c0f 0xbeffff1c07fff0e0

def z1045 : W := mkw 0x0eefa000def604c3 0xc8777d0006f7b026 0xdfffe000fffe03ef 0xbeffff0007fff01f

def z1046 : W := mkw 0x031a5e5900000008 0x0018d2f2c8000000 0xe73ffe7f00c713fd 0xff39fff3f806389f

def z1047 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffffff00c00009 0xff3ffffff8060000

def z1048 : W := mkw 0x225fc6fb0000001c 0x0112fe37d8000000 0x203fec7f00000000 0x2901ff63f8000000

def z1049 : W := mkw 0x07ffde5900000008 0x003ffef2c8000000 0xe7fffe7f00000000 0x7f3ffff3f8000000

def z1050 : W := mkw 0x81105e5d2109f328 0x340882f2e9084f99 0x00000c1c0000e000 0x00000060e0000700

def z1051 : W := mkw 0x224fc0fb40a0011d 0x01127e07da050008 0x200fe07f00c00180 0x21007f03f806000c

def z1052 : W := mkw 0x0010460900000008 0x0000823048000000 0x2003ee1f00000000 0x61001f70f8000000

def z1053 : W := mkw 0x2a4fc0fb48e4001d 0xc1527e07da472000 0x200fe07f00c00000 0x21007f03f8060000

def z1054 : W := mkw 0x80002004b71bfa22 0x3400010025b8dfd1 0x10000000e738e002 0x008000000739c700

def z1055 : W := mkw 0x0000400900000008 0x0000020048000000 0x6033e01f00000000 0x3b019f00f8000000

def z1056 : W := mkw 0x04e520a29e5604d2 0x8827290514f2b026 0xfffff3e3ffff1fff 0xffffff9f1ffff8ff

def z1057 : W := mkw 0x8010660d031a7228 0x340083306818d391 0xe8f3ee1f1f3ef27f 0xff479f70f8f9f793

def z1058 : W := mkw 0x27ffdffbb501d81e 0x213ffeffdda80ec0 0x373fec7fe700e002 0x29b9ff63ff380700

def z1059 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0xd7f2e000e7380002 0x1ebf97000739c000

def z1060 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0x9fc01f80ff01fc17 0xc4fe00fc07f80fe0

def z1061 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x6033ee1f073ee26a 0x7b019f70f839f713

def z1062 : W := mkw 0x81105f5d2109fb28 0x340882fae9084fd9 0x20001fff0001fff0 0x410000fff8000fff

def z1063 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0x2732ee1f00000000 0x49399770f8000000

def z1064 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xe7ffffff00c00180 0x7f3ffffff806000c

def z1065 : W := mkw 0x80002004031a7220 0x340001002018d391 0x40300000073ef27e 0x9a0180000039f793

def z1066 : W := mkw 0x0eefa0a2def60013 0xc0777d0516f7b000 0xfffff3e3fffe127f 0xffffff9f1ffff093

def z1067 : W := mkw 0x27badf590100500c 0x213dd6fac8080280 0x4732ee1c0700f016 0xda399770e0380780

def z1068 : W := mkw 0x0eefa000d6b20003 0x40777d0006b59000 0x173fe000e7380002 0x28b9ff000739c000

def z1069 : W := mkw 0x81555faf294dfef8 0xbc0aaafd794a6ff7 0xe8cd1fff18c7fffd 0xf74668fff8c63fff

def z1070 : W := mkw 0x05f55fab00000018 0x002faafd58000000 0xe7ffffff00000000 0x7f3ffffff8000000

def z1071 : W := mkw 0x80102604031a7220 0x340081302018d391 0x40300e000738f016 0xda0180700039c780

def z1072 : W := mkw 0x27ffdffb48e4001d 0x813ffeffda472000 0xfffffffff8fe000f 0xffffffffffc7f000

def z1073 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xa7cfffff00000000 0x653e7ffff8000000

def z1074 : W := mkw 0x06ffc6ab084404d8 0x8837fe3558422026 0xefffffff18c71ffd 0xff7ffffff8c638ff

def z1075 : W := mkw 0x0eaaa000def60003 0xc075550006f7b000 0xdf3ee000fffe000f 0xaef9f70007fff000

def z1076 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x6033ec1f073ee27a 0xeb019f60f839f713

def z1077 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xffce1c7cf8f9e39f 0xfffe70e3e7c7cf1c

def z1078 : W := mkw 0x224fc0fb0000001c 0x01127e07d8000000 0x000ee07c00000000 0x00007703e0000000

def z1079 : W := mkw 0x04a0200096120002 0x0025010004b09000 0xdff2e000ff380007 0x9eff970007f9c000

def z1080 : W := mkw 0x27ffdffbf5a1d91f 0x213ffeffdfad0ec8 0xffffffffffc1fd97 0xfffffffffffe0fec

def z1081 : W := mkw 0x2fffdffbfde5d81f 0xe17ffeffdfef2ec0 0xffffffffffc1fc17 0xfffffffffffe0fe0

def z1082 : W := mkw 0x27badf592001800c 0x013dd6fac9000c00 0x1732ec1ce000e002 0x08b99760e7000700

def z1083 : W := mkw 0x0000000000000000 0x0000000000000000 0x6033ec1c00000000 0x7b019f60e0000000

def z1084 : W := mkw 0x85b03f04bf5ffee2 0xbc2d81f825fafff7 0xdff01f80ffffffff 0xdeff80fc07ffffff

def z1085 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xc7fffdfc00000000 0x3e3fffefe0000000

def z1086 : W := mkw 0xa1105fff2109fa3c 0x350882fff9084fd1 0x20001fff0001fe70 0x410000fff8000ff3

def z1087 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xdfffe000ffff1c1f 0xbeffff0007fff8e0

def z1088 : W := mkw 0x024f20a24af604d1 0x881279051257b026 0xfffff3e3ffff1fff 0xffffff9f1ffff8ff

def z1089 : W := mkw 0x04a0000094000002 0x0025000004a00000 0xdff3e000ff000007 0xbeff9f0007f80000

def z1090 : W := mkw 0x0010460900000008 0x0000823048000000 0x6032ec1c00000000 0x6b019760e0000000

def z1091 : W := mkw 0x27ffdffb0100501c 0x213ffeffd8080280 0xe7ffffff0700e002 0x7f3ffffff8380700

def z1092 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xf70e1ffce0f9ff9b 0xefb870ffe707cffc

def z1093 : W := mkw 0x21105f590000000c 0x010882fac8000000 0x0032ec1c00000000 0x08019760e0000000

def z1094 : W := mkw 0x27badf592101d80c 0x213dd6fac9080ec0 0x0732ff9c0001fc10 0x483997fce0000fe0

def z1095 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0x1ff3e383ff3e1c66 0x18ff9f1c1ff9f0e3

def z1096 : W := mkw 0x24f5c7ab084404dc 0x8927ae3d58422026 0x68f3ef9f18061e7c 0xfb479f7cf8c030f3

def z1097 : W := mkw 0x25f5dfab0000001c 0x012faefd58000000 0xe7f3ff9f00000000 0x7f3f9ffcf8000000

def z1098 : W := mkw 0x80002004031a7220 0x340001002018d391 0x20010003073ef27e 0xa10008001839f793

def z1099 : W := mkw 0x04b0060095005002 0x2025803004a80280 0xdff01f80ff01fc17 0xdeff80fc07f80fe0

def z1100 : W := mkw 0x27ffdffb2001801c 0x013ffeffd9000c00 0xf7ffffffe0010001 0x7fbfffffff000800

def z1101 : W := mkw 0x0ce5a000def60003 0xc0672d0006f7b000 0xdff1e000fffe000f 0x9eff8f0007fff000

def z1102 : W := mkw 0x80002004031a7220 0x340001002018d391 0xe00c106007fff3ff 0xe7006083003fff9f

def z1103 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0x073eec7c00000000 0x0839f763e0000000

def z1104 : W := mkw 0x24b0c7090000000c 0x0125863848000000 0x0032ec1c00000000 0x08019760e0000000

def z1105 : W := mkw 0x224fc0fb084404dc 0x89127e07d8422026 0x200fe07f00c00180 0x21007f03f806000c

def z1106 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0x9ff01f80ff01fc15 0x54ff80fc07f80fe0

def z1107 : W := mkw 0x07ff9f50b501d802 0x203ffcfa85a80ec0 0xfffffffcff01fc17 0xffffffffe7f80fe0

def z1108 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xffffec1cfffe000f 0xffffff60e7fff000

def z1109 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0x5ff00f80ff00fc16 0xdaff807c07f807e0

def z1110 : W := mkw 0x27ffdffbb501d81e 0x213ffeffdda80ec0 0xdffefffcff01fc17 0xdefff7ffe7f80fe0

def z1111 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xfffff1e0ffff0f9f 0xffffff8f07fff87c

def z1112 : W := mkw 0x08002004fffffb03 0xf040010027ffffd8 0x18000000ffffff9f 0x80c0000007fffffc

def z1113 : W := mkw 0x27ffdffbb501d81e 0x213ffeffdda80ec0 0x9ffefdfcff01ec03 0x0cfff7efe7f80f60

def z1114 : W := mkw 0x27ffdffbb501d81e 0x213ffeffdda80ec0 0xf7ffffffe701e013 0xffbfffffff380f00

def z1115 : W := mkw 0x235fdffb084404dc 0x891afeffd8422026 0x200fffff00c71ff8 0x61007ffff80638ff

def z1116 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xfffd1fe3ffc7ffff 0xffffe8ff1ffe3fff

def z1117 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x1ff2e000ff380002 0x08ff970007f9c000

def z1118 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0x2733ec1f00000000 0x29399f60f8000000

def z1119 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0x9ff01f80ff01fc13 0x4cff80fc07f80fe0

def z1120 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xfffc1fe0ff01fc17 0xffffe0ff07f80fe0

def z1121 : W := mkw 0x80002004031a7220 0x340001002018d391 0x00000000073ef066 0x000000000039f783

def z1122 : W := mkw 0x080020044afe2301 0xd04001002257f118 0x0000000000fe0388 0x000000000007f01c

def z1123 : W := mkw 0x27badf59b501d80e 0x213dd6facda80ec0 0xfff3ff9fff01fc17 0xffff9ffcfff80fe0

def z1124 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0xdff2f380ff391c17 0xdeff979c07f9c8e0

def z1125 : W := mkw 0x804520a60b5e76f0 0xbc022905305af3b7 0x88cc11e01fffffff 0x8446608f00ffffff

def z1126 : W := mkw 0x27ffdffb9400001e 0x013ffeffdca00000 0xfffffffff8000001 0x7fffffffffc00000

def z1127 : W := mkw 0x27badf5940a0000d 0x013dd6faca050000 0x1732ec1ce0380002 0x08b99760e701c000

def z1128 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xdff01f80ff01ec03 0x5eff80fc07f80f60

def z1129 : W := mkw 0x27badffb0000001c 0x013dd6ffd8000000 0x0732fdfc00000000 0x083997efe0000000

def z1130 : W := mkw 0x27ffdffb2101d81c 0x213ffeffd9080ec0 0xe7ffffff0701fc16 0xff3ffffff8380fe0

def z1131 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x4033ee1f073ef076 0xda019f70f839f783

def z1132 : W := mkw 0x8010660d031a7228 0x340083306818d391 0xe0f3ff9f073ef27e 0xff079ffcf839f793

def z1133 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xdfffe200fffe101f 0xfeffff1007fff080

def z1134 : W := mkw 0x05f51fa2bd45dcd2 0xa82fa8fd15ea2ee6 0x373d0c63e7c6e3ea 0x29b9e8631f3e371f

def z1135 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7fefdfc00000000 0x6f3ff7efe0000000

def z1136 : W := mkw 0x010018042009a200 0x100800c021004d10 0xf70e1c7ce0f9e39b 0xefb870e3e707cf1c

def z1137 : W := mkw 0x005546ab084404d8 0x8802aa3558422026 0x603fee7f00c603e8 0x7b01ff73f806301f

def z1138 : W := mkw 0x88002004dffe76e3 0xfc40010026fff3b7 0x18000000ffffffff 0x80c0000007ffffff

def z1139 : W := mkw 0x80102604031a7220 0x340081302018d391 0x00000e00073ef27e 0xc00000700039f793

def z1140 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xb70e1c7ce0f9e393 0x4db870e3e707cf1c

def z1141 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xfffff3e3ffff0d8f 0xffffff9f1ffff86c

def z1142 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0xdffee000fff8000f 0xbefff70007ffc000

def z1143 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffffff00010390 0x7f3ffffff800081c

def z1144 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xdff11f80ff07fc1f 0xfeff88fc07f83fe0

def z1145 : W := mkw 0x27ffdffbbd45dcde 0xa93ffeffddea2ee6 0xffffffffffc1fd97 0xfffffffffffe0fec

def z1146 : W := mkw 0x07ba5f59b501d80a 0x203dd2facda80ec0 0xffffffffff01fc17 0xfffffffffff80fe0

def z1147 : W := mkw 0x27ffdffb0100501c 0x213ffeffd8080280 0xe7ffffff0000f010 0x7f3ffffff8000780

def z1148 : W := mkw 0x27badf59b501d80e 0x213dd6facda80ec0 0x1f32ec1cff01fc17 0x88f99760e7f80fe0

def z1149 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xfffff063ffff03ff 0xffffff831ffff81f

def z1150 : W := mkw 0x0010460900000008 0x0000823048000000 0x6033ee1f07000006 0xfb019f70f8380000

def z1151 : W := mkw 0x235fdffb084404dc 0x891afeffd8422026 0xe8cfffff18c71ffd 0xf7467ffff8c638ff

def z1152 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xdfffe000fff80003 0x3effff0007ffc000

def z1153 : W := mkw 0x27ffdffb9500581e 0x213ffeffdca802c0 0xefffffff1f011c15 0xff7ffffff8f808e0

def z1154 : W := mkw 0x8000200442ba2321 0x140001002215d119 0x0000000000fe03e8 0x000000000007f01f

def z1155 : W := mkw 0x2045c0ab0000001c 0x01022e0558000000 0x2003e01f00000000 0x21001f00f8000000

def z1156 : W := mkw 0x8cb02604dffe7223 0xf465813026fff391 0xdff00e00fffef27f 0xdeff807007fff793

def z1157 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0x5732e000e7380006 0x9ab997000739c000

def z1158 : W := mkw 0x8010660d031a7228 0x340083306818d391 0xe03fee1f07fef27f 0xff01ff70f83ff793

def z1159 : W := mkw 0x06bac60900000008 0x0035d63048000000 0x0732ec1c00000000 0x08399760e0000000

def z1160 : W := mkw 0x234fd9fb0000001c 0x011a7ecfd8000000 0x200ff1ff00000000 0x21007f8ff8000000

def z1161 : W := mkw 0x27ffdffbb501d81e 0x213ffeffdda80ec0 0xffffffffffc1ff9f 0xfffffffffffe0ffc

def z1162 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffffff00061064 0x7f3ffffff8003083

def z1163 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xdfffec00fffee01f 0xfeffff6007fff700

def z1164 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xe8cf1fff18c71ffd 0xff4678fff8c638ff

def z1165 : W := mkw 0x81105e5d2109f328 0x340882f2e9084f99 0x20000e1f0000f270 0x41000070f8000793

def z1166 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0x370e1c7ce0f9e39a 0x69b870e3e707cf1c

def z1167 : W := mkw 0x27aad9590000000c 0x013d56cac8000000 0x0702e01c00000000 0x00381700e0000000

def z1168 : W := mkw 0x0a4fa0004af60001 0xc0527d000257b000 0xd73fe000e7fe000f 0xbeb9ff00073ff000

def z1169 : W := mkw 0x80002004031a7220 0x340001002018d391 0x080000001f3ffe7f 0x8040000000f9fff3

def z1170 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xefffffff18c70d8d 0xff7ffffff8c6386c

def z1171 : W := mkw 0x804520a60a5e26f0 0x9c0229053052f137 0x200d006300fe03e8 0x210068031807f01f

def z1172 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xfff01fe0ff01ff97 0xdfff80ff07f80ffc

def z1173 : W := mkw 0x27ffdffb0844001c 0x813ffeffd8422000 0xe7ffffff00c60008 0x7f3ffffff8063000

def z1174 : W := mkw 0x0da03804feffa303 0xd06d01c027f7fd18 0xdff01c00ffffe39f 0xdeff80e007ffff1c

def z1175 : W := mkw 0x85b03f04f7bbfb23 0x342d81f827bddfd9 0xdff01f80ffffffff 0xdeff80fc07ffffff

def z1176 : W := mkw 0x80002004021a2220 0x140001002010d111 0x0000000000380000 0x000000000001c000

def z1177 : W := mkw 0x804520a60b5e76f0 0xbc022905305af3b7 0x200d006307fef3fe 0xa1006803183ff79f

def z1178 : W := mkw 0x81003804231bf220 0x340801c02118df91 0xd7001c00e73ff27f 0xceb800e00739ff93

def z1179 : W := mkw 0x27ffdffb60a1811d 0x013ffeffdb050c08 0xf7ffffffe0c1e193 0xffbfffffff060f0c

def z1180 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0x07f2ed9c00000000 0x083f976ce0000000

def z1181 : W := mkw 0x004540ab00000018 0x00022a0558000000 0xe0cff3ff00000000 0x77067f9ff8000000

def z1182 : W := mkw 0x26ffc7fb084404dc 0x8937fe3fd8422026 0xe8fff3ff18c71ffd 0xf747ff9ff8c638ff

def z1183 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffffff00c713fd 0xff3ffffff806389f

def z1184 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xfffff1e3ffff0fef 0xbfffff8f1ffff87f

def z1185 : W := mkw 0x27ffdffb68e585dd 0x893ffeffdb472c2e 0xfffffffff8c71ffd 0xffffffffffc638ff

def z1186 : W := mkw 0x01001800b501d802 0x200800c005a80ec0 0xdfc01f80ff01fc17 0xdefe00fc07f80fe0

def z1187 : W := mkw 0x27ffdffbb501d81e 0x213ffeffdda80ec0 0x1ff3ef9fff00fc06 0x18ff9f7cfff807e0

def z1188 : W := mkw 0x230ad8590000000c 0x011856c2c8000000 0xe70efc7c00000000 0x6f3877e3e0000000

def z1189 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xdffee000fff80007 0x9efff70007ffc000

def z1190 : W := mkw 0x85b05f09b501d82a 0x242d82f84da80ec1 0xdff01f83ff01fc77 0xdeff80fc1ff80fe3

def z1191 : W := mkw 0x830a385463bbf321 0x341851c2a31ddf99 0x970c1060e7fff3ff 0x84b86083073fff9f

def z1192 : W := mkw 0x05f55fab084404d8 0x882faafd58422026 0xefffffff18c71ffd 0xff7ffffff8c638ff

def z1193 : W := mkw 0x26ffc7fb9500581e 0x2137fe3fdca802c0 0x28ffe3ff1f001c04 0x3147ff1ff8f800e0

def z1194 : W := mkw 0x27ffdffb000004dc 0x093ffeffd8000026 0xe7ffffff000003e0 0x7f3ffffff800001f

def z1195 : W := mkw 0x88002004d7ba7223 0x7440010026bdd391 0x10000000e738e002 0x008000000739c700

def z1196 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0xcff2ff9c18011c15 0xde7f97fce0c008e0

def z1197 : W := mkw 0x2fffdffbdce404df 0xc97ffeffdee72026 0xfffffffff8c71ffd 0xffffffffffc638ff

def z1198 : W := mkw 0x27efd9fb0000001c 0x013f7ecfd8000000 0xe7cff3ff00000000 0x773e7f9ff8000000

def z1199 : W := mkw 0x27badf5960a1810d 0x013dd6facb050c08 0x973efc7ce0c10181 0x0cb9f7e3e706080c

def z1200 : W := mkw 0x2eefa0f2def60017 0xc1777d0796f7b000 0xdfffe060fffe000f 0xbeffff0307fff000

def z1201 : W := mkw 0x06efa00042b20001 0x00377d0002159000 0xd7ffe000e7fe000f 0xbebfff00073ff000

def z1202 : W := mkw 0x26ffc6fb0000001c 0x0137fe37d8000000 0xe7ffee7f00000000 0x7f3fff73f8000000

def z1203 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xdfffe203fffe106f 0xbeffff101ffff083

def z1204 : W := mkw 0x25f5dffbb501d81e 0x212faeffdda80ec0 0x28f1ffff1f01fc14 0x51478ffff8f80fe0

def z1205 : W := mkw 0x880020049f5e7222 0xf440010024faf391 0x080000001f3ef27e 0x8040000000f9f793

def z1206 : W := mkw 0x0eefa000d6b20003 0x40777d0006b59000 0x17f3e000e7380002 0x18bf9f000739c000

def z1207 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x0033ee1f073ef27e 0x98019f70f839f793

def z1208 : W := mkw 0x08002004f6bba303 0x5040010027b5dd18 0x10000000e7f9e39b 0x80800000073fcf1c

def z1209 : W := mkw 0x030a585900000008 0x001852c2c8000000 0xe70ffc7f00000000 0x6f387fe3f8000000

def z1210 : W := mkw 0x80002004031a76e0 0x3c0001002018d3b7 0x00000000073ffffe 0x800000000039ffff

def z1211 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0x8ffefdfc18c10d81 0x0c7ff7efe0c6086c

def z1212 : W := mkw 0x230ad8590000000c 0x011856c2c8000000 0x0702ec1c00000000 0x08381760e0000000

def z1213 : W := mkw 0x225fc6fb084404dc 0x8912fe37d8422026 0x603fee7f00c613fc 0xfb01ff73f806309f

def z1214 : W := mkw 0x05b05f09b501d80a 0x202d82f84da80ec0 0x7733ee1fe700e002 0x7bb99f70ff380700

def z1215 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xfffff3e3fffe03ef 0xffffff9f1ffff01f

def z1216 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0x1733e000e73e000a 0x28b99f000739f000

def z1217 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x1f3fe000fffe000f 0xa8f9ff0007fff000

def z1218 : W := mkw 0x81105e5d2109f328 0x340882f2e9084f99 0xe00d1e7f00c7f3fd 0xf70068f3f8063f9f

def z1219 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x9ffde000fffe000f 0x94ffef0007fff000

def z1220 : W := mkw 0x224fc0fb0844001c 0x81127e07d8422000 0x200fe07f00c60008 0x21007f03f8063000

def z1221 : W := mkw 0x27ffdffb40a0001d 0x013ffeffda050000 0xe7ffffff00f80008 0x7f3ffffff807c000

def z1222 : W := mkw 0x201047ab0000001c 0x0100823d58000000 0x6033ef9f00000000 0x7b019f7cf8000000

def z1223 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xefffffff18c11ff1 0x7f7ffffff8c608ff

def z1224 : W := mkw 0x234fd8fb60a1811d 0x011a7ec7db050c08 0xb70ff07fe0c10181 0x25b87f83ff06080c

def z1225 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x2033ee1f073ef26e 0x39019f70f839f793

def z1226 : W := mkw 0x26aac0590000000c 0x01355602c8000000 0x0732e01c00000000 0x08399700e0000000

def z1227 : W := mkw 0x27ffdffb2001801c 0x013ffeffd9000c00 0xf7ffffffe000e002 0x7fbfffffff000700

def z1228 : W := mkw 0x27ffdffb9400001e 0x013ffeffdca00000 0xffffffffff011c17 0xfffffffffff808e0

def z1229 : W := mkw 0x224fc0fb000004dc 0x09127e07d8000026 0x200fe07f000003e0 0x21007f03f800001f

def z1230 : W := mkw 0x27ffdffbb401881e 0x013ffeffdda00c40 0xffffffffff010c07 0xfffffffffff80860

def z1231 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x9fffe000fffe000b 0x2cffff0007fff000

def z1232 : W := mkw 0x0b0a3850def60003 0xc05851c286f7b000 0xff0e1c7cfffe000f 0xeff870e3e7fff000

def z1233 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffffff00010011 0xff3ffffff8000800

def z1234 : W := mkw 0x27ffdffb000004dc 0x093ffeffd8000026 0xe7ffffff00071ffc 0xff3ffffff80038ff

def z1235 : W := mkw 0x020a200042b20001 0x0010510002159000 0xf73ff263e7ff13ff 0xffb9ff931f3ff89f

def z1236 : W := mkw 0x224fc0fb084404dc 0x89127e07d8422026 0xa8cff1ff18c10d81 0x25467f8ff8c6086c

def z1237 : W := mkw 0x07ff9f5000000000 0x003ffcfa80000000 0xe7fffffc00000000 0x7f3fffffe0000000

def z1238 : W := mkw 0x21555ffb0000001c 0x010aaaffd8000000 0xe0ffffff00000000 0x7f07fffff8000000

def z1239 : W := mkw 0x005546ab084404d8 0x8802aa3558422026 0x68f3ef9f18061c64 0x7b479f7cf8c030e3

def z1240 : W := mkw 0x84f567ab9f565cfa 0xac27ab3d5cfab2e7 0x08f1e3831f061c64 0x10478f1c18f830e3

def z1241 : W := mkw 0x85b03f04b71bfa22 0x342d81f825b8dfd1 0x17300c00e738e002 0x08b980600739c700

def z1242 : W := mkw 0x27ffdffb2001801c 0x013ffeffd9000c00 0xf7ffffffe0c1e39b 0xffbfffffff060f1c

def z1243 : W := mkw 0x0eefa000def604c3 0xc8777d0006f7b026 0xdfffe000ffff0d8f 0xbeffff0007fff86c

def z1244 : W := mkw 0x27badf599500580e 0x213dd6facca802c0 0x0ff2ef9c1f001c04 0x187f977ce0f800e0

def z1245 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x1733e000e73e0002 0x08b99f000739f000

def z1246 : W := mkw 0x05b05f09b401880a 0x002d82f84da00c40 0xfff3ff9ff8010c01 0x7fff9ffcffc00860

def z1247 : W := mkw 0x224fc0fb0844001c 0x81127e07d8422000 0xe8cfe07f18c6000d 0xb7467f03f8c63000

def z1248 : W := mkw 0x01105e0920018008 0x000882f049000c00 0xf733fe1fe001e013 0xffb99ff0ff000f00

def z1249 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0x2732fc7c00000000 0x493997e3e0000000

def z1250 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x2033ec1f073ef27e 0xa9019f60f839f793

def z1251 : W := mkw 0x0010460901005008 0x2000823048080280 0x6033ee1f0700e002 0x7b019f70f8380700

def z1252 : W := mkw 0x224fc0fb0000001c 0x01127e07d8000000 0x600fe27f00000000 0x73007f13f8000000

def z1253 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x00000203073ef27e 0x800000101839f793

def z1254 : W := mkw 0x0010460900000008 0x0000823048000000 0x6033ee1f0000e012 0xfb019f70f8000700

def z1255 : W := mkw 0x801026040b5e76e0 0xbc008130205af3b7 0xc8f01f801fffffff 0xde4780fc00ffffff

def z1256 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xffcd13e3f8c71fff 0xfffe689f1fc638ff

def z1257 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xdff21f80ff39fc1f 0xfeff90fc07f9cfe0

def z1258 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0xc7f2ec1c00000000 0x1e3f9760e0000000

def z1259 : W := mkw 0x27ffdffbbd45d81e 0xa13ffeffddea2ec0 0xffffffffffc7fc1f 0xfffffffffffe3fe0

def z1260 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xf70f1e7fe0f9e39b 0xffb878f3ff07cf1c

def z1261 : W := mkw 0x80002004031a7220 0x340001002018d391 0x00000000073ee26a 0x000000000039f713

def z1262 : W := mkw 0x24f5c7ab0000001c 0x0127ae3d58000000 0xe0ffffff00000000 0x7f07fffff8000000

def z1263 : W := mkw 0x234fd8fb2001801c 0x011a7ec7d9000c00 0xf70ffc7fe001e013 0xefb87fe3ff000f00

def z1264 : W := mkw 0x07ef98f2084404d0 0x883f7cc790422026 0xefffffff18c71ffd 0xff7ffffff8c638ff

def z1265 : W := mkw 0x05b05f0900000008 0x002d82f848000000 0x0732ec1c00000000 0x08399760e0000000

def z1266 : W := mkw 0x81105f0d2109fa28 0x340882f869084fd1 0x00001f9c0001fc10 0x400000fce0000fe0

def z1267 : W := mkw 0x06ef805000000000 0x00377c0280000000 0xe7ffe07c00000000 0x3f3fff03e0000000

def z1268 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0x1ff2e000ff380006 0x18ff970007f9c000

def z1269 : W := mkw 0x800020046bfff7e1 0xbc000100235fffbf 0x18000000ffffffff 0x80c0000007ffffff

def z1270 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xefffffff18001c04 0x7f7ffffff8c000e0

def z1271 : W := mkw 0x030a185000000000 0x001850c280000000 0xe73ffc7c00000000 0x7f39ffe3e0000000

def z1272 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0x873efc7c00000000 0x0c39f7e3e0000000

def z1273 : W := mkw 0x224fc0fb0000001c 0x01127e07d8000000 0xe8cff3ff18011c15 0xf7467f9ff8c008e0

def z1274 : W := mkw 0x020a005440a82301 0x10105002a2054118 0xf70e0c7ce0f8e39b 0xefb87063e707c71c

def z1275 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x0033ec1f073ee062 0x08019f60f839f703

def z1276 : W := mkw 0x06ef800460a9a301 0x10377c0023054d18 0xd7ffe000e0f9e39b 0xbebfff000707cf1c

def z1277 : W := mkw 0x05b05f09b501d80a 0x202d82f84da80ec0 0xfff01f9fff01fc17 0xdfff80fcfff80fe0

def z1278 : W := mkw 0x8000600d021a2228 0x140003006810d111 0x6033ec1f073ee27e 0xfb019f60f839f713

def z1279 : W := mkw 0x0eefa0a2def60013 0xc0777d0516f7b000 0xfffff3e3ffff1c1f 0xffffff9f1ffff8e0

def z1280 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0xd73fe000e7fe000f 0xbeb9ff00073ff000

def z1281 : W := mkw 0x0000400900000008 0x0000020048000000 0x6003e21f0006127c 0xf3001f10f8003093

def z1282 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0x170e0c7ce0f8e182 0x08b87063e707c70c

def z1283 : W := mkw 0x800020040b5e7220 0xb4000100205af391 0x080000001ffef27f 0x8040000000fff793

def z1284 : W := mkw 0x224fc0fb40a0001d 0x01127e07da050000 0x200fe07f00f80008 0x21007f03f807c000

def z1285 : W := mkw 0x88002004defe2223 0xd440010026f7f111 0x18000000fffe026f 0x80c0000007fff013

def z1286 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0x1ff00f80ff01fc17 0x98ff807c07f80fe0

def z1287 : W := mkw 0x224fc0fb0000001c 0x01127e07d8000000 0x603fe07f00000000 0x3b01ff03f8000000

def z1288 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0x373fe063e7fe03ea 0x29b9ff031f3ff01f

def z1289 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xefffffff18c11f9d 0xff7ffffff8c608fc

def z1290 : W := mkw 0x07ba5f5900000008 0x003dd2fac8000000 0xe7ffffff00000000 0x7f3ffffff8000000

def z1291 : W := mkw 0x0010460901005008 0x2000823048080280 0x6033ee1f07001004 0x7b019f70f8380080

def z1292 : W := mkw 0x08002004defe2203 0xd040010026f7f110 0x18000000fffee21f 0x80c0000007fff710

def z1293 : W := mkw 0x27ffdffb9500581e 0x213ffeffdca802c0 0xefffffff1f00fc16 0xff7ffffff8f807e0

def z1294 : W := mkw 0x27ffdffb40a0001d 0x013ffeffda050000 0xf7ffffffe0380002 0x7fbfffffff01c000

def z1295 : W := mkw 0x0010460900000008 0x0000823048000000 0x6033ee1f00001014 0xfb019f70f8000080

def z1296 : W := mkw 0x24f5c7ab0000001c 0x0127ae3d58000000 0x20f3e39f00000000 0x31079f1cf8000000

def z1297 : W := mkw 0x05f55fabbd45dcda 0xa82faafd5dea2ee6 0xffffffffffc7ffff 0xfffffffffffe3fff

def z1298 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xdffff383ffff1c7f 0xfeffff9c1ffff8e3

def z1299 : W := mkw 0x21105ffb0000001c 0x010882ffd8000000 0x2031ffff00000000 0x51018ffff8000000

def z1300 : W := mkw 0x05a01900b4018802 0x002d00c805a00c40 0xdff01d80ff01ec17 0xdeff80ec07f80f60

def z1301 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x6033ee1f073ef066 0x7b019f70f839f783

def z1302 : W := mkw 0x27ffdffbb501d81e 0x213ffeffdda80ec0 0xefffffff1f01fc14 0x7f7ffffff8f80fe0

def z1303 : W := mkw 0x21105ffb0000001c 0x010882ffd8000000 0x2032ffff00000000 0x490197fff8000000

def z1304 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xffffe383fffe1e7f 0xffffff1c1ffff0f3

def z1305 : W := mkw 0x234fd8fb084404dc 0x891a7ec7d8422026 0xe70ffc7f00c703f9 0xef387fe3f806381f

def z1306 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffffff00060268 0x7f3ffffff8003013

def z1307 : W := mkw 0x27ffdffbb401881e 0x013ffeffdda00c40 0xfffffffff8011c15 0xffffffffffc008e0

def z1308 : W := mkw 0x24f5c7ab0000001c 0x0127ae3d58000000 0x00f3ef9f00000000 0x18079f7cf8000000

def z1309 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xdfffe060fffe018f 0xbeffff0307fff00c

def z1310 : W := mkw 0x27ffdffb40a0001d 0x013ffeffda050000 0xf7ffffffe0f9039b 0xffbfffffff07c81c

def z1311 : W := mkw 0x25b0df09b501d80e 0x212d86f84da80ec0 0xdff0ff80ff01fc17 0xdeff87fc07f80fe0

def z1312 : W := mkw 0x80002004031a7220 0x340001002018d391 0x000000000706f274 0x0000000000383793

def z1313 : W := mkw 0x85b03f04b71bfa22 0x342d81f825b8dfd1 0xfff11f83ff3ffe7f 0xffff88fc1ff9fff3

def z1314 : W := mkw 0x04b047099500580a 0x202582384ca802c0 0x68f3ef9f1f001c04 0x7b479f7cf8f800e0

def z1315 : W := mkw 0x0fef9850fce58103 0xc07f7cc287e72c08 0xfffffc7cf8c10181 0x7fffffe3e7c6080c

def z1316 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0xe7fefffc00000000 0x7f3ff7ffe0000000

def z1317 : W := mkw 0x27ffdffb0100501c 0x213ffeffd8080280 0xefffffff1f01fc17 0xff7ffffff8f80fe0

def z1318 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffffff00c10181 0x7f3ffffff806080c

def z1319 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xfff21f9cff01fc17 0xffff90fce7f80fe0

def z1320 : W := mkw 0x27ffdffb68e585dd 0x893ffeffdb472c2e 0xfffffffff8c10d81 0x7fffffffffc6086c

def z1321 : W := mkw 0x27ffdffb0844001c 0x813ffeffd8422000 0xefffffff18c6127d 0xff7ffffff8c63093

def z1322 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0xf73ef060e7f9039b 0xefb9f783073fc81c

def z1323 : W := mkw 0x0eefa000def604c3 0xc8777d0006f7b026 0xdfffe000fffe1c6f 0xbeffff0007fff0e3

def z1324 : W := mkw 0x26efc0590000000c 0x01377e02c8000000 0xc7ffe01c00000000 0x3e3fff00e0000000

def z1325 : W := mkw 0x85b03f04031a7220 0x342d81f82018d391 0xc7f01f80073ef27e 0xde3f80fc0039f793

def z1326 : W := mkw 0x0eaaa000def60003 0xc075550006f7b000 0x1f32e000ff3e0006 0x08f9970007f9f000

def z1327 : W := mkw 0x25f5dfabb501d81e 0x212faefd5da80ec0 0xfff3ff9fff01fc17 0xffff9ffcfff80fe0

def z1328 : W := mkw 0x88002004fffffa23 0xf440010027ffffd1 0x18000000fffffe7f 0x80c0000007fffff3

def z1329 : W := mkw 0x05b05f09b501d80a 0x202d82f84da80ec0 0x1732ec1ce700e002 0x08b99760e7380700

def z1330 : W := mkw 0x27ffdffb9d445cde 0xa93ffeffdcea22e6 0xefffffff1f061c64 0x7f7ffffff8f830e3

def z1331 : W := mkw 0x27efd9fb0000001c 0x013f7ecfd8000000 0xe7cffdff00000000 0x6f3e7feff8000000

def z1332 : W := mkw 0x0010460900000008 0x0000823048000000 0x2033e21f00000000 0x31019f10f8000000

def z1333 : W := mkw 0x08002004f6bba303 0x5040010027b5dd18 0x10000000e738e002 0x008000000739c700

def z1334 : W := mkw 0x035f5efb084404d8 0x881afaf7d8422026 0xefffffff18c71ffd 0xff7ffffff8c638ff

def z1335 : W := mkw 0x04e520009e560002 0x8027290004f2b000 0xdfffe000fffe000f 0xbeffff0007fff000

def z1336 : W := mkw 0x2fffdffbdce404df 0xc97ffeffdee72026 0xfffffffff8c10d81 0x7fffffffffc6086c

def z1337 : W := mkw 0x0010460900000008 0x0000823048000000 0x6033ee1f00060268 0x7b019f70f8003013

def z1338 : W := mkw 0xa1105fff2109f33c 0x350882fff9084f99 0x20001fff0001f3f0 0x410000fff8000f9f

def z1339 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0x6733ee1f0006127c 0xfb399f70f8003093

def z1340 : W := mkw 0x8000200443ba7221 0x34000100221dd391 0x10000000e7fef27f 0x80800000073ff793

def z1341 : W := mkw 0x221ac6590000000c 0x0110d632c8000000 0x6033ee1f00000000 0x7b019f70f8000000

def z1342 : W := mkw 0x005546ab01005018 0x2002aa3558080280 0xe8ffffff1f01fc17 0xff47fffff8f80fe0

def z1343 : W := mkw 0x27ffdf590000000c 0x013ffefac8000000 0xe7fffc7c00000000 0x7f3fffe3e0000000

def z1344 : W := mkw 0x27ffdffb9d445cde 0xa93ffeffdcea22e6 0xefffffff1fc71ffd 0xff7ffffff8fe38ff

def z1345 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0x87f2fd9c00000000 0x0c3f97ece0000000

def z1346 : W := mkw 0x080020046affa301 0xd04001002357fd18 0x10000000e0ffe39b 0x808000000707ff1c

def z1347 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x68f3ef9f1f3efe7e 0xfb479f7cf8f9f7f3

def z1348 : W := mkw 0x0eaaa000def60003 0xc075550006f7b000 0xdff2e000fffe000f 0x9eff970007fff000

def z1349 : W := mkw 0x0a4fa0f64afe27d1 0xd8527d07b257f13e 0x200fe07f00fe03e8 0x21007f03f807f01f

def z1350 : W := mkw 0x224fc0fb000004dc 0x09127e07d8000026 0x200ff3ff00011ff0 0x61007f9ff80008ff

def z1351 : W := mkw 0x24f5c7ab0000001c 0x0127ae3d58000000 0x20f1ef9f00000000 0x51078f7cf8000000

def z1352 : W := mkw 0x80102604031a7220 0x340081302018d391 0x60310e03073ef27e 0xfb0188701839f793

def z1353 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0x07f2ef9c00000000 0x183f977ce0000000

def z1354 : W := mkw 0x024f805000000000 0x00127c0280000000 0x200fe07c00000000 0x21007f03e0000000

def z1355 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0x1732e000e7f8000b 0x88b99700073fc000

def z1356 : W := mkw 0x8010660d031a7228 0x340083306818d391 0xe033fe1f073ff27f 0xff019ff0f839ff93

def z1357 : W := mkw 0x800020040b5e76e0 0xbc000100205af3b7 0x080000001f3efe7e 0x8040000000f9f7f3

def z1358 : W := mkw 0x225fc6fb084404dc 0x8912fe37d8422026 0xe8ffffff18c71ffd 0xff47fffff8c638ff

def z1359 : W := mkw 0x800020040a5e26e0 0x9c0001002052f137 0x0000000000fe03e8 0x000000000007f01f

def z1360 : W := mkw 0x031a5e5900000008 0x0018d2f2c8000000 0xe73efc7c00000000 0x6f39f7e3e0000000

def z1361 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0x273fec7f00c603e8 0x2939ff63f806301f

def z1362 : W := mkw 0x0000400900000008 0x0000020048000000 0x2003e01f00060268 0x21001f00f8003013

def z1363 : W := mkw 0x07aa985000000000 0x003d54c280000000 0x0732ec1c00000000 0x08399760e0000000

def z1364 : W := mkw 0x224fc0fb0000001c 0x01127e07d8000000 0x200fe07f00060268 0x21007f03f8003013

def z1365 : W := mkw 0x04b0070095005802 0x2025803804a802c0 0xdff00f80ff00fc17 0xdeff807c07f807e0

def z1366 : W := mkw 0x0010460900000008 0x0000823048000000 0x2033ec1f00000000 0x29019f60f8000000

def z1367 : W := mkw 0x084520a6feffa7d3 0xd842290537f7fd3e 0xf8cd13e3ffffffff 0xf7c6689f1fffffff

def z1368 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x2033ee1f073ef276 0x59019f70f839f793

def z1369 : W := mkw 0x8010660d031a7228 0x340083306818d391 0xe03ffe7f073ef27e 0xff01fff3f839f793

def z1370 : W := mkw 0x25f5dffb0000001c 0x012faeffd8000000 0xe7f1ffff00000000 0x5f3f8ffff8000000

def z1371 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xdffc1f80ffc1fc1f 0xfeffe0fc07fe0fe0

def z1372 : W := mkw 0x234fd8fb0000001c 0x011a7ec7d8000000 0xe7cfffff00000000 0x7f3e7ffff8000000

def z1373 : W := mkw 0x220ac0590000000c 0x01105602c8000000 0x200ee07c00000000 0x21007703e0000000

def z1374 : W := mkw 0x27ffdffb2101d81c 0x213ffeffd9080ec0 0xefffffff1801fc15 0xff7ffffff8c00fe0

def z1375 : W := mkw 0x27ffdffb0100581c 0x213ffeffd80802c0 0xe7ffffff00001c00 0x7f3ffffff80000e0

def z1376 : W := mkw 0x27efd8fb0000001c 0x013f7ec7d8000000 0xe7fffc7f00000000 0x7f3fffe3f8000000

def z1377 : W := mkw 0x8010670d031a7a28 0x340083386818d3d1 0x6033ef9f073efe7e 0xfb019f7cf839f7f3

def z1378 : W := mkw 0x225fc6fb0000001c 0x0112fe37d8000000 0x200fee7f00000000 0x61007f73f8000000

def z1379 : W := mkw 0x2fffdffbfce5811f 0xc17ffeffdfe72c08 0xfffffffff8c10181 0x7fffffffffc6080c

def z1380 : W := mkw 0x27ffdf590000000c 0x013ffefac8000000 0x07f3ec1c00000000 0x183f9f60e0000000

def z1381 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x573fe000e7fe000e 0xbab9ff00073ff000

def z1382 : W := mkw 0x021a460900000008 0x0010d23048000000 0xe73fee1f00000000 0x7f39ff70f8000000

def z1383 : W := mkw 0x04b00700b501d802 0x2025803805a80ec0 0xdff00380ff01fc17 0x9eff801c07f80fe0

def z1384 : W := mkw 0x80002004f7bbfb23 0x3400010027bddfd9 0x18000000ffffffff 0x80c0000007ffffff

def z1385 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffffff0000e012 0xff3ffffff8000700

def z1386 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xd70e1c7ce0f9e18b 0xaeb870e3e707cf0c

def z1387 : W := mkw 0x2fffdf59dce4000f 0xc17ffefacee72000 0x9ffeec1cf8c00001 0x0cfff760e7c60000

def z1388 : W := mkw 0x01105e0900000008 0x000882f048000000 0xe733fe1f00000000 0x7f399ff0f8000000

def z1389 : W := mkw 0x80002004231bf320 0x340001002118df99 0x00000000073ff3fe 0x800000000039ff9f

def z1390 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0x1ff01f80ff01fc16 0x58ff80fc07f80fe0

def z1391 : W := mkw 0x04a0200096120002 0x0025010004b09000 0x5733e000e73e000e 0xbab99f000739f000

def z1392 : W := mkw 0x27ffdffb000004dc 0x093ffeffd8000026 0xe7ffffff00010d80 0x7f3ffffff800086c

def z1393 : W := mkw 0x27ffdffb2001801c 0x013ffeffd9000c00 0xe7ffffff0001e010 0x7f3ffffff8000f00

def z1394 : W := mkw 0x231a5ffb0000001c 0x0118d2ffd8000000 0xe73fffff00000000 0x7f39fffff8000000

def z1395 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xefffffff18061e7c 0xff7ffffff8c030f3

def z1396 : W := mkw 0x80002004031a7220 0x340001002018d391 0x40000200073ef27e 0xd20000100039f793

def z1397 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xa8cd13e318c71ff9 0x6546689f18c638ff

def z1398 : W := mkw 0x26efc0fb0000001c 0x01377e07d8000000 0xe7fff3ff00000000 0x7f3fff9ff8000000

def z1399 : W := mkw 0x80002004b71bfa22 0x3400010025b8dfd1 0x18000000ff39fc17 0x80c0000007f9cfe0

def z1400 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xd7ffe000e7fe000a 0x3ebfff00073ff000

def z1401 : W := mkw 0x0010460901005008 0x2000823048080280 0x6033ee1f0000f010 0x7b019f70f8000780

def z1402 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0x970e1c7ce0f9e39b 0x8cb870e3e707cf1c

def z1403 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0xc732fc1c00000000 0x4e3997e0e0000000

def z1404 : W := mkw 0x0100180020018000 0x000800c001000c00 0xf7021c1ce001e013 0xefb810e0e7000f00

def z1405 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xdffff000ffff001f 0xfeffff8007fff800

def z1406 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0x273eec7c00000000 0x2939f763e0000000

def z1407 : W := mkw 0x031a5e592101d008 0x2018d2f2c9080e80 0xf73ffe7fe701f017 0xffb9fff3ff380f80

def z1408 : W := mkw 0x235fdffb0000001c 0x011afeffd8000000 0x603fffff00000000 0x7b01fffff8000000

def z1409 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xefffffff18c11d95 0xff7ffffff8c608ec

def z1410 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xffffe000fffe021f 0xffffff0007fff010

def z1411 : W := mkw 0x27efd9fb0000001c 0x013f7ecfd8000000 0x270fe07f00000000 0x21387f03f8000000

def z1412 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0x4732ee1c00000000 0x5a399770e0000000

def z1413 : W := mkw 0x27badf59b501d80e 0x213dd6facda80ec0 0xfffefffcff01fc17 0xfffff7ffe7f80fe0

def z1414 : W := mkw 0x27ffdffbb501dcde 0x293ffeffdda80ee6 0xffffffffff01fff7 0xfffffffffff80fff

def z1415 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0x973ee000e7f80003 0x0cb9f700073fc000

def z1416 : W := mkw 0x27efd9fbb401881e 0x013f7ecfdda00c40 0xbfcff1fff8010c01 0x25fe7f8fffc00860

def z1417 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xdff01f80ffc1ff9f 0xdeff80fc07fe0ffc

def z1418 : W := mkw 0x2fffdffbdce4001f 0xc17ffeffdee72000 0xfffffffff8c6000d 0xffffffffffc63000

def z1419 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xfffff3e0ffff1f9f 0xffffff9f07fff8fc

def z1420 : W := mkw 0x0055460908440008 0x8002aa3048422000 0xe8ffee1f18c6000d 0xff47ff70f8c63000

def z1421 : W := mkw 0x800020a6031a76f0 0x3c0001053018d3b7 0x200013e3073ffffe 0xc100009f1839ffff

def z1422 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xe7ffffff00060060 0x7f3ffffff8003003

def z1423 : W := mkw 0x0010460900000008 0x0000823048000000 0xe03ffe7f00c10399 0xff01fff3f806081c

def z1424 : W := mkw 0x27ffdffb0100501c 0x213ffeffd8080280 0xe7ffffff07001004 0x7f3ffffff8380080

def z1425 : W := mkw 0x020a000440a82201 0x1010500022054110 0xf70e1c7ce0f9e39b 0xefb870e3e707cf1c

def z1426 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xdffff180ffff0c0f 0xbeffff8c07fff860

def z1427 : W := mkw 0x08002004feffa7c3 0xd840010027f7fd3e 0x18000000ffffffff 0x80c0000007ffffff

def z1428 : W := mkw 0x0eefa000def604c3 0xc8777d0006f7b026 0xdffff380ffff1fff 0xfeffff9c07fff8ff

def z1429 : W := mkw 0x2045c0fb0000001c 0x01022e07d8000000 0x2001e07f00000000 0x01000f03f8000000

def z1430 : W := mkw 0x88002004d7ba7223 0x7440010026bdd391 0x10000000e73ef27e 0x808000000739f793

def z1431 : W := mkw 0x27ffdffb9c4404de 0x893ffeffdce22026 0xffffffffffc71fff 0xfffffffffffe38ff

def z1432 : W := mkw 0x81103e0463bbf321 0x340881f0231ddf99 0xd7301e00e7fff3ff 0xdeb980f0073fff9f

def z1433 : W := mkw 0x85a03904b71bfa22 0x342d01c825b8dfd1 0x9fc01180ff3ffe7f 0x84fe008c07f9fff3

def z1434 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x2033ee1f073ef27a 0x69019f70f839f793

def z1435 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xe7ffffff00c703f9 0xff3ffffff806381f

def z1436 : W := mkw 0x26efc0fb0000001c 0x01377e07d8000000 0x20ffe07f00000000 0x3107ff03f8000000

def z1437 : W := mkw 0x81103f04231bfa20 0x340881f82118dfd1 0x00001f80073ffe7e 0xc00000fc0039fff3

def z1438 : W := mkw 0x0eaaa000def604c3 0xc875550006f7b026 0x1f32e000ffff1fff 0x88f9970007fff8ff

def z1439 : W := mkw 0x80002004231bfa20 0x340001002118dfd1 0x00000000073ffe7e 0x800000000039fff3

def z1440 : W := mkw 0x8db03f04fffffa23 0xf46d81f827ffffd1 0xdff01f80fffffe7f 0xdeff80fc07fffff3

def z1441 : W := mkw 0x27ffdf590000000c 0x013ffefac8000000 0xc7ffff9c00000000 0x7e3ffffce0000000

def z1442 : W := mkw 0x27ffdf590000000c 0x013ffefac8000000 0x87feec1c00000000 0x0c3ff760e0000000

def z1443 : W := mkw 0x04a0200096120002 0x0025010004b09000 0xfff3f383ff3f1e7f 0xffff9f9c1ff9f8f3

def z1444 : W := mkw 0x26ffc7ab0000001c 0x0137fe3d58000000 0xe7ffef9f00000000 0x7f3fff7cf8000000

def z1445 : W := mkw 0x25b0df590000000c 0x012d86fac8000000 0x0030ec1c00000000 0x00018760e0000000

def z1446 : W := mkw 0x234fd8fb0000001c 0x011a7ec7d8000000 0xa70ff07f00000000 0x25387f83f8000000

def z1447 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0x27f3ffff00000000 0x593f9ffff8000000

def z1448 : W := mkw 0x004540ab084404d8 0x88022a0558422026 0xe8cff3ff18c71ffd 0xf7467f9ff8c638ff

def z1449 : W := mkw 0x27ffdffbf5a1d81f 0x213ffeffdfad0ec0 0xfffffffffff9fc1f 0xffffffffffffcfe0

def z1450 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xfffff263ffff13ff 0xffffff931ffff89f

def z1451 : W := mkw 0x26efc0fb9400001e 0x01377e07dca00000 0xffffe07fff000007 0xbfffff03fff80000

def z1452 : W := mkw 0x804520a6bf5ffef2 0xbc02290535fafff7 0xf8cd13e3ffffffff 0xf7c6689f1fffffff

def z1453 : W := mkw 0x80002004bf5ffee2 0xbc00010025fafff7 0x18000000ffffffff 0x80c0000007ffffff

def z1454 : W := mkw 0x80002004021a2220 0x140001002010d111 0x20010003003e0268 0x210008001801f013

def z1455 : W := mkw 0x80002004031a7220 0x340001002018d391 0x00000000003ef278 0x000000000001f793

def z1456 : W := mkw 0x0000400900000008 0x0000020048000000 0x0002e01c00000000 0x00001700e0000000

def z1457 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xa8cd13e318c71ff5 0x5546689f18c638ff

def z1458 : W := mkw 0x01105f092101d808 0x200882f849080ec0 0x6033ff9f0001fc10 0x7b019ffcf8000fe0

def z1459 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x6033ee1f07fff3ff 0xfb019f70f83fff9f

def z1460 : W := mkw 0x27ffdffb0844001c 0x813ffeffd8422000 0xefffffff18c00001 0x7f7ffffff8c60000

def z1461 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xefffffff18c61fec 0x7f7ffffff8c630ff

def z1462 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xf73e1c7ce7f9e39f 0xffb9f0e3e73fcf1c

def z1463 : W := mkw 0x234fd8fb0000001c 0x011a7ec7d8000000 0x270fec7f00000000 0x29387f63f8000000

def z1464 : W := mkw 0x80002004031a7220 0x340001002018d391 0x40010000073ef27e 0xb20008000039f793

def z1465 : W := mkw 0x80002004b71bfa22 0x3400010025b8dfd1 0xf8c11383ff3ffe7f 0xf7c6089c1ff9fff3

def z1466 : W := mkw 0x87ba7f5df7bbfb2b 0x343dd3faefbddfd9 0x1732ec1ce738e002 0x08b99760e739c700

def z1467 : W := mkw 0x80002004971a7a22 0x3400010024b8d3d1 0x080000001f3efe7e 0x8040000000f9f7f3

def z1468 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0x87ffffff00000000 0x1c3ffffff8000000

def z1469 : W := mkw 0x27badffb0000001c 0x013dd6ffd8000000 0xe7f2ffff00000000 0x5f3f97fff8000000

def z1470 : W := mkw 0x80002004031a7220 0x340001002018d391 0x40020000073ef27e 0xaa0010000039f793

def z1471 : W := mkw 0x2fffdffbdce4001f 0xc17ffeffdee72000 0xffffffffffc00007 0xfffffffffffe0000

def z1472 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x603fee7f07fef3fe 0xfb01ff73f83ff79f

def z1473 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xdffff380fffe000f 0xfeffff9c07fff000

def z1474 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffffff0006000c 0xff3ffffff8003000

def z1475 : W := mkw 0x81555eff294df7f8 0xbc0aaaf7f94a6fbf 0xe8cd1fff18c7fffd 0xf74668fff8c63fff

def z1476 : W := mkw 0x8000200462bba321 0x140001002315dd19 0x10000000e0ffe3fb 0x808000000707ff1f

def z1477 : W := mkw 0x224fc0fb084404dc 0x89127e07d8422026 0x200fe07f00060060 0x21007f03f8003003

def z1478 : W := mkw 0x08452004feffa303 0xd042290027f7fd18 0xf8cd1060ffffe39f 0xf7c6688307ffff1c

def z1479 : W := mkw 0x01101e002101d000 0x200880f001080e80 0xdff01f80ff01fc17 0xdeff80fc07f80fe0

def z1480 : W := mkw 0x224fc0fb0000001c 0x01127e07d8000000 0xe0cfe07f00000000 0x37067f03f8000000

def z1481 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0x4733ec1c00000000 0x3a399f60e0000000

def z1482 : W := mkw 0x2fbadf59d4a0000f 0x417dd6facea50000 0x1732ec1ce0000000 0x08b99760e7000000

def z1483 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xe8cf13e318ff1fff 0xff46789f18c7f8ff

def z1484 : W := mkw 0x224fc0fb0000001c 0x01127e07d8000000 0x600fe27f0006127c 0xf3007f13f8003093

def z1485 : W := mkw 0x27ffdffbb501d81e 0x213ffeffdda80ec0 0xf7ffffffe701fc12 0x7fbfffffff380fe0

def z1486 : W := mkw 0x0eefa100def60803 0xc0777d0806f7b040 0xdfffe180fffe0c0f 0xbeffff0c07fff060

def z1487 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0x0732ff9c00000000 0x483997fce0000000

def z1488 : W := mkw 0x27ffdffbbc458cde 0x893ffeffdde22c66 0xfffffffff8c71ffd 0xffffffffffc638ff

def z1489 : W := mkw 0x04a0200096120002 0x0025010004b09000 0x1732e000e7380002 0x08b997000739c000

def z1490 : W := mkw 0x06ffc60908440008 0x8037fe3048422000 0xefffee1f18c6127d 0xff7fff70f8c63093

def z1491 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xffcf1ffff8ffffff 0xfffe78ffffc7ffff

def z1492 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xf70f1c7fe0ffe3fb 0xefb878e3ff07ff1f

def z1493 : W := mkw 0x84a02004971a7222 0x3425010024b8d391 0xdff00000ff3ef27f 0x9eff800007f9f793

def z1494 : W := mkw 0x224fc0fb0000001c 0x01127e07d8000000 0xe00ff07f00000000 0x67007f83f8000000

def z1495 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x1ff3e000fffe000f 0x98ff9f0007fff000

def z1496 : W := mkw 0x85b03f04b71bfa22 0x342d81f825b8dfd1 0x17300c00e73ef27e 0x88b980600739f793

def z1497 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0x7733e203e73e127e 0xfbb99f101f39f093

def z1498 : W := mkw 0x224fc0590000000c 0x01127e02c8000000 0x000fe01c00000000 0x20007f00e0000000

def z1499 : W := mkw 0x020a405900000008 0x00105202c8000000 0x200fe07f00000000 0x21007f03f8000000

def z1500 : W := mkw 0x81105faf2109fef8 0x3c0882fd79084ff7 0x20001fff0001fff0 0x410000fff8000fff

def z1501 : W := mkw 0x27ffdffb094454dc 0xa93ffeffd84a22a6 0xefffffff1fc7ffff 0xff7ffffff8fe3fff

def z1502 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xf70e0c7ce0f8e38b 0xafb87063e707c71c

def z1503 : W := mkw 0x80002004031a7220 0x340001002018d391 0x000000000738f272 0x000000000039c793

def z1504 : W := mkw 0x804520a66bfff7f1 0xbc022905335fffbf 0xf8cd13e3ffffffff 0xf7c6689f1fffffff

def z1505 : W := mkw 0x004500a2084404d0 0x8802280510422026 0xe8fd13e31fc71fff 0xff47e89f18fe38ff

def z1506 : W := mkw 0x07ef985008440000 0x803f7cc280422000 0xeffffc7c18c7039d 0xff7fffe3e0c6381c

def z1507 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xffce1dfcf8f9ef9b 0xeffe70efe7c7cf7c

def z1508 : W := mkw 0x27ffdffb40a0001d 0x013ffeffda050000 0xf7ffffffe0c00001 0x7fbfffffff060000

def z1509 : W := mkw 0x01105f0900000008 0x000882f848000000 0x6033ff9f00000000 0x7b019ffcf8000000

def z1510 : W := mkw 0x80002004031a7220 0x340001002018d391 0x60000000073ef27e 0xe30000000039f793

def z1511 : W := mkw 0x0eefa0a2def604d3 0xc8777d0516f7b026 0xfffff3e3fffe1c6f 0xffffff9f1ffff0e3

def z1512 : W := mkw 0x020a200042b20001 0x0010510002159000 0x1732e000e7380002 0x08b997000739c000

def z1513 : W := mkw 0x27ffdffbbd45dcde 0xa93ffeffddea2ee6 0xffffffffff07fc77 0xfffffffffff83fe3

def z1514 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xa7feffff00000000 0x4d3ff7fff8000000

def z1515 : W := mkw 0x26efc1fb0000001c 0x01377e0fd8000000 0x20cfe1ff00000000 0x21067f0ff8000000

def z1516 : W := mkw 0x05b05f0900000008 0x002d82f848000000 0xc7f2ff9c00000000 0x5e3f97fce0000000

def z1517 : W := mkw 0x27ffdffb0844001c 0x813ffeffd8422000 0xefffffff18c71c1d 0xff7ffffff8c638e0

def z1518 : W := mkw 0x26ffc7fb084404dc 0x8937fe3fd8422026 0x28ffe3ff18c61fec 0x3147ff1ff8c630ff

def z1519 : W := mkw 0x220ac0fb0000001c 0x01105607d8000000 0x2002e07f00000000 0x01001703f8000000

def z1520 : W := mkw 0x80002004031a7220 0x340001002018d391 0x40000c00073ef27e 0xca0000600039f793

def z1521 : W := mkw 0x224fc0fb0000001c 0x01127e07d8000000 0xe70fe07f00000000 0x2f387f03f8000000

def z1522 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0x6732ec1c00000000 0x6b399760e0000000

def z1523 : W := mkw 0x25b05ffb0000001c 0x012d82ffd8000000 0xe7f3ffff00000000 0x7f3f9ffff8000000

def z1524 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xefffffff18000c00 0x7f7ffffff8c00060

def z1525 : W := mkw 0x80002004031a7220 0x340001002018d391 0xc8c013801f3ffe7f 0xd646009c00f9fff3

def z1526 : W := mkw 0x2055c6ab0000001c 0x0102ae3558000000 0x6033ee1f00000000 0x7b019f70f8000000

def z1527 : W := mkw 0x27badffbb501d81e 0x213dd6ffdda80ec0 0x3732ffffe701fc12 0x49b997ffff380fe0

def z1528 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0x1733e000e73e0006 0x18b99f000739f000

def z1529 : W := mkw 0x27ffdffb000004dc 0x093ffeffd8000026 0xefffffff18011ff5 0xff7ffffff8c008ff

def z1530 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffffff00001270 0x7f3ffffff8000093

def z1531 : W := mkw 0x05b01f00b501d802 0x202d80f805a80ec0 0xfff01f83ff01fe77 0xdfff80fc1ff80ff3

def z1532 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xf70f1c7ce0ffe39f 0xffb878e3e707ff1c

def z1533 : W := mkw 0x25f5dffb0000001c 0x012faeffd8000000 0x60f3ffff00000000 0x7b079ffff8000000

def z1534 : W := mkw 0x27badf590000000c 0x013dd6fac8000000 0xc73eec1c00000000 0x2e39f760e0000000

def z1535 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xefffffff18c10f99 0xff7ffffff8c6087c

def z1536 : W := mkw 0x27ffdffb60a1801d 0x013ffeffdb050c00 0xf7ffffffe0f9e01b 0xffbfffffff07cf00

def z1537 : W := mkw 0x0effc609dce4000b 0xc077fe304ee72000 0xffffee1ff8c00001 0x7fffff70ffc60000

def z1538 : W := mkw 0x234fd8fb0000001c 0x011a7ec7d8000000 0x200ffc7f00000000 0x61007fe3f8000000

def z1539 : W := mkw 0x020a200042b20001 0x0010510002159000 0xd73ee000e7f8000b 0xaeb9f700073fc000

def z1540 : W := mkw 0x224fc0fb0000001c 0x01127e07d8000000 0xa0cff1ff00000000 0x25067f8ff8000000

def z1541 : W := mkw 0x27ffdffbf4a1891f 0x013ffeffdfa50c48 0xfffffffff8c10d81 0x7fffffffffc6086c

def z1542 : W := mkw 0x0db03f04fffffb03 0xf06d81f827ffffd8 0xdff01f80ffffff9f 0xdeff80fc07fffffc

def z1543 : W := mkw 0x27badffb0000001c 0x013dd6ffd8000000 0x2732ec7f00000000 0x09399763f8000000

def z1544 : W := mkw 0x2fffdffbfce5881f 0xc17ffeffdfe72c40 0xfffffffff8c10c01 0x7fffffffffc60860

def z1545 : W := mkw 0x804520a60a5e26f0 0x9c0229053052f137 0xe8cd13e318ff1ffd 0xf746689f18c7f8ff

def z1546 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x9fffe000fffe0007 0x1cffff0007fff000

def z1547 : W := mkw 0x0010460900000008 0x0000823048000000 0x4032ee1c00000000 0x5a019770e0000000

def z1548 : W := mkw 0x80002004021a2220 0x140001002010d111 0x00000000003ee27a 0x800000000001f713

def z1549 : W := mkw 0x88002004fffff323 0xf440010027ffff99 0x18000000fffff3ff 0x80c0000007ffff9f

def z1550 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0xefffffff18c61c6d 0xff7ffffff8c630e3

def z1551 : W := mkw 0x27ffdffb2945dcdc 0xa93ffeffd94a2ee6 0xefffffff18c7fffd 0xff7ffffff8c63fff

def z1552 : W := mkw 0x035f5efb00000018 0x001afaf7d8000000 0xe7ffffff00000000 0x7f3ffffff8000000

def z1553 : W := mkw 0x27ffdf59b501d80e 0x213ffefacda80ec0 0xdfffec1cff00e007 0xbeffff60e7f80700

def z1554 : W := mkw 0x27ffdffb2001811c 0x013ffeffd9000c08 0xe7ffffff00010180 0x7f3ffffff800080c

def z1555 : W := mkw 0x8010660d031a7228 0x340083306818d391 0x6833ee1f1f3ffe7f 0xfb419f70f8f9fff3

def z1556 : W := mkw 0x27badffbb501d81e 0x213dd6ffdda80ec0 0xfff2ffffff01fc17 0xdfff97fffff80fe0

def z1557 : W := mkw 0x27ffdffb2101d81c 0x213ffeffd9080ec0 0xf7ffffffe001fc13 0xffbfffffff000fe0

def z1558 : W := mkw 0x24f5c7fb0000001c 0x0127ae3fd8000000 0x20f1e3ff00000000 0x11078f1ff8000000

def z1559 : W := mkw 0x224fc0fb0000001c 0x01127e07d8000000 0x20cfe3ff00000000 0x31067f1ff8000000

def z1560 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xff0e1c7cf8f9ff9f 0xeff870e3e7c7cffc

def z1561 : W := mkw 0x80002004031a7220 0x340001002018d391 0x00000000073ee00e 0x800000000039f700

def z1562 : W := mkw 0x231adf590000000c 0x0118d6fac8000000 0x0002ec1c00000000 0x00001760e0000000

def z1563 : W := mkw 0x224fc0fb0000001c 0x01127e07d8000000 0x200ff3ff00000000 0x61007f9ff8000000

def z1564 : W := mkw 0x81105e5d2109f328 0x340882f2e9084f99 0x20001c7c0001e390 0x410000e3e0000f1c

def z1565 : W := mkw 0x25f5dffb084404dc 0x892faeffd8422026 0x28f1ffff18071ff4 0x51478ffff8c038ff

def z1566 : W := mkw 0x0eefa000def604c3 0xc8777d0006f7b026 0xfffff060ffff1fff 0xffffff8307fff8ff

def z1567 : W := mkw 0x8000200463bbf321 0x34000100231ddf99 0x10000000e73ef27e 0x808000000739f793

def z1568 : W := mkw 0x00104609084404c8 0x8800823048422026 0x6833ee1f18c71ffd 0xfb419f70f8c638ff

def z1569 : W := mkw 0x8010660d031a7228 0x340083306818d391 0xf733ee1fe73ef27f 0xffb99f70ff39f793

def z1570 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xb70e1c7ce0f9e399 0x65b870e3e707cf1c

def z1571 : W := mkw 0x80002004021a2220 0x140001002010d111 0x60010203003e127c 0xf30008101801f093

def z1572 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x9fffe000fffe000d 0x34ffff0007fff000

def z1573 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xa7fff3ff00000000 0x353fff9ff8000000

def z1574 : W := mkw 0x004540ab00000018 0x00022a0558000000 0x200fe07f00000000 0x21007f03f8000000

def z1575 : W := mkw 0x27ffdffbb501d81e 0x213ffeffdda80ec0 0xf7ffffffe700f016 0xffbfffffff380780

def z1576 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xf7ce1ffce0f9e39b 0xffbe70ffe707cf1c

def z1577 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xa7fffdff00000000 0x2d3fffeff8000000

def z1578 : W := mkw 0x2fffdffb9c44001e 0xc17ffeffdce22000 0xefffffff18000000 0x7f7ffffff8c00000

def z1579 : W := mkw 0x200040fb0000001c 0x01000207d8000000 0x2003e07f00000000 0x21001f03f8000000

def z1580 : W := mkw 0x27ffdffb60a1811d 0x013ffeffdb050c08 0xf7ffffffe0f9018b 0xffbfffffff07c80c

def z1581 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xf70e1e7fe0f9f3fb 0xefb870f3ff07cf9f

def z1582 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xc7f3ff9f00000000 0x5e3f9ffcf8000000

def z1583 : W := mkw 0x27ffdffb2001801c 0x013ffeffd9000c00 0xfffffffff801fc17 0xffffffffffc00fe0

def z1584 : W := mkw 0x26bac7590000000c 0x0135d63ac8000000 0x0032e01c00000000 0x00019700e0000000

def z1585 : W := mkw 0x0eefa0a2def60013 0xc0777d0516f7b000 0xdfffe383fffe000f 0xbeffff1c1ffff000

def z1586 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0x27ffefff00000000 0x393fff7ff8000000

def z1587 : W := mkw 0x25f5dffbb501d81e 0x212faeffdda80ec0 0xfff1ffffff01fc17 0xdfff8ffffff80fe0

def z1588 : W := mkw 0x27badf5960a1810d 0x013dd6facb050c08 0x1732ec1ce0000000 0x08b99760e7000000

def z1589 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xffffe003fffe026f 0xbfffff001ffff013

def z1590 : W := mkw 0x0eaaa000def60003 0xc075550006f7b000 0x5f33e000fffe000f 0xbaf99f0007fff000

def z1591 : W := mkw 0x0fffff09fff7d80b 0xe07ffff84fffbec0 0xffffff9ffffffc1f 0xfffffffcffffffe0

def z1592 : W := mkw 0x034f985000000000 0x001a7cc280000000 0xe70ffc7c00000000 0x6f387fe3e0000000

def z1593 : W := mkw 0x0eaaa000d6b20003 0x4075550006b59000 0x173ee000e7f8000a 0x28b9f700073fc000

def z1594 : W := mkw 0x0eefa0a2def60013 0xc0777d0516f7b000 0xdffff1e0fffe000f 0xbeffff8f07fff000

def z1595 : W := mkw 0x27efd9fb084404dc 0x893f7ecfd8422026 0xafcff1ff18c70fe9 0x257e7f8ff8c6387f

def z1596 : W := mkw 0x824f60ff4afe27f9 0x9c127b07fa57f13f 0x200fe07f00fe03e8 0x21007f03f807f01f

def z1597 : W := mkw 0x0010460900000008 0x0000823048000000 0xe8f3ff9f18011c15 0xff479ffcf8c008e0

def z1598 : W := mkw 0x81105f0d2109fa28 0x340882f869084fd1 0x00000c1c0000e000 0x00000060e0000700

def z1599 : W := mkw 0x04b0470900000008 0x0025823848000000 0x60f3ef9f00000000 0x7b079f7cf8000000

def z1600 : W := mkw 0x27ffdffb2101d01c 0x213ffeffd9080e80 0xf7ffffffe701f017 0xffbfffffff380f80

def z1601 : W := mkw 0x2fffdffbdce4001f 0xc17ffeffdee72000 0xfffffffff8f8000b 0xffffffffffc7c000

def z1602 : W := mkw 0x27ffdffb2001881c 0x013ffeffd9000c40 0xe7ffffff00010c00 0x7f3ffffff8000860

def z1603 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x1fffe000fffe000e 0x38ffff0007fff000

def z1604 : W := mkw 0x06ffc6099500500a 0x2037fe304ca80280 0xffffee1fff00f017 0xffffff70fff80780

def z1605 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0xfffff060fffe000f 0xffffff8307fff000

def z1606 : W := mkw 0x08002004feffa303 0xd040010027f7fd18 0x18000000fffee00f 0x80c0000007fff700

def z1607 : W := mkw 0x25b05ffbb501d81e 0x212d82ffdda80ec0 0xfff3ffffff01fc17 0xffff9ffffff80fe0

def z1608 : W := mkw 0x27efd9fb0000001c 0x013f7ecfd8000000 0x87cef1fc00000000 0x043e778fe0000000

def z1609 : W := mkw 0x27ffdffbbc458cde 0x893ffeffdde22c66 0xfffffffff8c10d81 0x7fffffffffc6086c

def z1610 : W := mkw 0x05b05f0900000008 0x002d82f848000000 0xeff3ff9f18071e7d 0xff7f9ffcf8c038f3

def z1611 : W := mkw 0x27badf599500580e 0x213dd6facca802c0 0x0732ec1c07000000 0x08399760e0380000

def z1612 : W := mkw 0x224fc0fb0000001c 0x01127e07d8000000 0x600fec7f00000000 0x6b007f63f8000000

def z1613 : W := mkw 0x224fc0fb0000001c 0x01127e07d8000000 0xe00ff07f00c10399 0xe7007f83f806081c

def z1614 : W := mkw 0x004500a2084404d0 0x8802280510422026 0x000c006000c603e8 0x000060030006301f

def z1615 : W := mkw 0x00104609b501d80a 0x200082304da80ec0 0x7833ee1fff01fc17 0xfbc19f70fff80fe0

def z1616 : W := mkw 0x0eefa000def60003 0xc0777d0006f7b000 0x173ee000e7f80002 0x08b9f700073fc000

def z1617 : W := mkw 0x27ffdffbb501d81e 0x213ffeffdda80ec0 0xffffffffff00e007 0xfffffffffff80700

def z1618 : W := mkw 0x0fefb854feffa303 0xd07f7dc2a7f7fd18 0x9fcc1060ffffe39f 0x84fe608307ffff1c

def z1619 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xe7ffec7f00000000 0x3f3fff63f8000000

def z1620 : W := mkw 0x27ffdffb9400081e 0x013ffeffdca00040 0xefffffff18000c00 0x7f7ffffff8c00060

def z1621 : W := mkw 0x05b01f50b501d902 0x202d80fa85a80ec8 0xdff01fe0ff01fd97 0xdeff80ff07f80fec

def z1622 : W := mkw 0x27ffdffb0000001c 0x013ffeffd8000000 0xa7fdffff00000000 0x553feffff8000000

def z1623 : W := mkw 0x27ffdffb084404dc 0x893ffeffd8422026 0x0ff3ef9f18061c64 0x187f9f7cf8c030e3

def z1624 : W := mkw 0x030a185460a9a301 0x101850c2a3054d18 0xf70e1e7ce0f9f39f 0xffb870f3e707cf9c

def z1625 : W := mkw 0x85b03f04b71bfa22 0x342d81f825b8dfd1 0xdff01f80ff39fc17 0xdeff80fc07f9cfe0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z7,z4,z6,z8]),(0,[z0,z9,z1,z2,z3,z10,z6])],[(1,[z0,z1,z2,z3,z11,z6]),(1,[z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z13,z6,z14])],[(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z15]),(0,[z16,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z17,z6]),(0,[z0,z1,z2,z3,z4,z18,z6])],[(0,[z0,z1,z2,z7,z3,z10,z6]),(0,[z0,z1,z19,z2,z3,z20,z6]),(0,[z0,z21,z1,z2,z4,z6,z22]),(0,[z23,z0,z24,z1,z2,z4,z6]),(0,[z23,z25,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z12,z26,z4,z6]),(0,[z0,z1,z2,z27,z3,z4,z6]),(0,[z0,z1,z2,z28,z3,z10,z6]),(0,[z0,z1,z2,z29,z3,z10,z6]),(0,[z0,z30,z1,z2,z3,z4,z6]),(0,[z25,z0,z1,z31,z2,z3,z6])],[(0,[z0,z32,z1,z2,z3,z33,z6]),(0,[z34,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z35,z3,z36,z6]),(0,[z0,z1,z2,z3,z37,z4,z6]),(0,[z0,z1,z2,z3,z38,z4,z6]),(0,[z0,z1,z39,z3,z4,z40,z6]),(0,[z0,z41,z1,z2,z3,z4,z6])],[(0,[z42,z0,z1,z2,z3,z4,z6]),(0,[z0,z43,z1,z2,z3,z10,z6]),(0,[z0,z44,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z3,z4,z45,z6]),(1,[z0,z1,z2,z3,z46,z6]),(0,[z0,z1,z47,z2,z3,z4,z6]),(0,[z48,z0,z1,z49,z3,z4,z6])],[],[(0,[z50,z51,z1,z2,z3,z4,z6]),(0,[z51,z0,z1,z2,z3,z13,z6]),(0,[z0,z1,z2,z3,z52,z53,z6])],[(0,[z0,z1,z2,z54,z3,z4,z6]),(0,[z50,z1,z2,z35,z3,z4,z6]),(0,[z0,z1,z2,z3,z12,z4,z6]),(0,[z0,z1,z2,z3,z10,z13,z6]),(0,[z0,z1,z2,z3,z55,z4,z6])],[(1,[z0,z1,z2,z3,z56,z6]),(0,[z0,z57,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z58,z4,z6])],[(0,[z0,z30,z1,z2,z12,z4,z6]),(0,[z59,z1,z2,z3,z4,z6,z60]),(0,[z0,z1,z2,z3,z52,z61,z6])],[(0,[z0,z1,z2,z3,z62,z4,z6]),(0,[z0,z1,z63,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z64]),(0,[z48,z0,z1,z2,z3,z52,z6])],[(0,[z25,z65,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z36,z45,z6])],[(0,[z0,z1,z2,z35,z3,z10,z6]),(0,[z0,z1,z2,z3,z66,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z67,z6]),(0,[z59,z0,z1,z2,z3,z52,z6])],[],[(0,[z0,z68,z1,z2,z3,z4,z6]),(0,[z0,z1,z49,z35,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z69,z6]),(0,[z0,z30,z1,z2,z3,z46,z6])],[(0,[z0,z1,z2,z3,z4,z70,z6]),(0,[z0,z1,z71,z3,z4,z6,z72]),(0,[z0,z73,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z29,z3,z4,z6]),(0,[z74,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z10,z6,z75]),(0,[z0,z1,z76,z2,z3,z36,z6])],[(0,[z0,z1,z2,z3,z77,z4,z6]),(0,[z0,z1,z49,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z78])],[(0,[z0,z1,z2,z3,z4,z6,z79]),(0,[z0,z1,z2,z3,z4,z6,z80])],[(0,[z0,z1,z2,z3,z81,z4,z6]),(1,[z0,z1,z2,z3,z82,z6]),(1,[z0,z1,z2,z3,z52,z6])],[(0,[z0,z1,z2,z3,z4,z83,z6]),(0,[z0,z1,z2,z84,z3,z4,z6]),(0,[z85,z0,z1,z2,z3,z10,z6]),(0,[z0,z1,z19,z2,z3,z86,z6]),(0,[z87,z0,z1,z2,z3,z4,z6]),(0,[z0,z88,z1,z2,z3,z36,z6]),(0,[z0,z1,z2,z3,z4,z89,z6])],[(0,[z0,z90,z2,z91,z3,z4,z6]),(1,[z0,z1,z2,z92,z4,z6]),(0,[z0,z1,z2,z3,z10,z93,z6]),(0,[z94,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z95,z12,z4,z6]),(1,[z0,z1,z2,z3,z96,z6])],[(0,[z0,z1,z2,z97,z3,z10,z6]),(0,[z0,z1,z2,z3,z4,z98,z6])],[(0,[z0,z1,z2,z3,z36,z6,z99])],[(0,[z0,z1,z2,z91,z3,z52,z6]),(0,[z0,z1,z2,z3,z100,z4,z6]),(0,[z0,z88,z1,z2,z4,z93,z6]),(0,[z0,z1,z2,z3,z101,z4,z6]),(0,[z23,z0,z1,z2,z3,z52,z6])],[(0,[z102,z0,z1,z2,z103,z4,z6]),(0,[z0,z1,z2,z3,z104,z10,z6]),(0,[z105,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z53,z6]),(0,[z0,z1,z2,z3,z36,z6,z106])],[(0,[z107,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z4,z6,z60]),(1,[z0,z1,z2,z12,z52,z6]),(0,[z108,z0,z1,z2,z3,z40,z6])]],
   [[(0,[z0,z1,z2,z109,z3,z4,z6])],[(0,[z0,z88,z1,z2,z3,z10,z6]),(0,[z0,z1,z110,z2,z4,z93,z6]),(0,[z48,z0,z1,z2,z3,z40,z6]),(0,[z0,z1,z2,z3,z111,z4,z6])],[(0,[z0,z1,z112,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z92,z4,z6]),(0,[z0,z1,z2,z113,z3,z4,z6]),(0,[z0,z30,z1,z2,z3,z52,z6])],[(0,[z107,z25,z0,z1,z2,z3,z6]),(0,[z0,z114,z1,z2,z7,z4,z6])],[],[(0,[z115,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z40,z36,z6])],[(0,[z48,z0,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z13,z116,z6]),(0,[z0,z1,z117,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z118,z6]),(0,[z107,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z7,z4,z6,z106])],[(0,[z0,z1,z35,z91,z3,z4,z6]),(0,[z0,z1,z2,z3,z12,z52,z6]),(0,[z0,z1,z2,z119,z3,z120,z6]),(0,[z0,z1,z2,z121,z3,z4,z6])],[(0,[z0,z122,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z123,z10,z6]),(1,[z0,z124,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z125,z4,z6]),(0,[z0,z1,z2,z126,z3,z52,z6])],[(0,[z127,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z97,z3,z4,z6]),(0,[z0,z1,z2,z3,z52,z6,z72]),(0,[z0,z1,z2,z3,z4,z36,z6])],[(0,[z50,z0,z1,z2,z3,z36,z6]),(0,[z0,z1,z2,z3,z128,z6,z60]),(1,[z0,z1,z2,z3,z40,z6]),(0,[z0,z129,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z130])],[(0,[z0,z1,z2,z12,z4,z131,z6])],[(0,[z0,z1,z132,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z104,z4,z6])],[(0,[z127,z25,z0,z1,z2,z3,z6]),(0,[z0,z133,z1,z2,z3,z4,z6])],[(0,[z0,z1,z134,z2,z12,z4,z6]),(1,[z0,z1,z2,z4,z6,z135]),(0,[z25,z0,z136,z1,z2,z3,z6])]],
   [[(0,[z137,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z7,z3,z52,z6]),(0,[z0,z1,z2,z138,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z139])],[(0,[z0,z1,z2,z29,z3,z52,z6]),(0,[z0,z1,z2,z140,z3,z4,z6])],[(0,[z127,z0,z1,z2,z3,z11,z6]),(0,[z127,z0,z1,z2,z12,z4,z6])],[(0,[z25,z0,z44,z1,z2,z3,z6]),(0,[z0,z1,z49,z2,z3,z52,z6])],[(0,[z50,z0,z1,z2,z3,z10,z6]),(1,[z59,z1,z2,z3,z4,z60])],[(0,[z0,z141,z90,z2,z3,z4,z6]),(0,[z142,z0,z1,z2,z3,z13,z6]),(1,[z0,z1,z2,z3,z143,z6]),(0,[z59,z0,z1,z2,z144,z4,z6])],[(0,[z0,z30,z1,z2,z3,z40,z6]),(0,[z0,z1,z2,z4,z6,z135,z72]),(0,[z0,z1,z2,z3,z145,z4,z6])],[(0,[z0,z1,z2,z7,z146,z4,z6]),(0,[z0,z147,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z93,z6,z8]),(0,[z25,z0,z148,z1,z2,z3,z6]),(0,[z0,z148,z1,z2,z3,z4,z6]),(0,[z0,z149,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z150,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z135])],[(1,[z0,z1,z2,z54,z4,z6]),(0,[z0,z1,z2,z12,z4,z6,z22])],[(0,[z0,z1,z19,z2,z3,z10,z6])],[(0,[z0,z30,z1,z2,z7,z4,z6]),(1,[z0,z1,z2,z119,z3,z6]),(0,[z0,z1,z2,z3,z100,z52,z6]),(0,[z25,z0,z1,z2,z3,z6,z72])],[(0,[z127,z0,z1,z2,z3,z56,z6]),(1,[z0,z1,z2,z144,z4,z6]),(0,[z0,z1,z2,z3,z4,z151,z6]),(0,[z0,z152,z1,z2,z3,z4,z6]),(0,[z0,z153,z1,z2,z3,z4,z6]),(0,[z25,z0,z1,z110,z2,z3,z6])],[(0,[z0,z1,z2,z3,z4,z6,z154]),(0,[z59,z0,z1,z2,z12,z4,z6]),(0,[z107,z0,z1,z2,z3,z52,z6]),(0,[z0,z1,z2,z3,z155,z10,z6]),(0,[z0,z1,z2,z3,z156,z4,z6]),(0,[z0,z1,z2,z157,z3,z4,z6])],[(0,[z0,z1,z90,z2,z3,z4,z6]),(0,[z0,z1,z71,z2,z3,z13,z6]),(0,[z158,z0,z2,z3,z159,z4,z6]),(0,[z0,z1,z2,z3,z26,z36,z6]),(0,[z0,z160,z1,z2,z3,z4,z6])],[(0,[z23,z0,z88,z1,z2,z4,z6])]],
   [[(0,[z161,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z52,z162,z6])],[(0,[z0,z1,z2,z12,z4,z163,z6]),(0,[z164,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z165,z6]),(0,[z0,z1,z2,z3,z66,z40,z6]),(0,[z25,z0,z1,z2,z126,z3,z6])],[],[(0,[z166,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z167]),(0,[z0,z1,z2,z3,z4,z168,z6]),(0,[z0,z1,z2,z169,z3,z13,z6]),(0,[z0,z170,z1,z2,z3,z4,z6]),(1,[z0,z44,z2,z3,z61,z6]),(1,[z0,z1,z49,z3,z40,z6])],[(0,[z171,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z172])],[(0,[z0,z1,z2,z3,z56,z4,z6]),(1,[z25,z0,z1,z2,z7,z6]),(0,[z0,z1,z2,z173,z3,z4,z6])],[(0,[z0,z1,z90,z2,z12,z4,z6]),(0,[z0,z1,z19,z35,z3,z4,z6]),(0,[z0,z1,z174,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z175]),(0,[z0,z1,z2,z3,z176,z4,z6])],[(0,[z0,z1,z2,z3,z118,z4,z6]),(0,[z0,z1,z2,z3,z26,z10,z6]),(0,[z0,z1,z49,z2,z3,z40,z6]),(0,[z0,z1,z2,z177,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z178]),(0,[z0,z1,z2,z179,z3,z36,z6])],[(0,[z127,z0,z1,z2,z3,z52,z6]),(0,[z180,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z181,z6]),(0,[z0,z1,z182,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z120,z13,z6]),(0,[z1,z2,z3,z4,z45,z6,z60]),(0,[z0,z1,z19,z2,z3,z4,z6])],[(0,[z0,z1,z183,z2,z3,z4,z6]),(0,[z0,z1,z2,z91,z12,z4,z6]),(0,[z23,z0,z1,z2,z12,z4,z6]),(0,[z0,z184,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z185,z3,z4,z6])],[(0,[z0,z1,z2,z3,z186,z4,z6]),(0,[z0,z1,z2,z3,z104,z52,z6])],[(0,[z0,z1,z2,z187,z7,z4,z6]),(0,[z0,z1,z49,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z188,z4,z6]),(0,[z0,z43,z1,z2,z3,z4,z22]),(0,[z0,z24,z1,z2,z26,z4,z6])],[(0,[z0,z1,z2,z189,z3,z4,z6])],[(0,[z0,z1,z2,z190,z3,z4,z6]),(1,[z0,z1,z2,z7,z52,z6]),(0,[z0,z1,z2,z3,z4,z6,z191]),(0,[z0,z1,z2,z126,z3,z4,z6]),(0,[z0,z1,z192,z2,z3,z4,z6])],[(0,[z0,z1,z2,z27,z12,z4,z6])]],
   [[(1,[z0,z32,z91,z3,z4,z6])],[(0,[z107,z0,z1,z2,z3,z40,z6]),(0,[z193,z0,z1,z2,z3,z4,z6]),(0,[z0,z43,z2,z3,z4,z163,z6])],[(0,[z0,z9,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z194,z3,z120,z6])],[(0,[z0,z1,z2,z3,z4,z6,z195]),(0,[z25,z0,z1,z2,z3,z93,z6])],[(0,[z196,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z197,z13,z6]),(0,[z0,z1,z2,z3,z4,z86,z6]),(1,[z0,z1,z2,z3,z198,z6]),(0,[z199,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z7,z3,z4,z6]),(0,[z0,z1,z2,z3,z13,z6,z106]),(0,[z0,z1,z2,z3,z10,z116,z6]),(0,[z200,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z201,z6]),(0,[z0,z202,z1,z2,z3,z4,z6])],[(0,[z0,z57,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z126,z12,z4,z6]),(0,[z107,z0,z1,z2,z7,z4,z6]),(0,[z0,z203,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z28,z3,z4,z6]),(0,[z0,z1,z2,z3,z150,z52,z6]),(0,[z0,z1,z2,z3,z204,z6,z72])],[(0,[z0,z30,z2,z3,z120,z4,z6]),(0,[z0,z1,z2,z3,z4,z205,z6])],[],[(0,[z0,z206,z1,z2,z3,z4,z6]),(0,[z207,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z208,z2,z3,z13,z6]),(0,[z0,z44,z1,z2,z3,z4,z6]),(0,[z0,z43,z1,z2,z3,z4,z6]),(0,[z209,z0,z1,z2,z3,z40,z6])],[(0,[z0,z1,z2,z7,z4,z45,z6]),(0,[z210,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z211,z6]),(0,[z0,z1,z2,z121,z3,z40,z6]),(0,[z0,z1,z2,z3,z4,z6,z212])],[(0,[z0,z1,z213,z2,z3,z4,z6])],[(0,[z127,z0,z1,z2,z3,z40,z6]),(0,[z0,z1,z90,z2,z3,z52,z6]),(0,[z102,z0,z1,z2,z3,z36,z6]),(1,[z0,z1,z2,z3,z33,z6])],[(0,[z214,z0,z1,z2,z3,z215,z6]),(0,[z0,z1,z2,z216,z3,z4,z6]),(0,[z0,z1,z2,z7,z12,z4,z6]),(0,[z0,z1,z2,z3,z10,z6,z8]),(0,[z0,z1,z2,z3,z217,z4,z6])],[(0,[z0,z1,z2,z29,z12,z4,z6]),(0,[z0,z1,z2,z3,z198,z218,z6])],[(0,[z0,z1,z110,z2,z3,z36,z6]),(0,[z219,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z220,z3,z221,z6])]],
   [[(0,[z0,z1,z49,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z159,z13,z6]),(0,[z0,z1,z2,z3,z222,z4,z6]),(0,[z0,z1,z2,z3,z223,z36,z6])],[(0,[z127,z0,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z35,z3,z4,z6]),(0,[z0,z43,z1,z2,z12,z4,z6]),(1,[z0,z1,z2,z224,z3,z6])],[(0,[z0,z1,z2,z7,z66,z4,z6]),(0,[z171,z0,z1,z2,z3,z52,z6]),(0,[z0,z225,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z12,z226,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z227]),(0,[z158,z0,z1,z2,z126,z3,z6])],[(1,[z0,z1,z2,z3,z4,z70]),(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z0,z1,z228,z2,z3,z4,z6]),(0,[z0,z229,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z230])],[(0,[z214,z0,z1,z2,z3,z13,z6]),(0,[z0,z231,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z4,z40,z6]),(0,[z0,z1,z2,z3,z232,z4,z6]),(0,[z233,z0,z1,z2,z3,z36,z6]),(0,[z102,z0,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z3,z234,z4,z6]),(0,[z0,z1,z2,z3,z235,z4,z6]),(0,[z48,z0,z1,z2,z3,z4,z72])],[(0,[z127,z0,z236,z2,z3,z4,z6]),(0,[z158,z0,z1,z2,z3,z13,z6]),(0,[z0,z1,z2,z3,z52,z222,z6])],[(0,[z214,z236,z1,z2,z3,z4,z6]),(0,[z59,z0,z1,z2,z3,z40,z6]),(0,[z0,z1,z19,z2,z3,z52,z6]),(0,[z0,z1,z2,z3,z4,z237,z6]),(0,[z0,z238,z1,z2,z3,z4,z6])],[(0,[z0,z1,z110,z2,z3,z10,z6])],[(0,[z0,z1,z2,z35,z12,z4,z6]),(0,[z239,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z240,z3,z4,z6]),(0,[z85,z0,z1,z2,z3,z4,z6]),(0,[z241,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z7,z4,z83,z6]),(0,[z242,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z243,z2,z3,z4,z6]),(0,[z59,z0,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z40,z6,z60]),(0,[z0,z1,z2,z244,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z245])],[(0,[z0,z1,z2,z3,z4,z6,z246])],[(0,[z0,z1,z2,z3,z4,z247,z6]),(0,[z25,z0,z30,z1,z2,z3,z6]),(0,[z0,z1,z2,z248,z3,z4,z6])],[(0,[z51,z0,z1,z2,z249,z4,z6]),(0,[z250,z0,z1,z3,z4,z6,z72]),(0,[z242,z25,z0,z1,z2,z3,z6]),(0,[z0,z1,z76,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z90,z2,z3,z40,z6]),(0,[z65,z0,z1,z2,z3,z13,z6]),(1,[z0,z251,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z252]),(0,[z0,z253,z1,z2,z3,z4,z6]),(1,[z0,z1,z39,z3,z40,z6]),(0,[z254,z0,z1,z2,z3,z4,z6])],[(0,[z51,z0,z1,z2,z3,z255,z6]),(0,[z256,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z13,z6,z8]),(0,[z0,z257,z1,z2,z3,z4,z6]),(0,[z258,z0,z1,z2,z3,z4,z6])],[(0,[z259,z0,z1,z2,z3,z4,z6]),(0,[z260,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z110,z2,z29,z4,z6])],[(0,[z261,z0,z1,z2,z3,z4,z6]),(0,[z1,z2,z7,z3,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z262,z6]),(0,[z0,z88,z1,z2,z3,z4,z6])],[(0,[z0,z122,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z10,z45,z6]),(0,[z0,z1,z2,z91,z3,z40,z6]),(0,[z0,z1,z2,z28,z3,z52,z6]),(0,[z0,z263,z1,z2,z3,z4,z6]),(0,[z23,z0,z1,z2,z3,z40,z6]),(0,[z0,z1,z2,z3,z36,z36,z6])],[(0,[z0,z1,z90,z2,z7,z4,z6])],[(1,[z0,z1,z2,z12,z40,z6]),(0,[z0,z264,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z52,z13,z6]),(0,[z0,z1,z2,z265,z3,z4,z6]),(0,[z0,z1,z132,z2,z3,z6,z22]),(0,[z0,z1,z2,z220,z3,z36,z6]),(1,[z0,z136,z1,z2,z3,z6]),(0,[z0,z136,z1,z2,z3,z4,z6])],[(0,[z0,z32,z1,z2,z3,z13,z6]),(0,[z0,z44,z1,z2,z3,z52,z6]),(0,[z0,z43,z1,z2,z3,z52,z6])],[(1,[z0,z1,z266,z3,z4,z6]),(0,[z25,z0,z43,z1,z2,z3,z6]),(1,[z258,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z91,z7,z4,z6]),(0,[z23,z0,z1,z2,z7,z4,z6])],[(0,[z260,z0,z1,z2,z12,z4,z6])],[(0,[z0,z1,z2,z3,z123,z4,z6]),(0,[z0,z88,z1,z2,z12,z4,z6]),(0,[z267,z0,z1,z2,z3,z4,z45]),(0,[z268,z0,z1,z2,z3,z4,z6]),(0,[z0,z269,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z220,z4,z93,z6])],[(0,[z0,z1,z2,z12,z4,z218,z6]),(0,[z25,z0,z141,z1,z2,z3,z6]),(1,[z0,z1,z2,z126,z116,z6])],[(1,[z0,z1,z2,z270,z4,z6]),(0,[z0,z1,z2,z7,z4,z36,z6]),(0,[z0,z1,z2,z271,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z45,z72]),(0,[z0,z1,z2,z272,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z273,z6])],[(0,[z0,z1,z2,z35,z3,z52,z6]),(0,[z51,z0,z1,z2,z274,z4,z6]),(0,[z0,z1,z2,z3,z12,z40,z6]),(0,[z0,z1,z2,z3,z143,z4,z6]),(0,[z0,z1,z2,z220,z3,z10,z6]),(0,[z0,z1,z2,z3,z4,z6,z275])]],
   [[(0,[z0,z1,z2,z7,z104,z4,z6]),(0,[z0,z1,z2,z126,z3,z40,z6]),(0,[z0,z1,z276,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z13,z5,z6]),(0,[z0,z1,z2,z3,z277,z4,z6]),(0,[z0,z1,z2,z3,z278,z4,z6])],[(0,[z0,z1,z2,z2,z3,z52,z6]),(0,[z25,z0,z1,z2,z173,z3,z6]),(0,[z279,z0,z1,z2,z3,z36,z6])],[(1,[z0,z1,z2,z280,z4,z6]),(0,[z50,z0,z1,z35,z3,z4,z6]),(0,[z0,z141,z19,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z281]),(0,[z0,z1,z2,z3,z282,z4,z6])],[(0,[z0,z1,z2,z3,z10,z6,z106]),(0,[z0,z1,z2,z3,z10,z66,z6]),(0,[z283,z0,z1,z2,z3,z45,z6]),(0,[z0,z1,z2,z284,z3,z4,z6])],[(0,[z50,z0,z285,z2,z3,z4,z6]),(0,[z0,z1,z2,z126,z7,z4,z6]),(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z0,z1,z2,z3,z52,z93,z6])],[(0,[z0,z1,z2,z3,z270,z4,z6]),(0,[z50,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z40,z6,z22]),(0,[z0,z1,z286,z2,z3,z4,z6]),(0,[z25,z0,z1,z2,z287,z3,z6])],[(0,[z0,z1,z2,z7,z3,z40,z6]),(0,[z25,z0,z1,z2,z3,z13,z6]),(0,[z288,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z13,z45,z6]),(0,[z0,z1,z39,z2,z3,z13,z6]),(0,[z0,z1,z2,z3,z4,z289,z6]),(0,[z0,z1,z2,z29,z3,z40,z6])],[(0,[z0,z236,z1,z2,z3,z13,z6]),(0,[z290,z0,z1,z2,z3,z4,z6]),(0,[z25,z0,z1,z2,z3,z120,z6]),(1,[z23,z0,z1,z2,z4,z8])],[(0,[z50,z25,z0,z1,z2,z3,z6]),(0,[z0,z24,z1,z2,z3,z13,z6]),(0,[z291,z0,z1,z2,z3,z4,z6])],[(0,[z279,z0,z1,z2,z3,z10,z6]),(0,[z0,z0,z1,z2,z3,z10,z6]),(0,[z0,z43,z1,z2,z3,z40,z6]),(0,[z0,z1,z49,z2,z3,z4,z72])],[(0,[z0,z1,z2,z3,z280,z4,z6]),(1,[z0,z1,z2,z3,z292,z6]),(0,[z0,z1,z2,z7,z7,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z293])],[(0,[z0,z1,z2,z3,z4,z11,z6]),(0,[z0,z1,z2,z29,z7,z4,z6]),(0,[z0,z1,z2,z3,z4,z294,z6]),(0,[z0,z88,z30,z2,z3,z4,z6]),(0,[z0,z1,z2,z224,z3,z6,z8]),(1,[z0,z1,z2,z3,z6,z295])],[(0,[z50,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z296,z4,z6])],[(0,[z0,z297,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z155,z4,z6]),(0,[z59,z267,z1,z2,z3,z4,z6]),(0,[z298,z0,z1,z2,z3,z4,z6]),(0,[z25,z0,z1,z2,z3,z116,z6])]],
   [[(0,[z25,z0,z236,z1,z2,z3,z6]),(0,[z25,z0,z1,z2,z3,z12,z6]),(0,[z0,z43,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z299,z4,z6])],[(0,[z0,z1,z300,z2,z3,z4,z6]),(0,[z0,z88,z1,z2,z3,z52,z6])],[],[(0,[z0,z1,z2,z35,z3,z40,z6]),(0,[z0,z1,z301,z2,z3,z4,z6]),(0,[z0,z1,z302,z2,z3,z4,z6]),(0,[z267,z0,z1,z2,z3,z277,z6])],[(0,[z0,z1,z19,z2,z12,z4,z6]),(0,[z0,z303,z1,z2,z3,z13,z6]),(0,[z25,z0,z1,z2,z3,z26,z6])],[(0,[z127,z0,z1,z2,z3,z4,z70]),(0,[z0,z43,z236,z2,z3,z4,z6]),(0,[z304,z0,z1,z2,z3,z4,z6]),(0,[z0,z305,z1,z2,z3,z4,z6]),(0,[z0,z1,z110,z2,z3,z52,z6]),(0,[z0,z1,z2,z3,z4,z6,z306])],[(0,[z0,z1,z2,z307,z3,z4,z6]),(0,[z308,z0,z1,z2,z3,z4,z6]),(0,[z25,z0,z1,z2,z29,z3,z6]),(0,[z0,z1,z2,z2,z3,z40,z6])],[(0,[z309,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z217,z6]),(0,[z0,z1,z2,z3,z310,z4,z6])],[(0,[z0,z1,z2,z35,z7,z4,z6]),(0,[z311,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z312,z3,z4,z6]),(0,[z0,z1,z313,z2,z3,z4,z6])],[(0,[z0,z1,z314,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z315]),(0,[z0,z1,z2,z3,z26,z4,z6])],[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z167,z6]),(0,[z250,z0,z1,z2,z3,z13,z6])],[(0,[z0,z1,z2,z12,z4,z316,z6])],[(1,[z0,z1,z2,z3,z6,z317])],[(0,[z267,z0,z1,z2,z3,z13,z6])],[(0,[z0,z1,z2,z12,z4,z61,z6]),(1,[z0,z1,z3,z40,z6,z72])],[(0,[z318,z0,z1,z2,z3,z4,z6]),(0,[z102,z0,z1,z2,z319,z4,z6]),(0,[z25,z0,z1,z19,z2,z3,z6])]],
   [[(0,[z0,z1,z2,z12,z10,z4,z6]),(0,[z320,z0,z1,z2,z3,z4,z6]),(0,[z321,z0,z1,z2,z3,z36,z6])],[(0,[z0,z1,z2,z322,z3,z4,z6]),(0,[z0,z1,z2,z28,z12,z4,z6]),(0,[z0,z1,z323,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z40,z6,z324])],[(0,[z0,z1,z2,z3,z104,z40,z6]),(0,[z0,z1,z325,z2,z3,z4,z6]),(0,[z0,z1,z2,z179,z3,z4,z6])],[(0,[z258,z0,z1,z2,z3,z40,z6])],[(0,[z50,z0,z1,z2,z3,z52,z6]),(0,[z1,z71,z2,z35,z3,z4,z6]),(0,[z0,z44,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z326,z6]),(0,[z0,z1,z2,z3,z327,z4,z6]),(0,[z0,z328,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z329])],[(0,[z0,z90,z2,z3,z4,z6,z22]),(0,[z0,z1,z2,z330,z3,z4,z6]),(1,[z0,z1,z2,z7,z40,z6]),(0,[z0,z88,z1,z2,z3,z40,z6]),(0,[z0,z1,z2,z331,z3,z4,z6]),(0,[z0,z332,z1,z2,z3,z36,z6])],[(0,[z0,z30,z1,z2,z28,z4,z6]),(0,[z0,z2,z28,z3,z120,z4,z6]),(0,[z0,z1,z333,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z324])],[(0,[z0,z334,z1,z2,z3,z4,z6]),(0,[z335,z0,z1,z2,z3,z36,z6])],[(0,[z158,z0,z1,z2,z287,z3,z6]),(0,[z0,z1,z2,z336,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z337,z6])],[(0,[z127,z0,z1,z266,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z338,z6])],[(0,[z0,z88,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z339,z4,z6]),(0,[z0,z1,z2,z3,z340,z4,z6]),(0,[z0,z1,z341,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z13,z36,z6]),(0,[z342,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z159,z116,z6]),(0,[z0,z1,z49,z3,z4,z40,z6]),(0,[z25,z0,z1,z31,z3,z4,z6]),(0,[z25,z0,z1,z2,z3,z4,z106])],[(0,[z59,z0,z251,z2,z3,z4,z6]),(0,[z0,z343,z1,z2,z3,z4,z6]),(0,[z0,z141,z1,z19,z3,z4,z6]),(0,[z0,z1,z2,z3,z104,z159,z6]),(0,[z0,z1,z3,z52,z4,z40,z6])],[(0,[z127,z0,z1,z2,z54,z4,z6]),(0,[z214,z0,z90,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z344,z4,z6]),(0,[z0,z1,z2,z3,z155,z52,z6])],[(0,[z127,z0,z1,z2,z270,z4,z6]),(0,[z0,z44,z2,z3,z4,z61,z6]),(0,[z0,z1,z2,z3,z4,z6,z345])],[(0,[z0,z1,z2,z3,z4,z163,z60])]],
   [[(1,[z0,z1,z2,z3,z346,z6])],[(0,[z233,z0,z1,z2,z3,z10,z6]),(0,[z0,z347,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z40,z40,z6])],[(0,[z348,z0,z1,z2,z3,z4,z6]),(0,[z0,z141,z1,z91,z3,z4,z6]),(0,[z0,z1,z2,z220,z3,z237,z6])],[(0,[z50,z0,z1,z2,z3,z118,z6]),(0,[z0,z1,z2,z3,z4,z6,z60])],[(0,[z0,z1,z2,z287,z3,z13,z6]),(0,[z0,z1,z2,z3,z36,z6,z345])],[(0,[z349,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z350,z6]),(0,[z25,z267,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z351,z4,z6])],[(0,[z0,z1,z49,z71,z3,z4,z6]),(0,[z102,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z26,z52,z6])],[(0,[z50,z0,z1,z2,z3,z40,z6])],[],[(0,[z0,z1,z110,z2,z3,z4,z6]),(0,[z0,z352,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z40,z353,z6])],[(0,[z102,z25,z0,z1,z2,z3,z6]),(1,[z0,z1,z2,z3,z354,z6]),(0,[z0,z1,z2,z3,z36,z6,z60])],[(0,[z0,z1,z2,z12,z4,z6,z72]),(0,[z0,z1,z355,z2,z3,z4,z6])],[(0,[z50,z0,z1,z2,z7,z4,z6]),(0,[z0,z141,z1,z2,z3,z36,z6]),(0,[z0,z356,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z287,z3,z116,z6])],[(0,[z0,z1,z19,z2,z3,z40,z6]),(0,[z0,z1,z2,z3,z4,z6,z357]),(1,[z0,z1,z2,z3,z222,z6]),(0,[z25,z0,z1,z2,z3,z6,z106])],[(0,[z0,z1,z2,z358,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z353,z6]),(0,[z250,z0,z1,z3,z52,z4,z6])]],
   [[(0,[z359,z0,z1,z2,z3,z4,z6]),(0,[z233,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z131,z6]),(0,[z360,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z52,z116,z6]),(0,[z361,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z110,z2,z12,z4,z6]),(0,[z0,z1,z2,z362,z3,z4,z6]),(0,[z0,z1,z49,z3,z4,z218,z6])],[(0,[z0,z1,z19,z2,z7,z4,z6]),(0,[z0,z32,z2,z91,z3,z4,z6]),(0,[z363,z0,z1,z2,z3,z4,z6])],[(0,[z48,z0,z1,z2,z3,z13,z6]),(1,[z0,z1,z2,z3,z277,z6]),(0,[z0,z44,z1,z2,z3,z61,z6]),(0,[z0,z1,z2,z3,z364,z4,z6]),(0,[z0,z1,z2,z3,z365,z4,z6])],[],[(1,[z0,z1,z2,z3,z215,z6]),(0,[z0,z141,z1,z2,z3,z10,z6]),(1,[z0,z1,z366,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z367,z6])],[(0,[z0,z1,z2,z358,z12,z4,z6]),(0,[z0,z1,z2,z368,z3,z4,z6]),(0,[z0,z1,z2,z3,z116,z36,z6])],[(0,[z369,z0,z1,z2,z3,z36,z6])],[(1,[z0,z1,z2,z370,z4,z6]),(0,[z0,z1,z2,z3,z40,z218,z6]),(0,[z0,z1,z2,z3,z52,z6,z8]),(1,[z0,z1,z2,z3,z204,z6]),(0,[z0,z1,z2,z371,z3,z4,z6]),(0,[z23,z0,z1,z2,z3,z4,z93]),(0,[z0,z1,z2,z3,z4,z6,z372])],[(0,[z0,z1,z2,z3,z4,z373,z6]),(1,[z0,z1,z2,z3,z4,z374]),(0,[z0,z1,z3,z4,z218,z6,z72])],[(0,[z375,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z376,z4,z6]),(0,[z0,z1,z2,z28,z3,z40,z6]),(0,[z0,z1,z2,z3,z26,z40,z6]),(0,[z0,z1,z2,z3,z377,z4,z6])],[(0,[z0,z1,z2,z3,z96,z4,z6])],[],[(1,[z0,z1,z2,z3,z13,z6]),(0,[z0,z44,z1,z2,z3,z40,z6]),(0,[z0,z1,z2,z3,z4,z6,z22])],[(0,[z0,z1,z2,z3,z4,z378,z6]),(1,[z0,z1,z2,z194,z3,z6]),(0,[z0,z1,z2,z3,z379,z4,z6]),(0,[z0,z347,z1,z2,z3,z52,z6])]],
   [[(0,[z50,z0,z1,z2,z3,z4,z167]),(0,[z0,z1,z2,z28,z7,z4,z6]),(0,[z0,z380,z1,z2,z3,z4,z6])],[(0,[z369,z0,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z3,z40,z163,z6]),(0,[z0,z1,z2,z220,z3,z4,z6])],[],[(0,[z0,z44,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z4,z6,z381,z22])],[],[(0,[z0,z236,z2,z91,z3,z4,z6]),(0,[z102,z0,z1,z2,z3,z52,z6]),(0,[z59,z0,z1,z2,z382,z4,z6]),(0,[z59,z0,z1,z2,z3,z383,z6]),(0,[z0,z141,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z36,z6,z22]),(0,[z0,z1,z2,z3,z40,z384,z6])],[(0,[z0,z1,z2,z3,z4,z46,z6]),(0,[z0,z1,z2,z3,z120,z36,z6]),(0,[z0,z1,z2,z3,z4,z163,z6]),(2,[z0,z1,z173,z3,z6])],[(0,[z385,z0,z1,z2,z3,z4,z6]),(0,[z0,z386,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z322,z7,z4,z6]),(0,[z0,z44,z1,z2,z3,z159,z6])],[(0,[z51,z0,z1,z2,z3,z36,z6]),(0,[z0,z30,z1,z2,z3,z13,z6]),(0,[z0,z1,z2,z387,z3,z4,z6])],[(0,[z0,z1,z2,z3,z10,z36,z6]),(0,[z0,z1,z2,z3,z4,z384,z6]),(0,[z25,z0,z1,z2,z3,z6,z8])],[(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z0,z1,z2,z3,z104,z61,z6])],[(1,[z0,z1,z2,z382,z4,z6]),(1,[z0,z1,z2,z3,z383,z6]),(0,[z0,z1,z2,z3,z4,z388,z6]),(0,[z48,z0,z1,z3,z4,z6,z72])],[(0,[z279,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z285,z2,z3,z4,z6]),(0,[z0,z1,z389,z2,z3,z4,z6])],[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z390,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z7,z4,z6,z22]),(0,[z233,z0,z1,z2,z3,z52,z6])],[(0,[z0,z1,z2,z12,z120,z4,z6]),(0,[z0,z1,z2,z391,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z52,z45,z6]),(0,[z392,z0,z1,z2,z3,z4,z6]),(0,[z25,z0,z1,z49,z2,z3,z6])],[(1,[z210,z0,z1,z2,z3,z6]),(0,[z0,z393,z1,z2,z3,z4,z6]),(0,[z279,z25,z0,z1,z2,z3,z6])],[(0,[z51,z0,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z103,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z394,z6]),(0,[z25,z0,z24,z1,z2,z3,z6]),(0,[z25,z0,z1,z192,z2,z3,z6]),(0,[z0,z1,z2,z3,z36,z6,z6])],[(0,[z0,z1,z2,z266,z3,z4,z6]),(0,[z0,z1,z2,z12,z4,z6,z395]),(0,[z0,z1,z2,z3,z10,z10,z6])],[(0,[z0,z1,z71,z2,z3,z168,z6]),(0,[z0,z1,z2,z3,z66,z13,z6]),(0,[z0,z1,z2,z3,z4,z6,z396])],[(1,[z0,z1,z2,z307,z4,z6]),(0,[z0,z1,z397,z2,z3,z4,z6]),(0,[z0,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z382,z4,z6])],[(0,[z0,z1,z2,z3,z4,z82,z6]),(0,[z267,z0,z1,z2,z3,z398,z6]),(0,[z0,z24,z1,z110,z3,z4,z6])],[(0,[z0,z1,z2,z3,z10,z399,z6])],[(0,[z0,z1,z2,z3,z4,z400,z6]),(0,[z59,z0,z1,z2,z3,z4,z45])],[(0,[z0,z1,z401,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z402])],[(0,[z0,z1,z2,z3,z4,z218,z60]),(0,[z0,z24,z1,z2,z3,z403,z6]),(0,[z0,z1,z2,z3,z4,z404,z6])],[(0,[z0,z1,z2,z3,z40,z61,z6])],[(0,[z0,z1,z2,z7,z26,z4,z6]),(0,[z0,z1,z110,z2,z3,z40,z6]),(0,[z0,z1,z2,z3,z4,z223,z6])],[(0,[z267,z0,z1,z2,z405,z4,z6]),(0,[z0,z19,z2,z91,z3,z4,z6]),(0,[z406,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z53,z6]),(0,[z0,z407,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z408])],[(0,[z0,z1,z2,z409,z3,z4,z6]),(0,[z0,z1,z110,z3,z26,z4,z6]),(0,[z0,z1,z2,z220,z3,z52,z6]),(0,[z0,z1,z2,z3,z410,z4,z6])]],
   [[(0,[z411,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z61,z6]),(0,[z0,z1,z412,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z52,z6,z106]),(0,[z0,z1,z2,z3,z52,z66,z6])],[(0,[z51,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z110,z2,z7,z4,z6]),(0,[z0,z1,z413,z2,z3,z4,z6]),(0,[z25,z0,z1,z2,z3,z45,z6]),(0,[z406,z25,z0,z1,z2,z3,z6])],[(0,[z25,z0,z1,z90,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z414,z6]),(0,[z267,z1,z2,z3,z4,z45,z6]),(1,[z369,z0,z2,z3,z4,z22]),(1,[z0,z1,z31,z3,z4,z6])],[(0,[z283,z0,z1,z2,z3,z10,z6]),(0,[z0,z141,z1,z2,z3,z52,z6])],[(0,[z0,z1,z2,z35,z3,z292,z6]),(0,[z107,z0,z1,z2,z3,z13,z6]),(0,[z0,z1,z2,z3,z13,z350,z6])],[],[(0,[z0,z1,z2,z12,z159,z4,z6]),(1,[z0,z1,z2,z3,z415,z6]),(0,[z48,z0,z1,z2,z3,z416,z6]),(0,[z0,z417,z1,z2,z3,z4,z6]),(0,[z0,z1,z49,z2,z3,z217,z6]),(1,[z25,z0,z1,z2,z3,z106])],[(0,[z418,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z419,z2,z3,z4,z6]),(0,[z0,z1,z2,z271,z7,z4,z6]),(0,[z0,z1,z420,z2,z3,z4,z6]),(0,[z0,z1,z2,z421,z3,z4,z6])],[(0,[z0,z1,z2,z3,z226,z4,z6]),(0,[z0,z1,z2,z422,z3,z4,z6]),(0,[z0,z1,z423,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z424])],[(0,[z0,z1,z2,z425,z3,z4,z6])],[(0,[z426,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z40,z6])],[(0,[z25,z0,z1,z2,z35,z3,z6]),(0,[z279,z0,z1,z2,z3,z52,z6]),(0,[z321,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z287,z104,z6]),(0,[z0,z1,z2,z3,z427,z4,z6])],[(0,[z0,z1,z2,z428,z3,z4,z6]),(0,[z0,z1,z2,z3,z429,z4,z6])],[(0,[z236,z1,z90,z2,z3,z4,z6]),(1,[z0,z430,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z350,z45,z6])],[(0,[z431,z0,z1,z2,z3,z4,z6]),(0,[z0,z43,z1,z2,z3,z4,z163]),(1,[z25,z0,z1,z31,z3,z6])],[(0,[z127,z0,z1,z2,z3,z13,z6]),(1,[z0,z1,z2,z3,z128,z6])]],
   [[(0,[z127,z214,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z416,z6]),(0,[z0,z332,z1,z2,z3,z4,z6])],[(0,[z0,z432,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z433,z4,z6]),(0,[z0,z1,z434,z2,z3,z4,z6]),(0,[z25,z0,z1,z2,z3,z66,z6])],[(0,[z102,z0,z1,z2,z12,z4,z6]),(0,[z283,z0,z1,z2,z3,z4,z6]),(0,[z59,z0,z1,z366,z3,z4,z6]),(0,[z335,z0,z1,z2,z3,z4,z6]),(0,[z431,z25,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z220,z3,z40,z6])],[(0,[z0,z435,z1,z2,z3,z4,z6]),(0,[z0,z1,z71,z91,z3,z4,z6]),(0,[z0,z32,z1,z2,z3,z36,z6]),(0,[z369,z0,z43,z2,z3,z4,z6]),(0,[z0,z1,z436,z2,z3,z4,z6])],[],[(0,[z0,z1,z2,z3,z4,z6,z437]),(0,[z0,z438,z1,z2,z3,z4,z6]),(0,[z283,z25,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z7,z4,z6,z60]),(0,[z0,z1,z2,z439,z3,z4,z6]),(0,[z440,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z12,z4,z13,z6]),(0,[z0,z1,z2,z3,z4,z6,z441]),(0,[z0,z1,z2,z3,z442,z4,z6])],[(0,[z0,z251,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z40,z6,z72])],[(0,[z0,z1,z2,z7,z4,z40,z6]),(0,[z59,z0,z1,z2,z3,z13,z6])],[(1,[z214,z236,z2,z3,z4,z6]),(0,[z65,z1,z2,z3,z12,z4,z6]),(0,[z233,z0,z1,z2,z12,z4,z6]),(0,[z23,z0,z1,z2,z220,z4,z6]),(0,[z443,z25,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z12,z52,z4,z6]),(0,[z0,z1,z2,z3,z13,z6,z22]),(0,[z444,z0,z1,z2,z3,z4,z6]),(0,[z0,z445,z1,z2,z3,z4,z6]),(0,[z0,z446,z1,z2,z3,z4,z6]),(0,[z25,z0,z1,z2,z3,z104,z6]),(1,[z0,z1,z2,z173,z3,z6])],[(1,[z0,z1,z2,z3,z4,z447]),(0,[z0,z32,z1,z2,z3,z10,z6]),(0,[z25,z0,z1,z39,z2,z3,z6]),(0,[z0,z1,z2,z3,z448,z4,z6]),(0,[z0,z1,z2,z3,z221,z4,z6])],[(0,[z0,z1,z71,z2,z3,z36,z6]),(0,[z0,z1,z2,z119,z3,z4,z6])],[(0,[z449,z0,z1,z2,z3,z4,z6]),(0,[z51,z0,z1,z2,z3,z52,z6]),(0,[z0,z1,z2,z3,z4,z450,z6]),(1,[z0,z1,z2,z4,z6,z381])]],
   [[(0,[z50,z0,z1,z2,z280,z4,z6]),(0,[z0,z1,z2,z12,z4,z116,z6]),(0,[z25,z0,z32,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z4,z218,z6])],[(0,[z0,z1,z2,z3,z4,z451,z6]),(0,[z48,z0,z1,z2,z3,z4,z218])],[(0,[z0,z1,z90,z2,z3,z13,z6]),(0,[z0,z452,z1,z2,z3,z4,z6]),(0,[z453,z0,z1,z2,z3,z4,z6]),(0,[z369,z0,z2,z3,z4,z6,z22]),(0,[z0,z1,z2,z3,z40,z292,z6]),(0,[z0,z1,z2,z177,z3,z6,z72]),(0,[z0,z1,z2,z3,z36,z6,z372])],[(0,[z214,z0,z1,z2,z454,z4,z6]),(0,[z0,z0,z1,z2,z7,z4,z6]),(0,[z23,z0,z1,z2,z3,z4,z8]),(0,[z25,z0,z1,z2,z3,z36,z6])],[(0,[z0,z88,z1,z2,z28,z4,z6]),(0,[z0,z1,z39,z2,z3,z36,z6])],[(0,[z0,z1,z71,z2,z3,z455,z6]),(0,[z0,z1,z2,z3,z4,z6,z456]),(0,[z369,z0,z1,z2,z3,z4,z22]),(0,[z0,z1,z2,z3,z457,z4,z6]),(0,[z0,z1,z110,z2,z3,z201,z6]),(0,[z0,z1,z458,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z459,z4,z6])],[(0,[z0,z1,z71,z2,z3,z10,z6]),(0,[z0,z1,z2,z12,z4,z93,z6]),(0,[z0,z1,z2,z91,z3,z13,z6]),(0,[z23,z0,z1,z2,z3,z13,z6]),(1,[z0,z1,z2,z3,z398,z6]),(0,[z0,z1,z2,z3,z460,z4,z6])],[(0,[z0,z1,z2,z3,z4,z292,z6]),(0,[z0,z1,z2,z3,z4,z6,z381]),(0,[z0,z1,z2,z3,z36,z218,z6])],[(1,[z0,z1,z2,z12,z13,z6])],[],[(0,[z461,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z220,z12,z4,z6])],[(0,[z142,z0,z1,z2,z3,z4,z6]),(0,[z25,z0,z1,z2,z3,z10,z6])],[(0,[z0,z1,z39,z2,z3,z10,z6]),(1,[z0,z1,z2,z405,z4,z6]),(0,[z25,z0,z88,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z40,z198,z6])],[]],
   [[(0,[z0,z1,z462,z2,z3,z4,z6]),(0,[z0,z141,z1,z2,z12,z4,z6]),(0,[z0,z1,z401,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z186,z13,z6]),(0,[z0,z1,z2,z463,z3,z4,z6]),(0,[z0,z1,z2,z3,z36,z163,z6]),(0,[z0,z1,z2,z3,z350,z36,z6])],[(0,[z0,z1,z2,z7,z4,z218,z6]),(0,[z0,z1,z2,z3,z10,z6,z60]),(0,[z0,z1,z2,z3,z4,z60,z22]),(0,[z0,z464,z1,z2,z3,z4,z6])],[(0,[z465,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z466,z3,z4,z6]),(0,[z0,z1,z2,z3,z12,z13,z6]),(0,[z0,z1,z2,z3,z120,z10,z6]),(1,[z0,z1,z2,z3,z467,z6]),(0,[z0,z1,z2,z224,z3,z4,z6])],[(0,[z233,z0,z1,z2,z92,z4,z6]),(0,[z0,z1,z2,z126,z3,z13,z6]),(0,[z468,z0,z1,z2,z3,z4,z6]),(0,[z369,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z198,z6])],[(0,[z0,z1,z2,z3,z4,z469,z6]),(1,[z0,z1,z2,z3,z470,z6]),(0,[z0,z1,z2,z471,z3,z4,z6]),(0,[z472,z0,z1,z2,z3,z4,z6])],[],[(0,[z0,z1,z71,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z405,z4,z6]),(0,[z0,z1,z2,z3,z473,z4,z6]),(0,[z369,z25,z0,z1,z2,z3,z6]),(0,[z250,z0,z1,z2,z3,z36,z6])],[(0,[z50,z0,z1,z71,z3,z4,z6]),(0,[z65,z0,z1,z2,z3,z69,z6]),(0,[z279,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z474,z4,z6]),(0,[z475,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z476]),(0,[z0,z1,z2,z3,z4,z477,z6])],[(0,[z0,z1,z2,z7,z4,z163,z6]),(0,[z0,z1,z2,z3,z4,z478,z6]),(0,[z0,z1,z2,z479,z3,z4,z6])],[(0,[z0,z1,z2,z7,z3,z13,z6]),(0,[z267,z0,z1,z2,z3,z36,z6])],[(0,[z369,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z29,z3,z13,z6]),(0,[z0,z1,z2,z169,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z33,z6]),(0,[z0,z1,z2,z480,z3,z4,z6]),(0,[z0,z1,z2,z481,z3,z4,z6]),(0,[z0,z44,z1,z2,z126,z3,z6])],[(0,[z214,z0,z1,z2,z3,z482,z6]),(0,[z0,z1,z2,z3,z4,z6,z483]),(0,[z102,z0,z1,z2,z3,z40,z6]),(0,[z0,z1,z2,z484,z3,z10,z6]),(0,[z48,z0,z1,z2,z3,z485,z6])],[(0,[z0,z1,z49,z2,z3,z13,z6]),(0,[z0,z1,z2,z3,z77,z13,z6]),(0,[z0,z1,z2,z486,z3,z4,z6]),(0,[z0,z1,z2,z487,z3,z4,z6])],[(0,[z0,z1,z19,z71,z3,z4,z6]),(0,[z0,z43,z1,z2,z3,z13,z6]),(0,[z0,z1,z488,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z403,z6])],[(1,[z50,z1,z35,z3,z4,z6]),(0,[z210,z0,z1,z2,z3,z13,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z316,z6]),(0,[z0,z1,z2,z3,z159,z36,z6]),(1,[z0,z1,z2,z3,z489,z6])],[(0,[z51,z0,z1,z35,z3,z4,z6]),(0,[z102,z0,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z366,z3,z4,z6]),(0,[z0,z1,z2,z3,z120,z4,z6]),(0,[z0,z490,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z66,z36])],[(0,[z25,z214,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z370,z3,z4,z6])],[(0,[z267,z0,z1,z2,z3,z10,z6]),(0,[z0,z30,z1,z2,z120,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z491])],[(0,[z59,z0,z1,z314,z3,z4,z6]),(0,[z492,z0,z1,z2,z3,z4,z6]),(0,[z0,z24,z1,z2,z3,z299,z6]),(1,[z0,z1,z49,z3,z4,z218])],[(0,[z214,z0,z1,z2,z3,z36,z6]),(0,[z0,z493,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z10,z4,z6]),(0,[z233,z0,z1,z2,z3,z40,z6]),(0,[z0,z1,z2,z3,z13,z6,z60])],[(0,[z0,z1,z2,z35,z3,z13,z6]),(1,[z0,z1,z2,z3,z255,z6]),(0,[z0,z32,z1,z19,z3,z4,z6]),(0,[z158,z0,z1,z2,z3,z36,z6]),(0,[z0,z1,z2,z3,z4,z6,z494]),(1,[z0,z1,z2,z3,z485,z6])],[(0,[z0,z1,z35,z3,z4,z6,z72]),(0,[z0,z21,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z495,z3,z4,z6])],[(0,[z0,z1,z2,z3,z13,z40,z6]),(0,[z0,z1,z2,z194,z3,z4,z6]),(0,[z0,z1,z2,z3,z61,z116,z6])],[(0,[z0,z1,z2,z3,z159,z10,z6]),(0,[z0,z1,z2,z3,z383,z4,z6])],[(1,[z107,z1,z2,z7,z4,z6]),(0,[z233,z0,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z287,z3,z104,z6])],[(0,[z0,z496,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z10,z6,z22]),(1,[z283,z0,z1,z2,z3,z6]),(1,[z0,z1,z314,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z346,z6]),(0,[z0,z497,z1,z2,z3,z4,z6]),(0,[z51,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z197,z4,z6]),(0,[z0,z1,z2,z3,z10,z442,z6])],[(0,[z50,z0,z1,z2,z3,z346,z6]),(0,[z0,z32,z1,z91,z3,z4,z6]),(0,[z0,z2,z3,z4,z163,z6,z22]),(0,[z498,z0,z1,z2,z3,z4,z6])],[(0,[z127,z0,z1,z2,z3,z4,z447]),(0,[z214,z0,z1,z2,z3,z10,z6]),(0,[z1,z2,z3,z10,z4,z13,z6]),(0,[z0,z1,z2,z3,z4,z6,z499])],[(1,[z127,z90,z2,z3,z4,z6]),(0,[z158,z0,z1,z2,z3,z10,z6])]],
   [[(0,[z65,z0,z1,z2,z3,z36,z6]),(0,[z0,z1,z49,z2,z3,z470,z6])],[(1,[z0,z1,z2,z3,z67,z6]),(0,[z0,z1,z500,z2,z3,z4,z6]),(0,[z0,z1,z208,z2,z3,z4,z6]),(0,[z369,z0,z1,z2,z3,z52,z6])],[(0,[z0,z501,z1,z2,z3,z4,z6]),(1,[z0,z30,z2,z120,z4,z6]),(0,[z0,z1,z2,z3,z502,z4,z6]),(0,[z0,z1,z2,z503,z3,z4,z6]),(0,[z0,z1,z2,z287,z3,z36,z6])],[(0,[z0,z1,z2,z7,z4,z61,z6]),(0,[z0,z1,z2,z3,z4,z504,z6])],[(0,[z214,z0,z1,z2,z189,z4,z6]),(1,[z0,z1,z2,z274,z4,z6]),(0,[z0,z1,z71,z2,z3,z52,z6]),(0,[z0,z1,z2,z3,z379,z40,z6]),(1,[z0,z1,z2,z3,z221,z6])],[(0,[z0,z1,z505,z2,z3,z4,z6]),(0,[z0,z1,z2,z7,z10,z4,z6]),(0,[z0,z1,z2,z3,z104,z13,z6])],[(0,[z0,z506,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z52,z36,z6]),(1,[z0,z1,z2,z3,z6,z99])],[(0,[z0,z1,z2,z428,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z354,z6]),(0,[z507,z0,z1,z2,z3,z4,z6]),(0,[z508,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z7,z13,z6]),(0,[z0,z88,z1,z2,z3,z13,z6]),(0,[z509,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z459,z40,z6])],[(0,[z65,z0,z1,z2,z3,z10,z6]),(1,[z267,z1,z2,z3,z4,z45]),(0,[z510,z0,z1,z2,z3,z4,z6])],[(0,[z443,z0,z1,z2,z3,z4,z6]),(0,[z0,z141,z1,z2,z3,z40,z6]),(0,[z0,z511,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z287,z3,z10,z6]),(0,[z0,z1,z2,z3,z66,z4,z106])],[(0,[z0,z1,z2,z3,z512,z4,z6]),(0,[z0,z1,z2,z3,z52,z6,z139])],[(0,[z513,z0,z1,z2,z3,z4,z6])],[(0,[z0,z430,z1,z2,z3,z4,z6]),(0,[z514,z0,z1,z2,z3,z4,z6])],[(0,[z0,z141,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z13,z218,z6]),(0,[z0,z1,z2,z3,z52,z10,z6]),(0,[z0,z1,z2,z3,z120,z52,z6]),(0,[z0,z490,z1,z2,z3,z52,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z515]),(0,[z516,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z517]),(0,[z25,z0,z1,z173,z3,z4,z6])],[(0,[z518,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z519,z3,z4,z6]),(0,[z0,z1,z110,z2,z26,z4,z6]),(0,[z520,z0,z1,z2,z3,z52,z6]),(0,[z0,z1,z2,z3,z4,z6,z72])],[(0,[z51,z0,z1,z2,z3,z82,z6]),(0,[z0,z1,z2,z521,z3,z4,z6]),(0,[z102,z1,z2,z3,z10,z4,z6]),(0,[z522,z0,z1,z2,z3,z4,z6]),(0,[z279,z0,z1,z2,z3,z40,z6]),(0,[z514,z25,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z523,z3,z4,z6])],[(0,[z0,z141,z236,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z155,z6]),(1,[z0,z1,z2,z177,z3,z6]),(0,[z0,z1,z524,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z525,z4,z6]),(0,[z369,z0,z1,z2,z3,z40,z6]),(0,[z0,z1,z2,z3,z4,z204,z6])],[(0,[z0,z1,z526,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z527,z6])],[(0,[z50,z0,z1,z2,z3,z4,z374]),(0,[z279,z0,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z13,z163,z6]),(0,[z0,z1,z2,z3,z4,z6,z528])],[(0,[z25,z0,z1,z2,z7,z3,z6]),(0,[z0,z1,z2,z3,z36,z6,z72]),(0,[z0,z1,z2,z3,z4,z6,z529]),(0,[z25,z0,z1,z2,z3,z4,z36])],[(0,[z0,z236,z1,z2,z3,z36,z6])],[(0,[z0,z1,z2,z521,z12,z4,z6]),(0,[z369,z0,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z20,z4,z6]),(0,[z0,z24,z1,z2,z3,z36,z6])],[(0,[z50,z0,z1,z2,z3,z13,z6]),(0,[z0,z1,z2,z12,z4,z6,z8]),(0,[z0,z1,z2,z3,z530,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z531])],[(0,[z0,z1,z2,z3,z4,z6,z295])],[(0,[z0,z1,z2,z3,z4,z6,z532]),(0,[z0,z1,z2,z3,z533,z4,z6]),(0,[z534,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z535,z3,z4,z6]),(0,[z23,z0,z1,z110,z2,z4,z6])],[(0,[z536,z0,z1,z2,z3,z4,z6]),(0,[z267,z0,z1,z2,z3,z4,z60]),(0,[z0,z1,z2,z3,z4,z537,z6])],[(0,[z25,z233,z0,z1,z2,z3,z6]),(0,[z0,z32,z1,z2,z3,z4,z6]),(0,[z0,z24,z1,z2,z4,z93,z6]),(0,[z0,z1,z2,z3,z538,z4,z6]),(0,[z539,z0,z1,z2,z3,z4,z6])]],
   [[(1,[z0,z1,z2,z103,z4,z6])],[(0,[z0,z1,z2,z7,z4,z6,z72]),(0,[z0,z1,z2,z7,z220,z4,z6]),(0,[z0,z1,z19,z2,z3,z13,z6]),(1,[z0,z1,z2,z3,z55,z6])],[(0,[z0,z236,z1,z2,z3,z10,z6]),(0,[z540,z0,z1,z2,z3,z4,z6])],[(0,[z0,z24,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z3,z4,z6,z541]),(0,[z539,z25,z0,z1,z2,z3,z6])],[(0,[z0,z24,z1,z29,z3,z4,z6]),(0,[z0,z1,z2,z3,z40,z93,z6]),(0,[z0,z506,z1,z2,z3,z52,z6])],[(0,[z0,z124,z1,z2,z3,z6,z60]),(1,[z0,z88,z2,z28,z4,z6]),(0,[z0,z1,z542,z2,z3,z4,z6])],[(0,[z51,z0,z1,z2,z3,z40,z6]),(0,[z543,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z544,z4,z6])],[(0,[z107,z0,z1,z2,z3,z67,z6]),(0,[z0,z1,z2,z3,z10,z40,z6]),(0,[z0,z1,z2,z3,z4,z162,z6])],[(0,[z0,z1,z545,z2,z3,z4,z6]),(1,[z0,z1,z3,z52,z40,z6])],[(0,[z0,z1,z2,z546,z3,z4,z6]),(0,[z0,z1,z2,z409,z7,z4,z6]),(1,[z1,z2,z3,z10,z13,z6])],[],[(0,[z214,z0,z1,z2,z3,z52,z6]),(0,[z51,z0,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z547,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z317])],[(1,[z25,z0,z1,z2,z12,z6]),(0,[z0,z493,z1,z2,z7,z4,z6]),(0,[z548,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z151,z6]),(0,[z0,z1,z549,z2,z3,z4,z6]),(0,[z0,z24,z1,z2,z29,z4,z6]),(0,[z550,z0,z1,z2,z3,z36,z6])],[(0,[z551,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z28,z3,z13,z6]),(0,[z0,z1,z2,z3,z26,z13,z6]),(0,[z0,z1,z2,z3,z13,z316,z6]),(0,[z0,z1,z2,z3,z399,z4,z6]),(0,[z0,z1,z552,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z553]),(0,[z0,z1,z2,z126,z3,z116,z6]),(0,[z0,z1,z2,z554,z3,z4,z6])],[(0,[z0,z555,z1,z2,z3,z4,z6]),(0,[z25,z0,z1,z2,z91,z3,z6]),(0,[z0,z1,z2,z556,z3,z4,z6]),(1,[z48,z0,z1,z3,z4,z72]),(0,[z25,z0,z1,z2,z3,z4,z6]),(0,[z557,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z65,z0,z1,z2,z3,z525,z6]),(0,[z0,z1,z2,z3,z4,z6,z558]),(0,[z158,z0,z44,z2,z3,z4,z6]),(0,[z0,z44,z1,z2,z287,z3,z6]),(0,[z0,z1,z2,z3,z559,z4,z6]),(0,[z0,z1,z2,z3,z489,z6,z22]),(0,[z0,z1,z39,z2,z3,z4,z6]),(0,[z560,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z71,z2,z12,z4,z6]),(0,[z0,z44,z1,z2,z3,z13,z6]),(0,[z0,z1,z2,z3,z13,z61,z6])],[(0,[z50,z0,z1,z2,z307,z4,z6]),(0,[z561,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z4,z45,z6]),(0,[z562,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z36,z6,z317])],[(0,[z0,z1,z2,z3,z255,z4,z6]),(0,[z250,z0,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z3,z4,z6,z563]),(0,[z0,z1,z2,z3,z4,z6,z564]),(0,[z25,z25,z0,z1,z2,z3,z6])],[(1,[z0,z1,z2,z3,z168,z6]),(0,[z0,z1,z2,z565,z3,z4,z6])],[(0,[z0,z1,z2,z3,z482,z4,z6]),(0,[z25,z0,z1,z2,z3,z6,z22])],[(0,[z65,z0,z1,z2,z3,z52,z6]),(0,[z520,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z566]),(1,[z0,z1,z2,z249,z4,z6]),(0,[z0,z555,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z198,z36,z6])],[(0,[z0,z1,z2,z12,z62,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z395]),(1,[z0,z1,z2,z3,z299,z6])],[(0,[z0,z501,z1,z2,z7,z4,z6]),(0,[z0,z124,z1,z2,z3,z4,z6]),(0,[z267,z0,z1,z2,z109,z4,z6])],[(0,[z0,z1,z567,z2,z3,z4,z6]),(0,[z0,z568,z1,z2,z3,z4,z6]),(0,[z569,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z66,z4,z6])],[(0,[z0,z1,z2,z7,z474,z4,z6]),(0,[z0,z1,z3,z4,z40,z6,z72]),(0,[z0,z1,z49,z2,z3,z4,z218])],[(0,[z0,z303,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z570,z3,z4,z6]),(1,[z0,z1,z2,z454,z4,z6]),(0,[z0,z32,z1,z2,z3,z52,z6]),(0,[z0,z1,z2,z571,z3,z4,z6]),(0,[z539,z0,z1,z2,z3,z52,z6])],[(0,[z0,z1,z2,z274,z3,z4,z6]),(0,[z0,z1,z572,z2,z3,z4,z6]),(0,[z0,z1,z2,z484,z3,z4,z6]),(0,[z0,z1,z2,z3,z10,z218,z6]),(0,[z0,z1,z2,z3,z4,z573,z6]),(1,[z158,z0,z2,z3,z159,z6]),(0,[z0,z1,z2,z574,z3,z4,z6])],[(0,[z0,z1,z2,z575,z3,z4,z6]),(0,[z0,z1,z2,z576,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z577,z3,z4,z6]),(0,[z0,z1,z2,z3,z249,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z14]),(0,[z0,z1,z2,z578,z3,z4,z6]),(1,[z250,z0,z1,z3,z52,z6])],[(0,[z0,z579,z1,z2,z3,z4,z6]),(0,[z0,z446,z1,z2,z3,z40,z6])],[(0,[z580,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z81,z4,z6]),(0,[z0,z1,z2,z12,z4,z6,z106]),(0,[z250,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z448,z40,z6])],[(1,[z0,z1,z2,z3,z512,z6])],[(0,[z0,z1,z2,z7,z120,z4,z6]),(0,[z0,z1,z2,z581,z3,z4,z6]),(0,[z582,z0,z1,z2,z3,z36,z6])],[(0,[z267,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z454,z4,z6]),(1,[z0,z1,z2,z3,z69,z6]),(0,[z0,z1,z2,z3,z10,z163,z6]),(0,[z0,z1,z2,z583,z3,z4,z6]),(0,[z250,z25,z0,z1,z2,z3,z6])],[(0,[z0,z32,z141,z2,z3,z4,z6])],[(0,[z0,z584,z1,z2,z3,z4,z6])],[(0,[z0,z585,z1,z2,z3,z4,z6])],[(0,[z127,z0,z90,z2,z3,z4,z6]),(0,[z50,z0,z430,z2,z3,z4,z6])],[(0,[z127,z1,z90,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z128,z6]),(0,[z0,z1,z2,z3,z159,z4,z6]),(1,[z0,z1,z2,z3,z211,z6])],[],[(0,[z0,z1,z2,z3,z52,z6,z60]),(0,[z0,z1,z2,z3,z467,z4,z6]),(0,[z0,z1,z2,z556,z3,z52,z6]),(0,[z25,z0,z1,z2,z3,z52,z6]),(0,[z0,z1,z2,z3,z4,z6,z586]),(0,[z587,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z588,z3,z4,z6]),(0,[z0,z1,z39,z2,z3,z52,z6])],[(1,[z0,z1,z2,z3,z232,z6]),(0,[z0,z1,z110,z2,z3,z13,z6]),(0,[z0,z1,z2,z3,z13,z6,z72]),(0,[z23,z0,z30,z1,z2,z4,z6]),(0,[z589,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z214,z0,z1,z2,z3,z4,z6]),(0,[z233,z0,z1,z2,z370,z4,z6]),(0,[z590,z0,z1,z2,z3,z4,z6])],[(0,[z158,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z591,z6]),(0,[z0,z1,z2,z592,z3,z4,z6])],[(0,[z593,z0,z1,z2,z3,z4,z6])],[],[(0,[z534,z0,z1,z2,z7,z4,z6]),(0,[z594,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z595,z6]),(0,[z0,z1,z2,z3,z596,z4,z6]),(0,[z48,z0,z1,z2,z3,z36,z6])],[(0,[z0,z1,z2,z3,z4,z215,z6]),(1,[z0,z1,z2,z3,z482,z6]),(0,[z0,z1,z2,z3,z4,z597,z6]),(0,[z0,z1,z2,z271,z3,z13,z6]),(0,[z158,z25,z0,z1,z2,z3,z6])],[(0,[z598,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z599]),(0,[z0,z1,z2,z3,z201,z4,z6]),(0,[z0,z600,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z601])],[(0,[z107,z1,z2,z7,z3,z4,z6]),(0,[z0,z1,z2,z3,z143,z13,z6]),(0,[z59,z0,z1,z2,z3,z36,z6]),(0,[z0,z1,z2,z3,z4,z602,z6]),(0,[z603,z0,z1,z2,z3,z36,z6])],[(0,[z214,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z604]),(1,[z0,z21,z1,z2,z4,z6]),(1,[z0,z1,z132,z2,z3,z6]),(0,[z0,z1,z29,z3,z26,z4,z6]),(1,[z0,z1,z2,z3,z237,z6]),(0,[z0,z1,z2,z3,z605,z4,z6])],[(0,[z158,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z13,z292,z6]),(0,[z0,z1,z2,z3,z606,z4,z6])],[(0,[z250,z0,z1,z49,z3,z4,z6])],[(0,[z0,z1,z71,z2,z3,z40,z6]),(0,[z65,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z7,z159,z4,z6]),(0,[z0,z1,z2,z3,z607,z4,z6]),(0,[z0,z1,z2,z220,z3,z4,z93])],[(0,[z608,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z609])],[(0,[z0,z1,z2,z3,z4,z13,z6]),(0,[z48,z0,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z287,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z610,z6])],[(0,[z0,z1,z2,z3,z4,z611,z6]),(0,[z0,z1,z612,z2,z3,z4,z6]),(0,[z25,z0,z1,z2,z3,z6,z60]),(0,[z25,z0,z1,z2,z3,z605,z6]),(1,[z0,z1,z2,z3,z36,z6])],[(0,[z0,z1,z2,z613,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z614])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z615]),(0,[z0,z1,z71,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z10,z61,z6]),(0,[z0,z1,z2,z3,z40,z116,z6]),(0,[z250,z0,z1,z2,z3,z52,z6])],[(0,[z0,z1,z2,z616,z3,z4,z6]),(0,[z0,z1,z2,z3,z52,z4,z6]),(0,[z25,z0,z1,z2,z3,z40,z6])],[(0,[z0,z88,z1,z2,z120,z4,z6])],[(0,[z65,z0,z1,z2,z12,z4,z6]),(1,[z102,z1,z2,z3,z10,z6]),(0,[z267,z0,z1,z2,z3,z52,z6])],[(0,[z0,z236,z2,z3,z4,z6,z22]),(0,[z0,z1,z2,z3,z4,z60,z72]),(0,[z0,z1,z2,z91,z3,z36,z6]),(0,[z23,z0,z1,z2,z3,z36,z6])],[(0,[z0,z1,z2,z7,z4,z597,z6]),(0,[z0,z1,z2,z3,z4,z116,z6]),(0,[z0,z1,z2,z3,z617,z4,z6])],[(1,[z0,z1,z2,z3,z455,z6]),(1,[z0,z1,z2,z12,z36,z6]),(0,[z25,z0,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z618,z4,z6]),(0,[z0,z1,z2,z3,z120,z40,z6])],[(1,[z0,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z3,z4,z6,z75]),(0,[z0,z1,z2,z3,z52,z6,z22])],[(0,[z0,z1,z619,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z40,z6,z8]),(0,[z539,z0,z1,z2,z3,z218,z6]),(0,[z0,z1,z2,z126,z3,z104,z6])],[(0,[z59,z0,z1,z2,z3,z151,z6]),(0,[z0,z620,z1,z2,z3,z4,z6]),(0,[z0,z30,z1,z2,z3,z36,z6])],[(0,[z0,z1,z621,z2,z3,z4,z6]),(0,[z0,z32,z1,z2,z12,z4,z6]),(0,[z0,z1,z622,z2,z3,z4,z6]),(0,[z108,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z399,z6]),(0,[z0,z1,z2,z3,z4,z623,z6]),(0,[z624,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z374]),(0,[z625,z0,z1,z2,z3,z4,z6]),(1,[z0,z300,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z93,z6])],[(1,[z0,z1,z2,z189,z4,z6]),(0,[z626,z0,z1,z2,z3,z4,z6]),(0,[z25,z0,z1,z71,z2,z3,z6]),(0,[z0,z1,z2,z7,z4,z13,z6]),(0,[z23,z0,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z3,z4,z6,z627]),(0,[z0,z628,z1,z2,z3,z4,z6])],[(0,[z0,z30,z1,z2,z4,z93,z6]),(0,[z0,z1,z2,z629,z3,z4,z6])],[(1,[z0,z1,z2,z12,z10,z6]),(0,[z0,z1,z2,z3,z4,z6,z630]),(0,[z631,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z632,z6]),(0,[z158,z0,z1,z2,z3,z52,z6])]],
   [[(0,[z0,z1,z2,z7,z533,z4,z6]),(0,[z311,z0,z1,z2,z3,z13,z6]),(0,[z633,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z470,z6])],[(0,[z0,z1,z2,z7,z52,z4,z6])],[(0,[z0,z0,z1,z2,z3,z13,z6]),(0,[z0,z30,z1,z2,z3,z10,z6]),(0,[z0,z634,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z20,z6]),(0,[z0,z1,z2,z635,z3,z4,z6]),(0,[z0,z1,z2,z3,z36,z93,z6])],[(0,[z0,z236,z1,z2,z3,z4,z6]),(0,[z636,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z66,z36,z6])],[(0,[z107,z0,z1,z2,z3,z232,z6]),(0,[z0,z1,z2,z484,z7,z4,z6]),(1,[z0,z141,z19,z3,z4,z6]),(0,[z0,z24,z1,z2,z3,z4,z6]),(0,[z0,z637,z1,z2,z3,z4,z6])],[(0,[z638,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z110,z2,z3,z415,z6]),(1,[z25,z0,z1,z173,z3,z6])],[(0,[z0,z1,z2,z12,z12,z4,z6]),(0,[z25,z0,z1,z2,z3,z218,z6])],[(0,[z0,z43,z90,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z58,z10,z6])],[(0,[z25,z0,z1,z2,z12,z4,z6]),(0,[z102,z233,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z639]),(0,[z0,z1,z2,z3,z4,z403,z6]),(0,[z0,z1,z49,z2,z3,z36,z6]),(1,[z25,z0,z1,z2,z3,z6])],[(1,[z0,z1,z545,z3,z4,z6]),(0,[z0,z1,z39,z2,z12,z4,z6]),(0,[z0,z640,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z62,z10,z6]),(0,[z0,z1,z2,z641,z3,z4,z6]),(0,[z0,z642,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z287,z3,z52,z6]),(0,[z0,z1,z2,z104,z4,z116,z6])],[(0,[z0,z236,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z35,z3,z155,z6]),(1,[z1,z2,z7,z12,z4,z6]),(0,[z0,z1,z2,z7,z4,z93,z6])],[(0,[z0,z24,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z61,z36,z6]),(0,[z0,z1,z2,z3,z159,z40,z6]),(0,[z0,z1,z643,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z644,z6]),(0,[z0,z1,z2,z3,z10,z6,z72])],[(0,[z0,z645,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z40,z45,z6]),(0,[z0,z1,z2,z3,z467,z40,z6]),(0,[z0,z1,z2,z3,z52,z52,z6]),(0,[z0,z1,z2,z3,z595,z36,z6])]],
   [[(0,[z51,z1,z71,z2,z3,z4,z6]),(0,[z25,z0,z1,z2,z3,z163,z6])],[(0,[z646,z0,z1,z2,z3,z4,z6]),(0,[z0,z43,z1,z2,z3,z55,z6]),(1,[z0,z1,z110,z26,z4,z6])],[(0,[z214,z0,z1,z2,z3,z40,z6]),(0,[z647,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z648,z52,z6])],[(0,[z233,z1,z2,z3,z4,z13,z6]),(0,[z0,z1,z49,z2,z3,z10,z6]),(0,[z0,z32,z1,z2,z3,z96,z6]),(0,[z25,z0,z1,z2,z28,z3,z6]),(0,[z158,z0,z1,z2,z3,z40,z6]),(0,[z0,z1,z2,z3,z4,z649,z6])],[(0,[z107,z0,z1,z2,z3,z36,z6]),(0,[z0,z1,z2,z3,z4,z218,z45])],[(0,[z0,z650,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z415,z6]),(0,[z25,z0,z1,z2,z3,z6,z6])],[(0,[z0,z1,z2,z3,z52,z340,z6]),(0,[z0,z1,z2,z3,z4,z651,z6])],[(0,[z214,z0,z1,z2,z7,z4,z6]),(0,[z652,z0,z1,z2,z3,z4,z6]),(0,[z250,z0,z1,z39,z3,z4,z6]),(0,[z0,z1,z31,z2,z3,z4,z6])],[(0,[z158,z0,z1,z2,z7,z4,z6]),(0,[z550,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z86,z6]),(0,[z369,z0,z1,z2,z3,z4,z163]),(1,[z539,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z287,z104,z4,z6])],[(0,[z0,z1,z2,z3,z485,z4,z6])],[(0,[z653,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z654,z4,z6]),(0,[z59,z0,z1,z2,z3,z4,z60]),(1,[z0,z24,z1,z29,z4,z6]),(0,[z655,z0,z1,z2,z3,z4,z6])],[(0,[z214,z0,z236,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z656,z4,z6]),(0,[z657,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z163,z45])],[(0,[z658,z0,z1,z2,z3,z4,z6]),(0,[z65,z0,z1,z2,z3,z40,z6]),(0,[z250,z0,z1,z2,z12,z4,z6]),(0,[z107,z0,z1,z2,z3,z10,z6]),(0,[z158,z0,z1,z2,z3,z159,z6])],[(1,[z0,z1,z2,z3,z525,z6])],[(0,[z127,z0,z1,z2,z3,z36,z6]),(0,[z0,z1,z2,z95,z3,z4,z6]),(0,[z102,z0,z1,z2,z3,z13,z6]),(0,[z0,z1,z2,z287,z3,z40,z6]),(0,[z0,z1,z2,z3,z40,z6,z106]),(0,[z0,z1,z2,z3,z4,z416,z6]),(1,[z0,z1,z2,z220,z4,z93])]],
   [[(0,[z267,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z659,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z660]),(0,[z0,z1,z661,z2,z3,z4,z6])],[(0,[z107,z65,z1,z2,z3,z4,z6]),(1,[z233,z1,z2,z3,z13,z6]),(0,[z0,z30,z1,z2,z3,z512,z6]),(0,[z0,z1,z662,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z663])],[(0,[z0,z236,z1,z2,z3,z52,z6]),(0,[z0,z1,z2,z187,z3,z4,z6]),(0,[z65,z0,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z664]),(0,[z0,z1,z2,z3,z104,z36,z6]),(0,[z0,z1,z2,z3,z4,z6,z99])],[(0,[z0,z1,z2,z665,z3,z4,z6]),(0,[z0,z24,z1,z2,z3,z52,z6]),(0,[z0,z1,z2,z3,z52,z40,z6]),(0,[z0,z1,z2,z3,z4,z666,z6])],[(0,[z0,z1,z2,z287,z7,z4,z6]),(0,[z0,z32,z1,z2,z3,z40,z6]),(1,[z0,z1,z313,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z106])],[(1,[z0,z1,z2,z7,z36,z6]),(0,[z667,z0,z1,z2,z3,z4,z6])],[(0,[z51,z0,z1,z71,z3,z4,z6])],[(0,[z0,z1,z668,z2,z3,z4,z6])],[(0,[z127,z0,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z12,z4,z36,z6]),(0,[z233,z0,z1,z2,z3,z13,z6]),(0,[z0,z1,z2,z669,z3,z4,z6])],[(0,[z0,z670,z1,z2,z3,z4,z6]),(0,[z0,z32,z1,z2,z7,z4,z6]),(0,[z671,z0,z1,z2,z3,z4,z6])],[(0,[z25,z0,z1,z2,z3,z61,z6]),(1,[z0,z1,z173,z3,z4,z6])],[(0,[z0,z1,z2,z12,z104,z4,z6]),(0,[z0,z1,z2,z3,z13,z13,z6]),(0,[z0,z1,z672,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z673,z4,z6])],[(0,[z0,z1,z2,z674,z3,z4,z6]),(0,[z0,z1,z2,z3,z52,z159,z6]),(0,[z25,z254,z0,z1,z2,z3,z6])],[(1,[z0,z1,z2,z7,z10,z6]),(0,[z0,z1,z2,z3,z675,z4,z6])],[(0,[z25,z51,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z455,z4,z6]),(0,[z0,z676,z1,z2,z3,z4,z6]),(0,[z582,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z677,z2,z3,z4,z6])],[(0,[z678,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z319,z4,z6]),(0,[z679,z0,z1,z2,z3,z4,z6]),(0,[z680,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z295,z8])],[(0,[z0,z1,z2,z681,z3,z4,z6])],[(0,[z0,z1,z90,z2,z3,z36,z6]),(0,[z59,z0,z1,z2,z3,z10,z6]),(0,[z0,z2,z3,z159,z4,z61,z6])],[(0,[z0,z1,z134,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z146,z4,z6]),(0,[z209,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z682,z3,z4,z6])],[(0,[z683,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z39,z2,z3,z40,z6]),(0,[z0,z1,z2,z684,z3,z4,z6]),(0,[z679,z25,z0,z1,z2,z3,z6])],[(0,[z0,z236,z1,z2,z3,z40,z6]),(0,[z0,z1,z2,z3,z4,z398,z6]),(0,[z0,z1,z2,z220,z3,z4,z8]),(1,[z25,z0,z1,z2,z3,z36])],[(0,[z685,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z350,z6]),(0,[z0,z24,z1,z2,z3,z40,z6]),(0,[z0,z1,z2,z3,z648,z4,z6]),(0,[z0,z1,z313,z2,z4,z6,z72])],[(0,[z0,z1,z2,z287,z12,z4,z6]),(0,[z59,z0,z300,z2,z3,z4,z6]),(0,[z686,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z220,z3,z13,z6])],[(0,[z0,z1,z39,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z13,z93,z6]),(0,[z0,z1,z2,z3,z319,z4,z6]),(0,[z0,z1,z2,z3,z52,z218,z6]),(0,[z25,z0,z1,z2,z220,z3,z6])],[(0,[z0,z236,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z10,z573,z6]),(0,[z0,z88,z2,z28,z3,z4,z6]),(0,[z0,z43,z1,z2,z3,z211,z6])],[(0,[z127,z0,z1,z545,z3,z4,z6]),(0,[z0,z1,z90,z2,z3,z10,z6]),(0,[z0,z114,z1,z2,z3,z4,z6]),(0,[z0,z24,z1,z2,z7,z4,z6])],[(0,[z0,z141,z1,z2,z3,z13,z6]),(1,[z0,z1,z2,z109,z4,z6]),(0,[z0,z1,z2,z687,z3,z4,z6]),(0,[z23,z0,z1,z2,z4,z6,z8])],[(0,[z0,z1,z19,z2,z3,z36,z6]),(0,[z25,z0,z1,z2,z3,z159,z6])],[(0,[z0,z1,z2,z3,z4,z6,z447]),(0,[z164,z0,z1,z2,z3,z10,z6]),(0,[z48,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z688,z6]),(0,[z0,z1,z2,z91,z3,z10,z6]),(0,[z0,z1,z2,z3,z4,z6,z8])],[(0,[z0,z1,z2,z126,z4,z116,z6])],[(0,[z0,z1,z2,z3,z12,z36,z6]),(0,[z0,z1,z2,z7,z4,z6,z614]),(0,[z59,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z52,z163,z6]),(0,[z603,z0,z1,z2,z3,z4,z6])],[(0,[z689,z0,z1,z2,z3,z4,z6]),(0,[z48,z25,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z126,z3,z36,z6])],[(0,[z0,z1,z174,z2,z3,z10,z6]),(0,[z0,z1,z2,z144,z3,z4,z6])],[(0,[z0,z690,z1,z2,z3,z4,z6]),(0,[z279,z0,z1,z2,z3,z13,z6]),(0,[z691,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z578,z3,z40,z6])],[(1,[z65,z1,z2,z12,z4,z6]),(0,[z59,z25,z0,z1,z2,z3,z6]),(0,[z0,z692,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z126,z287,z4,z6])],[(0,[z48,z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z10,z354,z6]),(0,[z0,z1,z2,z3,z693,z4,z6]),(0,[z250,z0,z1,z2,z3,z40,z6]),(0,[z0,z1,z2,z3,z36,z6,z8])],[(1,[z0,z285,z2,z3,z4,z6]),(0,[z0,z1,z2,z7,z4,z116,z6]),(0,[z369,z0,z1,z2,z3,z13,z6]),(0,[z0,z694,z1,z2,z3,z4,z6]),(0,[z695,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z66,z4,z36])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z696,z6])],[(0,[z0,z1,z2,z7,z3,z36,z6]),(0,[z267,z0,z1,z2,z3,z40,z6]),(0,[z0,z1,z2,z3,z4,z45,z22]),(0,[z697,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z698,z6]),(0,[z0,z1,z2,z699,z3,z4,z6])],[(0,[z0,z1,z2,z3,z12,z10,z6]),(0,[z0,z1,z2,z28,z3,z36,z6]),(0,[z0,z1,z2,z29,z3,z36,z6]),(0,[z0,z1,z2,z700,z3,z4,z6])],[(0,[z0,z1,z701,z2,z3,z4,z6]),(0,[z250,z0,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z126,z3,z10,z6]),(0,[z0,z702,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z703,z3,z4,z6]),(0,[z158,z0,z1,z2,z3,z61,z6]),(0,[z0,z704,z1,z2,z3,z4,z6])],[],[(0,[z0,z1,z705,z2,z3,z4,z6]),(0,[z0,z44,z1,z2,z3,z36,z6]),(0,[z0,z43,z1,z2,z3,z36,z6]),(0,[z25,z0,z1,z2,z140,z3,z6])],[(0,[z267,z0,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z91,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z706,z6]),(0,[z0,z1,z2,z3,z4,z489,z6]),(0,[z658,z0,z1,z2,z3,z40,z6]),(0,[z23,z0,z1,z2,z3,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z707,z6]),(0,[z0,z1,z2,z249,z36,z6]),(0,[z0,z1,z49,z3,z36,z218])],[(0,[z25,z0,z285,z2,z3,z6]),(0,[z0,z1,z708,z2,z3,z6]),(0,[z709,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z387,z116,z6])],[(0,[z653,z1,z2,z3,z4,z45]),(0,[z0,z1,z2,z710,z4,z6]),(0,[z0,z1,z2,z3,z4,z711])],[(0,[z0,z1,z2,z3,z712,z6]),(0,[z0,z1,z2,z3,z713,z6]),(0,[z1,z2,z714,z3,z4,z6]),(0,[z0,z1,z2,z3,z715,z6]),(0,[z0,z1,z110,z3,z399,z6]),(0,[z0,z1,z2,z144,z383,z6]),(0,[z0,z1,z173,z716,z3,z6])],[(0,[z0,z1,z2,z3,z717,z6]),(0,[z50,z1,z35,z3,z10,z6])],[(0,[z0,z1,z2,z3,z4,z718]),(0,[z461,z1,z2,z3,z4,z45]),(0,[z0,z1,z2,z3,z719,z6]),(0,[z25,z0,z1,z2,z6,z381]),(0,[z0,z1,z2,z3,z720,z6]),(0,[z0,z1,z3,z721,z40,z6]),(0,[z0,z1,z2,z722,z4,z6]),(0,[z0,z1,z2,z3,z723,z6])],[(0,[z0,z724,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z725,z6]),(0,[z0,z1,z2,z3,z726,z6]),(0,[z107,z1,z2,z7,z36,z6]),(0,[z25,z0,z1,z2,z3,z711])],[(0,[z0,z1,z2,z3,z727,z6])],[(0,[z0,z1,z2,z3,z728,z6]),(0,[z0,z1,z2,z3,z470,z6])],[(0,[z0,z1,z2,z249,z10,z6]),(0,[z0,z1,z2,z729,z4,z6]),(0,[z0,z1,z49,z3,z10,z218]),(0,[z0,z1,z2,z484,z573,z6]),(0,[z0,z1,z2,z3,z730,z6])],[(0,[z0,z1,z266,z3,z4,z70]),(0,[z0,z1,z2,z27,z104,z6]),(0,[z0,z1,z2,z287,z533,z6]),(0,[z0,z24,z1,z173,z3,z6]),(0,[z0,z1,z3,z40,z6,z601]),(0,[z0,z1,z192,z173,z3,z6])],[(0,[z127,z90,z2,z3,z36,z6]),(0,[z1,z2,z714,z12,z4,z6]),(0,[z0,z1,z2,z12,z383,z6]),(0,[z0,z1,z2,z3,z731,z6]),(0,[z0,z1,z732,z3,z4,z6]),(0,[z107,z25,z1,z2,z7,z6]),(0,[z0,z1,z2,z4,z6,z733]),(0,[z0,z1,z2,z220,z4,z734])],[(0,[z254,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z3,z735,z6])],[(0,[z0,z1,z2,z3,z4,z736]),(0,[z214,z236,z2,z3,z52,z6]),(0,[z737,z0,z1,z2,z3,z6]),(0,[z0,z1,z213,z3,z52,z6]),(0,[z0,z1,z173,z3,z6,z106])],[(0,[z59,z1,z2,z3,z4,z738]),(0,[z0,z739,z1,z2,z3,z6]),(0,[z0,z30,z2,z120,z36,z6]),(0,[z25,z0,z1,z740,z3,z6]),(0,[z741,z0,z1,z173,z3,z6]),(0,[z25,z0,z1,z31,z3,z36]),(0,[z25,z0,z742,z2,z3,z6])],[(0,[z0,z1,z2,z3,z52,z374]),(0,[z107,z1,z2,z7,z10,z6]),(0,[z0,z1,z3,z52,z399,z6]),(0,[z0,z1,z2,z3,z743,z6])]],
   [[(0,[z0,z1,z2,z274,z36,z6]),(0,[z0,z88,z2,z428,z4,z6]),(0,[z0,z744,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z745,z6]),(0,[z0,z1,z49,z3,z4,z450]),(0,[z0,z1,z2,z3,z746,z6]),(0,[z0,z1,z2,z747,z4,z6]),(1,[z0,z1,z3,z4,z748])],[(0,[z0,z1,z2,z3,z749,z6]),(0,[z0,z1,z2,z3,z403,z6]),(0,[z0,z1,z471,z3,z40,z6])],[(0,[z0,z430,z2,z3,z40,z6]),(0,[z0,z1,z2,z307,z4,z167]),(0,[z0,z1,z2,z224,z7,z6]),(0,[z25,z0,z1,z2,z3,z644]),(0,[z0,z1,z313,z2,z13,z6]),(0,[z0,z1,z2,z3,z750,z6]),(0,[z25,z0,z1,z751,z3,z6])],[(0,[z127,z90,z2,z3,z10,z6]),(0,[z0,z1,z2,z3,z752,z6]),(0,[z283,z0,z1,z2,z12,z6]),(0,[z0,z1,z2,z3,z753,z6]),(0,[z0,z1,z173,z173,z3,z6])],[(0,[z0,z1,z134,z81,z4,z6]),(0,[z0,z1,z2,z92,z13,z6]),(0,[z210,z0,z1,z754,z3,z6]),(0,[z267,z1,z2,z3,z36,z45]),(0,[z0,z1,z2,z3,z755,z6]),(0,[z0,z1,z3,z756,z4,z6]),(0,[z258,z0,z1,z2,z3,z72])],[(1,[z0,z1,z173,z7,z6]),(0,[z0,z1,z2,z3,z757,z6]),(0,[z369,z0,z21,z2,z4,z22]),(0,[z0,z1,z2,z758,z40,z6]),(0,[z0,z1,z177,z173,z3,z6])],[(0,[z0,z1,z2,z3,z6,z759]),(0,[z0,z30,z2,z120,z10,z6]),(0,[z760,z1,z2,z3,z4,z6])],[(0,[z0,z430,z2,z7,z4,z6]),(0,[z0,z1,z3,z40,z60,z72]),(0,[z0,z1,z313,z40,z6,z72])],[(0,[z0,z1,z2,z274,z10,z6]),(0,[z0,z122,z2,z120,z4,z6]),(0,[z0,z1,z2,z7,z354,z6]),(0,[z369,z0,z2,z3,z4,z22]),(0,[z0,z1,z31,z3,z4,z6]),(0,[z587,z0,z1,z2,z3,z36]),(0,[z0,z1,z2,z761,z4,z6])],[(0,[z0,z1,z90,z173,z3,z6]),(0,[z51,z1,z71,z3,z13,z6]),(0,[z0,z2,z12,z4,z6,z762]),(0,[z0,z1,z2,z3,z763,z6]),(0,[z0,z1,z2,z3,z485,z6])],[(0,[z0,z1,z2,z358,z4,z93]),(0,[z492,z1,z2,z3,z13,z6])],[(0,[z764,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z7,z222,z6]),(0,[z283,z267,z1,z2,z3,z45]),(0,[z25,z0,z1,z2,z3,z80]),(0,[z283,z0,z1,z173,z3,z6])],[(0,[z0,z1,z2,z3,z765,z4]),(0,[z766,z0,z1,z2,z3,z6]),(0,[z767,z0,z1,z2,z3,z6]),(0,[z0,z30,z2,z474,z4,z6]),(0,[z0,z1,z2,z3,z768,z6]),(0,[z0,z1,z2,z3,z415,z6]),(0,[z0,z1,z2,z769,z4,z6]),(0,[z0,z1,z2,z4,z770,z6]),(0,[z25,z0,z1,z2,z3,z106])],[(0,[z267,z1,z2,z3,z10,z45]),(0,[z0,z1,z2,z3,z771,z6]),(0,[z59,z1,z2,z3,z128,z60])],[(0,[z0,z1,z2,z3,z118,z374]),(0,[z0,z1,z314,z3,z4,z6]),(0,[z1,z2,z3,z364,z13,z6]),(0,[z0,z1,z366,z3,z40,z6]),(0,[z0,z772,z1,z2,z3,z6]),(0,[z0,z773,z1,z2,z3,z6]),(0,[z520,z1,z2,z3,z155,z6])]],
   [[(0,[z200,z1,z2,z3,z13,z6]),(0,[z0,z1,z774,z2,z3,z6]),(0,[z0,z1,z2,z3,z775,z6])],[(0,[z551,z0,z1,z3,z4,z72]),(0,[z369,z0,z2,z12,z4,z22]),(0,[z0,z1,z31,z12,z4,z6]),(0,[z267,z0,z1,z173,z3,z6]),(0,[z0,z21,z1,z2,z36,z6])],[(0,[z0,z1,z3,z168,z6,z72]),(0,[z0,z1,z2,z7,z277,z6]),(0,[z0,z1,z2,z370,z40,z6]),(0,[z0,z2,z776,z120,z4,z6]),(0,[z0,z1,z2,z777,z3,z6]),(0,[z0,z1,z2,z3,z778,z6]),(0,[z0,z1,z2,z287,z104,z6]),(0,[z25,z0,z1,z779,z3,z6])],[(0,[z0,z1,z266,z270,z4,z6]),(0,[z0,z1,z780,z3,z4,z6]),(0,[z0,z1,z2,z3,z781,z6]),(0,[z0,z1,z2,z3,z40,z374]),(0,[z0,z1,z2,z7,z782,z6]),(0,[z783,z1,z2,z3,z4,z6])],[(0,[z0,z645,z1,z3,z40,z6]),(0,[z0,z1,z2,z7,z215,z6]),(0,[z0,z1,z366,z7,z4,z6])],[(0,[z0,z1,z2,z12,z765,z4]),(0,[z0,z1,z2,z12,z415,z6]),(0,[z59,z1,z2,z3,z6,z317]),(0,[z0,z225,z1,z3,z52,z6]),(0,[z25,z0,z1,z31,z3,z6])],[(0,[z25,z0,z1,z784,z3,z6])],[(0,[z0,z1,z35,z3,z6,z99]),(0,[z0,z1,z2,z7,z785,z6]),(0,[z0,z1,z2,z7,z204,z6]),(0,[z0,z1,z2,z3,z786,z6]),(0,[z0,z1,z2,z3,z787,z6]),(0,[z0,z1,z2,z788,z3,z6])],[(0,[z127,z90,z545,z3,z4,z6]),(0,[z0,z1,z2,z3,z789,z6]),(0,[z0,z1,z2,z7,z4,z374]),(0,[z0,z136,z1,z2,z7,z6]),(0,[z59,z1,z366,z3,z4,z60]),(0,[z0,z1,z677,z3,z40,z6])],[(0,[z25,z0,z1,z2,z319,z6]),(0,[z0,z1,z2,z3,z790,z6]),(0,[z0,z1,z2,z791,z4,z6]),(0,[z258,z0,z1,z49,z3,z6]),(0,[z0,z1,z173,z3,z6,z8])],[(0,[z258,z0,z1,z2,z7,z6]),(0,[z0,z21,z1,z2,z10,z6]),(0,[z0,z1,z2,z3,z792,z6]),(0,[z0,z1,z2,z3,z6,z99]),(0,[z0,z1,z2,z3,z793,z6])],[(0,[z0,z430,z2,z3,z4,z167]),(0,[z0,z1,z2,z3,z794,z6]),(0,[z795,z0,z1,z2,z3,z6]),(0,[z0,z1,z796,z3,z4,z6]),(0,[z0,z1,z2,z797,z4,z6])],[(0,[z0,z430,z2,z12,z4,z6]),(0,[z798,z0,z1,z2,z3,z374]),(0,[z0,z1,z2,z7,z13,z6]),(0,[z0,z1,z2,z103,z36,z6]),(0,[z799,z0,z1,z2,z4,z6])],[(0,[z0,z24,z1,z95,z4,z6]),(0,[z0,z1,z2,z3,z800,z6]),(0,[z0,z801,z1,z173,z3,z6])],[(0,[z802,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z803,z6]),(0,[z0,z1,z2,z4,z6,z804]),(0,[z0,z1,z2,z12,z128,z6]),(0,[z0,z1,z132,z2,z12,z6]),(0,[z0,z1,z2,z3,z36,z172]),(0,[z0,z1,z3,z40,z6,z639]),(0,[z0,z24,z1,z29,z299,z6]),(0,[z0,z1,z76,z3,z40,z6])],[(0,[z0,z1,z2,z12,z416,z6]),(0,[z1,z2,z3,z13,z6,z317]),(0,[z520,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z3,z805,z6]),(0,[z0,z44,z192,z2,z3,z6]),(0,[z0,z1,z806,z3,z4,z6]),(0,[z0,z1,z2,z52,z6,z135]),(0,[z25,z0,z1,z807,z3,z6])]],
   [[(0,[z0,z1,z2,z484,z116,z6]),(0,[z59,z1,z2,z3,z13,z60]),(0,[z0,z1,z366,z144,z4,z6])],[(0,[z0,z1,z2,z3,z808,z6]),(0,[z0,z1,z2,z809,z4,z6]),(0,[z25,z0,z30,z2,z120,z6]),(0,[z0,z88,z2,z28,z36,z6]),(0,[z158,z0,z2,z3,z459,z6]),(0,[z0,z1,z2,z3,z6,z810])],[(0,[z0,z811,z2,z3,z4,z6]),(0,[z0,z1,z2,z109,z398,z6]),(0,[z812,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z813,z6]),(0,[z0,z1,z2,z7,z814,z6]),(0,[z0,z1,z110,z146,z4,z6]),(0,[z0,z1,z2,z173,z3,z6]),(0,[z0,z1,z2,z815,z4,z6])],[(0,[z0,z1,z2,z3,z4,z447]),(0,[z0,z816,z2,z3,z4,z6]),(0,[z0,z1,z2,z817,z3,z6])],[(0,[z0,z1,z2,z54,z13,z6]),(0,[z0,z1,z2,z103,z10,z6]),(0,[z283,z136,z1,z2,z3,z6]),(0,[z0,z1,z2,z382,z40,z6]),(0,[z0,z1,z818,z26,z4,z6]),(0,[z0,z490,z2,z3,z100,z6]),(0,[z0,z1,z819,z3,z36,z6])],[(0,[z0,z1,z820,z3,z4,z6]),(0,[z283,z0,z1,z821,z3,z6]),(0,[z0,z1,z2,z3,z822,z6])],[(0,[z823,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z824,z6]),(0,[z0,z1,z2,z3,z825,z6]),(0,[z0,z1,z2,z826,z7,z6]),(0,[z369,z0,z2,z3,z52,z22]),(0,[z0,z1,z31,z3,z52,z6])],[(0,[z25,z0,z1,z2,z3,z447]),(0,[z1,z2,z12,z4,z6,z178]),(0,[z0,z1,z2,z144,z13,z6]),(0,[z0,z1,z2,z177,z3,z6]),(0,[z0,z1,z2,z3,z6,z827])],[(0,[z0,z1,z2,z3,z828,z6]),(0,[z0,z1,z2,z829,z4,z6]),(0,[z464,z1,z2,z3,z13,z6]),(0,[z0,z1,z2,z830,z4,z6])],[(0,[z214,z236,z2,z12,z4,z6]),(0,[z0,z1,z2,z307,z118,z6]),(0,[z0,z1,z3,z831,z4,z6]),(0,[z0,z1,z832,z3,z4,z6]),(0,[z0,z88,z2,z28,z10,z6]),(0,[z0,z1,z2,z3,z696,z36])],[(0,[z0,z833,z1,z2,z3,z6]),(0,[z23,z0,z1,z2,z4,z357]),(0,[z48,z0,z1,z3,z36,z72])],[(0,[z0,z1,z2,z3,z11,z447]),(0,[z0,z1,z2,z12,z4,z447]),(0,[z0,z1,z2,z3,z834,z6]),(0,[z0,z835,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z836])],[(0,[z0,z1,z2,z3,z837,z6]),(0,[z1,z2,z3,z188,z10,z6]),(0,[z0,z1,z314,z3,z52,z6]),(0,[z0,z1,z2,z36,z6,z381]),(0,[z0,z1,z838,z2,z3,z6])],[(0,[z0,z1,z2,z3,z839,z6]),(0,[z0,z1,z2,z307,z40,z6]),(0,[z0,z1,z2,z194,z7,z6]),(0,[z0,z1,z2,z3,z398,z6]),(0,[z1,z2,z3,z10,z840,z6]),(0,[z0,z1,z2,z3,z841,z6])],[(0,[z0,z1,z2,z3,z13,z167]),(0,[z0,z1,z49,z3,z416,z6]),(0,[z0,z1,z2,z3,z842,z6])]],
   [[(0,[z0,z1,z2,z454,z482,z6]),(0,[z0,z843,z2,z3,z4,z6]),(0,[z0,z1,z173,z3,z45,z6]),(0,[z0,z1,z2,z844,z4,z6])],[(0,[z0,z1,z2,z3,z845,z6]),(0,[z0,z1,z2,z846,z4,z6]),(1,[z0,z1,z2,z4,z734]),(0,[z0,z1,z2,z220,z221,z93])],[(0,[z0,z1,z2,z3,z847,z6])],[(0,[z25,z65,z1,z2,z12,z6]),(0,[z0,z1,z2,z3,z848,z6]),(0,[z637,z1,z2,z12,z4,z6]),(0,[z1,z2,z12,z4,z6,z306]),(0,[z0,z141,z1,z3,z399,z6]),(0,[z0,z1,z2,z3,z849,z6])],[(0,[z0,z1,z545,z3,z36,z6]),(0,[z0,z1,z850,z3,z4,z6]),(0,[z0,z1,z2,z3,z851,z6]),(0,[z390,z0,z2,z3,z4,z22]),(0,[z48,z0,z1,z3,z10,z72]),(0,[z0,z1,z2,z3,z852,z6]),(0,[z539,z0,z1,z2,z3,z139])],[(0,[z1,z2,z7,z12,z36,z6]),(0,[z0,z1,z2,z405,z4,z6]),(0,[z102,z1,z2,z3,z467,z6])],[(0,[z0,z1,z2,z3,z56,z447]),(0,[z0,z1,z2,z274,z52,z6]),(0,[z0,z1,z2,z12,z398,z6]),(0,[z0,z1,z2,z3,z36,z469]),(0,[z0,z88,z1,z173,z3,z6]),(0,[z0,z1,z3,z40,z6,z99])],[(0,[z0,z1,z2,z3,z853,z6]),(0,[z199,z1,z2,z12,z4,z6]),(0,[z0,z300,z2,z3,z151,z6]),(0,[z0,z1,z3,z756,z40,z6]),(0,[z0,z1,z2,z791,z52,z6])],[(0,[z85,z0,z2,z3,z123,z6]),(0,[z0,z1,z2,z3,z854,z6])],[(0,[z0,z1,z2,z454,z36,z6]),(0,[z0,z1,z2,z3,z855,z6]),(0,[z0,z1,z2,z3,z467,z6]),(0,[z0,z1,z2,z12,z856,z6]),(0,[z0,z1,z2,z857,z12,z6]),(0,[z0,z1,z2,z7,z403,z6]),(0,[z267,z1,z2,z3,z4,z738]),(0,[z0,z88,z2,z28,z4,z6]),(0,[z0,z1,z2,z3,z858,z6]),(0,[z25,z0,z1,z2,z3,z89])],[(0,[z0,z1,z2,z859,z4,z6]),(0,[z0,z1,z2,z860,z4,z6]),(0,[z0,z1,z2,z3,z861,z6]),(0,[z0,z1,z173,z35,z3,z6]),(0,[z0,z1,z2,z3,z862,z6]),(0,[z0,z1,z2,z12,z863,z6]),(0,[z0,z1,z754,z3,z4,z6])],[(0,[z267,z1,z2,z3,z52,z45]),(0,[z369,z0,z2,z3,z40,z22]),(0,[z0,z1,z31,z3,z40,z6]),(0,[z0,z1,z49,z173,z3,z6])],[(0,[z0,z501,z2,z474,z4,z6]),(0,[z0,z32,z91,z3,z13,z6]),(0,[z0,z1,z2,z864,z3,z6]),(0,[z0,z1,z2,z3,z865,z6]),(0,[z0,z1,z2,z3,z866,z6]),(0,[z0,z1,z2,z867,z4,z6])],[(0,[z0,z1,z545,z3,z10,z6]),(0,[z0,z868,z1,z2,z4,z6]),(0,[z0,z1,z869,z2,z3,z6]),(0,[z25,z0,z1,z173,z12,z6]),(0,[z1,z2,z3,z10,z13,z6]),(0,[z0,z1,z2,z3,z870,z6]),(0,[z0,z1,z871,z2,z3,z6])],[(0,[z0,z1,z2,z3,z872,z6]),(0,[z1,z2,z7,z12,z10,z6]),(0,[z0,z1,z2,z3,z873,z6])],[(0,[z142,z0,z2,z3,z186,z6]),(0,[z164,z0,z1,z3,z52,z6]),(0,[z0,z1,z874,z3,z4,z6]),(0,[z158,z0,z2,z3,z6,z345])]],
   [[(0,[z210,z0,z1,z2,z7,z6]),(0,[z369,z0,z2,z7,z4,z22]),(0,[z0,z1,z31,z7,z4,z6]),(0,[z0,z1,z2,z875,z3,z6]),(0,[z0,z1,z2,z876,z4,z6]),(0,[z0,z1,z173,z3,z66,z6])],[(0,[z25,z0,z1,z2,z189,z6]),(0,[z1,z2,z3,z222,z10,z6]),(0,[z0,z1,z314,z3,z40,z6]),(0,[z0,z1,z2,z3,z877,z6]),(0,[z0,z1,z2,z287,z559,z6]),(0,[z0,z1,z2,z3,z878,z6])],[(0,[z0,z1,z2,z3,z52,z447]),(0,[z0,z1,z2,z3,z879,z447]),(0,[z0,z1,z2,z454,z10,z6]),(0,[z0,z430,z2,z3,z118,z6]),(0,[z0,z1,z2,z3,z880,z6]),(0,[z1,z2,z669,z7,z4,z6]),(0,[z507,z1,z2,z7,z4,z6])],[(0,[z0,z1,z2,z12,z470,z6])],[(0,[z0,z493,z2,z322,z4,z6]),(0,[z0,z1,z2,z7,z415,z6]),(0,[z0,z881,z1,z2,z3,z6]),(0,[z0,z24,z1,z29,z36,z6]),(0,[z0,z1,z2,z3,z882,z6]),(0,[z0,z1,z2,z883,z36,z6])],[(0,[z50,z285,z35,z3,z4,z6]),(0,[z0,z1,z2,z3,z884,z6])],[(0,[z50,z1,z35,z3,z4,z6]),(0,[z0,z1,z314,z7,z4,z6]),(0,[z0,z1,z2,z3,z885,z6])],[(0,[z0,z1,z2,z3,z489,z6]),(0,[z0,z1,z76,z3,z198,z6])],[(0,[z0,z1,z2,z3,z66,z36]),(0,[z0,z1,z2,z3,z6,z711])],[(0,[z0,z1,z886,z3,z4,z6]),(0,[z0,z1,z2,z3,z887,z6]),(0,[z0,z1,z547,z3,z40,z6]),(0,[z0,z1,z751,z3,z4,z6])],[(0,[z0,z1,z2,z3,z888,z6]),(0,[z214,z0,z1,z173,z3,z6]),(0,[z59,z1,z314,z3,z4,z60])],[(0,[z0,z1,z2,z249,z4,z6]),(0,[z0,z1,z2,z3,z6,z889]),(0,[z890,z0,z1,z2,z3,z6]),(0,[z0,z1,z49,z3,z4,z218]),(0,[z0,z1,z2,z204,z6,z135]),(0,[z0,z1,z173,z3,z104,z6])],[],[(0,[z0,z1,z2,z3,z891,z6]),(0,[z0,z1,z2,z3,z255,z6]),(0,[z25,z0,z1,z2,z249,z6]),(0,[z0,z1,z2,z12,z403,z6]),(0,[z0,z1,z2,z7,z128,z6]),(0,[z0,z493,z2,z28,z4,z6]),(0,[z0,z24,z1,z29,z10,z6])],[(0,[z50,z1,z35,z12,z4,z6]),(0,[z539,z0,z1,z2,z12,z6]),(0,[z0,z1,z2,z7,z416,z6]),(0,[z0,z892,z1,z2,z3,z6]),(0,[z267,z1,z2,z3,z350,z45]),(1,[z0,z874,z3,z4,z6]),(0,[z893,z1,z2,z3,z4,z6]),(0,[z0,z894,z2,z3,z4,z6]),(0,[z0,z1,z2,z895,z4,z6])],[(0,[z0,z1,z2,z12,z489,z6])]],
   [[(0,[z0,z1,z2,z3,z13,z70]),(0,[z25,z214,z236,z2,z3,z6]),(0,[z0,z57,z2,z428,z4,z6]),(0,[z0,z1,z896,z3,z4,z6]),(0,[z0,z1,z2,z3,z897,z6])],[(0,[z0,z1,z2,z280,z346,z6]),(0,[z107,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z898,z6]),(0,[z0,z1,z2,z899,z4,z6]),(0,[z0,z1,z49,z3,z467,z6])],[(0,[z900,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z7,z794,z6]),(0,[z283,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z103,z52,z6]),(0,[z0,z1,z314,z144,z4,z6]),(0,[z158,z0,z2,z3,z159,z6]),(0,[z0,z1,z2,z3,z901,z6])],[(0,[z1,z2,z3,z467,z292,z6]),(0,[z0,z1,z49,z12,z4,z218]),(0,[z0,z1,z2,z405,z52,z6]),(0,[z0,z1,z173,z3,z36,z6])],[(0,[z214,z236,z2,z3,z40,z6]),(0,[z0,z251,z366,z3,z4,z6]),(0,[z267,z1,z2,z109,z4,z45]),(0,[z0,z1,z2,z902,z4,z6]),(0,[z250,z0,z1,z3,z52,z6])],[(0,[z0,z1,z2,z3,z903,z6]),(0,[z0,z1,z2,z12,z255,z6]),(0,[z0,z1,z2,z12,z485,z6]),(0,[z25,z0,z1,z2,z7,z106]),(0,[z0,z1,z2,z3,z904,z6]),(0,[z0,z1,z2,z3,z905,z6]),(0,[z283,z254,z1,z2,z3,z6])],[(0,[z127,z90,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z40,z447]),(0,[z0,z1,z2,z3,z906,z6]),(0,[z25,z136,z1,z2,z12,z6]),(0,[z0,z1,z2,z3,z907,z6]),(0,[z539,z0,z1,z173,z3,z6]),(0,[z0,z1,z2,z4,z93,z734])],[(0,[z65,z1,z2,z12,z69,z6]),(0,[z136,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z3,z908,z6]),(0,[z0,z88,z2,z28,z52,z6])],[(0,[z0,z1,z2,z3,z67,z6]),(0,[z0,z141,z19,z3,z86,z6])],[(0,[z909,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z910,z4,z6]),(0,[z214,z236,z2,z7,z4,z6]),(0,[z107,z1,z2,z714,z4,z6]),(0,[z85,z0,z2,z3,z159,z6]),(0,[z0,z30,z2,z120,z4,z6]),(0,[z911,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z912,z4,z6]),(0,[z0,z1,z2,z3,z69,z6]),(0,[z0,z1,z314,z12,z4,z6]),(0,[z210,z0,z1,z2,z3,z14]),(0,[z0,z1,z2,z319,z36,z6]),(0,[z0,z1,z2,z3,z913,z6]),(0,[z0,z1,z2,z914,z4,z6]),(0,[z0,z1,z2,z3,z915,z6]),(0,[z0,z916,z1,z2,z3,z6])],[(0,[z0,z1,z2,z7,z4,z447]),(0,[z0,z1,z2,z274,z4,z6]),(0,[z0,z1,z2,z3,z221,z6])],[(0,[z0,z1,z2,z3,z917,z6]),(0,[z0,z251,z2,z3,z13,z6]),(0,[z0,z1,z173,z3,z10,z6])],[(0,[z0,z1,z918,z3,z4,z6]),(0,[z0,z1,z2,z919,z4,z6]),(0,[z426,z1,z2,z3,z4,z60])],[(0,[z127,z90,z2,z3,z11,z6]),(0,[z127,z90,z2,z12,z4,z6]),(0,[z0,z1,z2,z920,z12,z6]),(0,[z0,z1,z2,z3,z921,z6])],[(0,[z922,z0,z1,z2,z3,z6]),(0,[z102,z1,z2,z319,z10,z6]),(0,[z0,z1,z2,z923,z3,z6]),(0,[z0,z1,z2,z126,z605,z6])]],
   [[(0,[z0,z236,z2,z3,z4,z447]),(0,[z0,z1,z2,z189,z482,z6]),(0,[z0,z1,z2,z12,z67,z6]),(0,[z267,z1,z2,z3,z4,z45]),(0,[z0,z1,z2,z3,z924,z6])],[(0,[z0,z1,z925,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z926]),(0,[z0,z1,z875,z3,z4,z6]),(0,[z0,z1,z3,z448,z40,z72])],[(0,[z0,z1,z2,z3,z927,z6]),(0,[z0,z1,z2,z928,z4,z6])],[(0,[z214,z136,z1,z2,z3,z6]),(0,[z0,z1,z2,z12,z221,z6]),(0,[z0,z1,z2,z3,z6,z929]),(0,[z25,z0,z24,z1,z29,z6])],[(0,[z0,z1,z266,z3,z13,z6]),(0,[z50,z1,z35,z3,z52,z6]),(0,[z0,z1,z2,z13,z6,z381]),(0,[z0,z2,z3,z159,z930,z6])],[(0,[z0,z1,z2,z12,z6,z99]),(0,[z0,z1,z134,z3,z40,z6]),(0,[z0,z1,z2,z7,z398,z6]),(0,[z406,z0,z1,z173,z3,z6]),(0,[z679,z0,z1,z173,z3,z6])],[(0,[z0,z1,z2,z931,z4,z6]),(0,[z1,z2,z703,z7,z4,z6]),(0,[z1,z2,z3,z4,z738,z60]),(0,[z0,z1,z2,z109,z36,z6])],[(0,[z0,z1,z2,z405,z40,z6]),(0,[z0,z141,z874,z3,z4,z6]),(0,[z0,z30,z2,z120,z46,z6]),(0,[z0,z1,z2,z710,z40,z6])],[(0,[z127,z90,z2,z3,z56,z6]),(0,[z267,z1,z2,z12,z4,z45]),(0,[z0,z300,z2,z3,z36,z6]),(0,[z0,z1,z2,z3,z4,z932]),(0,[z0,z1,z39,z173,z3,z6]),(0,[z0,z1,z542,z3,z40,z6])],[(0,[z0,z1,z2,z3,z482,z6]),(0,[z0,z1,z2,z270,z13,z6]),(0,[z0,z933,z2,z3,z4,z6]),(0,[z0,z1,z2,z189,z36,z6]),(0,[z0,z1,z2,z249,z52,z6]),(0,[z0,z1,z2,z3,z934,z6]),(0,[z0,z650,z1,z3,z52,z6]),(0,[z0,z1,z49,z3,z52,z218]),(0,[z25,z0,z1,z2,z3,z139]),(0,[z25,z0,z1,z313,z2,z6])],[(0,[z0,z1,z2,z3,z935,z6]),(0,[z0,z251,z2,z382,z4,z6]),(0,[z0,z251,z2,z3,z383,z6]),(0,[z0,z1,z2,z722,z40,z6]),(0,[z0,z1,z2,z936,z3,z6]),(0,[z23,z0,z1,z2,z4,z734])],[(0,[z0,z937,z1,z2,z3,z6]),(0,[z0,z68,z91,z3,z4,z6]),(0,[z0,z1,z2,z280,z4,z374]),(0,[z0,z1,z2,z3,z155,z6]),(0,[z0,z1,z2,z173,z7,z6]),(0,[z695,z1,z2,z3,z13,z6]),(0,[z0,z32,z1,z173,z3,z6]),(0,[z0,z490,z2,z3,z159,z6]),(0,[z0,z938,z2,z3,z4,z6])],[(0,[z0,z1,z2,z939,z4,z6]),(0,[z25,z0,z1,z2,z12,z36]),(0,[z0,z21,z1,z2,z4,z6]),(0,[z0,z1,z2,z177,z6,z135]),(0,[z0,z1,z2,z940,z4,z6]),(0,[z23,z0,z1,z2,z224,z8]),(0,[z25,z0,z1,z2,z220,z93])],[(0,[z0,z1,z134,z12,z40,z6]),(0,[z560,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z941,z6]),(0,[z0,z1,z2,z4,z6,z942])],[(0,[z0,z1,z943,z2,z3,z6]),(0,[z0,z1,z2,z3,z944,z6]),(0,[z0,z1,z2,z945,z36,z6])],[(0,[z0,z1,z2,z454,z52,z6]),(0,[z0,z1,z2,z280,z13,z6]),(0,[z0,z1,z2,z3,z946,z6]),(0,[z65,z1,z2,z12,z36,z6]),(0,[z107,z1,z2,z7,z52,z6]),(0,[z0,z1,z2,z3,z36,z610])]],
   [[(1,[z933,z2,z3,z4,z6]),(0,[z0,z1,z2,z307,z346,z6]),(0,[z0,z1,z2,z3,z947,z6]),(0,[z0,z1,z2,z7,z467,z6]),(0,[z0,z114,z1,z29,z4,z6]),(0,[z0,z1,z2,z948,z4,z6]),(0,[z0,z1,z2,z949,z4,z6]),(0,[z0,z1,z2,z3,z36,z591])],[(0,[z0,z1,z2,z3,z950,z6]),(0,[z0,z285,z2,z3,z36,z6]),(0,[z0,z300,z2,z3,z10,z6]),(0,[z0,z1,z29,z3,z399,z6]),(0,[z0,z141,z19,z3,z36,z6]),(0,[z0,z1,z2,z3,z6,z951])],[(0,[z0,z1,z2,z3,z36,z6]),(0,[z0,z1,z2,z189,z10,z6]),(0,[z0,z1,z2,z7,z470,z6]),(0,[z0,z1,z2,z876,z40,z6])],[(0,[z0,z1,z2,z12,z155,z6]),(0,[z279,z0,z1,z173,z3,z6])],[(0,[z127,z90,z2,z3,z52,z6]),(0,[z0,z1,z2,z3,z952,z6]),(0,[z50,z1,z35,z3,z118,z6]),(0,[z646,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z3,z953,z6]),(0,[z25,z0,z1,z173,z3,z36])],[(0,[z23,z0,z1,z2,z13,z8]),(0,[z25,z0,z1,z2,z3,z275]),(0,[z0,z1,z2,z3,z6,z954]),(0,[z0,z1,z2,z3,z955,z6])],[],[(0,[z0,z1,z2,z103,z4,z6]),(0,[z1,z63,z2,z7,z4,z6]),(0,[z102,z1,z2,z3,z10,z6]),(0,[z233,z0,z1,z173,z3,z6]),(0,[z0,z30,z2,z120,z52,z6]),(0,[z0,z1,z2,z3,z6,z956])],[(0,[z50,z1,z35,z3,z40,z6]),(0,[z0,z1,z2,z957,z4,z6]),(0,[z0,z1,z2,z3,z55,z6]),(0,[z0,z1,z2,z3,z958,z6])],[(0,[z0,z1,z2,z959,z4,z6]),(0,[z0,z1,z2,z274,z82,z6]),(0,[z0,z1,z2,z960,z3,z6])],[(0,[z0,z961,z2,z3,z4,z6]),(0,[z0,z1,z2,z962,z3,z6]),(0,[z1,z2,z3,z13,z651,z6]),(0,[z0,z141,z19,z3,z10,z6])],[(0,[z0,z1,z2,z3,z10,z6]),(0,[z25,z0,z1,z2,z963,z6])],[(0,[z0,z1,z2,z3,z964,z6]),(0,[z0,z1,z35,z3,z399,z6]),(0,[z0,z1,z2,z3,z965,z6])],[(0,[z0,z966,z1,z2,z4,z6]),(0,[z50,z1,z35,z7,z4,z6]),(0,[z0,z1,z2,z3,z967,z6]),(0,[z0,z1,z366,z382,z4,z6]),(0,[z0,z1,z366,z3,z383,z6]),(0,[z0,z1,z2,z3,z968,z6]),(0,[z0,z1,z110,z26,z36,z6]),(0,[z0,z1,z49,z3,z40,z218]),(0,[z0,z1,z3,z4,z748,z72])],[(0,[z0,z1,z2,z4,z6,z969]),(0,[z107,z0,z1,z173,z3,z6]),(0,[z0,z1,z2,z7,z489,z6]),(0,[z590,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z970,z4,z6]),(0,[z25,z0,z1,z49,z3,z218])],[(0,[z0,z1,z971,z3,z4,z6]),(0,[z0,z1,z2,z3,z399,z6]),(0,[z0,z1,z3,z4,z6,z972]),(0,[z0,z1,z2,z7,z66,z36]),(0,[z25,z0,z141,z19,z3,z6]),(0,[z0,z1,z616,z3,z40,z6]),(0,[z0,z1,z3,z52,z40,z6]),(0,[z0,z1,z2,z3,z973,z6]),(0,[z974,z1,z2,z3,z4,z6]),(0,[z975,z0,z1,z2,z3,z6]),(0,[z25,z976,z1,z2,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z977,z6]),(0,[z0,z300,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z55,z6]),(0,[z0,z1,z819,z3,z4,z6]),(0,[z0,z1,z366,z3,z978,z6]),(0,[z0,z1,z458,z3,z40,z6])],[(0,[z979,z0,z1,z2,z3,z6])],[(0,[z0,z1,z49,z7,z4,z218]),(0,[z0,z9,z2,z3,z442,z6]),(0,[z0,z1,z3,z648,z40,z6])],[(0,[z0,z1,z71,z3,z4,z374]),(0,[z980,z0,z1,z2,z3,z6]),(0,[z25,z0,z1,z2,z12,z6]),(0,[z107,z1,z2,z7,z40,z6]),(0,[z0,z1,z2,z981,z3,z6]),(0,[z0,z1,z2,z3,z982,z6])],[(0,[z0,z1,z2,z7,z255,z6]),(0,[z0,z1,z2,z12,z467,z6]),(0,[z0,z1,z2,z7,z485,z6]),(0,[z0,z1,z2,z3,z151,z6]),(0,[z0,z1,z2,z931,z52,z6]),(0,[z25,z0,z1,z983,z3,z6])],[(0,[z0,z1,z2,z3,z354,z45]),(0,[z0,z1,z2,z220,z237,z93]),(0,[z25,z0,z1,z2,z984,z6])],[(0,[z25,z254,z1,z2,z12,z6]),(0,[z0,z1,z110,z26,z10,z6]),(0,[z0,z141,z19,z3,z20,z6]),(0,[z48,z0,z1,z3,z4,z72])],[(0,[z0,z1,z2,z3,z985,z6]),(0,[z0,z1,z134,z26,z4,z6]),(0,[z0,z1,z2,z857,z3,z6]),(0,[z0,z1,z2,z3,z20,z6]),(0,[z0,z1,z2,z3,z986,z6])],[(0,[z127,z90,z2,z3,z40,z6]),(0,[z0,z1,z2,z987,z4,z6]),(0,[z0,z430,z2,z3,z346,z6]),(0,[z392,z1,z2,z7,z4,z6]),(0,[z0,z988,z2,z3,z36,z6])],[(0,[z989,z0,z1,z2,z3,z6]),(0,[z0,z141,z19,z3,z4,z6]),(0,[z593,z0,z1,z3,z52,z6])],[(0,[z267,z1,z2,z12,z13,z6]),(0,[z0,z21,z1,z2,z52,z6]),(0,[z0,z1,z2,z3,z990,z6])],[(0,[z0,z1,z2,z3,z168,z6]),(0,[z25,z267,z1,z2,z3,z45]),(0,[z0,z30,z2,z120,z40,z6]),(0,[z0,z1,z2,z220,z36,z93]),(0,[z25,z0,z1,z173,z3,z6])],[(0,[z0,z1,z2,z991,z3,z6]),(0,[z0,z1,z2,z12,z151,z6]),(0,[z539,z0,z1,z49,z3,z218])],[(0,[z127,z90,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z992,z6]),(0,[z0,z1,z2,z274,z40,z6]),(0,[z0,z1,z2,z3,z993,z6])],[(0,[z0,z994,z1,z173,z3,z6])],[(0,[z0,z1,z545,z3,z4,z6]),(0,[z0,z1,z2,z7,z67,z6]),(0,[z0,z1,z7,z52,z40,z6]),(0,[z25,z0,z1,z2,z3,z315]),(0,[z0,z1,z2,z3,z299,z6]),(0,[z0,z1,z2,z3,z995,z6])]],
   [[(0,[z50,z1,z35,z3,z4,z167]),(0,[z1,z2,z7,z12,z4,z6]),(0,[z1,z2,z7,z10,z13,z6]),(0,[z233,z136,z1,z2,z3,z6]),(0,[z0,z1,z366,z3,z4,z45]),(0,[z0,z1,z110,z818,z4,z6]),(0,[z0,z1,z313,z2,z36,z6]),(0,[z0,z996,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z997,z6]),(0,[z0,z1,z3,z52,z282,z6])],[(0,[z127,z933,z2,z3,z4,z6]),(0,[z0,z1,z2,z7,z221,z6]),(0,[z0,z1,z2,z998,z4,z6]),(0,[z267,z1,z2,z3,z40,z45])],[(0,[z25,z0,z430,z2,z3,z6]),(0,[z0,z1,z3,z292,z6,z72]),(0,[z0,z1,z2,z12,z168,z6]),(0,[z0,z1,z2,z12,z66,z36]),(0,[z0,z1,z2,z484,z83,z6]),(0,[z0,z1,z2,z10,z6,z381]),(0,[z0,z1,z2,z382,z383,z6]),(0,[z0,z1,z2,z3,z999,z6])],[(0,[z0,z1,z2,z454,z4,z6]),(0,[z0,z1,z2,z3,z1000,z6]),(0,[z0,z1,z2,z12,z887,z6]),(0,[z0,z1,z2,z7,z6,z99]),(0,[z1,z2,z3,z350,z6,z317]),(0,[z0,z1,z2,z220,z10,z93]),(0,[z0,z1,z2,z3,z4,z1001]),(0,[z0,z1,z2,z1002,z4,z6]),(0,[z0,z1,z3,z40,z6,z139])],[(0,[z233,z1,z2,z3,z222,z6]),(0,[z511,z1,z2,z3,z13,z6])],[(0,[z127,z90,z2,z54,z4,z6]),(0,[z233,z1,z2,z3,z840,z6]),(0,[z1003,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z1004,z4,z6])],[(0,[z0,z1,z545,z3,z11,z6]),(0,[z0,z1,z2,z1005,z4,z6]),(0,[z0,z1,z2,z12,z299,z6]),(0,[z107,z136,z1,z2,z3,z6]),(0,[z267,z1,z2,z7,z4,z45]),(0,[z0,z1,z173,z7,z3,z6]),(0,[z0,z1,z2,z3,z1006,z6]),(0,[z0,z1,z2,z3,z1007,z6])],[(0,[z0,z1,z2,z3,z346,z374]),(0,[z594,z0,z1,z2,z3,z36])],[(0,[z254,z1,z2,z12,z4,z6]),(0,[z0,z1,z313,z2,z10,z6]),(0,[z242,z0,z1,z173,z3,z6])],[(0,[z283,z0,z1,z2,z7,z6]),(0,[z0,z1,z2,z3,z512,z6]),(0,[z0,z1,z3,z52,z429,z6]),(0,[z321,z0,z1,z2,z6,z372])],[],[(0,[z0,z1,z2,z3,z6,z1008]),(0,[z0,z1,z1009,z3,z10,z6]),(0,[z0,z300,z2,z3,z4,z60]),(0,[z0,z1,z2,z3,z1010,z6]),(0,[z0,z1,z2,z3,z86,z6]),(0,[z0,z2,z28,z776,z4,z6]),(0,[z539,z0,z1,z2,z3,z6])],[(0,[z158,z0,z2,z12,z159,z6]),(0,[z0,z1,z2,z3,z1011,z6]),(0,[z0,z1,z40,z6,z135,z72]),(0,[z0,z1,z3,z52,z756,z6])],[(0,[z0,z1,z2,z3,z1012,z6]),(0,[z0,z430,z2,z280,z4,z6]),(0,[z0,z300,z2,z3,z52,z6]),(0,[z0,z21,z1,z2,z40,z6])],[(0,[z250,z0,z1,z12,z52,z6]),(0,[z0,z2,z3,z4,z6,z762]),(0,[z0,z1,z84,z3,z52,z6]),(0,[z0,z1,z2,z883,z4,z6]),(0,[z0,z1,z2,z3,z1013,z6]),(0,[z0,z24,z1,z29,z4,z6]),(0,[z0,z1,z2,z3,z1014,z6])]],
   [[(0,[z1015,z0,z1,z2,z3,z6]),(0,[z25,z0,z1,z31,z7,z6]),(0,[z0,z1,z2,z3,z6,z1016])],[(0,[z0,z1,z545,z3,z56,z6]),(0,[z59,z25,z1,z2,z3,z60])],[(0,[z0,z1,z2,z7,z155,z6]),(0,[z0,z1,z2,z3,z211,z6]),(0,[z0,z1,z2,z3,z1017,z6])],[(0,[z0,z1,z266,z3,z4,z447]),(0,[z0,z1,z2,z1018,z4,z6]),(0,[z0,z1,z49,z3,z168,z6]),(0,[z0,z1,z3,z399,z6,z72]),(0,[z0,z1,z173,z1019,z3,z6])],[(0,[z0,z1,z2,z3,z4,z1020]),(0,[z0,z1,z2,z3,z1021,z6]),(0,[z0,z446,z2,z3,z353,z6]),(0,[z0,z1,z2,z1022,z4,z6]),(0,[z48,z0,z1,z3,z52,z72]),(0,[z0,z1,z1023,z173,z3,z6])],[(0,[z0,z1,z2,z12,z69,z6]),(0,[z0,z1,z2,z3,z6,z1024]),(0,[z0,z1,z2,z1025,z4,z6])],[(0,[z0,z1,z2,z3,z232,z6]),(0,[z0,z1,z2,z319,z10,z6]),(0,[z0,z1,z2,z3,z6,z1026]),(0,[z0,z1,z2,z3,z6,z1027])],[(0,[z0,z1,z2,z54,z4,z447]),(0,[z0,z141,z19,z3,z52,z6]),(0,[z0,z1,z2,z3,z1028,z6]),(0,[z0,z1,z313,z2,z177,z6]),(0,[z0,z1,z31,z3,z217,z6])],[(0,[z0,z1,z2,z270,z4,z447]),(0,[z0,z1029,z2,z3,z4,z6])],[(0,[z0,z1,z2,z1030,z4,z6]),(0,[z0,z1,z2,z103,z40,z6]),(0,[z1031,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z121,z116,z6]),(0,[z0,z1,z2,z3,z4,z748])],[(0,[z0,z1,z3,z155,z399,z6]),(0,[z0,z1,z2,z12,z211,z6]),(0,[z0,z303,z2,z3,z61,z6]),(0,[z0,z1,z2,z1032,z3,z6])],[(0,[z0,z1,z1033,z3,z4,z6]),(0,[z0,z1,z2,z3,z1034,z6]),(0,[z0,z1,z1009,z3,z4,z6]),(0,[z1035,z0,z1,z2,z3,z6]),(0,[z210,z0,z1,z2,z3,z45]),(0,[z0,z1,z333,z3,z40,z6])],[(0,[z0,z90,z266,z3,z4,z6]),(0,[z0,z1,z2,z1036,z4,z6]),(0,[z0,z1,z2,z920,z3,z6]),(0,[z0,z1,z2,z249,z82,z6]),(0,[z0,z1,z2,z3,z1037,z6]),(0,[z0,z1,z2,z3,z1038,z6]),(0,[z258,z0,z1,z3,z4,z72])],[(0,[z0,z1,z545,z3,z52,z6]),(0,[z1,z933,z2,z3,z4,z6]),(0,[z0,z1,z95,z3,z40,z6]),(0,[z170,z1,z2,z7,z4,z6]),(0,[z59,z1,z2,z3,z36,z60])],[(0,[z207,z0,z1,z3,z4,z72]),(0,[z1,z2,z7,z12,z52,z6]),(0,[z0,z1,z2,z12,z232,z6]),(0,[z102,z1,z2,z7,z10,z6]),(0,[z0,z1,z173,z91,z3,z6]),(0,[z0,z88,z2,z28,z40,z6]),(0,[z369,z0,z2,z3,z4,z1039]),(0,[z0,z1,z173,z3,z4,z6])],[(0,[z0,z1,z545,z3,z1040,z6]),(0,[z0,z124,z1,z2,z12,z6]),(0,[z0,z1,z2,z7,z55,z6]),(0,[z0,z1,z132,z2,z3,z6]),(0,[z0,z1,z2,z4,z1041,z6]),(0,[z0,z1,z2,z3,z237,z6])]],
   [[(0,[z0,z555,z1,z95,z4,z6]),(0,[z320,z1,z2,z12,z4,z6])],[(0,[z0,z1,z2,z3,z1042,z6]),(0,[z136,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z1043,z6]),(0,[z25,z0,z1,z2,z3,z527])],[(0,[z0,z1,z2,z1044,z4,z6]),(0,[z0,z1,z2,z1045,z4,z6]),(0,[z0,z1,z366,z3,z13,z6]),(0,[z0,z1,z1046,z2,z3,z6]),(0,[z0,z1,z2,z109,z10,z6])],[(0,[z0,z1,z2,z3,z1047,z6]),(0,[z0,z1,z2,z177,z7,z6]),(0,[z0,z1,z2,z3,z1048,z6])],[(0,[z0,z1,z2,z12,z482,z6]),(0,[z0,z1,z2,z1049,z3,z6]),(0,[z0,z1,z2,z1004,z52,z6]),(0,[z976,z1,z2,z3,z4,z6])],[(0,[z0,z1,z266,z3,z712,z6]),(0,[z0,z1,z2,z4,z6,z1050]),(0,[z0,z1,z2,z319,z4,z6]),(0,[z0,z1,z2,z370,z13,z6]),(0,[z250,z0,z1,z3,z143,z6]),(0,[z158,z0,z1,z173,z3,z6]),(0,[z0,z1,z2,z3,z1051,z6]),(0,[z1052,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z721,z6]),(0,[z0,z1,z2,z770,z116,z6]),(0,[z0,z1,z2,z3,z1053,z6])],[(0,[z0,z1,z2,z3,z13,z374])],[(0,[z0,z1,z2,z12,z237,z6]),(0,[z0,z1,z401,z146,z4,z6]),(1,[z0,z1,z818,z4,z6]),(0,[z0,z506,z2,z3,z340,z6]),(0,[z0,z1,z3,z416,z6,z72])],[(0,[z0,z1,z2,z3,z1054,z6]),(0,[z1055,z0,z1,z2,z3,z6]),(1,[z0,z1,z3,z756,z6]),(0,[z48,z0,z1,z3,z40,z72]),(0,[z0,z1,z1056,z2,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1057]),(0,[z0,z1,z2,z3,z1058,z6]),(0,[z0,z1,z2,z287,z6,z372])],[(0,[z1,z2,z387,z3,z10,z6]),(0,[z25,z0,z1,z2,z3,z36])],[(0,[z65,z1,z2,z12,z10,z6]),(0,[z0,z1,z2,z7,z151,z6]),(0,[z0,z1,z2,z1059,z4,z6]),(0,[z0,z1,z1060,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1061]),(0,[z0,z1,z2,z3,z36,z167]),(0,[z0,z1,z2,z4,z6,z1062]),(0,[z0,z1,z2,z3,z1063,z6])],[(0,[z900,z0,z1,z2,z3,z70]),(0,[z0,z285,z2,z3,z10,z6]),(0,[z0,z430,z2,z307,z4,z6]),(0,[z0,z1,z2,z3,z455,z6]),(0,[z0,z1,z2,z3,z1064,z6]),(0,[z0,z1,z2,z12,z36,z6]),(0,[z48,z0,z1,z7,z4,z72]),(0,[z0,z1,z2,z3,z1065,z6]),(0,[z0,z24,z1,z29,z52,z6])],[(0,[z1,z2,z3,z840,z13,z6])],[(0,[z59,z1,z2,z3,z151,z60]),(0,[z258,z0,z1,z3,z6,z72]),(0,[z0,z1,z2,z1066,z4,z6])]],
   [[(0,[z0,z1,z2,z249,z40,z6]),(0,[z0,z1,z2,z3,z1067,z6]),(0,[z0,z1,z2,z1068,z4,z6]),(0,[z0,z1,z2,z4,z6,z1069])],[(0,[z127,z90,z2,z3,z4,z70]),(0,[z25,z0,z1,z2,z307,z6]),(0,[z0,z1,z2,z1070,z3,z6]),(0,[z0,z1,z2,z109,z4,z6]),(0,[z0,z21,z1,z132,z2,z6]),(0,[z0,z1,z49,z3,z4,z748])],[(0,[z0,z1,z2,z7,z168,z6]),(0,[z1,z2,z7,z12,z40,z6]),(0,[z102,z1,z2,z12,z10,z6]),(0,[z239,z1,z2,z3,z13,z6]),(0,[z0,z1,z3,z467,z6,z72])],[(0,[z0,z1,z2,z556,z150,z6])],[(0,[z0,z1,z2,z189,z4,z6]),(0,[z0,z1,z2,z3,z1071,z6]),(0,[z0,z1,z39,z3,z399,z6])],[(0,[z0,z1,z2,z3,z1072,z6]),(0,[z0,z1,z2,z12,z455,z6]),(0,[z0,z1,z71,z173,z3,z6]),(0,[z1,z2,z12,z473,z4,z6]),(0,[z0,z1,z208,z3,z40,z6]),(0,[z0,z1,z2,z3,z1073,z6]),(0,[z0,z1,z2,z1074,z3,z6])],[(0,[z0,z1,z2,z454,z40,z6]),(0,[z0,z1,z2,z1075,z4,z6]),(0,[z0,z1,z2,z12,z10,z6]),(0,[z0,z1,z2,z7,z299,z6])],[(0,[z0,z1,z2,z3,z4,z1076]),(0,[z0,z141,z505,z3,z4,z6]),(0,[z0,z1077,z2,z3,z4,z6]),(0,[z1,z2,z7,z714,z4,z6]),(0,[z0,z32,z1,z3,z399,z6]),(0,[z0,z1,z2,z144,z151,z6])],[(0,[z0,z1,z2,z382,z13,z6]),(0,[z23,z0,z1,z2,z4,z531]),(0,[z0,z1,z2,z489,z6,z381])],[(0,[z0,z285,z35,z3,z4,z6]),(0,[z0,z251,z314,z3,z4,z6]),(0,[z0,z1,z2,z3,z1078,z6]),(0,[z0,z1,z1079,z2,z4,z6]),(0,[z0,z1,z2,z3,z1080,z6]),(0,[z0,z1,z2,z902,z40,z6]),(0,[z0,z1,z2,z3,z1081,z6]),(0,[z250,z0,z1,z3,z756,z6]),(0,[z0,z1,z2,z945,z4,z6])],[(0,[z65,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z12,z399,z6]),(0,[z0,z2,z3,z930,z4,z6])],[(0,[z0,z300,z2,z12,z4,z6]),(0,[z0,z1,z2,z981,z7,z6]),(0,[z258,z0,z1,z2,z3,z106])],[(0,[z0,z285,z2,z3,z4,z6]),(0,[z158,z0,z2,z7,z159,z6]),(0,[z0,z1,z2,z3,z1082,z6]),(0,[z1083,z0,z1,z2,z3,z6]),(0,[z0,z1,z173,z3,z52,z6]),(1,[z0,z1,z2,z770,z6])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z307,z4,z374]),(0,[z671,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z6,z1084]),(0,[z0,z1,z49,z3,z721,z6])],[(0,[z250,z0,z1,z7,z52,z6])],[(0,[z0,z1,z2,z3,z1085,z6]),(0,[z0,z1,z2,z40,z6,z1086]),(0,[z25,z0,z1,z2,z809,z6])]],
   [[(0,[z0,z1,z2,z1087,z4,z6]),(0,[z0,z1088,z1,z2,z4,z6]),(0,[z0,z1,z1089,z173,z3,z6])],[(0,[z25,z0,z1,z2,z3,z6]),(0,[z1090,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z307,z13,z6]),(0,[z0,z1,z2,z3,z1091,z6]),(0,[z48,z0,z1,z12,z4,z72]),(0,[z0,z1,z2,z7,z512,z6]),(0,[z0,z24,z1,z29,z40,z6]),(0,[z0,z1,z325,z3,z40,z6]),(0,[z0,z136,z1,z31,z3,z6])],[(0,[z0,z1092,z2,z3,z4,z6]),(0,[z0,z1,z2,z12,z20,z6]),(0,[z691,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z1093,z6])],[(0,[z1,z2,z12,z13,z6,z60]),(0,[z0,z1,z2,z319,z52,z6]),(0,[z0,z1,z2,z3,z1094,z6]),(0,[z105,z1,z2,z3,z10,z6]),(0,[z0,z1,z779,z3,z45,z6])],[(0,[z0,z1,z2,z1095,z4,z6]),(0,[z0,z1,z2,z7,z69,z6]),(0,[z0,z141,z19,z12,z4,z6]),(0,[z0,z1,z2,z3,z1096,z6]),(0,[z0,z1,z2,z3,z1097,z6]),(0,[z0,z1,z2,z4,z6,z1086])],[(0,[z0,z1,z2,z3,z11,z6]),(0,[z127,z90,z266,z3,z4,z6]),(0,[z0,z1,z2,z92,z36,z6]),(0,[z25,z0,z300,z2,z3,z6]),(0,[z0,z446,z2,z3,z61,z6])],[],[(0,[z0,z1,z2,z3,z1098,z6]),(0,[z431,z0,z1,z173,z3,z6])],[(0,[z0,z1,z1099,z3,z4,z6]),(0,[z1,z2,z3,z467,z13,z6]),(0,[z0,z1,z2,z97,z62,z6]),(0,[z0,z1,z2,z3,z1100,z6]),(0,[z0,z1,z2,z1101,z4,z6]),(0,[z0,z1,z110,z26,z4,z6])],[(0,[z0,z1,z2,z3,z1102,z6]),(0,[z50,z1,z35,z3,z292,z6]),(0,[z0,z1,z2,z7,z211,z6]),(0,[z0,z1,z700,z3,z40,z6]),(0,[z0,z1,z2,z3,z1103,z6])],[(0,[z0,z1,z545,z12,z4,z6]),(0,[z127,z90,z2,z270,z4,z6]),(0,[z0,z1,z49,z3,z399,z6]),(0,[z25,z0,z1,z2,z3,z632])],[(0,[z0,z1,z2,z126,z316,z6]),(0,[z0,z1,z2,z3,z1104,z6]),(0,[z0,z1,z2,z3,z1105,z6]),(0,[z0,z1,z1106,z3,z4,z6]),(0,[z0,z1,z2,z1107,z3,z6]),(0,[z25,z0,z1,z2,z1108,z6])],[],[(0,[z0,z1,z1109,z3,z4,z6]),(0,[z0,z1,z2,z3,z36,z70]),(0,[z0,z1,z2,z7,z232,z6]),(0,[z0,z1,z2,z3,z1110,z6]),(0,[z0,z1,z173,z3,z6,z60]),(0,[z0,z1,z2,z1111,z4,z6]),(0,[z0,z1,z173,z3,z605,z6])],[(0,[z0,z1,z2,z92,z10,z6]),(0,[z369,z0,z2,z3,z13,z22]),(0,[z0,z1,z31,z3,z13,z6]),(0,[z0,z1,z2,z1112,z3,z6]),(0,[z0,z202,z2,z3,z159,z6]),(0,[z258,z0,z1,z3,z40,z72]),(0,[z0,z1,z2,z1068,z52,z6]),(0,[z0,z1,z173,z3,z648,z6])],[(0,[z0,z1,z2,z3,z56,z6]),(0,[z0,z1,z2,z3,z1113,z6]),(0,[z0,z1,z2,z109,z52,z6])]],
   [[(0,[z0,z1,z2,z3,z1114,z6]),(0,[z0,z1,z1099,z12,z4,z6]),(0,[z0,z1,z2,z3,z1115,z6]),(0,[z1,z2,z669,z3,z13,z6]),(0,[z0,z1,z1116,z3,z4,z6]),(0,[z0,z1,z2,z1117,z4,z6]),(0,[z0,z1,z173,z3,z40,z6]),(0,[z0,z1,z2,z3,z66,z53]),(0,[z0,z1,z2,z3,z1118,z6])],[(0,[z0,z1,z1119,z3,z4,z6]),(0,[z0,z1,z3,z40,z45,z72]),(0,[z0,z1,z2,z776,z4,z6])],[(0,[z0,z1,z2,z189,z52,z6]),(0,[z65,z1,z2,z12,z525,z6])],[(0,[z0,z1,z1120,z3,z4,z6]),(0,[z0,z1,z2,z3,z1121,z6]),(0,[z0,z1,z2,z7,z482,z6]),(0,[z0,z1,z2,z7,z934,z6]),(0,[z0,z1,z208,z3,z292,z6]),(0,[z0,z988,z2,z3,z4,z6]),(0,[z0,z2,z776,z3,z4,z6]),(0,[z0,z1,z2,z1122,z3,z6]),(0,[z0,z1,z3,z40,z6,z275]),(0,[z0,z1,z49,z3,z4,z591])],[(0,[z0,z1,z2,z3,z1123,z6]),(0,[z25,z0,z88,z2,z28,z6]),(0,[z23,z0,z1,z2,z295,z8])],[(0,[z0,z430,z2,z3,z4,z374]),(0,[z0,z1,z2,z1124,z4,z6]),(0,[z0,z1,z2,z3,z525,z6]),(0,[z0,z1,z2,z12,z512,z6]),(0,[z0,z1,z173,z7,z4,z6]),(0,[z0,z1,z2,z3,z6,z1125]),(0,[z0,z1,z2,z3,z1126,z6])],[(0,[z0,z1,z2,z3,z10,z70]),(0,[z0,z1,z2,z7,z237,z6]),(0,[z0,z1,z2,z3,z1127,z6]),(0,[z0,z1,z2,z220,z4,z93]),(1,[z0,z1,z2,z3,z711]),(0,[z0,z1,z1128,z3,z36,z6])],[(0,[z0,z1,z2,z12,z86,z6]),(0,[z0,z1,z174,z3,z399,z6]),(0,[z0,z1,z2,z3,z1129,z6]),(0,[z0,z1,z2,z3,z1130,z6])],[(0,[z0,z1,z2,z3,z4,z1131]),(0,[z0,z1,z2,z3,z4,z1132]),(0,[z0,z1,z2,z1133,z4,z6]),(0,[z50,z1,z1134,z3,z4,z6]),(0,[z65,z1,z2,z12,z52,z6]),(0,[z510,z1,z2,z7,z4,z6]),(0,[z233,z1,z2,z3,z13,z6]),(0,[z25,z0,z1,z2,z144,z6]),(0,[z25,z0,z1,z821,z3,z6])],[(0,[z0,z1,z2,z3,z1135,z6]),(0,[z0,z430,z2,z3,z13,z6]),(0,[z0,z1136,z2,z3,z4,z6]),(0,[z25,z0,z1,z2,z370,z6]),(0,[z0,z1,z821,z3,z10,z6]),(0,[z0,z1,z49,z3,z217,z218]),(0,[z0,z1,z49,z3,z198,z218])],[(0,[z127,z25,z90,z2,z3,z6]),(0,[z0,z285,z2,z3,z52,z6]),(0,[z0,z1137,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1138]),(0,[z0,z1,z2,z3,z1139,z6])],[(0,[z0,z1,z2,z3,z52,z6]),(0,[z0,z1,z2,z3,z879,z6]),(0,[z0,z1140,z2,z3,z4,z6]),(0,[z0,z1,z313,z2,z4,z6]),(0,[z0,z1,z2,z1141,z36,z6])],[(0,[z0,z1,z2,z7,z36,z6]),(0,[z241,z1,z2,z12,z4,z6]),(0,[z1,z2,z3,z10,z673,z6]),(0,[z0,z148,z2,z3,z159,z6])],[(0,[z0,z1,z2,z3,z1040,z6]),(0,[z0,z1,z2,z12,z525,z6]),(0,[z171,z1,z2,z3,z222,z6]),(0,[z0,z1,z2,z126,z770,z6])],[(0,[z0,z1,z2,z1142,z4,z6]),(0,[z253,z1,z2,z12,z4,z6]),(0,[z369,z25,z0,z2,z3,z22]),(0,[z242,z0,z1,z2,z140,z6])],[(0,[z0,z1,z2,z3,z1143,z6]),(0,[z214,z236,z2,z3,z215,z6]),(0,[z0,z1,z1144,z3,z4,z6]),(0,[z0,z1,z2,z3,z1145,z6]),(0,[z0,z1,z2,z1146,z3,z6]),(0,[z0,z1,z2,z3,z1147,z6]),(0,[z0,z1,z2,z3,z4,z734])]],
   [[(0,[z50,z0,z1,z173,z3,z6]),(0,[z233,z1,z2,z12,z13,z6]),(0,[z0,z1,z2,z3,z1148,z6]),(0,[z0,z1,z2,z1149,z4,z6]),(1,[z0,z2,z776,z4,z6]),(0,[z1150,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1151,z6]),(0,[z0,z1,z2,z1152,z36,z6])],[(0,[z0,z1,z2,z3,z1153,z6]),(0,[z210,z0,z1,z2,z3,z106])],[(0,[z0,z1,z314,z382,z4,z6]),(0,[z0,z1,z314,z3,z383,z6]),(0,[z0,z1,z2,z3,z1154,z6]),(0,[z0,z1,z2,z3,z1155,z6]),(0,[z0,z1,z2,z3,z6,z1156]),(0,[z443,z0,z1,z173,z3,z6])],[(0,[z0,z1,z2,z1157,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1158]),(0,[z0,z1,z2,z7,z455,z6]),(0,[z0,z1,z2,z1159,z3,z6]),(0,[z0,z1,z2,z3,z1160,z6])],[(0,[z0,z1,z2,z3,z1161,z6]),(0,[z0,z1,z2,z54,z36,z6]),(0,[z0,z1,z2,z3,z1162,z6]),(0,[z0,z1,z2,z7,z10,z6]),(0,[z0,z300,z2,z3,z40,z6]),(0,[z0,z1,z2,z1163,z4,z6]),(0,[z1164,z1,z2,z3,z4,z6]),(0,[z258,z0,z1,z2,z3,z218]),(0,[z254,z0,z1,z173,z3,z6])],[(0,[z0,z1,z2,z270,z36,z6]),(0,[z0,z1,z2,z189,z40,z6]),(0,[z0,z1,z2,z4,z6,z1165]),(0,[z0,z1166,z2,z3,z4,z6]),(0,[z0,z1,z1033,z12,z4,z6]),(0,[z0,z1,z1009,z12,z4,z6]),(0,[z655,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z1167,z6]),(0,[z0,z44,z2,z3,z442,z6]),(0,[z472,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z1168,z4,z6]),(0,[z0,z1,z110,z26,z52,z6]),(0,[z0,z1,z2,z1101,z52,z6])],[(0,[z214,z236,z2,z3,z13,z6]),(0,[z0,z1,z2,z3,z1169,z374]),(0,[z51,z0,z1,z173,z3,z6]),(0,[z0,z1,z2,z12,z1037,z6]),(0,[z0,z1,z132,z2,z7,z6]),(0,[z0,z1,z173,z3,z6,z22])],[(0,[z0,z1,z95,z12,z40,z6]),(0,[z25,z0,z1,z2,z92,z6]),(0,[z0,z1,z821,z3,z4,z6]),(0,[z0,z1,z2,z144,z36,z6]),(0,[z369,z0,z1,z173,z3,z6]),(0,[z0,z1,z2,z3,z1170,z6]),(0,[z0,z1,z2,z3,z6,z1171])],[(0,[z0,z1,z1172,z3,z4,z6]),(0,[z0,z1,z2,z3,z13,z447]),(0,[z0,z1,z2,z3,z1173,z6]),(0,[z0,z1,z173,z12,z4,z6]),(0,[z0,z1,z2,z7,z399,z6]),(0,[z59,z1,z2,z3,z10,z60]),(0,[z0,z1,z2,z1174,z3,z6]),(0,[z0,z1,z2,z3,z6,z1175])],[(0,[z0,z1,z545,z3,z4,z70]),(0,[z0,z1,z2,z3,z1176,z6]),(0,[z0,z1,z2,z3,z6,z1177]),(0,[z0,z300,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z6,z1178]),(0,[z0,z1,z2,z3,z1179,z6])],[(0,[z0,z1,z2,z521,z316,z6]),(0,[z0,z32,z874,z3,z4,z6]),(0,[z0,z30,z2,z776,z4,z6]),(0,[z0,z1,z2,z3,z1180,z6]),(0,[z0,z1181,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1182,z6])],[(0,[z50,z1,z35,z3,z346,z6]),(0,[z0,z124,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1183,z6]),(0,[z0,z1,z2,z1184,z4,z6])],[(0,[z0,z1,z2,z54,z10,z6]),(0,[z0,z1,z2,z3,z350,z6]),(0,[z0,z1,z2,z3,z1185,z6]),(0,[z0,z1,z1128,z3,z4,z6]),(0,[z0,z1186,z1,z3,z10,z6]),(0,[z59,z300,z2,z3,z4,z60]),(0,[z0,z141,z19,z3,z40,z6]),(0,[z0,z1,z2,z40,z6,z135])],[(0,[z25,z0,z1,z545,z3,z6]),(0,[z0,z1,z2,z3,z1187,z6]),(0,[z0,z1,z2,z3,z1188,z6]),(0,[z0,z1,z2,z1189,z4,z6]),(0,[z0,z1,z71,z3,z6,z99]),(0,[z0,z1,z3,z4,z6,z1190]),(0,[z0,z1,z2,z52,z6,z381]),(0,[z0,z1,z2,z3,z6,z1191]),(0,[z0,z1,z173,z3,z163,z6]),(0,[z0,z1,z2,z1192,z3,z6])]],
   [[(0,[z0,z1,z2,z405,z277,z6]),(0,[z0,z1,z2,z3,z1193,z6]),(0,[z158,z0,z2,z3,z930,z6])],[(0,[z0,z1,z2,z7,z20,z6]),(0,[z603,z1,z2,z3,z13,z6]),(0,[z0,z1,z2,z144,z10,z6]),(0,[z0,z1,z2,z556,z104,z6])],[(0,[z0,z1,z2,z3,z1194,z6]),(0,[z0,z1,z2,z3,z6,z1195]),(1,[z0,z1,z779,z3,z6]),(0,[z0,z1,z173,z28,z3,z6])],[(0,[z0,z141,z19,z7,z4,z6]),(0,[z0,z1,z2,z4,z6,z135])],[(0,[z0,z1,z545,z3,z40,z6]),(0,[z0,z1,z2,z3,z1196,z6]),(0,[z0,z1,z2,z119,z12,z6]),(0,[z704,z1,z2,z3,z13,z6]),(0,[z0,z1,z2,z271,z77,z6]),(0,[z0,z1,z2,z3,z1197,z6]),(0,[z199,z1,z2,z3,z13,z6]),(0,[z0,z1,z2,z220,z52,z93]),(0,[z0,z1,z173,z3,z6,z6])],[(0,[z0,z1,z2,z3,z1198,z6]),(0,[z0,z1,z2,z3,z1199,z6])],[(0,[z0,z1,z2,z12,z350,z6]),(0,[z0,z300,z2,z144,z4,z6]),(0,[z0,z1,z2,z52,z1200,z6])],[(0,[z25,z0,z1,z2,z280,z6]),(0,[z25,z0,z251,z2,z3,z6]),(0,[z0,z1,z2,z1201,z4,z6]),(0,[z0,z1,z2,z3,z1202,z6]),(0,[z0,z1,z3,z198,z6,z72])],[(0,[z0,z1,z2,z1203,z4,z6]),(0,[z798,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z10,z167]),(0,[z233,z1,z2,z92,z13,z6]),(0,[z59,z1,z2,z3,z4,z60]),(0,[z0,z1,z2,z3,z1204,z6]),(0,[z0,z1,z3,z40,z6,z329])],[(0,[z0,z1,z545,z7,z4,z6]),(0,[z283,z0,z1,z2,z3,z354]),(0,[z1,z2,z3,z4,z45,z738]),(0,[z0,z1,z677,z3,z4,z218]),(0,[z0,z1,z313,z2,z52,z6]),(0,[z48,z0,z1,z4,z135,z72])],[(0,[z0,z1,z2,z405,z13,z6]),(0,[z25,z0,z1,z314,z3,z6]),(0,[z0,z1,z110,z26,z40,z6]),(0,[z0,z1,z2,z4,z93,z553]),(0,[z0,z1,z2,z3,z36,z563])],[(0,[z0,z1,z2,z92,z52,z6]),(0,[z0,z1,z2,z3,z6,z1205]),(0,[z0,z1,z2,z1206,z4,z6]),(0,[z23,z25,z0,z1,z2,z8]),(0,[z443,z136,z1,z2,z3,z6])],[(0,[z0,z32,z91,z3,z36,z6])],[(0,[z0,z1,z2,z3,z4,z1207]),(0,[z0,z1,z2,z1208,z3,z6])],[(0,[z328,z1,z2,z7,z4,z6]),(0,[z0,z1,z420,z3,z52,z6]),(0,[z1,z2,z3,z13,z6,z212]),(0,[z680,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z3,z36,z18]),(0,[z0,z1,z29,z818,z4,z6]),(0,[z0,z1,z1209,z2,z3,z6])],[]],
   [[(0,[z0,z1,z2,z144,z4,z6]),(0,[z161,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z1210,z6]),(0,[z633,z1,z2,z3,z13,z6])],[(0,[z260,z0,z1,z2,z4,z395]),(0,[z0,z1,z2,z3,z1211,z6]),(0,[z0,z1,z2,z3,z1212,z6])],[(0,[z0,z1,z545,z54,z4,z6]),(0,[z0,z1,z2,z3,z1213,z6]),(0,[z0,z1,z2,z126,z162,z6]),(0,[z0,z1,z2,z287,z675,z6])],[(0,[z0,z1,z545,z270,z4,z6]),(0,[z50,z1,z35,z280,z4,z6]),(0,[z562,z1,z2,z7,z4,z6])],[(0,[z0,z44,z2,z3,z340,z6])],[(0,[z51,z1,z2,z3,z222,z6]),(0,[z0,z1,z2,z1214,z3,z6]),(0,[z0,z32,z91,z3,z10,z6]),(0,[z0,z44,z2,z371,z3,z6]),(0,[z0,z1,z2,z1215,z4,z6]),(0,[z25,z0,z1,z2,z6,z135]),(0,[z0,z1,z2,z1216,z4,z6])],[(0,[z0,z285,z2,z3,z4,z167]),(0,[z0,z1,z2,z1217,z4,z6]),(0,[z0,z1,z2,z7,z86,z6]),(0,[z0,z1,z2,z4,z6,z1218]),(0,[z25,z0,z1,z173,z7,z6]),(0,[z0,z1,z2,z3,z66,z354]),(0,[z0,z1,z47,z3,z52,z6]),(0,[z0,z1,z2,z1219,z4,z6])],[(0,[z0,z1,z2,z3,z4,z167]),(0,[z0,z285,z2,z12,z4,z6]),(0,[z50,z1,z35,z3,z4,z374]),(0,[z0,z1,z2,z3,z1220,z6]),(0,[z0,z1,z2,z3,z1221,z6]),(0,[z0,z30,z2,z119,z120,z6]),(0,[z0,z1,z2,z3,z1222,z6]),(0,[z0,z44,z2,z3,z61,z6]),(0,[z250,z0,z1,z3,z217,z6])],[(0,[z0,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z220,z40,z93]),(0,[z0,z637,z1,z3,z4,z72])],[(0,[z0,z1,z173,z3,z61,z6])],[],[(0,[z25,z0,z1,z2,z3,z167]),(0,[z50,z1,z35,z3,z13,z6]),(0,[z0,z1,z2,z3,z1223,z6])],[(0,[z0,z1,z2,z7,z525,z6]),(0,[z0,z1,z2,z3,z1224,z6]),(0,[z0,z1,z2,z818,z4,z6]),(0,[z0,z1,z31,z173,z3,z6])],[(0,[z0,z1,z2,z3,z4,z1225]),(0,[z0,z1,z2,z3,z1226,z6]),(0,[z0,z1,z313,z2,z40,z6])],[(0,[z933,z90,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1227,z6]),(0,[z283,z0,z1,z2,z3,z75]),(0,[z0,z1,z2,z3,z46,z6])],[(0,[z233,z1,z2,z7,z13,z6])]],
   [[(0,[z0,z1,z2,z12,z11,z6]),(0,[z0,z1,z12,z40,z6,z72]),(0,[z0,z1,z2,z3,z1228,z6]),(0,[z0,z1,z2,z3,z1229,z6]),(0,[z0,z1,z49,z3,z13,z218]),(0,[z0,z1,z3,z4,z6,z748]),(0,[z0,z1,z2,z3,z1230,z6]),(0,[z0,z1,z2,z179,z223,z6])],[(0,[z0,z1,z2,z1231,z4,z6]),(0,[z0,z1,z2,z1232,z3,z6])],[(0,[z0,z1,z2,z3,z1233,z6]),(0,[z0,z1,z2,z7,z52,z6]),(0,[z0,z1,z2,z3,z1234,z6])],[(0,[z0,z1235,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z1236,z6]),(0,[z0,z1,z2,z1237,z3,z6]),(0,[z48,z0,z1,z173,z3,z6]),(0,[z25,z0,z1,z1060,z3,z6])],[(0,[z0,z1,z2,z3,z1238,z6])],[(0,[z0,z1239,z1,z2,z3,z6]),(0,[z0,z2,z3,z4,z6,z1240]),(0,[z0,z2,z3,z4,z1039,z22]),(0,[z0,z1,z177,z3,z40,z6]),(0,[z0,z1,z524,z3,z40,z6]),(0,[z0,z1,z2,z3,z6,z1241])],[(0,[z0,z1,z2,z3,z1242,z6]),(0,[z0,z1,z2,z12,z46,z6]),(0,[z107,z1,z2,z7,z13,z6]),(0,[z0,z1,z2,z1243,z4,z6]),(0,[z0,z1,z2,z3,z1244,z6]),(0,[z59,z1,z2,z3,z52,z60]),(0,[z0,z1,z2,z1245,z4,z6]),(0,[z0,z1,z2,z1246,z3,z6])],[(0,[z0,z1,z2,z3,z1247,z6]),(0,[z539,z0,z1,z2,z7,z6]),(0,[z0,z1,z314,z3,z13,z6]),(0,[z0,z1248,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1249,z6]),(0,[z0,z1,z2,z1045,z40,z6])],[(0,[z0,z1,z2,z3,z4,z1250]),(0,[z1251,z0,z1,z2,z3,z6]),(0,[z0,z1,z314,z3,z1252,z6]),(0,[z0,z1,z2,z3,z1253,z6]),(0,[z582,z0,z1,z3,z6,z99])],[(0,[z0,z1,z2,z126,z573,z6]),(0,[z1254,z0,z1,z2,z3,z6]),(0,[z0,z1,z173,z220,z3,z6])],[(0,[z0,z1,z2,z12,z56,z6]),(0,[z0,z1,z2,z224,z12,z6]),(0,[z0,z1,z2,z3,z197,z350]),(0,[z0,z1,z2,z319,z40,z6]),(0,[z0,z1,z2,z3,z1255,z6]),(0,[z1256,z1,z2,z3,z4,z6]),(0,[z0,z1,z1257,z3,z4,z6]),(0,[z0,z1,z2,z3,z36,z517]),(0,[z0,z1,z2,z3,z1258,z6]),(0,[z0,z1,z3,z40,z367,z6])],[(0,[z127,z90,z2,z3,z13,z6]),(0,[z0,z1,z2,z3,z1259,z6]),(0,[z0,z1260,z2,z3,z4,z6]),(0,[z16,z0,z1,z3,z4,z72]),(0,[z267,z1,z2,z3,z277,z45])],[(0,[z0,z1,z2,z3,z1261,z6]),(0,[z0,z251,z2,z3,z36,z6])],[(0,[z0,z1,z2,z3,z1262,z6]),(1,[z0,z1,z173,z12,z6]),(0,[z0,z1,z2,z3,z1263,z6]),(0,[z0,z1,z2,z1264,z3,z6]),(0,[z0,z1,z173,z3,z159,z6])],[(0,[z0,z1,z2,z3,z82,z6]),(0,[z0,z30,z2,z120,z13,z6]),(0,[z0,z1,z2,z1265,z3,z6]),(0,[z0,z1,z2,z144,z52,z6]),(0,[z0,z1,z2,z4,z6,z1266]),(0,[z0,z1,z2,z1267,z3,z6]),(0,[z0,z1,z2,z1268,z4,z6])],[(0,[z0,z1,z2,z3,z1269,z6]),(0,[z0,z1,z2,z3,z1270,z6]),(0,[z0,z1271,z1,z2,z3,z6])]],
   [[(0,[z0,z1,z2,z274,z13,z6]),(0,[z0,z1,z2,z92,z4,z6]),(0,[z0,z1,z2,z126,z37,z6]),(0,[z0,z1,z2,z3,z1272,z6]),(0,[z0,z1,z355,z3,z40,z6])],[(0,[z0,z1,z2,z3,z1273,z6]),(0,[z0,z1,z2,z169,z316,z6]),(0,[z0,z1,z2,z3,z96,z6]),(0,[z0,z1274,z2,z3,z4,z6])],[(0,[z50,z1,z35,z307,z4,z6]),(0,[z522,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z4,z1275]),(0,[z0,z1,z2,z1276,z3,z6]),(0,[z0,z1,z2,z287,z770,z6]),(0,[z0,z1,z1277,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1278]),(0,[z0,z1,z2,z1279,z4,z6])],[(0,[z0,z1,z266,z3,z36,z6]),(0,[z0,z1,z2,z1280,z4,z6]),(0,[z0,z1,z110,z26,z201,z6]),(0,[z1281,z0,z1,z2,z3,z6]),(0,[z0,z1282,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z52,z167]),(0,[z0,z1,z2,z3,z1283,z6]),(0,[z0,z1,z2,z12,z6,z1138]),(0,[z0,z1,z2,z7,z350,z6]),(0,[z267,z1,z2,z3,z13,z45]),(0,[z0,z251,z2,z3,z10,z6]),(0,[z0,z1,z2,z3,z1284,z6]),(0,[z0,z1,z2,z3,z53,z6]),(0,[z0,z1,z2,z3,z6,z1285])],[(0,[z0,z1,z1286,z3,z4,z6]),(0,[z1,z2,z1134,z3,z4,z6]),(0,[z0,z1,z2,z12,z82,z6]),(0,[z0,z1,z2,z12,z52,z6]),(0,[z0,z1,z875,z3,z13,z6]),(0,[z0,z1,z2,z109,z40,z6]),(0,[z0,z24,z1,z818,z4,z6]),(0,[z0,z1,z2,z3,z1287,z6])],[(0,[z0,z1,z2,z1288,z4,z6]),(0,[z0,z1,z2,z3,z1289,z6]),(0,[z0,z1,z2,z1290,z3,z6]),(0,[z1291,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z1292,z3,z6]),(0,[z0,z1,z2,z3,z1293,z6])],[(0,[z0,z1,z2,z3,z4,z70]),(0,[z0,z1,z2,z3,z1294,z6]),(0,[z1295,z0,z1,z2,z3,z6]),(0,[z108,z1,z2,z3,z292,z6]),(0,[z0,z1,z2,z3,z1296,z6]),(0,[z0,z1,z173,z1297,z3,z6])],[(0,[z0,z1,z2,z12,z96,z6]),(0,[z0,z1,z2,z1298,z4,z6]),(0,[z0,z1,z2,z3,z1299,z6])],[(0,[z0,z1,z1300,z3,z4,z6]),(0,[z0,z1,z173,z3,z218,z6])],[(0,[z0,z1,z2,z3,z4,z1301]),(0,[z0,z1,z2,z3,z1302,z6]),(0,[z0,z43,z2,z3,z36,z163]),(0,[z0,z1,z3,z217,z40,z6])],[(0,[z25,z0,z1,z2,z3,z70]),(0,[z0,z1,z2,z3,z1303,z6]),(0,[z0,z1,z2,z1304,z4,z6])],[(0,[z0,z1,z266,z3,z10,z6]),(0,[z0,z285,z2,z3,z118,z6]),(0,[z0,z1,z2,z12,z53,z6]),(0,[z0,z1,z2,z3,z1305,z6]),(0,[z0,z1,z173,z140,z3,z6])],[(0,[z0,z1,z2,z3,z118,z6]),(0,[z0,z1,z2,z3,z1306,z6]),(0,[z0,z251,z2,z3,z151,z6]),(0,[z0,z1,z314,z3,z735,z6]),(0,[z0,z1,z2,z3,z1307,z6])],[(0,[z214,z933,z2,z3,z4,z6]),(0,[z0,z1,z2,z280,z36,z6]),(0,[z65,z1,z2,z12,z40,z6]),(0,[z0,z136,z1,z2,z12,z6]),(0,[z0,z1,z2,z3,z1308,z6]),(0,[z0,z30,z341,z2,z4,z6]),(0,[z0,z1,z2,z963,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z11,z70]),(0,[z0,z1,z2,z1309,z4,z6]),(0,[z508,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z1310,z6]),(0,[z0,z1,z3,z1311,z10,z6]),(0,[z0,z742,z2,z3,z4,z6])],[(0,[z0,z285,z2,z3,z40,z6]),(0,[z258,z0,z1,z2,z12,z6]),(0,[z25,z0,z1,z2,z3,z441]),(0,[z0,z1,z2,z3,z1312,z6])],[(0,[z0,z1,z2,z3,z40,z6]),(0,[z0,z1,z2,z270,z10,z6]),(0,[z0,z1,z2,z370,z36,z6]),(0,[z0,z1,z779,z3,z10,z6]),(0,[z0,z1,z2,z97,z104,z6])],[(0,[z25,z0,z1,z266,z3,z6]),(0,[z94,z90,z2,z3,z4,z6]),(0,[z200,z1,z2,z12,z4,z6]),(0,[z1,z2,z387,z7,z4,z6]),(0,[z0,z1,z2,z3,z6,z1313])],[(0,[z65,z1,z2,z714,z4,z6]),(0,[z25,z0,z1,z2,z103,z6]),(0,[z0,z1,z1314,z2,z3,z6]),(0,[z0,z1,z2,z3,z1315,z6]),(0,[z0,z1,z39,z3,z40,z6]),(0,[z0,z1,z2,z3,z36,z627])],[(0,[z0,z1,z2,z3,z1316,z6]),(0,[z25,z0,z1,z2,z7,z36]),(0,[z0,z1,z2,z3,z1317,z6]),(0,[z25,z0,z1,z2,z109,z6]),(0,[z23,z0,z1,z2,z36,z8])],[(0,[z0,z1,z2,z3,z1318,z6]),(0,[z0,z285,z2,z7,z4,z6]),(0,[z0,z1,z2,z12,z118,z6]),(1,[z136,z1,z2,z12,z6]),(0,[z25,z0,z1,z1319,z3,z6]),(0,[z0,z1,z2,z1141,z4,z6])],[(0,[z0,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z1320,z6]),(0,[z0,z1,z2,z287,z379,z6]),(0,[z0,z1,z2,z3,z1321,z6]),(0,[z0,z136,z1,z173,z3,z6])],[(0,[z0,z1,z2,z1322,z4,z6]),(0,[z0,z1,z2,z1323,z4,z6]),(0,[z0,z1,z2,z280,z10,z6]),(0,[z0,z1,z2,z3,z1324,z6]),(0,[z0,z1,z2,z12,z1310,z6]),(0,[z0,z1,z240,z3,z40,z6]),(0,[z0,z1,z2,z3,z6,z1325])],[(0,[z0,z1,z35,z3,z143,z6]),(0,[z0,z1,z2,z1326,z4,z6]),(0,[z0,z1,z2,z3,z1327,z6]),(0,[z0,z1,z2,z3,z6,z1328]),(0,[z258,z0,z1,z173,z3,z6]),(0,[z0,z1,z1329,z173,z3,z6])],[(0,[z0,z1,z2,z3,z56,z70]),(0,[z50,z430,z35,z3,z4,z6]),(0,[z0,z1,z2,z3,z1330,z6]),(0,[z0,z1,z2,z12,z40,z6]),(0,[z0,z1,z2,z3,z1331,z6]),(0,[z0,z1,z2,z669,z104,z6]),(0,[z25,z0,z1,z832,z3,z6])],[(0,[z0,z1,z2,z370,z10,z6]),(0,[z0,z1,z2,z1152,z4,z6]),(0,[z59,z1,z2,z144,z4,z60]),(0,[z1332,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z479,z104,z6])],[(0,[z0,z1,z2,z3,z143,z6]),(0,[z0,z1,z2,z1333,z3,z6]),(0,[z0,z1,z2,z103,z13,z6]),(0,[z0,z452,z91,z3,z4,z6]),(0,[z0,z1,z1334,z2,z3,z6]),(0,[z0,z1,z173,z3,z198,z6])],[(0,[z0,z1,z1335,z2,z4,z6]),(0,[z0,z1,z2,z3,z1336,z6]),(0,[z0,z1,z3,z40,z6,z402]),(0,[z0,z1,z2,z36,z6,z135]),(0,[z25,z0,z1,z2,z3,z528])],[(0,[z0,z1,z2,z3,z1121,z70]),(0,[z1337,z0,z1,z2,z3,z6]),(0,[z1,z549,z2,z3,z10,z6]),(0,[z23,z0,z1,z2,z10,z8]),(0,[z0,z1,z2,z4,z6,z1338]),(0,[z25,z0,z1,z2,z3,z529])],[(0,[z0,z1,z2,z7,z11,z6]),(0,[z0,z1,z2,z714,z4,z6]),(0,[z23,z0,z1,z2,z4,z614]),(0,[z0,z1,z2,z3,z1339,z6]),(0,[z0,z1,z2,z3,z1340,z6]),(0,[z0,z148,z1,z173,z3,z6])]],
   [[(0,[z0,z1,z2,z54,z4,z6]),(0,[z0,z1186,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z1341,z6]),(0,[z0,z1342,z1,z2,z3,z6]),(0,[z0,z347,z1,z2,z162,z6]),(0,[z0,z1,z2,z126,z116,z6])],[(0,[z0,z1,z2,z270,z4,z6]),(0,[z0,z88,z2,z28,z13,z6]),(0,[z0,z1,z779,z3,z4,z6]),(0,[z0,z1,z366,z3,z151,z6]),(0,[z25,z0,z1,z31,z3,z106])],[(0,[z0,z1,z2,z3,z1343,z6]),(0,[z0,z1,z2,z3,z1344,z6]),(0,[z0,z1,z754,z3,z13,z6]),(0,[z0,z1,z2,z119,z3,z6]),(0,[z25,z0,z1,z2,z3,z53]),(0,[z0,z1,z2,z3,z1345,z6])],[(0,[z59,z1,z2,z12,z4,z60]),(0,[z0,z1,z2,z405,z398,z6]),(0,[z0,z1,z2,z1346,z3,z6])],[(0,[z0,z1,z2,z3,z4,z1347]),(0,[z0,z1,z2,z1348,z4,z6]),(0,[z0,z1,z2,z12,z143,z6]),(0,[z0,z1,z110,z173,z3,z6]),(0,[z25,z974,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z711,z106])],[(0,[z0,z1,z2,z12,z1336,z6]),(0,[z0,z1,z2,z194,z12,z6]),(0,[z0,z1,z2,z7,z46,z6]),(0,[z0,z1,z2,z382,z36,z6])],[(0,[z0,z1,z2,z3,z52,z70]),(0,[z0,z1,z1349,z3,z4,z6]),(1,[z1,z2,z714,z4,z6]),(0,[z0,z1,z2,z3,z1350,z6]),(0,[z48,z0,z1,z3,z204,z72]),(0,[z0,z1,z3,z4,z218,z748]),(0,[z0,z1,z2,z3,z1351,z6])],[(0,[z0,z1,z2,z3,z1352,z6]),(0,[z0,z1,z2,z3,z1353,z6])],[(0,[z0,z1,z2,z54,z11,z6]),(0,[z0,z1354,z1,z2,z3,z6]),(0,[z0,z1,z2,z1355,z4,z6])],[(0,[z0,z1,z2,z270,z11,z6]),(0,[z0,z1,z2,z7,z56,z6]),(0,[z1,z2,z35,z3,z222,z6]),(0,[z1,z2,z7,z185,z4,z6]),(0,[z25,z0,z1,z1277,z3,z6])],[(0,[z0,z1,z2,z3,z4,z1356]),(0,[z0,z1,z2,z3,z1357,z6]),(0,[z0,z1,z2,z287,z77,z6]),(0,[z0,z874,z91,z3,z4,z6]),(0,[z0,z1,z49,z3,z40,z6]),(0,[z0,z1,z2,z3,z1358,z6])],[(0,[z0,z1,z2,z7,z1238,z6]),(0,[z0,z1,z2,z3,z1359,z6]),(0,[z0,z1,z1360,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1361,z6]),(0,[z25,z0,z1,z2,z7,z6]),(0,[z1362,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z1363,z3,z6]),(0,[z0,z1,z2,z3,z1364,z6])],[(0,[z0,z1,z3,z143,z40,z6]),(0,[z0,z1,z1365,z3,z4,z6]),(0,[z48,z0,z1,z3,z6,z99]),(0,[z23,z0,z1,z2,z4,z8])],[(0,[z0,z1,z2,z307,z36,z6]),(0,[z0,z1,z1349,z12,z4,z6]),(0,[z0,z1,z2,z382,z10,z6]),(0,[z686,z0,z2,z3,z4,z22]),(0,[z0,z511,z2,z3,z4,z22])],[]],
   [[(0,[z1366,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z292,z6]),(0,[z0,z1,z2,z1367,z3,z6]),(0,[z0,z1,z2,z3,z756,z6]),(0,[z658,z1,z2,z3,z467,z6]),(0,[z539,z0,z1,z2,z3,z53])],[(0,[z0,z1,z2,z3,z4,z1368]),(0,[z0,z1,z2,z3,z4,z1369]),(0,[z0,z1,z2,z454,z215,z6]),(0,[z0,z1,z276,z3,z40,z6])],[(0,[z0,z1,z2,z54,z56,z6]),(0,[z0,z1,z2,z12,z4,z167]),(0,[z0,z44,z2,z12,z61,z6]),(0,[z0,z1,z49,z12,z40,z6]),(0,[z0,z1,z2,z92,z40,z6]),(0,[z210,z0,z1,z2,z3,z350]),(0,[z158,z0,z2,z3,z186,z6]),(0,[z0,z1,z2,z3,z1370,z6]),(0,[z0,z2,z3,z4,z6,z1039]),(0,[z0,z1,z39,z3,z756,z6])],[(0,[z0,z1,z1371,z3,z4,z6]),(0,[z0,z1,z2,z270,z56,z6]),(0,[z0,z1,z2,z3,z1372,z6]),(0,[z0,z1,z2,z3,z1373,z6]),(0,[z0,z1,z2,z249,z13,z6]),(0,[z0,z1,z2,z3,z1374,z6]),(0,[z0,z300,z2,z3,z383,z6]),(0,[z0,z1,z2,z3,z1375,z6]),(0,[z0,z1,z2,z3,z1376,z6]),(0,[z0,z1,z2,z3,z4,z1377]),(0,[z0,z1,z2,z3,z1378,z6])],[(0,[z0,z1,z71,z3,z399,z6]),(0,[z0,z1,z2,z3,z1379,z6]),(0,[z0,z1,z2,z3,z1380,z6])],[(0,[z0,z1,z2,z1381,z4,z6]),(0,[z0,z1,z2,z7,z82,z6]),(0,[z0,z1,z2,z3,z4,z1039]),(0,[z0,z1,z2,z1279,z40,z6])],[(0,[z0,z297,z91,z3,z4,z6]),(0,[z0,z1382,z1,z2,z3,z6]),(0,[z0,z1,z1383,z3,z4,z6])],[(0,[z0,z1,z2,z307,z10,z6]),(0,[z51,z1,z71,z3,z40,z6]),(0,[z210,z0,z1,z2,z12,z6]),(0,[z0,z1,z2,z779,z3,z6]),(0,[z0,z1,z2,z382,z151,z6]),(0,[z0,z32,z91,z3,z4,z6]),(0,[z0,z1,z2,z3,z1384,z6]),(0,[z0,z1,z983,z3,z4,z6])],[(0,[z0,z1,z2,z7,z96,z6]),(0,[z0,z1,z2,z3,z1385,z6]),(0,[z0,z30,z2,z194,z120,z6])],[(0,[z0,z1,z2,z454,z13,z6]),(0,[z65,z0,z1,z173,z3,z6]),(0,[z0,z1386,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1387,z6]),(0,[z0,z1388,z1,z2,z3,z6])],[(0,[z0,z1,z266,z3,z52,z6]),(0,[z127,z90,z2,z3,z4,z447]),(0,[z0,z1,z2,z3,z1389,z6])],[(0,[z0,z1,z1390,z3,z4,z6]),(0,[z0,z1,z1391,z2,z4,z6]),(0,[z0,z1,z2,z12,z1228,z6]),(0,[z0,z1,z2,z3,z1392,z6]),(0,[z0,z1,z2,z3,z198,z6]),(0,[z679,z0,z1,z2,z605,z6])],[(0,[z25,z0,z1,z2,z274,z6]),(0,[z51,z1,z71,z7,z4,z6]),(0,[z0,z1,z2,z7,z53,z6]),(0,[z102,z1,z2,z3,z6,z317]),(0,[z0,z1,z2,z3,z1393,z6]),(0,[z0,z1,z2,z3,z1394,z6]),(0,[z0,z1,z643,z3,z40,z6]),(0,[z0,z1,z2,z3,z1395,z6]),(0,[z0,z1,z2,z3,z201,z6])],[(0,[z0,z1,z2,z3,z1396,z6]),(0,[z1397,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z54,z52,z6]),(0,[z209,z0,z2,z3,z459,z6])],[(0,[z0,z1,z2,z270,z52,z6]),(0,[z440,z236,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1398,z6]),(0,[z0,z32,z91,z12,z4,z6]),(0,[z0,z1,z2,z7,z1294,z6]),(0,[z0,z1,z2,z3,z1399,z6]),(0,[z0,z1,z807,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z1400,z4,z6]),(0,[z102,z0,z1,z173,z3,z6]),(0,[z0,z1,z2,z3,z978,z6]),(0,[z1401,z0,z1,z2,z3,z6])],[(0,[z0,z1402,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1403,z6]),(0,[z0,z1,z2,z3,z448,z198]),(0,[z0,z1,z2,z126,z651,z6]),(0,[z0,z1404,z1,z173,z3,z6])],[(0,[z0,z1,z2,z1405,z4,z6]),(0,[z0,z1,z2,z1348,z52,z6])],[(0,[z0,z1,z2,z12,z198,z6]),(0,[z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z1406,z6]),(0,[z0,z1,z2,z3,z448,z36])],[(0,[z0,z1,z266,z3,z1161,z6]),(0,[z0,z1,z2,z12,z201,z6]),(0,[z0,z1,z1407,z2,z3,z6]),(0,[z0,z1,z2,z3,z1408,z6]),(0,[z0,z1,z2,z3,z1409,z6])],[(0,[z0,z1,z2,z1410,z4,z6]),(0,[z0,z1,z2,z7,z118,z6]),(0,[z0,z1,z2,z248,z116,z6]),(0,[z25,z893,z1,z2,z3,z6])],[(0,[z0,z430,z2,z3,z36,z6]),(0,[z0,z1,z2,z3,z1261,z167]),(0,[z0,z300,z2,z3,z4,z45]),(0,[z0,z1,z2,z3,z1411,z6]),(0,[z258,z0,z1,z2,z3,z198]),(0,[z0,z1,z2,z3,z1412,z6]),(0,[z0,z1,z49,z3,z470,z218])],[(0,[z0,z1,z2,z3,z1413,z6]),(0,[z0,z1,z2,z3,z1414,z6]),(0,[z0,z303,z2,z3,z5,z6]),(0,[z0,z1,z2,z1415,z4,z6]),(0,[z48,z0,z1,z313,z4,z72])],[(0,[z0,z1,z49,z3,z292,z6]),(0,[z0,z2,z3,z930,z61,z6]),(0,[z0,z1,z2,z3,z1416,z6]),(0,[z258,z0,z1,z2,z3,z36]),(0,[z0,z1,z2,z224,z3,z6])],[(0,[z0,z1,z1417,z3,z4,z6]),(0,[z0,z1,z2,z7,z40,z6]),(0,[z0,z1,z2,z271,z104,z6]),(0,[z0,z1,z2,z3,z1418,z6]),(0,[z0,z1,z2,z1419,z4,z6]),(0,[z0,z332,z2,z3,z61,z6])],[(0,[z0,z1420,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1421,z6]),(0,[z108,z1,z2,z3,z13,z6]),(0,[z0,z1,z173,z3,z6,z72])],[(0,[z0,z1,z2,z3,z1422,z6]),(0,[z0,z1,z2,z12,z33,z6]),(0,[z59,z124,z1,z2,z3,z60]),(1,[z0,z1,z173,z3,z6]),(0,[z23,z0,z1,z2,z52,z8])],[(0,[z1423,z0,z1,z2,z3,z6]),(0,[z1,z2,z12,z675,z4,z6]),(0,[z0,z1,z2,z3,z1424,z6])],[(0,[z59,z1,z2,z3,z40,z60]),(0,[z0,z1,z3,z52,z460,z6])],[(0,[z0,z1425,z2,z3,z4,z6]),(0,[z267,z1,z2,z3,z398,z45]),(0,[z0,z1,z421,z3,z52,z6])],[(0,[z0,z430,z2,z3,z10,z6]),(0,[z0,z1,z2,z1426,z4,z6]),(0,[z1,z1134,z35,z3,z4,z6]),(0,[z25,z1,z2,z7,z12,z6]),(0,[z0,z1,z2,z1427,z12,z6]),(0,[z0,z1,z2,z1428,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z1429,z6]),(0,[z0,z1,z173,z126,z3,z6])],[(0,[z0,z1,z2,z3,z6,z1430]),(0,[z0,z1,z2,z3,z1431,z6]),(0,[z0,z1,z2,z3,z6,z1432])],[(0,[z0,z1,z2,z54,z40,z6]),(0,[z59,z1,z2,z7,z4,z60]),(0,[z0,z1,z366,z3,z36,z6]),(0,[z0,z1,z2,z3,z6,z1433])],[(0,[z0,z1,z2,z12,z4,z70]),(0,[z236,z933,z2,z3,z4,z6]),(0,[z0,z285,z2,z3,z346,z6]),(0,[z0,z1,z2,z3,z4,z1434]),(0,[z0,z1,z2,z7,z143,z6]),(0,[z0,z1,z2,z3,z1435,z6]),(0,[z369,z0,z2,z3,z489,z22]),(0,[z0,z1,z49,z3,z198,z6])],[(0,[z0,z90,z2,z3,z4,z447]),(0,[z0,z1,z2,z3,z346,z6]),(0,[z0,z21,z1,z2,z13,z6]),(0,[z0,z1,z2,z13,z6,z135]),(0,[z0,z1,z2,z3,z1436,z6]),(0,[z0,z1,z2,z3,z6,z1437]),(0,[z0,z1,z2,z3,z66,z711])],[(0,[z0,z1,z2,z1438,z4,z6]),(0,[z511,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z144,z40,z6]),(0,[z267,z1,z2,z405,z4,z45]),(0,[z0,z32,z91,z3,z52,z6]),(0,[z0,z1,z2,z3,z1439,z6]),(0,[z0,z1,z3,z218,z6,z99]),(0,[z0,z1,z2,z4,z6,z734]),(0,[z0,z1,z2,z3,z6,z1440])],[(0,[z0,z1,z2,z3,z36,z374]),(0,[z0,z1,z2,z3,z1441,z6]),(0,[z510,z1,z2,z3,z13,z6]),(0,[z0,z1,z336,z3,z40,z6]),(0,[z0,z1,z2,z1329,z3,z6])],[(0,[z0,z251,z2,z3,z4,z6]),(0,[z1,z2,z3,z155,z222,z6]),(0,[z0,z1,z2,z3,z1442,z6])],[(0,[z0,z1,z2,z3,z118,z167]),(0,[z468,z1,z2,z12,z4,z6]),(0,[z0,z1,z1443,z2,z4,z6]),(0,[z0,z124,z1,z2,z7,z6]),(0,[z361,z1,z2,z7,z4,z6]),(0,[z25,z0,z1,z2,z3,z354]),(0,[z0,z1,z668,z3,z40,z6])],[(0,[z0,z297,z1,z3,z40,z6]),(0,[z260,z0,z1,z2,z4,z8]),(0,[z0,z1,z2,z3,z1444,z6]),(0,[z0,z24,z1,z4,z6,z329])],[(0,[z445,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z1445,z6]),(0,[z0,z1,z2,z3,z1446,z6]),(0,[z0,z1,z2,z3,z770,z6]),(0,[z0,z1,z2,z140,z104,z6])],[(0,[z0,z1,z2,z3,z1447,z6]),(0,[z0,z1,z366,z3,z10,z6]),(0,[z0,z1448,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z40,z167]),(0,[z0,z1,z2,z3,z1449,z6]),(0,[z0,z1,z362,z3,z52,z6]),(0,[z0,z1,z2,z1450,z4,z6]),(0,[z0,z1,z2,z3,z1451,z6]),(0,[z250,z0,z1,z173,z3,z6]),(0,[z0,z1,z2,z3,z6,z1452])],[(0,[z0,z1,z2,z3,z1453,z6]),(0,[z0,z122,z2,z226,z4,z6]),(0,[z0,z136,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1454,z6]),(0,[z0,z1,z2,z3,z1455,z6]),(0,[z48,z0,z1,z3,z416,z72]),(0,[z48,z25,z0,z1,z3,z72])],[(0,[z1456,z0,z1,z2,z3,z6]),(0,[z210,z0,z1,z2,z3,z60]),(0,[z1457,z1,z2,z3,z4,z6]),(0,[z0,z44,z1,z173,z3,z6]),(0,[z0,z1,z818,z3,z4,z6]),(0,[z0,z1458,z1,z2,z3,z6])],[(0,[z0,z1,z266,z3,z4,z6]),(0,[z0,z1,z2,z3,z10,z374]),(0,[z0,z251,z2,z12,z4,z6]),(0,[z0,z1,z39,z12,z40,z6]),(0,[z0,z1,z2,z3,z354,z6]),(0,[z102,z1,z2,z3,z840,z6]),(0,[z258,z0,z1,z2,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z1459]),(0,[z0,z1,z2,z3,z1460,z6]),(0,[z0,z300,z366,z3,z4,z6]),(0,[z0,z1,z2,z3,z1461,z6]),(0,[z0,z1,z132,z2,z6,z381]),(0,[z0,z43,z1,z173,z3,z6]),(0,[z0,z1462,z2,z3,z4,z6])],[(0,[z0,z1,z2,z189,z215,z6]),(0,[z0,z1,z2,z3,z1463,z6]),(0,[z0,z1,z2,z7,z4,z167]),(0,[z0,z1,z2,z3,z1464,z6]),(0,[z452,z1,z2,z12,z4,z6]),(0,[z0,z44,z2,z7,z61,z6]),(0,[z0,z1,z49,z7,z40,z6]),(0,[z0,z1,z2,z3,z1465,z6]),(0,[z1,z2,z3,z4,z6,z1466])],[(0,[z0,z1,z3,z1311,z4,z6]),(0,[z0,z1,z2,z3,z222,z6]),(0,[z0,z1,z2,z3,z1467,z6]),(0,[z25,z1164,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z840,z6]),(0,[z283,z0,z1,z779,z3,z6])],[(0,[z0,z1,z2,z3,z1468,z6]),(0,[z0,z1,z2,z3,z1469,z6]),(0,[z0,z141,z1,z173,z3,z6]),(0,[z0,z1,z2,z3,z1470,z6]),(0,[z0,z1,z2,z3,z1471,z6])],[(0,[z0,z1,z12,z831,z4,z6]),(0,[z0,z1,z2,z1108,z4,z6]),(0,[z158,z0,z2,z581,z3,z6])],[(0,[z0,z1,z366,z3,z1078,z6]),(0,[z0,z44,z2,z3,z930,z6]),(0,[z25,z0,z1402,z2,z3,z6]),(0,[z283,z0,z1,z31,z3,z6]),(0,[z550,z1,z2,z3,z6,z317])],[(0,[z0,z1,z266,z12,z4,z6]),(0,[z0,z1,z266,z3,z11,z6]),(0,[z0,z1,z2,z3,z4,z1472]),(0,[z689,z0,z2,z3,z4,z22]),(0,[z0,z1,z2,z1473,z4,z6]),(0,[z0,z1,z2,z3,z1474,z6]),(0,[z1,z2,z487,z7,z4,z6]),(0,[z25,z0,z21,z1,z2,z6]),(1,[z258,z0,z1,z3,z72]),(0,[z0,z1,z2,z3,z36,z711])],[(0,[z0,z1,z2,z274,z255,z6]),(0,[z0,z1,z2,z1208,z7,z6]),(0,[z0,z300,z2,z3,z13,z6]),(0,[z25,z0,z1,z2,z405,z6]),(0,[z0,z1,z2,z4,z6,z1475]),(0,[z0,z1,z2,z3,z1476,z6]),(0,[z335,z0,z2,z3,z6,z345])],[(0,[z0,z1,z2,z189,z13,z6]),(0,[z0,z1,z2,z3,z1477,z6]),(0,[z0,z285,z2,z280,z4,z6]),(0,[z107,z1,z2,z7,z67,z6]),(0,[z0,z1,z2,z1478,z3,z6]),(0,[z0,z32,z91,z3,z40,z6])],[(0,[z0,z1479,z1,z3,z4,z6]),(0,[z0,z1,z2,z280,z4,z6]),(0,[z0,z1,z366,z3,z4,z6]),(0,[z0,z1,z2,z1297,z3,z6]),(0,[z0,z1,z2,z3,z1480,z6]),(1,[z1,z2,z3,z840,z6]),(0,[z1,z2,z3,z4,z6,z738]),(0,[z25,z0,z32,z91,z3,z6]),(0,[z0,z1,z2,z3,z1481,z6]),(0,[z0,z1,z2,z3,z1482,z6])],[],[(0,[z0,z1,z2,z3,z4,z738]),(0,[z1483,z1,z2,z3,z4,z6])],[(0,[z127,z0,z1,z173,z3,z6]),(0,[z0,z1,z2,z370,z4,z6]),(0,[z25,z0,z1,z2,z3,z75]),(0,[z0,z1,z2,z3,z1484,z6]),(0,[z258,z0,z1,z2,z3,z324]),(0,[z0,z1,z2,z3,z204,z6]),(0,[z0,z1,z2,z1428,z52,z6])],[(0,[z0,z1,z2,z3,z1485,z6]),(0,[z0,z32,z91,z7,z4,z6]),(0,[z48,z0,z1,z3,z13,z72]),(0,[z210,z0,z1,z2,z3,z36]),(0,[z0,z1,z2,z1486,z4,z6]),(0,[z0,z1,z2,z3,z1487,z6])],[(0,[z25,z0,z1,z2,z270,z6]),(0,[z0,z1,z2,z3,z1488,z6])]],
   [[(0,[z0,z1,z1489,z2,z4,z6]),(0,[z0,z1,z2,z1490,z3,z6]),(0,[z0,z1491,z2,z3,z4,z6])],[(0,[z0,z1,z266,z3,z56,z6]),(0,[z0,z1492,z2,z3,z4,z6]),(0,[z0,z141,z19,z3,z13,z6])],[(0,[z0,z1,z2,z7,z198,z6]),(0,[z0,z1,z3,z365,z40,z6]),(0,[z0,z1,z2,z3,z6,z1493])],[(0,[z0,z1,z545,z3,z1494,z6]),(0,[z0,z1,z2,z409,z4,z597]),(0,[z0,z1,z2,z7,z201,z6]),(1,[z1,z2,z3,z4,z738]),(0,[z0,z1,z2,z194,z3,z6])],[(0,[z0,z1,z2,z1495,z4,z6]),(0,[z0,z1,z2,z3,z6,z1496]),(0,[z0,z1,z2,z1497,z4,z6]),(0,[z0,z1,z2,z3,z1498,z6]),(0,[z0,z1,z2,z271,z533,z6]),(0,[z0,z1499,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z295])],[(0,[z0,z251,z2,z3,z52,z6])],[(0,[z214,z236,z2,z454,z4,z6]),(0,[z0,z1,z2,z4,z6,z1500]),(0,[z1,z2,z3,z840,z4,z6]),(0,[z0,z1,z2,z3,z1501,z6]),(0,[z0,z300,z2,z382,z4,z6])],[(0,[z0,z1,z545,z3,z13,z6]),(0,[z1,z2,z12,z4,z651,z6])],[(0,[z0,z1502,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1503,z6]),(0,[z1,z2,z7,z12,z13,z6]),(0,[z0,z1,z2,z287,z62,z6]),(0,[z369,z0,z132,z2,z3,z22]),(0,[z0,z1,z2,z3,z6,z1504]),(0,[z1505,z1,z2,z3,z4,z6])],[(0,[z25,z0,z1,z2,z54,z6]),(0,[z0,z1,z2,z1506,z3,z6]),(0,[z0,z1,z2,z3,z197,z36])],[(0,[z0,z1507,z2,z3,z4,z6]),(0,[z1366,z0,z1,z2,z3,z167]),(0,[z0,z1,z2,z7,z33,z6]),(0,[z25,z0,z1,z366,z3,z6]),(0,[z0,z1,z2,z3,z1508,z6]),(0,[z0,z1509,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z1510,z6]),(0,[z0,z1,z2,z12,z292,z6]),(0,[z680,z1,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z354,z60]),(0,[z0,z1,z389,z3,z40,z6]),(0,[z0,z88,z2,z776,z4,z6]),(0,[z0,z1,z2,z1511,z4,z6]),(0,[z0,z1,z2,z3,z53,z72]),(0,[z431,z0,z192,z2,z3,z6])],[(0,[z0,z1,z2,z12,z6,z295]),(0,[z0,z1512,z1,z2,z4,z6]),(0,[z328,z1,z2,z3,z13,z6]),(0,[z369,z0,z2,z4,z381,z22])],[(0,[z0,z1,z2,z3,z40,z70]),(0,[z0,z1,z2,z3,z1513,z6]),(0,[z0,z1,z110,z26,z13,z6]),(0,[z34,z1,z2,z3,z4,z60]),(0,[z25,z0,z1,z110,z26,z6])],[(0,[z0,z1,z2,z3,z1514,z6]),(0,[z369,z0,z2,z3,z36,z22]),(0,[z0,z1,z2,z3,z1515,z6]),(0,[z0,z1,z2,z3,z217,z6]),(0,[z0,z1,z31,z3,z36,z6])],[(0,[z0,z1,z1134,z3,z4,z6]),(0,[z0,z1,z2,z220,z4,z597]),(0,[z0,z1,z2,z1516,z3,z6]),(0,[z25,z0,z1,z2,z1219,z6])]],
   [[(0,[z909,z0,z1,z2,z3,z447]),(0,[z0,z1,z2,z382,z4,z6]),(0,[z0,z1,z2,z3,z383,z6]),(0,[z0,z1,z2,z3,z1517,z6])],[(0,[z0,z285,z71,z3,z4,z6]),(0,[z0,z1,z2,z3,z1518,z6])],[(0,[z0,z1,z2,z7,z4,z70]),(0,[z0,z1,z2,z3,z1519,z6]),(0,[z0,z1,z2,z3,z1520,z6]),(0,[z25,z0,z1,z2,z998,z6])],[(0,[z0,z1,z2,z521,z116,z6]),(0,[z0,z1,z2,z3,z6,z317]),(0,[z0,z1,z2,z10,z6,z135]),(0,[z0,z1,z2,z3,z1521,z6])],[(0,[z667,z236,z2,z3,z4,z6]),(0,[z0,z1,z314,z3,z36,z6]),(0,[z0,z1,z2,z3,z1522,z6]),(0,[z0,z1,z2,z3,z1523,z6]),(0,[z23,z0,z1,z173,z3,z6])],[(0,[z25,z0,z1,z2,z454,z6]),(0,[z0,z1,z2,z3,z1524,z6]),(0,[z0,z1,z2,z3,z1525,z6]),(0,[z210,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1526,z6]),(0,[z0,z1,z3,z40,z6,z72]),(0,[z0,z1,z2,z104,z770,z6])],[(0,[z0,z1,z2,z3,z1527,z6]),(0,[z0,z1,z2,z12,z217,z6]),(0,[z0,z1,z366,z3,z4,z60])],[(0,[z0,z24,z1,z29,z13,z6]),(0,[z369,z0,z2,z3,z10,z22]),(0,[z0,z1,z31,z3,z10,z6]),(0,[z0,z1,z19,z173,z3,z6]),(0,[z0,z1,z2,z3,z930,z6]),(0,[z0,z1,z2,z1528,z4,z6])],[(0,[z0,z285,z2,z307,z4,z6]),(0,[z0,z1,z2,z280,z52,z6]),(0,[z0,z1,z2,z7,z6,z1430]),(0,[z233,z1,z2,z370,z13,z6]),(0,[z0,z1,z366,z3,z52,z6])],[(0,[z0,z1,z2,z307,z4,z6]),(0,[z0,z251,z2,z3,z40,z6]),(0,[z0,z1,z2,z3,z1529,z6])],[(0,[z0,z1,z2,z12,z1398,z6]),(0,[z0,z1,z2,z3,z1530,z6]),(0,[z0,z1,z784,z3,z4,z6])],[(0,[z0,z1,z2,z54,z4,z70]),(0,[z0,z1,z2,z7,z346,z6]),(0,[z0,z1,z2,z12,z6,z317]),(0,[z0,z1,z1531,z3,z4,z6]),(0,[z0,z114,z1,z187,z4,z6]),(0,[z0,z1,z2,z370,z52,z6]),(0,[z0,z1,z2,z220,z13,z93]),(0,[z0,z1,z313,z2,z204,z6])],[(0,[z0,z1,z2,z270,z4,z70]),(0,[z51,z1,z2,z3,z467,z6]),(0,[z0,z1532,z2,z3,z4,z6]),(0,[z25,z0,z1,z2,z382,z6]),(0,[z0,z1,z2,z3,z1533,z6])],[(0,[z1,z2,z35,z3,z467,z6]),(0,[z0,z1,z314,z3,z10,z6]),(0,[z0,z1,z2,z3,z1534,z6]),(0,[z0,z1,z2,z3,z1535,z6]),(0,[z0,z1,z2,z3,z1536,z6])],[(0,[z214,z236,z2,z3,z482,z6]),(0,[z0,z1,z3,z143,z292,z6]),(0,[z0,z251,z2,z7,z4,z6]),(0,[z0,z1,z39,z7,z40,z6]),(0,[z1,z2,z3,z45,z6,z317]),(0,[z0,z1,z2,z3,z1537,z6])],[(0,[z25,z0,z1,z2,z12,z106]),(0,[z164,z0,z1,z3,z155,z6]),(0,[z1,z2,z3,z675,z10,z6]),(0,[z0,z1,z2,z3,z1538,z6])]],
   [[(0,[z0,z1539,z1,z2,z4,z6]),(0,[z0,z88,z2,z4,z6,z130]),(0,[z0,z184,z2,z3,z61,z6])],[(0,[z0,z1,z266,z3,z40,z6]),(0,[z0,z1,z302,z3,z40,z6]),(0,[z0,z1,z1319,z3,z4,z6]),(0,[z0,z1,z2,z3,z648,z53])],[(0,[z0,z300,z314,z3,z4,z6]),(0,[z59,z251,z2,z3,z4,z60]),(0,[z0,z1,z2,z3,z1540,z6]),(0,[z0,z1,z2,z3,z1541,z6]),(0,[z0,z1,z2,z1542,z3,z6]),(0,[z0,z1,z2,z3,z1543,z6]),(0,[z0,z1,z2,z3,z1544,z6]),(0,[z0,z1,z2,z3,z6,z1545])],[(0,[z0,z1,z2,z1546,z4,z6]),(0,[z1547,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z126,z83,z6]),(0,[z0,z1,z2,z3,z1548,z6]),(0,[z0,z1,z2,z3,z6,z1549]),(0,[z0,z1,z2,z3,z1550,z6]),(0,[z48,z0,z1,z3,z485,z72]),(0,[z25,z0,z1,z796,z3,z6])],[(0,[z0,z1,z2,z3,z1551,z6]),(0,[z0,z1,z2,z984,z4,z6])],[(0,[z0,z1,z1552,z2,z3,z6]),(0,[z0,z1,z2,z3,z1553,z6]),(0,[z0,z1,z7,z40,z6,z72]),(0,[z1,z2,z682,z3,z10,z6]),(0,[z0,z2,z874,z3,z4,z6]),(0,[z0,z1,z2,z3,z1554,z6]),(0,[z0,z1,z173,z287,z3,z6])],[(0,[z0,z1,z266,z7,z4,z6]),(0,[z0,z1,z2,z270,z40,z6]),(0,[z0,z1,z2,z3,z4,z1555]),(0,[z0,z1,z2,z3,z1556,z6]),(0,[z0,z1,z173,z3,z13,z6]),(0,[z0,z1,z314,z3,z151,z6]),(0,[z0,z1,z2,z3,z1557,z6]),(1,[z0,z2,z3,z930,z6]),(0,[z0,z1,z2,z3,z1558,z6]),(0,[z250,z0,z1,z3,z6,z99])],[(0,[z0,z1,z2,z3,z1559,z6]),(0,[z214,z236,z2,z3,z36,z6]),(0,[z0,z1560,z2,z3,z4,z6]),(0,[z25,z0,z1,z31,z12,z6]),(0,[z25,z0,z1,z173,z3,z106]),(0,[z0,z811,z2,z3,z36,z6])],[(0,[z0,z1,z2,z280,z118,z6]),(0,[z0,z231,z19,z3,z4,z6]),(0,[z0,z1,z2,z3,z1561,z6]),(0,[z0,z1,z173,z3,z120,z6])],[(0,[z0,z1,z2,z3,z36,z447]),(0,[z0,z1425,z2,z12,z4,z6]),(0,[z0,z1,z2,z3,z1562,z6]),(0,[z0,z30,z1,z173,z3,z6]),(0,[z0,z1,z110,z471,z4,z6])],[(0,[z0,z1,z2,z358,z4,z131]),(0,[z136,z1,z2,z3,z12,z6]),(0,[z0,z251,z2,z144,z4,z6]),(0,[z0,z32,z91,z3,z33,z6])],[(0,[z0,z236,z266,z3,z4,z6]),(0,[z0,z1,z2,z249,z255,z6]),(0,[z0,z1,z2,z3,z1563,z6]),(0,[z0,z1,z2,z4,z6,z1564]),(0,[z0,z32,z91,z3,z96,z6]),(0,[z0,z1,z3,z198,z6,z99])],[(0,[z0,z1,z2,z280,z40,z6]),(0,[z0,z1,z2,z3,z1565,z6]),(0,[z624,z1,z2,z3,z13,z6]),(0,[z0,z1,z2,z1566,z4,z6])],[(0,[z0,z1,z2,z1427,z3,z6]),(0,[z695,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z319,z13,z6])],[(0,[z0,z1,z2,z3,z1567,z6]),(0,[z0,z1,z2,z3,z346,z167]),(0,[z1568,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z382,z52,z6]),(0,[z0,z1,z2,z3,z4,z1569]),(0,[z0,z1570,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1571,z6]),(0,[z0,z1,z173,z3,z116,z6])],[(0,[z0,z1,z266,z54,z4,z6]),(0,[z0,z1,z2,z12,z346,z6]),(0,[z0,z1,z173,z3,z12,z6]),(0,[z210,z0,z1,z875,z3,z6]),(0,[z0,z1,z2,z109,z277,z6]),(0,[z25,z0,z938,z2,z3,z6])]],
   [[(0,[z214,z236,z2,z3,z10,z6]),(0,[z802,z0,z1,z2,z12,z4]),(0,[z0,z1,z2,z1572,z4,z6]),(0,[z0,z1,z2,z3,z1573,z6]),(0,[z0,z1,z49,z3,z40,z72]),(0,[z514,z0,z148,z2,z3,z6])],[(0,[z0,z430,z2,z3,z4,z6]),(0,[z34,z1,z35,z3,z4,z6]),(0,[z0,z1574,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1575,z6])],[(0,[z0,z1,z2,z3,z10,z447]),(0,[z0,z1576,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1577,z6]),(0,[z50,z25,z1,z35,z3,z6]),(0,[z0,z1,z2,z3,z1578,z6]),(0,[z23,z0,z1,z2,z40,z8]),(0,[z0,z1,z2,z3,z1579,z6])],[(0,[z0,z1,z2,z27,z62,z6]),(0,[z0,z1,z2,z3,z128,z6]),(0,[z0,z1,z173,z3,z26,z6]),(0,[z0,z1,z2,z3,z1580,z6])],[(0,[z0,z1,z2,z758,z4,z6]),(0,[z0,z1581,z2,z3,z4,z6]),(0,[z0,z24,z1,z29,z403,z6]),(0,[z0,z1,z2,z3,z416,z6]),(0,[z250,z0,z1,z177,z3,z6])],[(0,[z0,z1,z2,z3,z1582,z6]),(0,[z0,z1,z2,z3,z1583,z6]),(0,[z0,z1,z2,z173,z12,z6]),(0,[z534,z0,z1,z2,z4,z614]),(0,[z0,z1,z2,z3,z1584,z6]),(0,[z0,z1,z110,z26,z415,z6]),(0,[z0,z1,z173,z29,z3,z6]),(0,[z0,z1,z173,z3,z93,z6])],[(0,[z214,z236,z2,z189,z4,z6]),(0,[z0,z1,z2,z1585,z4,z6]),(0,[z59,z0,z1,z173,z3,z6])],[(0,[z0,z1,z2,z3,z1586,z6]),(0,[z0,z1,z2,z307,z52,z6]),(0,[z0,z1,z2,z3,z1587,z6]),(0,[z0,z1,z2,z3,z1588,z6]),(0,[z603,z1,z2,z3,z350,z6])],[(0,[z0,z1,z2,z1589,z4,z6]),(0,[z0,z1,z2,z1590,z4,z6]),(0,[z0,z1,z3,z831,z10,z6]),(0,[z0,z1,z173,z3,z1591,z6])],[(0,[z0,z1,z2,z109,z13,z6]),(0,[z0,z1,z1592,z2,z3,z6]),(0,[z0,z1,z2,z179,z116,z6])],[(0,[z0,z1,z2,z7,z292,z6]),(0,[z0,z1,z2,z12,z354,z6]),(0,[z0,z1,z2,z177,z12,z6]),(0,[z0,z1,z2,z405,z36,z6]),(0,[z0,z1,z2,z1593,z4,z6]),(0,[z0,z1,z2,z3,z339,z36]),(0,[z0,z1,z2,z3,z218,z53]),(0,[z0,z332,z2,z3,z595,z6])],[(0,[z0,z1,z2,z7,z6,z295]),(0,[z0,z1,z2,z3,z277,z6]),(1,[z0,z1,z875,z3,z6]),(0,[z0,z1,z488,z3,z40,z6])],[(0,[z0,z1,z2,z3,z782,z6]),(0,[z0,z1,z2,z1594,z4,z6]),(0,[z0,z1,z2,z3,z1595,z6])],[(0,[z0,z1,z2,z3,z215,z6]),(0,[z0,z1,z3,z4,z6,z1596]),(0,[z1597,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z12,z222,z6]),(0,[z0,z1,z2,z4,z6,z1598]),(0,[z0,z1,z2,z7,z1374,z6]),(0,[z0,z1,z2,z119,z7,z6]),(0,[z0,z1,z1599,z2,z3,z6])],[(0,[z0,z1,z35,z3,z4,z374]),(0,[z0,z1,z740,z3,z4,z6]),(0,[z102,z1,z2,z103,z10,z6]),(0,[z0,z1,z2,z40,z6,z381]),(0,[z0,z1,z2,z121,z384,z6])],[(0,[z214,z236,z2,z3,z4,z6]),(0,[z0,z1,z2,z826,z3,z6]),(0,[z0,z1,z2,z3,z1600,z6])]],
   [[(0,[z0,z285,z2,z3,z4,z374]),(0,[z94,z1,z35,z3,z4,z6]),(0,[z0,z1,z2,z3,z785,z6]),(0,[z311,z0,z1,z3,z143,z6]),(0,[z0,z1,z2,z3,z1601,z6]),(0,[z0,z1,z2,z3,z1602,z6]),(0,[z0,z1,z2,z4,z734,z8]),(0,[z539,z0,z1,z31,z3,z6])],[(0,[z0,z1,z2,z3,z1494,z6]),(0,[z0,z1,z2,z3,z4,z374]),(0,[z0,z1,z2,z3,z58,z354]),(0,[z48,z0,z1,z177,z3,z72]),(0,[z25,z0,z1,z2,z3,z404])],[(0,[z65,z1,z2,z12,z13,z6]),(0,[z25,z0,z1260,z2,z3,z6])],[(0,[z0,z1,z2,z1603,z4,z6]),(0,[z0,z1,z2,z3,z1169,z6]),(0,[z0,z1,z2,z12,z277,z6]),(0,[z0,z1,z2,z405,z10,z6]),(0,[z0,z30,z2,z120,z512,z6]),(0,[z0,z1,z2,z4,z6,z381]),(0,[z0,z1,z2,z1604,z3,z6])],[(0,[z0,z1,z2,z1605,z4,z6]),(0,[z426,z90,z2,z3,z4,z6]),(0,[z0,z285,z2,z3,z13,z6]),(0,[z0,z1,z2,z280,z4,z167]),(0,[z50,z1,z35,z3,z155,z6]),(0,[z1,z2,z12,z176,z4,z6]),(0,[z560,z1,z2,z3,z10,z6]),(0,[z514,z0,z1,z173,z3,z6])],[(0,[z0,z1,z2,z3,z13,z6]),(0,[z0,z1,z2,z12,z215,z6]),(0,[z0,z1,z2,z1606,z3,z6]),(0,[z25,z0,z1,z2,z3,z374]),(0,[z0,z1,z366,z12,z4,z6]),(0,[z0,z1,z2,z7,z217,z6])],[(0,[z0,z1,z545,z3,z4,z447]),(0,[z0,z1,z2,z3,z1252,z6]),(0,[z0,z21,z1,z2,z489,z6]),(0,[z0,z1,z2,z3,z1607,z6])],[(0,[z107,z1,z2,z7,z232,z6]),(0,[z0,z1,z2,z7,z383,z6])],[(0,[z0,z1,z2,z3,z1608,z6]),(0,[z0,z1,z2,z3,z1609,z6]),(0,[z0,z1,z2,z12,z204,z6]),(0,[z0,z1,z2,z1610,z3,z6]),(0,[z136,z1,z2,z3,z45,z6]),(0,[z0,z1,z2,z3,z1611,z6]),(0,[z0,z1,z2,z3,z1612,z6])],[(0,[z0,z1,z2,z3,z1613,z6]),(0,[z136,z1,z90,z2,z3,z6]),(0,[z0,z1,z2,z12,z4,z374]),(0,[z0,z1,z2,z169,z116,z6]),(0,[z1614,z0,z1,z173,z3,z6])],[(0,[z0,z1,z12,z52,z40,z6]),(0,[z0,z1,z12,z4,z6,z972]),(0,[z0,z1,z2,z7,z6,z317]),(0,[z0,z1,z2,z4,z93,z191]),(0,[z1615,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z4,z1200,z6])],[(0,[z0,z236,z1,z173,z3,z6]),(0,[z50,z1,z35,z3,z36,z6]),(0,[z1,z2,z12,z10,z13,z6]),(0,[z59,z1,z2,z382,z4,z60]),(0,[z59,z1,z2,z3,z383,z60]),(0,[z0,z1,z2,z1616,z4,z6])],[(0,[z0,z497,z91,z3,z4,z6]),(0,[z0,z1,z2,z3,z1617,z6]),(0,[z0,z1,z2,z3,z814,z6]),(0,[z0,z1,z2,z3,z1618,z6]),(0,[z48,z0,z1,z3,z4,z748])],[(0,[z0,z1,z2,z3,z1619,z6]),(0,[z0,z1,z2,z12,z13,z6]),(0,[z0,z19,z874,z3,z4,z6]),(0,[z0,z1,z2,z3,z1620,z6]),(0,[z0,z1,z1621,z3,z4,z6]),(0,[z25,z0,z1,z2,z3,z98])],[(0,[z0,z1,z71,z3,z143,z6]),(0,[z0,z1,z2,z3,z856,z6]),(0,[z0,z1,z2,z3,z1622,z6]),(0,[z0,z1,z2,z578,z379,z6])],[(0,[z0,z1,z2,z3,z1623,z6]),(0,[z0,z430,z2,z3,z52,z6]),(0,[z0,z1624,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z863,z6]),(0,[z0,z1,z2,z3,z6,z1625]),(0,[z59,z136,z1,z2,z3,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 479) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 479).take 473) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 952).take 478) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1430).take 275) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1705)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [479, 473, 478, 275] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 94).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 94).take 93).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 187).take 93).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 280).take 99).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 379).take 95).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 474).take 38).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [94, 93, 93, 99, 95, 38] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_nil pcend))))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_40325

theorem PEqualNP.Outside.L_meta_40325 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4276677832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4276677832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40325.solve
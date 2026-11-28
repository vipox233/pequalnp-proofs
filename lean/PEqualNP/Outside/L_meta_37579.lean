import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37579

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
  Nat.testBit (4276809450 * 2 ^ 32 + 4276791968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0200000050005154#64 ++ 0x0080000014001455#64 ++ 0xfd013911f011ffff#64 ++ 0xff404e447c047fff#64 : BitVec 256),
   (0x04425266c866cb30#64 ++ 0x81109499b219b2cc#64 ++ 0xfb46d6eec8eecb33#64 ++ 0x7ed1b5bbb23bb2cc#64 : BitVec 256),
   (0xa818a70b0b0b0c29#64 ++ 0x2a0629c2c2c2c30a#64 ++ 0xb7b8e70f0f0f0c3e#64 ++ 0xedee39c3c3c3c30f#64 : BitVec 256),
   (0x302d07b00db00e82#64 ++ 0x4c0b41ec036c03a0#64 ++ 0x6fff07f00ff00fc1#64 ++ 0xdbffc1fc03fc03f0#64 : BitVec 256),
   (0xc037f80006dda000#64 ++ 0x700dfe0001b76800#64 ++ 0x1ffff8000ffff003#64 ++ 0xc7fffe0003fffc00#64 : BitVec 256),
   (0x003ffddda0000003#64 ++ 0x800fff7768000000#64 ++ 0xff3ffffff0000000#64 ++ 0x3fcffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.and, [6, 4]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [12, 4]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0200000050005154 0x0080000014001455 0xfd013911f011ffff 0xff404e447c047fff

def z1 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xfb46d6eec8eecb33 0x7ed1b5bbb23bb2cc

def z2 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x6fff07f00ff00fc1 0xdbffc1fc03fc03f0

def z3 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xb7b8e70f0f0f0c3e 0xedee39c3c3c3c30f

def z4 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0xfffffffffffff003 0xfffffffffffffc00

def z5 : W := mkw 0xc477fa66ceffeb30 0xf11dfe99b3bffacc 0xfffffeeecffffb33 0xffffffbbb3fffecc

def z6 : W := mkw 0x000805dda0000003 0x8002017768000000 0xe00007fff0000000 0x380001fffc000000

def z7 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff0000000 0x3fcffffffc000000

def z8 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x0246c6ee08ee0000 0x0091b1bb823b8000

def z9 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x1ffff8000ffff003 0xc7fffe0003fffc00

def z10 : W := mkw 0x001afddda0000003 0x8006bf7768000000 0xf000fffff0000000 0x3c003ffffc000000

def z11 : W := mkw 0x0018a5dda0000003 0x8006297768000000 0xf738e7fff0000000 0x3dce39fffc000000

def z12 : W := mkw 0x4027580004d4a000 0x5009d60001352800 0x0847180000f0f001 0x0211c600003c3c00

def z13 : W := mkw 0x4227580054d4f154 0x5089d60015353c55 0xfd473911f0f1ffff 0xff51ce447c3c7fff

def z14 : W := mkw 0x002758d4a0000002 0x8009d63528000000 0x480718f0f0000000 0x1201c63c3c000000

def z15 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0x023ec6ee00000000 0x008fb1bb80000000

def z16 : W := mkw 0xc037f80006992000 0x700dfe0001a64800 0x1fbff80007113000 0x87effe0001c44c00

def z17 : W := mkw 0x300002200db00e80 0x4c000088036c03a0 0x00c000000ff00fc1 0xc030000003fc03f0

def z18 : W := mkw 0x322d07b05db05fd6 0x4c8b41ec176c17f5 0xffff3ff1fff1ffff 0xffffcffc7ffc7fff

def z19 : W := mkw 0x202d079009000c02 0x080b41e402400300 0x6fbf07f00f000c00 0xdbefc1fc03c00300

def z20 : W := mkw 0x000000d4a0000002 0x8000003528000000 0x400000f0f0000000 0x1000003c3c000000

def z21 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xff47fffff8ffffff 0xffd1fffffe3fffff

def z22 : W := mkw 0x8810a00b020b0029 0x22042802c082c00a 0x9000e00f000f003e 0x24003803c003c00f

def z23 : W := mkw 0x0000000000000000 0x0000000000000000 0xb500210100010c3e 0xed4008404000430f

def z24 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0x4a46d6eec8eec301 0x1291b5bbb23bb0c0

def z25 : W := mkw 0x0200000050005154 0x0080000014001455 0xe8011911f010fffd 0x3a0046447c043fff

def z26 : W := mkw 0x023dad9970005157 0x008f6b665c001455 0xfd393911f011ffff 0xff4e4e447c047fff

def z27 : W := mkw 0x0002504480000000 0x8000941120000000 0xff07fffff0000000 0x3fc1fffffc000000

def z28 : W := mkw 0x302d059005900482 0x4c0b416401640120 0x00b8000007000000 0x002e000001c00000

def z29 : W := mkw 0x0200000050005154 0x0080000014001455 0xf9003801f001fb3f 0x7e400e007c007ecf

def z30 : W := mkw 0x320807b059205fd6 0x0c8201ec164817f5 0xfd013ff1f011ffff 0xff404ffc7c047fff

def z31 : W := mkw 0xac7fffffeb6fcf3b 0xab1ffffffadbf3ce 0xffffffffffefcf3f 0xfffffffffffbf3cf

def z32 : W := mkw 0xc035a80006992000 0x700d6a0001a64800 0x04b9280007113000 0x812e4a0001c44c00

def z33 : W := mkw 0x0037f8dda0000003 0x800dfe3768000000 0xd807f8fff0000000 0x3601fe3ffc000000

def z34 : W := mkw 0x2808070b09020c29 0x0a0201c2c240830a 0xa7b8070f0f000c3c 0xe9ee01c3c3c0030f

def z35 : W := mkw 0x0002504480000000 0x8000941120000000 0xfb06d6eec0000000 0x3ec1b5bbb0000000

def z36 : W := mkw 0x067ffffff866db77 0x819ffffffe19b6dd 0xff7ffffff8ffffff 0xffdffffffe3fffff

def z37 : W := mkw 0x2008070009000c00 0x080201c002400300 0x27b807000f000c00 0xc9ee01c003c00300

def z38 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0xffff27f10ff10fff 0xffffc9fc43fc43ff

def z39 : W := mkw 0xaa18a70b5b0b5d7d 0x2a8629c2d6c2d75f 0xffb9ff1fff1fffff 0xffee7fc7ffc7ffff

def z40 : W := mkw 0x0200000050005154 0x0080000014001455 0x48011810f010f3c1 0x120046043c043cf0

def z41 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0x02b8c60e0f0e0000 0x00ae318383c38000

def z42 : W := mkw 0xe83fff0b0fdfac29 0x7a0fffc2c3f7eb0a 0xb7fee70f0fef0c3e 0xedffb9c3c3fbc30f

def z43 : W := mkw 0x0200000050005154 0x0080000014001455 0x1d0138000011ffff 0xc7404e0000047fff

def z44 : W := mkw 0x0002500000448000 0x0000940000112000 0x1b46d00008eec003 0x46d1b400023bb000

def z45 : W := mkw 0x0200000050005154 0x0080000014001455 0x90003801f001f03e 0x24000e007c007c0f

def z46 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x02fe06e00fe00000 0x00bf81b803f80000

def z47 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x1b46d6ee08eec003 0x46d1b5bb823bb000

def z48 : W := mkw 0xb83da7bb0fbb0eab 0x6e0f69eec3eec3aa 0xffffe7ff0fff0fff 0xfffff9ffc3ffc3ff

def z49 : W := mkw 0x002d05dda0000003 0x800b417768000000 0xef3f07fff0000000 0x3bcfc1fffc000000

def z50 : W := mkw 0xc012f800024da000 0x3004be0000936800 0x1000f800000ff002 0x04003e000003fc00

def z51 : W := mkw 0x047fffffa8668a23 0x811fffffea19a288 0x027ec6ee08ee0000 0x009fb1bb823b8000

def z52 : W := mkw 0x88000002020b0028 0x220000008082c00a 0x00000000000f003e 0x000000000003c00f

def z53 : W := mkw 0x064002225866db74 0x019000889619b6dd 0x0040000008ffffff 0xc0100000023fffff

def z54 : W := mkw 0xc237f80056ddf154 0x708dfe0015b77c55 0xfffff911ffffffff 0xfffffe447fffffff

def z55 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x4aff06f00ff003c1 0x12bfc1bc03fc00f0

def z56 : W := mkw 0x102500b004b00282 0x4409402c012c00a0 0x4fff00f00ff003c1 0xd3ffc03c03fc00f0

def z57 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0xffff3ff1fff00fc1 0xffffcffc7ffc03f0

def z58 : W := mkw 0xc0000000024da000 0x3000000000936800 0x00000000000ff002 0x000000000003fc00

def z59 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0x9246d6eec8eec032 0x2491b5bbb23bb00c

def z60 : W := mkw 0xec7fff6fcfffef39 0xfb1fffdbf3fffbce 0xffffffefcfffff3f 0xfffffffbf3ffffcf

def z61 : W := mkw 0x000a55dda0000003 0x8002957768000000 0xfb06d7fff0000000 0x3ec1b5fffc000000

def z62 : W := mkw 0x0200000050005154 0x0080000014001455 0x6d0101100011ffff 0xdb40404400047fff

def z63 : W := mkw 0xf03fffb00ffdae82 0x7c0fffec03ff6ba0 0x1ffffee00ffff003 0xc7ffffb803fffc00

def z64 : W := mkw 0x023ffdddf0005157 0x808fff777c001455 0xff3ffffff010f3c1 0x3fcffffffc043cf0

def z65 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xfb47defef8fefbf3 0x7ed1f7bfbe3fbefc

def z66 : W := mkw 0x0200000050005154 0x0080000014001455 0xe0000111f0000ffc 0x380000447c0003ff

def z67 : W := mkw 0x002d059000000002 0x000b416400000000 0x0439011000000000 0x010e404400000000

def z68 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x02fec0000fee0000 0x00bfb00003fb8000

def z69 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x0fffc0000ffe0001 0xc3fff00003ff8000

def z70 : W := mkw 0x8010a00002090000 0x2004280000824000 0xb7b8e1010f0f0c3e 0xedee384043c3c30f

def z71 : W := mkw 0x8010a00002090000 0x2004280000824000 0x17b8e0000f0f0002 0xc5ee380003c3c000

def z72 : W := mkw 0x803ffddda2090003 0xa00fff7768824000 0xffbfffffff0f0002 0xffefffffffc3c000

def z73 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x7fff3ff00ff1ffc3 0xdfffcffc03fc7ff0

def z74 : W := mkw 0x0000022008200a00 0x0000008802080280 0x6b4606e008e00b01 0x5ad181b8023802c0

def z75 : W := mkw 0x346f57f6cdf6cfb2 0xcd1bd5fdb37db3ec 0xffffd7fecffecff3 0xfffff5ffb3ffb3fc

def z76 : W := mkw 0x302d05b005b00682 0x4c0b416c016c01a0 0x4cff01f007f007c1 0x933fc07c01fc01f0

def z77 : W := mkw 0x44675a66ccf6eb30 0xd119d699b33dbacc 0xfb47deeec8fefb33 0x7ed1f7bbb23fbecc

def z78 : W := mkw 0x0037f80000000000 0x000dfe0000000000 0x1f3ff80000000000 0x07cffe0000000000

def z79 : W := mkw 0x0000000000000000 0x0000000000000000 0x6d01011000100fc1 0xdb404044000403f0

def z80 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x06ffe8000fff3000 0x81bffa0003ffcc00

def z81 : W := mkw 0x0025000004900000 0x4009400001240000 0x0fff00000ff00001 0xc3ffc00003fc0000

def z82 : W := mkw 0x0200000010001044 0x0080000004000411 0x000028013001300c 0x00000a004c004c03

def z83 : W := mkw 0x2c48076fc9224f39 0x8b1201dbf24893ce 0xe00007efc0000f3c 0x380001fbf00003cf

def z84 : W := mkw 0xf03fffb00ffdae82 0x7c0fffec03ff6ba0 0x7ffffff00fffffc3 0xdffffffc03fffff0

def z85 : W := mkw 0xe83fff0b0fdfac29 0x7a0fffc2c3f7eb0a 0xbfffff0f0ffffc3f 0xefffffc3c3ffff0f

def z86 : W := mkw 0x102d05b004b00282 0x440b416c012c00a0 0x6f7f07f000f003c1 0x1bdfc1fc003c00f0

def z87 : W := mkw 0x0000000040004110 0x0000000010001044 0xf9001000c000cb33 0x7e400400300032cc

def z88 : W := mkw 0x0000000000000000 0x0000000000000000 0xfd013911f0000000 0x3f404e447c000000

def z89 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x02fe06e00ff00fc1 0xc0bf81b803fc03f0

def z90 : W := mkw 0x0200000050005154 0x0080000014001455 0x000000000011ffff 0xc000000000047fff

def z91 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z92 : W := mkw 0x320002205db05fd4 0x4c800088176c17f5 0x00c000000ff1ffff 0xc030000003fc7fff

def z93 : W := mkw 0x2008072009200e00 0x080201c802480380 0x6ffe07e00fe00f01 0xdbff81f803f803c0

def z94 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0x484610e0c8eecb33 0x52118438323bb2cc

def z95 : W := mkw 0x4027580004d4a000 0x5009d60001352800 0x0046000000e00000 0x0011800000380000

def z96 : W := mkw 0xa818a50b030b0429 0x2a062942c0c2c10a 0x94b8e10f070f043e 0xa52e3843c1c3c10f

def z97 : W := mkw 0x2808070b09020c29 0x0a0201c2c240830a 0x0000060e00000000 0x0000018380000000

def z98 : W := mkw 0xb80002220fbb0ea8 0x6e00008883eec3aa 0x00c000000fff0fff 0xc030000003ffc3ff

def z99 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x684707f000f00fc1 0x1a11c1fc003c03f0

def z100 : W := mkw 0xc037f84486dda000 0xf00dfe1121b76800 0xfffffeeecffff003 0xffffffbbb3fffc00

def z101 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0x923efeeff0000000 0x248fbfbbfc000000

def z102 : W := mkw 0xa818a50903090409 0x2a06294240c24102 0x04b821010701040c 0x812e084041c04103

def z103 : W := mkw 0x4000000004d4a000 0x5000000001352800 0x0040000000f0f001 0x00100000003c3c00

def z104 : W := mkw 0x04400266c8224b30 0x81100099b20892cc 0xe00006eec0000b30 0x380001bbb00002cc

def z105 : W := mkw 0x2808070b09020c29 0x0a0201c2c240830a 0xa000070f00000c3c 0x280001c3c000030f

def z106 : W := mkw 0x300002200db00e80 0x4c000088036c03a0 0x00c000000fe00000 0x0030000003f80000

def z107 : W := mkw 0x0200000050005154 0x0080000014001455 0xe4012911f0113ffc 0xb9004a447c044fff

def z108 : W := mkw 0x0000000000000000 0x0000000000000000 0xfd013911f011f003 0xff404e447c047c00

def z109 : W := mkw 0x302d07b009200e82 0x0c0b41ec024803a0 0x6f3f07f000000fc0 0x1bcfc1fc000003f0

def z110 : W := mkw 0x320807b059205fd6 0x0c8201ec164817f5 0xe00007f1f0000ffc 0x380001fc7c0003ff

def z111 : W := mkw 0x04425046c046c130 0x81109411b011b04c 0xf900d00ec00ecb33 0x7e403403b003b2cc

def z112 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xe23ec7fff0000000 0x388fb1fffc000000

def z113 : W := mkw 0x0012f84da0000001 0x8004be1368000000 0xfb06feeff0000000 0x3ec1bfbbfc000000

def z114 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x64b907f007100fc0 0x992e41fc01c403f0

def z115 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x04f901100ff00fc1 0xc13e404403fc03f0

def z116 : W := mkw 0x0000000000000000 0x0000000000000000 0x040021010001040c 0x8100084040004103

def z117 : W := mkw 0x000805dda0000003 0x8002017768000000 0x000006ee00000000 0x000001bb80000000

def z118 : W := mkw 0x064002225866db74 0x019000889619b6dd 0xfd413911f8ffffff 0xff504e447e3fffff

def z119 : W := mkw 0x302d07fdadb00e83 0xcc0b41ff6b6c03a0 0xefff07fffff00fc1 0xfbffc1fffffc03f0

def z120 : W := mkw 0x023ffdddf0005157 0x808fff777c001455 0xff3ffffff011ffff 0xffcffffffc047fff

def z121 : W := mkw 0xc677fa66defffb74 0xf19dfe99b7bffedd 0xffffffffffffffff 0xffffffffffffffff

def z122 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x62fe07f00fe00fc0 0x18bf81fc03f803f0

def z123 : W := mkw 0x06425064d064d354 0x81909419341934d5 0xfd4739f1f0f1ffff 0xff51ce7c7c3c7fff

def z124 : W := mkw 0x0008050900000001 0x0002014240000000 0xa000070f00000000 0x280001c3c0000000

def z125 : W := mkw 0x003ffffda8200a03 0x800fffff6a080280 0xff7ffffff8e00b01 0x7fdffffffe3802c0

def z126 : W := mkw 0x0037f84480000000 0x800dfe1120000000 0xff3ffeeec0000000 0x3fcfffbbb0000000

def z127 : W := mkw 0x8a10a00b520b517d 0x22842802d482d45f 0xfd01f91ff01fffff 0xff407e47fc07ffff

def z128 : W := mkw 0x323ffffdfdb05fd7 0xcc8fffff7f6c17f5 0xfffffffffff1ffff 0xfffffffffffc7fff

def z129 : W := mkw 0xc002500006dda000 0x7000940001b76800 0x1bc6d0000ffff003 0xc6f1b40003fffc00

def z130 : W := mkw 0x0000000000000000 0x0000000000000000 0x0401280000113000 0x81004a0000044c00

def z131 : W := mkw 0x000250004044c110 0x0000940010113044 0xfb46d000c8eecb33 0x7ed1b400323bb2cc

def z132 : W := mkw 0x003daddda0000003 0x800f6b7768000000 0xe4392ffff0000000 0x390e4bfffc000000

def z133 : W := mkw 0x146752f6ccf6cbb2 0xc519d4bdb33db2ec 0xfb47d6fec8fecbf3 0x7ed1f5bfb23fb2fc

def z134 : W := mkw 0x0002500000000000 0x0000940000000000 0x1b06d00000000000 0x06c1b40000000000

def z135 : W := mkw 0x047fffffe866cb33 0x811ffffffa19b2cc 0xff7ffffff8eecb33 0x7fdffffffe3bb2cc

def z136 : W := mkw 0x0218a50950005155 0x0086294254001455 0xff39ff1ff011ffff 0xffce7fc7fc047fff

def z137 : W := mkw 0x366f57f6ddf6dff6 0xcd9bd5fdb77db7fd 0xffffffffffffffff 0xffffffffffffffff

def z138 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0xbffff9010ffffc3f 0xeffffe4043ffff0f

def z139 : W := mkw 0x502758b004f4a282 0x5409d62c013d28a0 0x484718f000f0f3c1 0x1211c63c003c3cf0

def z140 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xffb9ff1fff0f0c3e 0xffee7fc7ffc3c30f

def z141 : W := mkw 0x0018a70b08020821 0x000629c2c2008208 0xb738e70f080e0832 0x6dce39c3c203820c

def z142 : W := mkw 0x0237f80050005154 0x008dfe0014001455 0xff3ff911f011ffff 0xffcffe447c047fff

def z143 : W := mkw 0x0200000010001044 0x0080000004000411 0xb501291130113cfe 0xed404a444c044f3f

def z144 : W := mkw 0x0200000010001044 0x0080000004000411 0x1d0139113011f4cf 0xc7404e444c047d33

def z145 : W := mkw 0xc035a80006dda000 0x700d6a0001b76800 0x04f928000ffff003 0xc13e4a0003fffc00

def z146 : W := mkw 0x045af76fc866cb31 0x8116bddbf219b2cc 0xff7ef7efc8eecb33 0x7fdfbdfbf23bb2cc

def z147 : W := mkw 0x0000000000000000 0x0000000000000000 0x04010110001004c0 0x8100404400040130

def z148 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0x4a3fdefef0000000 0x128ff7bfbc000000

def z149 : W := mkw 0x403ffddda4d4a003 0xd00fff7769352800 0xff7ffffff0f0f001 0x3fdffffffc3c3c00

def z150 : W := mkw 0x303ffffdadb00e83 0xcc0fffff6b6c03a0 0xfffffffffff00fc1 0xfffffffffffc03f0

def z151 : W := mkw 0x302d059005900482 0x4c0b416401640120 0x04b90110071004c0 0x812e404401c40130

def z152 : W := mkw 0x303ffddda5900483 0xcc0fff7769640120 0xffbffffff71004c0 0xbfeffffffdc40130

def z153 : W := mkw 0xf03dafb00fb92e82 0x7c0f6bec03ee4ba0 0x6fff2ff00ff13fc1 0xdbffcbfc03fc4ff0

def z154 : W := mkw 0xc010a00006dda000 0x7004280001b76800 0x17f8e0000ffff003 0xc5fe380003fffc00

def z155 : W := mkw 0xa818a7090b090c09 0x2a0629c242c24302 0x27b827010f010c0c 0xc9ee09c043c04303

def z156 : W := mkw 0xc037f8d4a6dda002 0xf00dfe3529b76800 0x5ffff8f0fffff003 0xd7fffe3c3ffffc00

def z157 : W := mkw 0xc03dad9926992003 0x700f6b6649a64800 0x04b9291137113000 0x812e4a444dc44c00

def z158 : W := mkw 0xaa0002025b0b5d7c 0x2a80008096c2d75f 0x008000000f1fffff 0xc020000003c7ffff

def z159 : W := mkw 0x04400266c8224b30 0x81100099b20892cc 0xeb4606eec8e00b31 0x7ad181bbb23802cc

def z160 : W := mkw 0xc000000006dda000 0x7000000001b76800 0x00c000000fee0000 0x0030000003fb8000

def z161 : W := mkw 0x0027580000000000 0x0009d60000000000 0x0807180000000000 0x0201c60000000000

def z162 : W := mkw 0x0000020208020820 0x0000008082008208 0xb300c60e080e0832 0x6cc031838203820c

def z163 : W := mkw 0x0200000050005154 0x0080000014001455 0xfd013911f010f3c1 0x3f404e447c043cf0

def z164 : W := mkw 0x102500b004b00282 0x4409402c012c00a0 0x484700f000f003c1 0x1211c03c003c00f0

def z165 : W := mkw 0x002f5dd4a0000002 0x800bd77528000000 0x6f3f1ff0f0000000 0x1bcfc7fc3c000000

def z166 : W := mkw 0xa018a7000b090c00 0x280629c002c24300 0x37b8e7000f0f0c02 0xcdee39c003c3c300

def z167 : W := mkw 0x0200000050005154 0x0080000014001455 0xfd013911f001f03e 0x3f404e447c007c0f

def z168 : W := mkw 0x0025000004900000 0x4009400001240000 0x02fe00000fe00000 0x00bf800003f80000

def z169 : W := mkw 0xc000000006dda000 0x7000000001b76800 0x00c000000ffff003 0xc030000003fffc00

def z170 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x6b46c6ee08ee0b01 0x5ad1b1bb823b82c0

def z171 : W := mkw 0x303dafb92db00e83 0x4c0f6bee4b6c03a0 0x6fff2ff13ff00fc1 0xdbffcbfc4ffc03f0

def z172 : W := mkw 0x002d059000000002 0x000b416400000000 0x6f3f07f000000000 0x1bcfc1fc00000000

def z173 : W := mkw 0x0018a50900000001 0x0006294240000000 0xb738e70f00000000 0x2dce39c3c0000000

def z174 : W := mkw 0x8000000002090000 0x2000000000824000 0x008000000f0f0002 0xc020000003c3c000

def z175 : W := mkw 0x0200000010001044 0x0080000004000411 0x04012911301134cc 0x81004a444c044d33

def z176 : W := mkw 0xa80002020b0b0c28 0x2a00008082c2c30a 0x008000000f0f0c3e 0xc020000003c3c30f

def z177 : W := mkw 0x0010a00000000000 0x0004280000000000 0x1738e00000000000 0x05ce380000000000

def z178 : W := mkw 0x0000000000000000 0x0000000000000000 0x190010000000c003 0x4640040000003000

def z179 : W := mkw 0x0000000000000000 0x0000000000000000 0x1d0138000011f003 0xc7404e0000047c00

def z180 : W := mkw 0x0442506480648200 0x8110941920192080 0x004600e000e00000 0x0011803800380000

def z181 : W := mkw 0xf83fffbb0fffaeab 0x7e0fffeec3ffebaa 0xffffffff0fffffff 0xffffffffc3ffffff

def z182 : W := mkw 0x0000000000000000 0x0000000000000000 0xf9001000c0000000 0x3e40040030000000

def z183 : W := mkw 0x300807b009200e82 0x0c0201ec024803a0 0x600007f000000fc0 0x180001fc000003f0

def z184 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff0100fc1 0xffcffffffc0403f0

def z185 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xffb9e71f0f1f0fff 0xffee79c7c3c7c3ff

def z186 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xfb46feeff8effb3f 0x7ed1bfbbfe3bfecf

def z187 : W := mkw 0xc03ffddda24da003 0xb00fff7768936800 0xff3ffffff00ff002 0x3fcffffffc03fc00

def z188 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff0010c3e 0xffcffffffc00430f

def z189 : W := mkw 0xa83da70b0f9b0c29 0x6a0f69c2c3e6c30a 0xbfffe70f0fff0c3f 0xeffff9c3c3ffc30f

def z190 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xbfb9ff0f0f1ffc3f 0xefee7fc3c3c7ff0f

def z191 : W := mkw 0x0000000000000000 0x0000000000000000 0x90003801f0000000 0x24000e007c000000

def z192 : W := mkw 0x04675266ccf6cb30 0xc119d499b33db2cc 0xffffd6eecffecb33 0xfffff5bbb3ffb2cc

def z193 : W := mkw 0x382d07bb0db20eab 0x4e0b41eec36c83aa 0xefff07ff0ff00ffd 0xfbffc1ffc3fc03ff

def z194 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x02fec0000ffff003 0xc0bfb00003fffc00

def z195 : W := mkw 0x0002504480000000 0x8000941120000000 0x480610e0c0000000 0x1201843830000000

def z196 : W := mkw 0x04425046c046c130 0x81109411b011b04c 0x9000d00ec00ec032 0x24003403b003b00c

def z197 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0x02b8c60e0f0f0c3e 0xc0ae318383c3c30f

def z198 : W := mkw 0x302d07b20db20ea2 0x4c0b41ec836c83a8 0xffffc7fe0ffe0ff3 0xfffff1ff83ff83fc

def z199 : W := mkw 0xa818a50903090409 0x2a06294240c24102 0x17b8e1010f0f040e 0xc5ee384043c3c103

def z200 : W := mkw 0x0002504480448000 0x8000941120112000 0xfb46d6eec8eec003 0x7ed1b5bbb23bb000

def z201 : W := mkw 0xa818a50903090409 0x2a06294240c24102 0x00b8000007000000 0x002e000001c00000

def z202 : W := mkw 0x346f57f68df68ea2 0xcd1bd5fda37da3a8 0x6fffc7fe0ffe0fc1 0xdbfff1ff83ff83f0

def z203 : W := mkw 0x8035a00006990000 0x600d680001a64000 0x1fffe0000fff0003 0xc7fff80003ffc000

def z204 : W := mkw 0x34425266cdf6cfb0 0xcd109499b37db3ec 0xfbc6d6eecffecff3 0xfef1b5bbb3ffb3fc

def z205 : W := mkw 0x8210a00052095154 0x2084280014825455 0xffb9f911ff1fffff 0xffee7e447fc7ffff

def z206 : W := mkw 0x002d059000000002 0x000b416400000000 0x023e06e000000000 0x008f81b800000000

def z207 : W := mkw 0xc012f80006dda000 0x7004be0001b76800 0x10c0f8000ffff003 0xc4303e0003fffc00

def z208 : W := mkw 0xc477fa668effaa20 0xf11dfe99a3bfea88 0x1ffffeee0ffff003 0xc7ffffbb83fffc00

def z209 : W := mkw 0xa818a50903090409 0x2a06294240c24102 0xb5b8210107010c3e 0xed6e084041c0430f

def z210 : W := mkw 0x2808070b09020c29 0x0a0201c2c240830a 0xb500270f00010c3e 0xed4009c3c000430f

def z211 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x14b9f800071ff002 0x852e7e0001c7fc00

def z212 : W := mkw 0x0027500004d48000 0x4009d40001352000 0x1fffd0000ffec003 0xc7fff40003ffb000

def z213 : W := mkw 0xc477f864c6fde310 0xf11dfe1931bf78c4 0x5ffff8e0cffff303 0xd7fffe3833fffcc0

def z214 : W := mkw 0x0225000054905154 0x4089400015241455 0xffff3911fff1ffff 0xffffce447ffc7fff

def z215 : W := mkw 0x0000000000000000 0x0000000000000000 0x48011810f0000000 0x120046043c000000

def z216 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0xfffff911fffff003 0xfffffe447ffffc00

def z217 : W := mkw 0x302d059005900482 0x4c0b416401640120 0x6db9011007100fc1 0xdb6e404401c403f0

def z218 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xe84616eec0e0cb31 0x3a1185bbb03832cc

def z219 : W := mkw 0x0012f84da0000001 0x8004be1368000000 0x0000c00e00000000 0x0000300380000000

def z220 : W := mkw 0x0200000050005154 0x0080000014001455 0x040129113011ffff 0xc1004a444c047fff

def z221 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0x04b821010f0f0c3e 0xc12e084043c3c30f

def z222 : W := mkw 0x0000020208020820 0x0000008082008208 0x0200c60e080e0000 0x0080318382038000

def z223 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff011f003 0xffcffffffc047c00

def z224 : W := mkw 0x0002500000448000 0x0000940000112000 0x1000d000000ec002 0x040034000003b000

def z225 : W := mkw 0x04400046c0024130 0x81100011b000904c 0x8000000ec0000030 0x20000003b000000c

def z226 : W := mkw 0x0000000040004110 0x0000000010001044 0xfd003101c001cf3f 0xff400c40700073cf

def z227 : W := mkw 0x003dad9920000003 0x000f6b6648000000 0x0439291130000000 0x010e4a444c000000

def z228 : W := mkw 0x044002224866cb30 0x011000889219b2cc 0x0040000008eecb33 0x40100000023bb2cc

def z229 : W := mkw 0x04425064c064c310 0x81109419301930c4 0x484610e0c0e0c301 0x12118438303830c0

def z230 : W := mkw 0xf02d07b00ffdae82 0x7c0b41ec03ff6ba0 0x6fff07f00fffffc3 0xdbffc1fc03fffff0

def z231 : W := mkw 0x0012f84da0000001 0x8004be1368000000 0x9000f80ff0000000 0x24003e03fc000000

def z232 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xa2b8c70f0f0e0c3c 0x28ae31c3c3c3830f

def z233 : W := mkw 0xac5af76fcb6fcf39 0xab16bddbf2dbf3ce 0xfffef7efcfefcf3f 0xffffbdfbf3fbf3cf

def z234 : W := mkw 0x320002205db05fd4 0x4c800088176c17f5 0xfdc13911fff1ffff 0xff704e447ffc7fff

def z235 : W := mkw 0x06425064d064d354 0x81909419341934d5 0x484718f0f0f0f3c1 0x1211c63c3c3c3cf0

def z236 : W := mkw 0x002f55d480000002 0x800bd57520000000 0xff3fd7fec0000000 0x3fcff5ffb0000000

def z237 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0x1ffffeee0ffff003 0xc7ffffbb83fffc00

def z238 : W := mkw 0x3000000005900480 0x4c00000001640120 0x00800000071004c0 0x8020000001c40130

def z239 : W := mkw 0xf037fa200ffdae80 0x7c0dfe8803ff6ba0 0x1ffff8000fffffc3 0xc7fffe0003fffff0

def z240 : W := mkw 0x0440022208668a20 0x011000888219a288 0x0040000008ee0000 0x00100000023b8000

def z241 : W := mkw 0x0000000040004110 0x0000000010001044 0xfd013800c011fb33 0xff404e0030047ecc

def z242 : W := mkw 0xb83da5990799048b 0x6e0f696641e64122 0x04b92111071104cc 0x812e484441c44133

def z243 : W := mkw 0xa808070b0b0b0c29 0x2a0201c2c2c2c30a 0xa080070f0f0f0c3e 0xe82001c3c3c3c30f

def z244 : W := mkw 0x002758d4a0000002 0x8009d63528000000 0xfd0739f1f0000000 0x3f41ce7c7c000000

def z245 : W := mkw 0x0000022208220a20 0x0000008882088288 0xfb46c6ee08ee0b33 0x7ed1b1bb823b82cc

def z246 : W := mkw 0x04425046c046c130 0x81109411b011b04c 0x9b46d00ec8eec033 0x66d1b403b23bb00c

def z247 : W := mkw 0x0000000004900000 0x4000000001240000 0x00c000000ff00001 0xc030000003fc0000

def z248 : W := mkw 0x0000022008200a00 0x0000008802080280 0x024606e008e00000 0x009181b802380000

def z249 : W := mkw 0xc035a80006992000 0x700d6a0001a64800 0x0fff28000ff13001 0xc3ffca0003fc4c00

def z250 : W := mkw 0xc037f84da6dda001 0xf00dfe1369b76800 0x9ffff80ffffff003 0xe7fffe03fffffc00

def z251 : W := mkw 0x04425264c864cb10 0x81109499321932c4 0x6b4616e0c8e0cb01 0x5ad185b8323832c0

def z252 : W := mkw 0x302502200db00e80 0x4c094088036c03a0 0x0fff00000ff00fc1 0xc3ffc00003fc03f0

def z253 : W := mkw 0x022758d4f0005156 0x8089d6353c001455 0x480718f0f010f3c1 0x1201c63c3c043cf0

def z254 : W := mkw 0xaa18a70b5b0b5d7d 0x2a8629c2d6c2d75f 0xb7b8ff0fff0ffc3e 0xedee3fc3ffc3ff0f

def z255 : W := mkw 0x0025000004900000 0x4009400001240000 0x6fff01100ff00fc1 0xdbffc04403fc03f0

def z256 : W := mkw 0x002502200cb00a00 0x40094088032c0280 0x6fff06e00ff00b01 0xdbffc1b803fc02c0

def z257 : W := mkw 0xa810a20b0b0b0c29 0x2a042882c2c2c30a 0x9080e00f0f0f0c3e 0xe4203803c3c3c30f

def z258 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000011000000fc0 0x18000044000003f0

def z259 : W := mkw 0x8c52f04fc24fc139 0xa314bc13f093f04e 0x9000f00fc00fc03e 0x24003c03f003f00f

def z260 : W := mkw 0xa83fffdfab0b0c2b 0xaa0ffff7eac2c30a 0xffbfffffff0f0c3e 0xffefffffffc3c30f

def z261 : W := mkw 0xb83da7bb0fbb0eab 0x6e0f69eec3eec3aa 0x6fffc7fe0ffe0fc1 0xdbfff1ff83ff83f0

def z262 : W := mkw 0x0000022008200a00 0x0000008802080280 0x600006e000000b00 0x180001b8000002c0

def z263 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0000111f0000000 0x380000447c000000

def z264 : W := mkw 0x020805ddf0005157 0x808201777c001455 0xfd013ffff011ffff 0xff404ffffc047fff

def z265 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xe246c6eec8ee0b30 0x3891b1bbb23b82cc

def z266 : W := mkw 0xa818a72b0b2b0e29 0x2a0629cac2cac38a 0xfffee7ef0fef0f3f 0xffffb9fbc3fbc3cf

def z267 : W := mkw 0x2a08070b59025d7d 0x0a8201c2d640975f 0xfd013f1ff011ffff 0xff404fc7fc047fff

def z268 : W := mkw 0x022758d4f0005156 0x8089d6353c001455 0xfd0739f1f011ffff 0xff41ce7c7c047fff

def z269 : W := mkw 0xa810a2020b0b0c28 0x2a04288082c2c30a 0x17b8e0000f0f0c3e 0xc5ee380003c3c30f

def z270 : W := mkw 0x0200000050005154 0x0080000014001455 0x80000001f000003c 0x200000007c00000f

def z271 : W := mkw 0x8810a20b0a0b0829 0x22042882c282c20a 0xb300e60f080f083e 0x6cc03983c203c20f

def z272 : W := mkw 0x0002500000448000 0x0000940000112000 0x0846100000e0c001 0x0211840000383000

def z273 : W := mkw 0xb03da7b00fb90e82 0x6c0f69ec03ee43a0 0x7fffe7f00fff0fc3 0xdffff9fc03ffc3f0

def z274 : W := mkw 0x047fffffe866cb33 0x811ffffffa19b2cc 0xfb7ed6eec8eecb33 0x7edfb5bbb23bb2cc

def z275 : W := mkw 0x002d07b008200a02 0x000b41ec02080280 0x6f7f07f008e00b01 0x5bdfc1fc023802c0

def z276 : W := mkw 0x0000020208020820 0x0000008082008208 0x00000000080e0832 0x400000000203820c

def z277 : W := mkw 0x0200000050005154 0x0080000014001455 0x48011810f011ffff 0xd20046043c047fff

def z278 : W := mkw 0x2000020009000c00 0x0800008002400300 0x008000000f000c00 0xc020000003c00300

def z279 : W := mkw 0x0200000050005154 0x0080000014001455 0x00001800f000f000 0x000006003c003c00

def z280 : W := mkw 0x06425046d046d174 0x81909411b411b45d 0xfd01f91ff01fffff 0xff407e47fc07ffff

def z281 : W := mkw 0x0000000000000000 0x0000000000000000 0xfd013911f0100fc1 0xff404e447c0403f0

def z282 : W := mkw 0xb83da7b90fb90e8b 0x6e0f69ee43ee43a2 0x6fff27f10ff10fcd 0xdbffc9fc43fc43f3

def z283 : W := mkw 0xf00002200ffdae80 0x7c00008803ff6ba0 0x00c000000fffffc3 0xc030000003fffff0

def z284 : W := mkw 0x0018a50900000001 0x0006294240000000 0x0438210100000000 0x010e084040000000

def z285 : W := mkw 0xa818a70b4b0b4d39 0x2a0629c2d2c2d34e 0xffb8f70fcf0fcf3f 0xffee3dc3f3c3f3cf

def z286 : W := mkw 0xac58a76fcb2b4f39 0xab1629dbf2cad3ce 0xf7b8e7efcf0f0f3e 0xfdee39fbf3c3c3cf

def z287 : W := mkw 0x0008059000000002 0x0002016400000000 0x600007f000000000 0x180001fc00000000

def z288 : W := mkw 0x044a57ffe866cb33 0x811295fffa19b2cc 0xfb46d7fff8eecb33 0x7ed1b5fffe3bb2cc

def z289 : W := mkw 0xf03fffb00ffdae82 0x7c0fffec03ff6ba0 0x02fec6e00fee0000 0x00bfb1b803fb8000

def z290 : W := mkw 0x0037f80000000000 0x000dfe0000000000 0x023ec00000000000 0x008fb00000000000

def z291 : W := mkw 0xc025000006dda000 0x7009400001b76800 0x0fff00000ffff003 0xc3ffc00003fffc00

def z292 : W := mkw 0x400258000044a000 0x1000960000112800 0x000018000000f000 0x0000060000003c00

def z293 : W := mkw 0xd037f8b006fda282 0x740dfe2c01bf68a0 0x5ffff8f00ffff3c3 0xd7fffe3c03fffcf0

def z294 : W := mkw 0x002d059000000002 0x000b416400000000 0x6f3f07f000100fc1 0xdbcfc1fc000403f0

def z295 : W := mkw 0x003ffddde0004113 0x800fff7778001044 0xff3ffffff000cb33 0x7fcffffffc0032cc

def z296 : W := mkw 0x302d07b04db04f92 0x4c0b41ec136c13e4 0xffff17f0cff0cff3 0xffffc5fc33fc33fc

def z297 : W := mkw 0xc477f846c6dfe130 0xf11dfe11b1b7f84c 0x9ffff80ecffff033 0xe7fffe03b3fffc0c

def z298 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xff47fffff8eecb33 0x7fd1fffffe3bb2cc

def z299 : W := mkw 0x0025009000000002 0x0009402400000000 0x480700f000000000 0x1201c03c00000000

def z300 : W := mkw 0x0000000000000000 0x0000000000000000 0x48010010001003c1 0x12004004000400f0

def z301 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x12fef8000feff002 0x04bfbe0003fbfc00

def z302 : W := mkw 0x0000020248024930 0x000000809200924c 0xfb00d60ec80ecb33 0x7ec03583b203b2cc

def z303 : W := mkw 0x04425044c044c110 0x8110941130113044 0x00001000c000c000 0x0000040030003000

def z304 : W := mkw 0x8010a2020a0b0820 0x200428808282c208 0xb7b8e60e0f0f0832 0xedee398383c3c20c

def z305 : W := mkw 0xe83fff0b0fdfac29 0x7a0fffc2c3f7eb0a 0x1ffffe0e0ffff003 0xc7ffff8383fffc00

def z306 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000010c3e 0xc00000000000430f

def z307 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xfb46d7fff8eecfff 0x7ed1b5fffe3bb3ff

def z308 : W := mkw 0xf03fffb00ffdae82 0x7c0fffec03ff6ba0 0x6fffc7f00ffe0fc1 0xdbfff1fc03ff83f0

def z309 : W := mkw 0x883ffddfa20b002b 0xa20fff77e882c00a 0xff3ffffff00f003e 0x3fcffffffc03c00f

def z310 : W := mkw 0x1000002004b00280 0x44000008012c00a0 0x0040000000f003c1 0x00100000003c00f0

def z311 : W := mkw 0xa818a7dfab0b0c2b 0xaa0629f7eac2c30a 0xf7b8e7ffff0f0c3e 0xfdee39ffffc3c30f

def z312 : W := mkw 0x44675864c4f4e310 0xd119d619313d38c4 0x484718e0c0f0f301 0x1211c638303c3cc0

def z313 : W := mkw 0x0008059920000003 0x0002016648000000 0x0000011130000000 0x000000444c000000

def z314 : W := mkw 0xe83fffdfafdfac2b 0xfa0ffff7ebf7eb0a 0xfffffffffffffc3f 0xffffffffffffff0f

def z315 : W := mkw 0x06400266d8225b74 0x81900099b60896dd 0xe00007fff0000ffc 0x380001fffc0003ff

def z316 : W := mkw 0x0037f8d4a0000002 0x800dfe3528000000 0x5f3ff8f0f0000000 0x17cffe3c3c000000

def z317 : W := mkw 0xc477fa224effeb30 0x711dfe8893bffacc 0x1ffff8000ffffb33 0xc7fffe0003fffecc

def z318 : W := mkw 0x0200000050005154 0x0080000014001455 0xf9011810f010fbf3 0x7e4046043c043efc

def z319 : W := mkw 0x0442526688668a20 0x81109499a219a288 0xfb46d6eec8ee0000 0x3ed1b5bbb23b8000

def z320 : W := mkw 0x2800020209020c28 0x0a0000808240830a 0x0000000000000c3c 0x000000000000030f

def z321 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x7ffff9100fffffc3 0xdffffe4403fffff0

def z322 : W := mkw 0x244a5766c966cf30 0x891295d9b259b3cc 0xfffed7eecfeecf33 0xffffb5fbb3fbb3cc

def z323 : W := mkw 0x0200000050005154 0x0080000014001455 0x0000000000000ffc 0x00000000000003ff

def z324 : W := mkw 0x0442504680468020 0x81109411a011a008 0x0000c00e000e0000 0x0000300380038000

def z325 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000010100000c3c 0x280000404000030f

def z326 : W := mkw 0xa83fffdfab0b0c2b 0xaa0ffff7eac2c30a 0xffbfffffff0e0000 0x3fefffffffc38000

def z327 : W := mkw 0x0037f80000448000 0x000dfe0000112000 0x1f7ff80008eec003 0x47dffe00023bb000

def z328 : W := mkw 0x4037f80004d4a000 0x500dfe0001352800 0x1f7ff80000f0f001 0x07dffe00003c3c00

def z329 : W := mkw 0x0000022008200a00 0x0000008802080280 0x6f4707f008f00fc1 0xdbd1c1fc023c03f0

def z330 : W := mkw 0xc237f80056ddf154 0x708dfe0015b77c55 0x1ffff8000fffffff 0xc7fffe0003ffffff

def z331 : W := mkw 0x3000022009200e80 0x0c000088024803a0 0x0000000000000fc0 0x00000000000003f0

def z332 : W := mkw 0x0000022048204b10 0x00000088120812c4 0xfb4616e0c8e0cb33 0x7ed185b8323832cc

def z333 : W := mkw 0xac5af76f8b6f8e29 0xab16bddbe2dbe38a 0xb7fee7ef0fef0c3e 0xedffb9fbc3fbc30f

def z334 : W := mkw 0x0000000000000000 0x0000000000000000 0x900020010001003e 0x240008004000400f

def z335 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x0affd8000ffef001 0x02bff60003ffbc00

def z336 : W := mkw 0xc47fffffeeffeb33 0xf11ffffffbbffacc 0xfffffffffffffb33 0xfffffffffffffecc

def z337 : W := mkw 0x04425064c064c310 0x81109419301930c4 0xfb46d6eec0e0c301 0x3ed1b5bbb03830c0

def z338 : W := mkw 0x322d07b05db05fd6 0x4c8b41ec176c17f5 0x6fff07f00ff1ffff 0xdbffc1fc03fc7fff

def z339 : W := mkw 0x02025044d0005154 0x8080941134001455 0xff07fffff011ffff 0xffc1fffffc047fff

def z340 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xb3b8c60e0f0e0832 0x6cee318383c3820c

def z341 : W := mkw 0x001afd4da0000001 0x8006bf5368000000 0xb738ff0ff0000000 0x2dce3fc3fc000000

def z342 : W := mkw 0x8810a00b020b0029 0x22042802c082c00a 0x97b8e00f0f0f003e 0xe5ee3803c3c3c00f

def z343 : W := mkw 0xc235a80056997154 0x708d6a0015a65c55 0xfdb93911f711ffff 0xff6e4e447dc47fff

def z344 : W := mkw 0x000805dda0000003 0x8002017768000000 0xfd013ffff0000000 0x3f404ffffc000000

def z345 : W := mkw 0x0000020208020820 0x0000008082008208 0xa000060e00000830 0x280001838000020c

def z346 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x0cff380007f1f001 0x833fce0001fc7c00

def z347 : W := mkw 0xc037f80046dde110 0x700dfe0011b77844 0xfffff800cffffb33 0xfffffe0033fffecc

def z348 : W := mkw 0xc035a80006992000 0x700d6a0001a64800 0x1db938000711f003 0xc76e4e0001c47c00

def z349 : W := mkw 0x322d07b05db05fd6 0x4c8b41ec176c17f5 0x6fff1ff0fff0ffc1 0xdbffc7fc3ffc3ff0

def z350 : W := mkw 0xc23ffdddf6ddf157 0xf08fff777db77c55 0xffffffffffffffff 0xffffffffffffffff

def z351 : W := mkw 0x2818a70b09020c29 0x0a0629c2c240830a 0xb738e70f00000c3c 0x2dce39c3c000030f

def z352 : W := mkw 0x0037f84da0000001 0x800dfe1368000000 0x9f3ff80ff0000000 0x27cffe03fc000000

def z353 : W := mkw 0x002758d4a0000002 0x8009d63528000000 0xfb07defef0000000 0x3ec1f7bfbc000000

def z354 : W := mkw 0xb818a7bb0b2b0eab 0x2e0629eec2cac3aa 0xf7b8e7ff0f0f0ffe 0xfdee39ffc3c3c3ff

def z355 : W := mkw 0x0200000050005154 0x0080000014001455 0xf9001111f000cfff 0x7e4004447c0033ff

def z356 : W := mkw 0x0002526488200a00 0x8000949922080280 0xfb46d6eec8e00b01 0x7ed1b5bbb23802c0

def z357 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xb000e70f000f0c3e 0x2c0039c3c003c30f

def z358 : W := mkw 0x046f57f6c866cb32 0x811bd5fdb219b2cc 0xff7fd7fec8eecb33 0x7fdff5ffb23bb2cc

def z359 : W := mkw 0x322d07b01db01ec6 0x4c8b41ec076c07b1 0x6fff2ff13ff13fcd 0xdbffcbfc4ffc4ff3

def z360 : W := mkw 0x8810a00b020b0029 0x22042802c082c00a 0x0000c00e000e0000 0x0000300380038000

def z361 : W := mkw 0xc44002224effeb30 0x7110008893bffacc 0x00c000000ffffb33 0xc030000003fffecc

def z362 : W := mkw 0xc452f846c24fe130 0xb114be11b093f84c 0x9000f80ec00ff032 0x24003e03b003fc0c

def z363 : W := mkw 0x0200000050005154 0x0080000014001455 0x5d013810f011f3c3 0xd7404e043c047cf0

def z364 : W := mkw 0x303ffffdadb00e83 0xcc0fffff6b6c03a0 0x02fec6ee0fe00000 0x00bfb1bb83f80000

def z365 : W := mkw 0xaa18a5091309144d 0x2a86294244c24513 0x04b92911371134cc 0x812e4a444dc44d33

def z366 : W := mkw 0xa83ffddda309040b 0xaa0fff7768c24102 0xffbffffff701040c 0xbfeffffffdc04103

def z367 : W := mkw 0x2c4a576fc966cf39 0x8b1295dbf259b3ce 0xfb46d7efc8eecf3f 0x7ed1b5fbf23bb3cf

def z368 : W := mkw 0xa818a50903090409 0x2a06294240c24102 0xb7b8e70f0701040c 0xadee39c3c1c04103

def z369 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0x1f3ffeee00000000 0x07cfffbb80000000

def z370 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0xffffffffffee0000 0x3ffffffffffb8000

def z371 : W := mkw 0x023ffdddb0001047 0x808fff776c000411 0xff3ffffff01134cc 0xbfcffffffc044d33

def z372 : W := mkw 0x346f57f68df68ea2 0xcd1bd5fda37da3a8 0x02fec6ee0fee0000 0x00bfb1bb83fb8000

def z373 : W := mkw 0x003dad9920000003 0x000f6b6648000000 0x0038000000000000 0x000e000000000000

def z374 : W := mkw 0x8037f80002090000 0x200dfe0000824000 0x1fbff8000f0f0002 0xc7effe0003c3c000

def z375 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0x06b8e70f0f0f040c 0x81ae39c3c3c3c103

def z376 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xff47d7fec8fecff3 0xffd1f5ffb23fb3fc

def z377 : W := mkw 0xc012f800024da000 0x3004be0000936800 0x1d01f800001ff003 0xc7407e000007fc00

def z378 : W := mkw 0xc035a80006992000 0x700d6a0001a64800 0x00b8000007000000 0x002e000001c00000

def z379 : W := mkw 0xc200000056ddf154 0x7080000015b77c55 0x00c000000fffffff 0xc030000003ffffff

def z380 : W := mkw 0xa83dad992309040b 0x2a0f6b6648c24102 0x04b929113701040c 0x812e4a444dc04103

def z381 : W := mkw 0xc237f80016ddb044 0x708dfe0005b76c11 0x1ffff9113ffff4cf 0xc7fffe444ffffd33

def z382 : W := mkw 0xc03ffddda6992003 0xf00fff7769a64800 0xffbffffff7113000 0xbfeffffffdc44c00

def z383 : W := mkw 0x0200000010001044 0x0080000004000411 0x00000111300004cc 0x000000444c000133

def z384 : W := mkw 0x8010a00002090000 0x2004280000824000 0x1fb9f8000f1ff003 0xc7ee7e0003c7fc00

def z385 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xa4b8270f07010c3c 0xa92e09c3c1c0430f

def z386 : W := mkw 0x346d07f6cdb24fb2 0xcd1b41fdb36c93ec 0xefff07fecff00ff1 0xfbffc1ffb3fc03fc

def z387 : W := mkw 0xaa18a70b1b0b1c6d 0x2a8629c2c6c2c71b 0xb7b9ef1f3f1f3cfe 0xedee7bc7cfc7cf3f

def z388 : W := mkw 0x023ffdddf0005157 0x808fff777c001455 0xff3ffffff001f03e 0x3fcffffffc007c0f

def z389 : W := mkw 0xb83da79b0f9b0cab 0x6e0f69e6c3e6c32a 0xb7b9e71f0f1f0cfe 0xedee79c7c3c7c33f

def z390 : W := mkw 0x04425066c066c330 0x81109419b019b0cc 0xd846d0eec0eec333 0x3611b43bb03bb0cc

def z391 : W := mkw 0xe03fff000fddac00 0x780fffc003f76b00 0x3fffff000ffffc03 0xcfffffc003ffff00

def z392 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xff47feeec8fffb33 0xffd1ffbbb23ffecc

def z393 : W := mkw 0x0452fa6fe866cb31 0x8114be9bfa19b2cc 0xfb46feeff8eecb33 0x7ed1bfbbfe3bb2cc

def z394 : W := mkw 0x280807dfa9020c2b 0x8a0201f7ea40830a 0xe00007fff0000c3c 0x380001fffc00030f

def z395 : W := mkw 0x346f57f6cdf6cfb2 0xcd1bd5fdb37db3ec 0xfbfed6eecfeecb33 0x7effb5bbb3fbb2cc

def z396 : W := mkw 0x3008059001000482 0x0c02016400400120 0x00000110000004c0 0x0000004400000130

def z397 : W := mkw 0xc012f800024da000 0x3004be0000936800 0x17b8f8000f0ff002 0xc5ee3e0003c3fc00

def z398 : W := mkw 0x0018a50900000001 0x0006294240000000 0x0238c60e00000000 0x008e318380000000

def z399 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xfb46d6eec8ffffff 0xfed1b5bbb23fffff

def z400 : W := mkw 0x04400266c8224b30 0x81100099b20892cc 0xf90016eec000cb33 0x7e4005bbb00032cc

def z401 : W := mkw 0x04400064c0204310 0x81100019300810c4 0x400000e0c0000300 0x10000038300000c0

def z402 : W := mkw 0xa83daf9b2b0b0c2b 0x2a0f6be6cac2c30a 0xb7b9ef1f3f0f0c3e 0xedee7bc7cfc3c30f

def z403 : W := mkw 0x303dad9925900483 0x4c0f6b6649640120 0x04b92911371004c0 0x812e4a444dc40130

def z404 : W := mkw 0x04425046c046c130 0x81109411b011b04c 0xfb06d6eec00ec032 0x3ec1b5bbb003b00c

def z405 : W := mkw 0x003dad9920000003 0x000f6b6648000000 0xfd393911f0000000 0x3f4e4e447c000000

def z406 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0x17b8e60e0f0f0002 0xc5ee398383c3c000

def z407 : W := mkw 0x300807fda9200e83 0x8c0201ff6a4803a0 0xe00007fff0000fc0 0x380001fffc0003f0

def z408 : W := mkw 0x4227580054d4f154 0x5089d60015353c55 0x48471810f0f0f3c1 0x1211c6043c3c3cf0

def z409 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0x9439f91ff0000000 0x250e7e47fc000000

def z410 : W := mkw 0xc037fa200efdaa00 0x700dfe8803bf6a80 0x7ffffee00ffffb03 0xdfffffb803fffec0

def z411 : W := mkw 0x0200000050005154 0x0080000014001455 0xf5002111f0010ffe 0xfd4008447c0043ff

def z412 : W := mkw 0x0010a80920000001 0x00042a0248000000 0x0000280130000000 0x00000a004c000000

def z413 : W := mkw 0x0200000050005154 0x0080000014001455 0x6d011910f010ffc1 0xdb4046443c043ff0

def z414 : W := mkw 0x046758f4e064c312 0x8119d63d381930c4 0x484718f0f0e0c301 0x1211c63c3c3830c0

def z415 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xb7b8e70f0f0e0000 0x2dee39c3c3c38000

def z416 : W := mkw 0x044000204064c310 0x01100008101930c4 0x0040000000e0c301 0x00100000003830c0

def z417 : W := mkw 0x0000000000000000 0x0000000000000000 0x080118000010f001 0x0200460000043c00

def z418 : W := mkw 0x0000000000000000 0x0000000000000000 0xfd01211100110fff 0xff404844400443ff

def z419 : W := mkw 0xa83da79b0b0b0c2b 0x2a0f69e6c2c2c30a 0xffbfe7ff0f0f0c3e 0xffeff9ffc3c3c30f

def z420 : W := mkw 0x002d059000000002 0x000b416400000000 0xff3f3ff1f0000000 0x3fcfcffc7c000000

def z421 : W := mkw 0x04425064c064c310 0x81109419301930c4 0x5b46d0e0c8eec303 0x56d1b438323bb0c0

def z422 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0x0246c6ee08eecb33 0x4091b1bb823bb2cc

def z423 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0x02fec6ee0fee0000 0x00bfb1bb83fb8000

def z424 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0x92b8e60f0f0f003e 0x24ae3983c3c3c00f

def z425 : W := mkw 0xea3fff0b5fdffd7d 0x7a8fffc2d7f7ff5f 0xffffff1fffffffff 0xffffffc7ffffffff

def z426 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xb73ee7ef00000000 0x2dcfb9fbc0000000

def z427 : W := mkw 0x0000020008000800 0x0000008002000200 0x2300060008000800 0x48c0018002000200

def z428 : W := mkw 0x0200000010001044 0x0080000004000411 0x6d01291130113fcd 0xdb404a444c044ff3

def z429 : W := mkw 0x044002224866cb30 0x011000889219b2cc 0x6b4606e008eecb33 0x5ad181b8023bb2cc

def z430 : W := mkw 0x0012f84da0000001 0x8004be1368000000 0xfd01f91ff0000000 0x3f407e47fc000000

def z431 : W := mkw 0x002f5ddda0000003 0x800bd77768000000 0xe8071ffff0000000 0x3a01c7fffc000000

def z432 : W := mkw 0x0212f84df0005155 0x8084be137c001455 0xfd01f91ff011ffff 0xff407e47fc047fff

def z433 : W := mkw 0x0200022058205b54 0x00800088160816d5 0xff473ff1f8f1ffff 0xffd1cffc7e3c7fff

def z434 : W := mkw 0xae5af76fdb6fdf7d 0xab96bddbf6dbf7df 0xffffffffffffffff 0xffffffffffffffff

def z435 : W := mkw 0x8010a00002090000 0x2004280000824000 0x02b8c0000f0e0000 0x00ae300003c38000

def z436 : W := mkw 0x8818a50b020b0029 0x22062942c082c00a 0xb738e70f000f003e 0x2dce39c3c003c00f

def z437 : W := mkw 0x300807b009200e82 0x0c0201ec024803a0 0x000006e000000000 0x000001b800000000

def z438 : W := mkw 0x023ffdddf0005157 0x808fff777c001455 0xff3ffffff0000ffc 0x3fcffffffc0003ff

def z439 : W := mkw 0xac5af74fcb4fcd39 0xab16bdd3f2d3f34e 0xb7b8f70fcf0fcc3e 0xedee3dc3f3c3f30f

def z440 : W := mkw 0x003dad9920000003 0x000f6b6648000000 0xb739ef1f30000000 0x2dce7bc7cc000000

def z441 : W := mkw 0x2008070009000c00 0x080201c002400300 0x02b806000f000000 0x00ae018003c00000

def z442 : W := mkw 0xc235a80016993044 0x708d6a0005a64c11 0x04b92911371134cc 0x812e4a444dc44d33

def z443 : W := mkw 0xa80002020b0b0c28 0x2a00008082c2c30a 0xb58021010f0f0c3e 0xed60084043c3c30f

def z444 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0x6f3fc7fe00000000 0x1bcff1ff80000000

def z445 : W := mkw 0x300002200db00e80 0x4c000088036c03a0 0x6dc101100ff00fc1 0xdb70404403fc03f0

def z446 : W := mkw 0xc200000056ddf154 0x7080000015b77c55 0xfdc13911ffffffff 0xff704e447fffffff

def z447 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x6bfe06e00fe00b01 0x5aff81b803f802c0

def z448 : W := mkw 0x003ffddda4900003 0xc00fff7769240000 0xfffffffffff00001 0xfffffffffffc0000

def z449 : W := mkw 0x302f57b00df48e82 0x4c0bd5ec037d23a0 0x7fffd7f00ffecfc3 0xdffff5fc03ffb3f0

def z450 : W := mkw 0x044807ffe8224b33 0x811201fffa0892cc 0xe00007fff0000b30 0x380001fffc0002cc

def z451 : W := mkw 0x302f5ff4adb00e82 0xcc0bd7fd2b6c03a0 0x6fff1ff0fff00fc1 0xdbffc7fc3ffc03f0

def z452 : W := mkw 0x0000000000000000 0x0000000000000000 0x0d01000000100001 0xc340400000040000

def z453 : W := mkw 0xc477fa66ceffeb30 0xf11dfe99b3bffacc 0xfbfed6eecfeecb33 0x7effb5bbb3fbb2cc

def z454 : W := mkw 0x344002224df6cfb0 0x4d100088937db3ec 0x00c000000ffecff3 0xc030000003ffb3fc

def z455 : W := mkw 0x2008050001000400 0x0802014000400100 0x04b8010007000400 0x812e004001c00100

def z456 : W := mkw 0x023dad9930001047 0x008f6b664c000411 0x04392911301134cc 0x810e4a444c044d33

def z457 : W := mkw 0x0002500000448000 0x0000940000112000 0x1f47f80008fff003 0xc7d1fe00023ffc00

def z458 : W := mkw 0x04400266c8224b30 0x81100099b20892cc 0xf300c6eec80e0b32 0x7cc031bbb20382cc

def z459 : W := mkw 0xa83fffdfab0b0c2b 0xaa0ffff7eac2c30a 0xb7bee7ef0f0f0c3e 0xedefb9fbc3c3c30f

def z460 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000011f003 0xc000000000047c00

def z461 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0x063fefff30000000 0x018ffbffcc000000

def z462 : W := mkw 0x1025009004900082 0x4409402401240020 0x00010010001000c0 0x0000400400040030

def z463 : W := mkw 0xf03ffd9007dda482 0x7c0fff6401f76920 0x1ffff9100ffff4c3 0xc7fffe4403fffd30

def z464 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xff46f7efc8efcf3f 0xffd1bdfbf23bf3cf

def z465 : W := mkw 0x2008070009000c00 0x080201c002400300 0x2000070000000c00 0x080001c000000300

def z466 : W := mkw 0x002d059004900002 0x400b416401240000 0x6fff07f00ff00001 0xdbffc1fc03fc0000

def z467 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x06ff07f00ff004c0 0x81bfc1fc03fc0130

def z468 : W := mkw 0x0010a00900000001 0x0004280240000000 0x9000e00f00000000 0x24003803c0000000

def z469 : W := mkw 0xf03ffffdaffdae83 0xfc0fffff6bff6ba0 0xffffffffffffffc3 0xfffffffffffffff0

def z470 : W := mkw 0x003ffddda0448003 0x800fff7768112000 0xff7ffffff8eec003 0x7fdffffffe3bb000

def z471 : W := mkw 0x380807bb09220eab 0x0e0201eec24883aa 0xe00007ff00000ffc 0x380001ffc00003ff

def z472 : W := mkw 0x100000b000200282 0x0400002c000800a0 0x400000f0000003c0 0x1000003c000000f0

def z473 : W := mkw 0x0200000050005154 0x0080000014001455 0xb50021010011ffff 0xed40084040047fff

def z474 : W := mkw 0x8810a00902090009 0x2204280240824002 0x000020010001000c 0x0000080040004003

def z475 : W := mkw 0x0037f80004900000 0x400dfe0001240000 0x1ffff8000ff00001 0xc7fffe0003fc0000

def z476 : W := mkw 0xe837fa020fdfac28 0x7a0dfe8083f7eb0a 0x1ffff8000ffffc3f 0xc7fffe0003ffff0f

def z477 : W := mkw 0x344807f6c9224fb2 0x8d1201fdb24893ec 0xe00007fec0000ff0 0x380001ffb00003fc

def z478 : W := mkw 0xa81af70b0b4f8c29 0x2a06bdc2c2d3e30a 0xbffef70f0fefcc3f 0xefffbdc3c3fbf30f

def z479 : W := mkw 0xa80807020b0b0c28 0x2a0201c082c2c30a 0x27b807000f0f0c3e 0xc9ee01c003c3c30f

def z480 : W := mkw 0xb818a72b0fbb0ea9 0x6e0629cac3eec3aa 0xb7f8e70f0fff0fff 0xedfe39c3c3ffc3ff

def z481 : W := mkw 0x044000024046c130 0x011000009011b04c 0x00000000000ec032 0x000000000003b00c

def z482 : W := mkw 0x0012f80000000000 0x0004be0000000000 0x1000f80000000000 0x04003e0000000000

def z483 : W := mkw 0x8010a00002090000 0x2004280000824000 0x1000e000000f0002 0x040038000003c000

def z484 : W := mkw 0xa83fffdfab0b0c2b 0xaa0ffff7eac2c30a 0x02bec6ee0f0e0000 0x00afb1bb83c38000

def z485 : W := mkw 0x2018a70909000c01 0x080629c242400300 0xb7b8e70f0f000c00 0xedee39c3c3c00300

def z486 : W := mkw 0x102758f4a4b00282 0xc409d63d292c00a0 0x484718f0f0f003c1 0x1211c63c3c3c00f0

def z487 : W := mkw 0x044252224866cb30 0x011094889219b2cc 0x1b46d00008eecb33 0x46d1b400023bb2cc

def z488 : W := mkw 0xe83fff0b0fdfac29 0x7a0fffc2c3f7eb0a 0x02fec60e0fee0000 0x00bfb18383fb8000

def z489 : W := mkw 0x2808050901000409 0x0a02014240400102 0x000001010000040c 0x0000004040000103

def z490 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xfb3ed6eec0000000 0x3ecfb5bbb0000000

def z491 : W := mkw 0x0037f80000000000 0x000dfe0000000000 0xff3ff911f0000000 0x3fcffe447c000000

def z492 : W := mkw 0x8010a00002090000 0x2004280000824000 0x04b8200007010000 0x812e080001c04000

def z493 : W := mkw 0xc812f80b024fa029 0x3204be02c093e80a 0x9000f80f000ff03e 0x24003e03c003fc0f

def z494 : W := mkw 0x0440022248224b30 0x01100088920892cc 0x0000000000000b30 0x00000000000002cc

def z495 : W := mkw 0x0000000000000000 0x0000000000000000 0xfd013911f0010c3e 0xff404e447c00430f

def z496 : W := mkw 0x0000020208020820 0x0000008082008208 0xb700e70f080f0c3e 0xedc039c3c203c30f

def z497 : W := mkw 0x102500b004b00282 0x4409402c012c00a0 0x004600e000e00000 0x0011803800380000

def z498 : W := mkw 0x8018a50902090001 0x2006294240824000 0xb7b8e70f0f0f0002 0xedee39c3c3c3c000

def z499 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x1847f80000fff003 0x0611fe00003ffc00

def z500 : W := mkw 0xf03dad9007992482 0x7c0f6b6401e64920 0x04b92910071134c0 0x812e4a4401c44d30

def z501 : W := mkw 0xb83fffffafbb0eab 0xee0fffffebeec3aa 0xffffffffffff0fff 0xffffffffffffc3ff

def z502 : W := mkw 0xe83ffd0907dda409 0x7a0fff4241f76902 0x1ffff9010ffff40f 0xc7fffe4043fffd03

def z503 : W := mkw 0xc452fa66ca6feb30 0xb114be99b29bfacc 0xfb46feeec8effb33 0x7ed1bfbbb23bfecc

def z504 : W := mkw 0xaa18a70b5b0b5d7d 0x2a8629c2d6c2d75f 0xb7b8e70f0f1fffff 0xedee39c3c3c7ffff

def z505 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0x9040d00ec8eecb33 0x64103403b23bb2cc

def z506 : W := mkw 0x0200000050005154 0x0080000014001455 0xfd013911f0000ffc 0x3f404e447c0003ff

def z507 : W := mkw 0x0200000010001044 0x0080000004000411 0x00010810301030c0 0x000042040c040c30

def z508 : W := mkw 0xe80002020fdfac28 0x7a00008083f7eb0a 0x00c000000ffffc3f 0xc030000003ffff0f

def z509 : W := mkw 0x303ffffdadb00e83 0xcc0fffff6b6c03a0 0x6fffc7fe0ff00fc1 0xdbfff1ff83fc03f0

def z510 : W := mkw 0x0000000040004110 0x0000000010001044 0x000000000000cb33 0x40000000000032cc

def z511 : W := mkw 0x0200000050005154 0x0080000014001455 0xf9001000c011ffff 0xfe40040030047fff

def z512 : W := mkw 0x2008070009000c00 0x080201c002400300 0xb7b827010f010c3e 0xedee09c043c0430f

def z513 : W := mkw 0x047ffddfe046c133 0x811fff77f811b04c 0xff3ffffff00ec032 0x3fcffffffc03b00c

def z514 : W := mkw 0x283fffdfa9020c2b 0x8a0ffff7ea40830a 0xff3ffffff0000c3c 0x3fcffffffc00030f

def z515 : W := mkw 0x0000000040004110 0x0000000010001044 0xe0000000c0000b30 0x38000000300002cc

def z516 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x1bfed0000feec003 0x46ffb40003fbb000

def z517 : W := mkw 0xc237f80056ddf154 0x708dfe0015b77c55 0x5ffff810fffff3c3 0xd7fffe043ffffcf0

def z518 : W := mkw 0x04425246c846c930 0x81109491b211b24c 0xb300d60ec80ec832 0x6cc03583b203b20c

def z519 : W := mkw 0xc212f800524df154 0x3084be0014937c55 0x9000f801f00ff03e 0x24003e007c03fc0f

def z520 : W := mkw 0x4025080004902000 0x5009420001240800 0x0001080000103000 0x0000420000040c00

def z521 : W := mkw 0x020805ddf0005157 0x808201777c001455 0xe00007fff0000ffc 0x380001fffc0003ff

def z522 : W := mkw 0xc010a80002092000 0x30042a0000824800 0x0000280000013000 0x00000a0000004c00

def z523 : W := mkw 0x0008050000000000 0x0002014000000000 0x2738070000000000 0x09ce01c000000000

def z524 : W := mkw 0xac425266cb6fcf38 0xab109499b2dbf3ce 0xfbc6d6eecfefcf3f 0xfef1b5bbb3fbf3cf

def z525 : W := mkw 0x302d059005900482 0x4c0b416401640120 0x0fff01100ff004c1 0xc3ffc04403fc0130

def z526 : W := mkw 0x322d07b05db05fd6 0x4c8b41ec176c17f5 0xefff07f1fff00ffd 0xfbffc1fc7ffc03ff

def z527 : W := mkw 0xf47ffff6cfffefb2 0xfd1ffffdb3fffbec 0xfffffffecffffff3 0xffffffffb3fffffc

def z528 : W := mkw 0x0200000050005154 0x0080000014001455 0x94013911f011f4fe 0xa5004e447c047d3f

def z529 : W := mkw 0x0212f84df0005155 0x8084be137c001455 0x9000f80ff001f03e 0x24003e03fc007c0f

def z530 : W := mkw 0x0000002000200200 0x0000000800080080 0x484600e000e00301 0x12118038003800c0

def z531 : W := mkw 0x003ffd0900000001 0x000fff4240000000 0xbf3fff0f00000000 0x2fcfffc3c0000000

def z532 : W := mkw 0x0025000000000000 0x0009400000000000 0x0f3f000000000000 0x03cfc00000000000

def z533 : W := mkw 0xc012f84da24da001 0xb004be1368936800 0x9000f80ff00ff002 0x24003e03fc03fc00

def z534 : W := mkw 0xc212f800524df154 0x3084be0014937c55 0xfd01f911f01fffff 0xff407e447c07ffff

def z535 : W := mkw 0xaa3fffdffb0b5d7f 0xaa8ffff7fec2d75f 0xffbfffffff1fffff 0xffefffffffc7ffff

def z536 : W := mkw 0xc4425266ceffeb30 0xf1109499b3bffacc 0xfbc6d6eecffffb33 0xfef1b5bbb3fffecc

def z537 : W := mkw 0xac4002224b6fcf38 0x2b10008892dbf3ce 0x00c000000fefcf3f 0xc030000003fbf3cf

def z538 : W := mkw 0x0000000000000000 0x0000000000000000 0x1d01380000000000 0x07404e0000000000

def z539 : W := mkw 0x0025000004900000 0x4009400001240000 0x1fff38000ff1f003 0xc7ffce0003fc7c00

def z540 : W := mkw 0x122500b054b053d6 0x4489402c152c14f5 0x484718f0f0f0f3c1 0x1211c63c3c3c3cf0

def z541 : W := mkw 0x0002504480000000 0x8000941120000000 0x0206c6ee00000000 0x0081b1bb80000000

def z542 : W := mkw 0x047fffffa8668a23 0x811fffffea19a288 0xff7ffffff8ee0000 0x3fdffffffe3b8000

def z543 : W := mkw 0x0000000000000000 0x0000000000000000 0x100038000001f002 0x04000e0000007c00

def z544 : W := mkw 0x0200020258025974 0x008000809600965d 0xff01ff1ff81fffff 0xffc07fc7fe07ffff

def z545 : W := mkw 0x0002522008648a00 0x0000948802192280 0x7b46d6e008eecb03 0x5ed1b5b8023bb2c0

def z546 : W := mkw 0x0002500000448000 0x0000940000112000 0x0246c00008ee0000 0x0091b000023b8000

def z547 : W := mkw 0x2a08070b59025d7d 0x0a8201c2d640975f 0xe000071ff0000ffc 0x380001c7fc0003ff

def z548 : W := mkw 0xac5af76fcb6fcf39 0xab16bddbf2dbf3ce 0xfbfed6eecfeecb33 0x7effb5bbb3fbb2cc

def z549 : W := mkw 0x302d07900d900c82 0x4c0b41e403640320 0x27b907100f100cc0 0xc9ee41c403c40330

def z550 : W := mkw 0x06400266d8225b74 0x81900099b60896dd 0xfd013ffff011ffff 0xff404ffffc047fff

def z551 : W := mkw 0xa83fff0b0b0b0c29 0x2a0fffc2c2c2c30a 0xbfbfff0f0f0f0c3e 0xefefffc3c3c3c30f

def z552 : W := mkw 0x300807b009200e82 0x0c0201ec024803a0 0x6b4607f008e00fc1 0x5ad181fc023803f0

def z553 : W := mkw 0x303da7b90db00e83 0x4c0f69ee436c03a0 0xffffe7ff0ff00fc1 0xfffff9ffc3fc03f0

def z554 : W := mkw 0x0002524688020820 0x80009491a2008208 0xfb06d6eec80e0832 0x7ec1b5bbb203820c

def z555 : W := mkw 0x0200000050005154 0x0080000014001455 0xed010111f0100ffd 0xfb4040447c0403ff

def z556 : W := mkw 0x0000000200020020 0x0000000080008008 0x9000c00e000e0032 0x240030038003800c

def z557 : W := mkw 0x047fffffe8224b33 0x811ffffffa0892cc 0xff3ffffff0000b30 0x3fcffffffc0002cc

def z558 : W := mkw 0x322d0590159014c6 0x4c8b416405640531 0x04b92911371134cc 0x812e4a444dc44d33

def z559 : W := mkw 0x300807b009200e82 0x0c0201ec024803a0 0x67b807f00f000fc0 0xd9ee01fc03c003f0

def z560 : W := mkw 0x06425046d046d174 0x81909411b411b45d 0x9000f80ff00ff03e 0x24003e03fc03fc0f

def z561 : W := mkw 0x0440026688220a20 0x81100099a2088288 0x000006ee00000000 0x000001bb80000000

def z562 : W := mkw 0xc012f800024da000 0x3004be0000936800 0x0000c000000e0000 0x0000300000038000

def z563 : W := mkw 0x300002200db00e80 0x4c000088036c03a0 0x6bc606e00ff00fc1 0xdaf181b803fc03f0

def z564 : W := mkw 0x0000000000000000 0x0000000000000000 0x2500010000000c00 0xc940004000000300

def z565 : W := mkw 0x0442526688668a20 0x81109499a219a288 0xb346c6ee08ee0832 0x6cd1b1bb823b820c

def z566 : W := mkw 0x001af54d80000001 0x8006bd5360000000 0xff3ef7efc0000000 0x3fcfbdfbf0000000

def z567 : W := mkw 0x0200000050005154 0x0080000014001455 0x40000010f00003c0 0x100000043c0000f0

def z568 : W := mkw 0x8812f84fa20b0029 0xa204be13e882c00a 0x9000f80ff00f003e 0x24003e03fc03c00f

def z569 : W := mkw 0x0200000050005154 0x0080000014001455 0xf0003911f001fffe 0x3c000e447c007fff

def z570 : W := mkw 0x04675af6e866cb32 0x8119d6bdba19b2cc 0xfb47defef8eecb33 0x7ed1f7bfbe3bb2cc

def z571 : W := mkw 0x0025000004900000 0x4009400001240000 0x04b9000007100000 0x812e400001c40000

def z572 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0x4c3f39f1f0000000 0x130fce7c7c000000

def z573 : W := mkw 0x0000000000000000 0x0000000000000000 0x07b800000f000000 0xc1ee000003c00000

def z574 : W := mkw 0x0200000050005154 0x0080000014001455 0xb5003901f001fc3e 0xed400e407c007f0f

def z575 : W := mkw 0x0000004480000000 0x8000001120000000 0xe00006eec0000000 0x380001bbb0000000

def z576 : W := mkw 0x0000000000448000 0x0000000000112000 0x0040000008eec003 0x40100000023bb000

def z577 : W := mkw 0x0000000000000000 0x0000000000000000 0x1500200000010002 0xc540080000004000

def z578 : W := mkw 0x0018a50900000001 0x0006294240000000 0xff39ff1ff0000000 0x3fce7fc7fc000000

def z579 : W := mkw 0x300807200db00e80 0x4c0201c8036c03a0 0x27f807000ff00fc1 0xc9fe01c003fc03f0

def z580 : W := mkw 0x0000000000000000 0x0000000000000000 0xb100000000000832 0x6c4000000000020c

def z581 : W := mkw 0x303ffffda9200e83 0x8c0fffff6a4803a0 0xff3ffffff0000fc0 0x3fcffffffc0003f0

def z582 : W := mkw 0x322d0590559055d6 0x4c8b416415641575 0xfdb93911f711ffff 0xff6e4e447dc47fff

def z583 : W := mkw 0xe83daf0b0f9b2c29 0x7a0f6bc2c3e6cb0a 0xb7b9ef0f0f1f3c3e 0xedee7bc3c3c7cf0f

def z584 : W := mkw 0x202d07000d900c00 0x480b41c003640300 0x2fff07000ff00c01 0xcbffc1c003fc0300

def z585 : W := mkw 0x0000000000000000 0x0000000000000000 0xb500210100000000 0x2d40084040000000

def z586 : W := mkw 0x0000000040004110 0x0000000010001044 0x48001000c000c301 0x12000400300030c0

def z587 : W := mkw 0xe81aff0b0b4fac29 0x3a06bfc2c2d3eb0a 0xb7b8ff0f0f0ffc3e 0xedee3fc3c3c3ff0f

def z588 : W := mkw 0xc837f80b06dfa029 0x720dfe02c1b7e80a 0x9ffff80f0ffff03f 0xe7fffe03c3fffc0f

def z589 : W := mkw 0x047ffdfde064c313 0x811fff7f781930c4 0xff7ffffff0e0c301 0x3fdffffffc3830c0

def z590 : W := mkw 0x344a57f6c966cfb2 0x8d1295fdb259b3ec 0xfb46d7fec8eecff3 0x7ed1b5ffb23bb3fc

def z591 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x6fff07f00fe00000 0x1bffc1fc03f80000

def z592 : W := mkw 0x346f57f4cdf4cf92 0xcd1bd5fd337d33e4 0x6fff17f0cff0cfc1 0xdbffc5fc33fc33f0

def z593 : W := mkw 0xc035a80006992000 0x700d6a0001a64800 0x17b9e8000f1f3002 0xc5ee7a0003c7cc00

def z594 : W := mkw 0x0000004da0000001 0x8000001368000000 0x8000000ff0000000 0x20000003fc000000

def z595 : W := mkw 0x302502b00db00e82 0x4c0940ac036c03a0 0x48c700f00ff00fc1 0xd231c03c03fc03f0

def z596 : W := mkw 0x04425266c8224b30 0x81109499b20892cc 0xfb06d6eec0000b30 0x3ec1b5bbb00002cc

def z597 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x27fe07e00fe00c00 0xc9ff81f803f80300

def z598 : W := mkw 0x003dad9920000003 0x000f6b6648000000 0x6f3f2ff130000000 0x1bcfcbfc4c000000

def z599 : W := mkw 0xc03ffd9006dda002 0x700fff6401b76800 0x7ffffff00ffff003 0xdffffffc03fffc00

def z600 : W := mkw 0x0000000000000000 0x0000000000000000 0x6d01011000000000 0x1b40404400000000

def z601 : W := mkw 0x102502b00cb00a82 0x440940ac032c02a0 0x6b4706f008f00bc1 0x5ad1c1bc023c02f0

def z602 : W := mkw 0x2008070209020c20 0x080201c082408308 0xb7b8c70e0f0e0c32 0xedee31c383c3830c

def z603 : W := mkw 0x00025844a0000000 0x8000961128000000 0x00001800f0000000 0x000006003c000000

def z604 : W := mkw 0x0200000050005154 0x0080000014001455 0x4c013911f011f7cd 0x93004e447c047df3

def z605 : W := mkw 0xc000000006dda000 0x7000000001b76800 0x1dc138000ffff003 0xc7704e0003fffc00

def z606 : W := mkw 0x0200000050005154 0x0080000014001455 0x90003801f011ffff 0xe4000e007c047fff

def z607 : W := mkw 0x044002224866cb30 0x011000889219b2cc 0xb340c60e08eecb33 0x6cd03183823bb2cc

def z608 : W := mkw 0x102500b004b00282 0x4409402c012c00a0 0x6d4701f000f00fc1 0xdb51c07c003c03f0

def z609 : W := mkw 0x0000000000000000 0x0000000000000000 0x0401291130000000 0x01004a444c000000

def z610 : W := mkw 0x146750f4c4f4c392 0xc519d43d313d30e4 0x484710f0c0f0c3c1 0x1211c43c303c30f0

def z611 : W := mkw 0x0002520208468820 0x000094808211a208 0xbb46d60e08eec833 0x6ed1b583823bb20c

def z612 : W := mkw 0x8012f000024d8000 0x2004bc0000936000 0x1ffef0000fefc003 0xc7ffbc0003fbf000

def z613 : W := mkw 0x00025044c0004110 0x8000941130001044 0xfb06d6eec000cb33 0x7ec1b5bbb00032cc

def z614 : W := mkw 0x0200000050005154 0x0080000014001455 0xe0000111f011ffff 0xf80000447c047fff

def z615 : W := mkw 0x0000000000000000 0x0000000000000000 0x7d0139100011ffc3 0xdf404e4400047ff0

def z616 : W := mkw 0xc237f80056ddf154 0x708dfe0015b77c55 0x9ffff801fffff03f 0xe7fffe007ffffc0f

def z617 : W := mkw 0xb83da7bb0fbb0eab 0x6e0f69eec3eec3aa 0xb7fee7ef0fef0c3e 0xedffb9fbc3fbc30f

def z618 : W := mkw 0x347fffffedf6cfb3 0xcd1ffffffb7db3ec 0xfffffffffffecff3 0xffffffffffffb3fc

def z619 : W := mkw 0x122500b054b053d6 0x4489402c152c14f5 0xfd4739f1f0f1ffff 0xff51ce7c7c3c7fff

def z620 : W := mkw 0x0200000050005154 0x0080000014001455 0x000000000010f3c1 0x0000000000043cf0

def z621 : W := mkw 0x303ffffdadb00e83 0xcc0fffff6b6c03a0 0xffffffffffe00000 0x3ffffffffff80000

def z622 : W := mkw 0x0000000000000000 0x0000000000000000 0x1300c000080e0002 0x44c0300002038000

def z623 : W := mkw 0x0200000050005154 0x0080000014001455 0x000000000001f03e 0x0000000000007c0f

def z624 : W := mkw 0xb82d07b20fbb0eaa 0x6e0b41ec83eec3aa 0x6fff07f00fff0fff 0xdbffc1fc03ffc3ff

def z625 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x17fee0000fef0002 0xc5ffb80003fbc000

def z626 : W := mkw 0x0800000b00020029 0x02000002c000800a 0x8000000f0000003c 0x20000003c000000f

def z627 : W := mkw 0x302f57f48db00e82 0xcc0bd5fd236c03a0 0xffffd7fecff00fc1 0xfffff5ffb3fc03f0

def z628 : W := mkw 0x346d07b24df6cfb2 0x4d1b41ec937db3ec 0x6fff07f00ffecff3 0xdbffc1fc03ffb3fc

def z629 : W := mkw 0x0000000040004110 0x0000000010001044 0x90001000c000c032 0x240004003000300c

def z630 : W := mkw 0xc037fa020edfa820 0x700dfe8083b7ea08 0xbffffe0e0ffff833 0xefffff8383fffe0c

def z631 : W := mkw 0x203fffdda9000c03 0x880ffff76a400300 0xffbfffffff000c00 0xffefffffffc00300

def z632 : W := mkw 0x020250005044d154 0x0080940014113455 0xff47f911f8ffffff 0xffd1fe447e3fffff

def z633 : W := mkw 0x8a10a00b520b517d 0x22842802d482d45f 0x9000f80ff00ff03e 0x24003e03fc03fc0f

def z634 : W := mkw 0xc000000006992000 0x7000000001a64800 0x0080000007113000 0x8020000001c44c00

def z635 : W := mkw 0x04425064c064c310 0x81109419301930c4 0xf94610e0c0e0cb33 0x7e518438303832cc

def z636 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xf000d6eec00ecb32 0x3c0035bbb003b2cc

def z637 : W := mkw 0x0037f80000000000 0x000dfe0000000000 0x1f3ff8000011f003 0xc7cffe0000047c00

def z638 : W := mkw 0x022d059050005156 0x008b416414001455 0xff3f3ff1f011ffff 0xffcfcffc7c047fff

def z639 : W := mkw 0xac5af76f8b6f8e29 0xab16bddbe2dbe38a 0x02fec6ee0fee0000 0x00bfb1bb83fb8000

def z640 : W := mkw 0x2808070b09020c29 0x0a0201c2c240830a 0xb300c70f080e0c3e 0x6cc031c3c203830f

def z641 : W := mkw 0xb83da7bb0fbb0eab 0x6e0f69eec3eec3aa 0x02fec6ee0fee0000 0x00bfb1bb83fb8000

def z642 : W := mkw 0xc027580006dda000 0x7009d60001b76800 0x08c718000ffff003 0xc231c60003fffc00

def z643 : W := mkw 0x4027580004d4a000 0x5009d60001352800 0x1b47d80008fef003 0x46d1f600023fbc00

def z644 : W := mkw 0x003da59900000003 0x000f696640000000 0xff3fe7ff00000000 0x3fcff9ffc0000000

def z645 : W := mkw 0x402758d4a4d4a002 0xd009d63529352800 0x484718f0f0f0f001 0x1211c63c3c3c3c00

def z646 : W := mkw 0xaa0002025b0b5d7c 0x2a80008096c2d75f 0xfd813911ff1fffff 0xff604e447fc7ffff

def z647 : W := mkw 0x0018a50900000001 0x0006294240000000 0xb738e70f00010c3e 0xedce39c3c000430f

def z648 : W := mkw 0x0002504480000000 0x8000941120000000 0x9000d00ec0000000 0x24003403b0000000

def z649 : W := mkw 0xa81aff4fab0b0c29 0xaa06bfd3eac2c30a 0xb7b8ff0fff0f0c3e 0xedee3fc3ffc3c30f

def z650 : W := mkw 0xc037f800024da000 0x300dfe0000936800 0x1f3ff800000ff002 0x07cffe000003fc00

def z651 : W := mkw 0xc012f800024da000 0x3004be0000936800 0x1b46f80008eff003 0x46d1be00023bfc00

def z652 : W := mkw 0xa80002020b0b0c28 0x2a00008082c2c30a 0xb380c60e0f0f0c3e 0xece0318383c3c30f

def z653 : W := mkw 0x103ffdfda4b00283 0xc40fff7f692c00a0 0xff7ffffff0f003c1 0x3fdffffffc3c00f0

def z654 : W := mkw 0x003ffd9000000002 0x000fff6400000000 0x7f3ffff000000000 0x1fcffffc00000000

def z655 : W := mkw 0x0035a80000000000 0x000d6a0000000000 0x0439280000000000 0x010e4a0000000000

def z656 : W := mkw 0x303fffb00db00e82 0x4c0fffec036c03a0 0x7ffffff00ff00fc1 0xdffffffc03fc03f0

def z657 : W := mkw 0xc03ffd0906dda001 0x700fff4241b76800 0xbfffff0f0ffff003 0xefffffc3c3fffc00

def z658 : W := mkw 0x0000000000000000 0x0000000000000000 0x0b46000008e00001 0x42d1800002380000

def z659 : W := mkw 0x0025000004900000 0x4009400001240000 0x0847000000f00001 0x0211c000003c0000

def z660 : W := mkw 0x4027580004d4a000 0x5009d60001352800 0x0fff18000ff0f001 0xc3ffc60003fc3c00

def z661 : W := mkw 0x0000000000000000 0x0000000000000000 0xbd0139010011fc3f 0xef404e4040047f0f

def z662 : W := mkw 0x702f5fb00df4ae82 0x5c0bd7ec037d2ba0 0x6fff1ff00ff0ffc1 0xdbffc7fc03fc3ff0

def z663 : W := mkw 0xa81af74f8b0b0c29 0xaa06bdd3e2c2c30a 0xffbef7efcf0f0c3e 0xffefbdfbf3c3c30f

def z664 : W := mkw 0x002758d4a0000002 0x8009d63528000000 0x000600e000000000 0x0001803800000000

def z665 : W := mkw 0xa800000003090408 0x2a00000000c24102 0x008000000701040c 0x8020000001c04103

def z666 : W := mkw 0x0452f84fe046c131 0x8114be13f811b04c 0x9000f80ff00ec032 0x24003e03fc03b00c

def z667 : W := mkw 0x302d059005900482 0x4c0b416401640120 0x6fbf07f0071004c0 0x9befc1fc01c40130

def z668 : W := mkw 0xc477fa668effaa20 0xf11dfe99a3bfea88 0x02fec6ee0fee0000 0x00bfb1bb83fb8000

def z669 : W := mkw 0x003ffd9920000003 0x000fff6648000000 0x1f3ff91130000000 0x07cffe444c000000

def z670 : W := mkw 0x0000000000000000 0x0000000000000000 0xb300c60e00000000 0x2cc0318380000000

def z671 : W := mkw 0x04400266c866cb30 0x81100099b219b2cc 0xe04006eec8eecb33 0x781001bbb23bb2cc

def z672 : W := mkw 0xf23fffb05ffdffd6 0x7c8fffec17ff7ff5 0xfffffff1ffffffff 0xfffffffc7fffffff

def z673 : W := mkw 0x8810a00b020b0029 0x22042802c082c00a 0xb500e10f000f0c3e 0xed403843c003c30f

def z674 : W := mkw 0x0200000050005154 0x0080000014001455 0xd8013811f011f3ff 0x36004e047c047cff

def z675 : W := mkw 0x8c52f26fca6fcb39 0xa314bc9bf29bf2ce 0xfb46f6efc8efcb3f 0x7ed1bdbbf23bf2cf

def z676 : W := mkw 0x0200000050005154 0x0080000014001455 0x9d013801f011f03f 0xe7404e007c047c0f

def z677 : W := mkw 0x044002224866cb30 0x011000889219b2cc 0xf9401000c8eecb33 0x7e500400323bb2cc

def z678 : W := mkw 0x0000000040004110 0x0000000010001044 0xfd013911f000cb33 0x7f404e447c0032cc

def z679 : W := mkw 0x0000000000000000 0x0000000000000000 0x6900000000000b01 0x5a400000000002c0

def z680 : W := mkw 0x0200000010001044 0x0080000004000411 0x00000000001134cc 0x8000000000044d33

def z681 : W := mkw 0x0025089020000002 0x0009422408000000 0x0001081030000000 0x000042040c000000

def z682 : W := mkw 0xac58a72b4b6fcf39 0x2b1629cad2dbf3ce 0xb7f8e70f0fefcf3f 0xedfe39c3c3fbf3cf

def z683 : W := mkw 0x0000000000000000 0x0000000000000000 0x6b0606e000000000 0x1ac181b800000000

def z684 : W := mkw 0x0477fa66c866cb30 0x811dfe99b219b2cc 0xff7ffeeec8eecb33 0x7fdfffbbb23bb2cc

def z685 : W := mkw 0x0000022008200a00 0x0000008802080280 0x0040000008e00b01 0x40100000023802c0

def z686 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0x27b8c70e0f0e0c00 0xc9ee31c383c38300

def z687 : W := mkw 0x300807b009200e82 0x0c0201ec024803a0 0x6d0107f000100fc1 0xdb4041fc000403f0

def z688 : W := mkw 0x2008070009000c00 0x080201c002400300 0x6fb907100f100fc1 0xdbee41c403c403f0

def z689 : W := mkw 0xaa18a70b5b0b5d7d 0x2a8629c2d6c2d75f 0xf7b8e71fff0f0ffe 0xfdee39c7ffc3c3ff

def z690 : W := mkw 0xc03ffd9926dda003 0x700fff6649b76800 0x1ffff9113ffff003 0xc7fffe444ffffc00

def z691 : W := mkw 0x0000000040004110 0x0000000010001044 0xfd011110c010cff3 0xff404444300433fc

def z692 : W := mkw 0x0200000010001044 0x0080000004000411 0xfd013911f01134cc 0xbf404e447c044d33

def z693 : W := mkw 0x300807b00db00e82 0x4c0201ec036c03a0 0x60c007f00ff00fc1 0xd83001fc03fc03f0

def z694 : W := mkw 0x003fffdfa8020823 0x800ffff7ea008208 0xff3ffffff80e0832 0x7fcffffffe03820c

def z695 : W := mkw 0xe83dad0907992409 0x7a0f6b4241e64902 0x04b929010711340c 0x812e4a4041c44d03

def z696 : W := mkw 0x4027580004d4a000 0x5009d60001352800 0x1d47380000f1f003 0xc751ce00003c7c00

def z697 : W := mkw 0x8452f266ca6fcb30 0xa114bc99b29bf2cc 0xfffef6eecfefcb33 0xffffbdbbb3fbf2cc

def z698 : W := mkw 0xe818a70b0fdfac29 0x7a0629c2c3f7eb0a 0xb7f8e70f0ffffc3f 0xedfe39c3c3ffff0f

def z699 : W := mkw 0xba3da7bb5fbb5fff 0x6e8f69eed7eed7ff 0xffffffffffffffff 0xffffffffffffffff

def z700 : W := mkw 0xbc7ff7ffcfffcfbb 0xef1ffdfff3fff3ee 0xfffff7ffcfffcfff 0xfffffdfff3fff3ff

def z701 : W := mkw 0xaa18a5095309555d 0x2a86294254c25557 0xfdb93911f711ffff 0xff6e4e447dc47fff

def z702 : W := mkw 0x2208070059005d54 0x088201c016401755 0xffb93f11ff11ffff 0xffee4fc47fc47fff

def z703 : W := mkw 0xa80002020b0b0c28 0x2a00008082c2c30a 0x008000000f0e0000 0x0020000003c38000

def z704 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000100fc1 0xc0000000000403f0

def z705 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x1ffff8000fee0000 0x07fffe0003fb8000

def z706 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x0fff06e00ff00001 0xc3ffc1b803fc0000

def z707 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xa6b8e70f0f0f0c3c 0xa9ae39c3c3c3c30f

def z708 : W := mkw 0xc037f84486dda000 0xf00dfe1121b76800 0x9ffff80ecffff003 0xe7fffe03b3fffc00

def z709 : W := mkw 0xaa18a70b5b0b5d7d 0x2a8629c2d6c2d75f 0x4ab9de1eff1ef3c1 0x12ae7787bfc7bcf0

def z710 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0x6b46d6eec8eecb01 0x5ad1b5bbb23bb2c0

def z711 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xfb47deeec8fefb33 0x7ed1f7bbb23fbecc

def z712 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x6cff07f007f00fc1 0x9b3fc1fc01fc03f0

def z713 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xff47feeec8ffffff 0xffd1ffbbb23fffff

def z714 : W := mkw 0x0000022208220a20 0x0000008882088288 0x6b46c6ee08ee0b01 0x5ad1b1bb823b82c0

def z715 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x2346c6ee08ee0800 0x48d1b1bb823b8200

def z716 : W := mkw 0xc837f80906dda009 0x720dfe0241b76802 0x1ffff8010ffff00f 0xc7fffe0043fffc03

def z717 : W := mkw 0xf01affb00b6dae82 0x3c06bfec02db6ba0 0x7000fff0000fffc2 0x1c003ffc0003fff0

def z718 : W := mkw 0x0642526698669a64 0x81909499a619a699 0x0647efff38ff34cc 0x8191fbffce3fcd33

def z719 : W := mkw 0x364807f6d9225ff6 0x8d9201fdb64897fd 0xe00007fff0000ffc 0x380001fffc0003ff

def z720 : W := mkw 0x003ffddda4900003 0xc00fff7769240000 0xffbffffff7100000 0xbfeffffffdc40000

def z721 : W := mkw 0xc025000006dda000 0x7009400001b76800 0x1fff38000ffff003 0xc7ffce0003fffc00

def z722 : W := mkw 0xa83ffddda309040b 0xaa0fff7768c24102 0xffbffffff7010c3e 0xffeffffffdc0430f

def z723 : W := mkw 0x883ffddda209000b 0xa20fff7768824002 0xff3ffffff001000c 0x3fcffffffc004003

def z724 : W := mkw 0x402f5ddda4d4a003 0xd00bd77769352800 0xe8471ffff0f0f001 0x3a11c7fffc3c3c00

def z725 : W := mkw 0x322d07b05db05fd6 0x4c8b41ec176c17f5 0x92fe3ee1ffe1f03e 0x24bf8fb87ff87c0f

def z726 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff0110fff 0xffcffffffc0443ff

def z727 : W := mkw 0xc03ffddda6992003 0xf00fff7769a64800 0xfffffffffff13001 0xfffffffffffc4c00

def z728 : W := mkw 0x403ffddda4d4a003 0xd00fff7769352800 0xff7ffffff8fef003 0x7fdffffffe3fbc00

def z729 : W := mkw 0xc035a80006dda000 0x700d6a0001b76800 0x17f9e8000ffff003 0xc5fe7a0003fffc00

def z730 : W := mkw 0x803ffddda24d8003 0xa00fff7768936000 0xffffffffffefc003 0xfffffffffffbf000

def z731 : W := mkw 0x003ffddda0448003 0x800fff7768112000 0xff3ffffff00ec002 0x3fcffffffc03b000

def z732 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xff46f7efc8ffffff 0xffd1bdfbf23fffff

def z733 : W := mkw 0x364002225df6dff4 0x4d900088977db7fd 0x00c000000fffffff 0xc030000003ffffff

def z734 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x67fe07f00fe00fc0 0xd9ff81fc03f803f0

def z735 : W := mkw 0xc03ffddda24da003 0xb00fff7768936800 0xff7ffffff8eff003 0x7fdffffffe3bfc00

def z736 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x62fe07f00ff00fc1 0xd8bf81fc03fc03f0

def z737 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xea46d6eec8eecb31 0x3a91b5bbb23bb2cc

def z738 : W := mkw 0xc237f80056ddf154 0x708dfe0015b77c55 0xe2fec111ffee0ffc 0x38bfb0447ffb83ff

def z739 : W := mkw 0x9835a0bb06bb02ab 0x660d682ec1aec0aa 0xd847e0ff00ff03ff 0x3611f83fc03fc0ff

def z740 : W := mkw 0x0442526688668a20 0x81109499a219a288 0xa246c6ee08ee0830 0x2891b1bb823b820c

def z741 : W := mkw 0x0002526488648a00 0x8000949922192280 0xfb46d6eec8eecb03 0x7ed1b5bbb23bb2c0

def z742 : W := mkw 0x047dafbb6866cb33 0x011f6beeda19b2cc 0x0479291138eecb33 0x411e4a444e3bb2cc

def z743 : W := mkw 0xa818a5dda309040b 0xaa06297768c24102 0xe4b827fff701040c 0xb92e09fffdc04103

def z744 : W := mkw 0x300805dda1000483 0x8c02017768400120 0xe00007fff00004c0 0x380001fffc000130

def z745 : W := mkw 0xc03ffddda6992003 0xf00fff7769a64800 0xffbffffff711f003 0xffeffffffdc47c00

def z746 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0xffff07f00ff00ff3 0xffffc1fc03fc03fc

def z747 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x3ffff9000ffffc03 0xcffffe4003ffff00

def z748 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x17fef8000feff002 0xc5ffbe0003fbfc00

def z749 : W := mkw 0x803ffddda6990003 0xe00fff7769a64000 0xffffffffffff0003 0xffffffffffffc000

def z750 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xff47fffff8effb3f 0x7fd1fffffe3bfecf

def z751 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x0fffc0000ffff003 0xc3fff00003fffc00

def z752 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x6fff07f00ff1ffc3 0xdbffc1fc03fc7ff0

def z753 : W := mkw 0x34425266c966cfb0 0x8d109499b259b3ec 0xfb46d6eec8eecff3 0x7ed1b5bbb23bb3fc

def z754 : W := mkw 0xae4002225b6fdf7c 0x2b90008896dbf7df 0x00c000000fffffff 0xc030000003ffffff

def z755 : W := mkw 0xc025000006dda000 0x7009400001b76800 0x04f900000ffff003 0xc13e400003fffc00

def z756 : W := mkw 0x3012fa6dadb00e81 0xcc04be9b6b6c03a0 0x90c0f80ffff00fc1 0xe4303e03fffc03f0

def z757 : W := mkw 0x0012f84da0000001 0x8004be1368000000 0x9206feeff0000000 0x2481bfbbfc000000

def z758 : W := mkw 0x000805dda0000003 0x8002017768000000 0xeb0607fff0000000 0x3ac181fffc000000

def z759 : W := mkw 0x302d05b005b00682 0x4c0b416c016c01a0 0x48ff00f007f003c1 0x123fc03c01fc00f0

def z760 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0x0246c6ee08ffffff 0xc091b1bb823fffff

def z761 : W := mkw 0x000a55dda0448003 0x8002957768112000 0xfb46d7fff8eec003 0x7ed1b5fffe3bb000

def z762 : W := mkw 0xba3da599179914cf 0x6e8f696645e64533 0x04b92911371134cc 0x812e4a444dc44d33

def z763 : W := mkw 0x803ffddda2090003 0xa00fff7768824000 0xff3ffffff00f0002 0x3fcffffffc03c000

def z764 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x7b46d6ee08eecb03 0x5ed1b5bb823bb2c0

def z765 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x1afff8000ffff003 0x06bffe0003fffc00

def z766 : W := mkw 0xc652f846d24ff174 0xb194be11b493fc5d 0x9000f80ff00ff03e 0x24003e03fc03fc0f

def z767 : W := mkw 0x002758d4a0000002 0x8009d63528000000 0xe8071efef0000000 0x3a01c7bfbc000000

def z768 : W := mkw 0x000805dda0000003 0x8002017768000000 0xe73807fff0000000 0x39ce01fffc000000

def z769 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x6246c6ee08ee0b00 0x1891b1bb823b82c0

def z770 : W := mkw 0x002d05dda0000003 0x800b417768000000 0xff3f3ffff0000000 0x3fcfcffffc000000

def z771 : W := mkw 0xc01afddda24da003 0xb006bf7768936800 0xf000fffff00ff002 0x3c003ffffc03fc00

def z772 : W := mkw 0x0200000050005154 0x0080000014001455 0xff473911f8f1ffff 0xffd1ce447e3c7fff

def z773 : W := mkw 0x302d07b20db20ea2 0x4c0b41ec836c83a8 0x6fffc7fe0ffe0fc1 0xdbfff1ff83ff83f0

def z774 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0x5ffffefefffff003 0xd7ffffbfbffffc00

def z775 : W := mkw 0xc035a80006dda000 0x700d6a0001b76800 0x1df938000ffff003 0xc77e4e0003fffc00

def z776 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x5ffff8100ffff3c3 0xd7fffe0403fffcf0

def z777 : W := mkw 0x000805dda0000003 0x8002017768000000 0x400006fef0000000 0x100001bfbc000000

def z778 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xfb46d7fff8ffffff 0xfed1b5fffe3fffff

def z779 : W := mkw 0x303ffddda5900483 0xcc0fff7769640120 0xfffffffffff004c1 0xfffffffffffc0130

def z780 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff01004c0 0xbfcffffffc040130

def z781 : W := mkw 0xc03ffddda24da003 0xb00fff7768936800 0xff3ffffff00e0000 0x3fcffffffc038000

def z782 : W := mkw 0x382d07bb0db20eab 0x4e0b41eec36c83aa 0x6fff07fe0ff00fc1 0xdbffc1ff83fc03f0

def z783 : W := mkw 0xc475aa66cebb6b30 0xf11d6a99b3aedacc 0xe4b92eeec7113b30 0xb92e4bbbb1c44ecc

def z784 : W := mkw 0x04425064c064c310 0x81109419301930c4 0xfb46d6eec8eec303 0x7ed1b5bbb23bb0c0

def z785 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xff46f6eec8efcb33 0xffd1bdbbb23bf2cc

def z786 : W := mkw 0x302d05b005b00682 0x4c0b416c016c01a0 0x6fff07f007f007c1 0x9bffc1fc01fc01f0

def z787 : W := mkw 0x000a5ddda0000003 0x8002977768000000 0xe0001ffff0000000 0x380007fffc000000

def z788 : W := mkw 0xc037f84da6dda001 0xf00dfe1369b76800 0xfffffeeffffff003 0xffffffbbfffffc00

def z789 : W := mkw 0x0012f84da0000001 0x8004be1368000000 0xff07fffff0000000 0x3fc1fffffc000000

def z790 : W := mkw 0x0027500004d48000 0x4009d40001352000 0x1ffff8000ffff003 0xc7fffe0003fffc00

def z791 : W := mkw 0x303ffddda1000483 0x8c0fff7768400120 0xff3ffffff00004c0 0x3fcffffffc000130

def z792 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x02fec0000ffef001 0x00bfb00003ffbc00

def z793 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xff47fffff8fffb33 0xffd1fffffe3ffecc

def z794 : W := mkw 0xc010a00006dda000 0x7004280001b76800 0x04f820000ffff003 0xc13e080003fffc00

def z795 : W := mkw 0x0002526688220a20 0x80009499a2088288 0xfb46d6eec8ee0b33 0x7ed1b5bbb23b82cc

def z796 : W := mkw 0x064002225866db74 0x019000889619b6dd 0x0040000008effb3f 0x40100000023bfecf

def z797 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xfb46d6eec8eec032 0x3ed1b5bbb23bb00c

def z798 : W := mkw 0x002d05dda4900003 0xc00b417769240000 0xefff07fffff00001 0xfbffc1fffffc0000

def z799 : W := mkw 0xa818af0b2b0b0c29 0x2a062bc2cac2c30a 0xb7b8ef0f3f0f0c3e 0xedee3bc3cfc3c30f

def z800 : W := mkw 0x102d05b004b00282 0x440b416c012c00a0 0x6fff07f00ff003c1 0xdbffc1fc03fc00f0

def z801 : W := mkw 0xc00805dda6dda003 0xf002017769b76800 0xe0c007fffffff003 0xf83001fffffffc00

def z802 : W := mkw 0x2008072009200e00 0x080201c802480380 0x6fff07f00ff00fc1 0xdbffc1fc03fc03f0

def z803 : W := mkw 0xc03dad9926992003 0x700f6b6649a64800 0x04b9280007113000 0x812e4a0001c44c00

def z804 : W := mkw 0x382d07b20db20eaa 0x4e0b41ec836c83aa 0x6fff07f00ff00ffd 0xdbffc1fc03fc03ff

def z805 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xff47d7fff8fecfff 0xffd1f5fffe3fb3ff

def z806 : W := mkw 0xa810a20b0b0b0c29 0x2a042882c2c2c30a 0x97b8e00f0f0f0c3e 0xe5ee3803c3c3c30f

def z807 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xffbee7ef0f0f0c3e 0xffefb9fbc3c3c30f

def z808 : W := mkw 0x003ffddda0448003 0x800fff7768112000 0xff7ffffff8fff003 0xffdffffffe3ffc00

def z809 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff7ffffff8e00001 0x7fdffffffe380000

def z810 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x06ffe8000ffff003 0xc1bffa0003fffc00

def z811 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff0000c3c 0x3fcffffffc00030f

def z812 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0x0246d6eec8eec000 0x0091b5bbb23bb000

def z813 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x12fef8000ffff003 0xc4bfbe0003fffc00

def z814 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xfb47defef8ffffff 0xfed1f7bfbe3fffff

def z815 : W := mkw 0xc23dad9936993047 0x708f6b664da64c11 0x04b92911371134cc 0x812e4a444dc44d33

def z816 : W := mkw 0x002d05dda0000003 0x800b417768000000 0xe23e07fff0000000 0x388f81fffc000000

def z817 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xfb46d7efc8eecf3f 0x7ed1b5fbf23bb3cf

def z818 : W := mkw 0x00025044c044c110 0x8000941130113044 0xfb46d6eec8eecb33 0x7ed1b5bbb23bb2cc

def z819 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0x0246c6ee08eec301 0x0091b1bb823bb0c0

def z820 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x6fff1ff00ff0ffc1 0xdbffc7fc03fc3ff0

def z821 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xec3f3ffff0000000 0x3b0fcffffc000000

def z822 : W := mkw 0xc037f8d4a6dda002 0xf00dfe3529b76800 0xfffffefefffff003 0xffffffbfbffffc00

def z823 : W := mkw 0x302d07b92db00e83 0x4c0b41ee4b6c03a0 0x6fff07f13ff00fc1 0xdbffc1fc4ffc03f0

def z824 : W := mkw 0x346f55d6c5d6c5b2 0xcd1bd575b175b16c 0x94b9d11ec71ec4f2 0xa52e7447b1c7b13c

def z825 : W := mkw 0xa818a50b030b0429 0x2a062942c0c2c10a 0x97b8e10f0f0f043e 0xe5ee3843c3c3c10f

def z826 : W := mkw 0x00025844a0000000 0x8000961128000000 0xfb06deeef0000000 0x3ec1b7bbbc000000

def z827 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xffb9ff1fff1f0fff 0xffee7fc7ffc7c3ff

def z828 : W := mkw 0xac5af56dc36dc719 0xab16bd5b70db71c6 0x4cfe31e1c7e1c70d 0x933f8c7871f871c3

def z829 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xb7b8e70f0f0f003e 0x2dee39c3c3c3c00f

def z830 : W := mkw 0x0002504480000000 0x8000941120000000 0xfb07defef0000000 0x3ec1f7bfbc000000

def z831 : W := mkw 0x0442526688668a20 0x81109499a219a288 0xbb46d6ee08eec833 0x6ed1b5bb823bb20c

def z832 : W := mkw 0x403ffddda4d4a003 0xd00fff7769352800 0xfffffffffff0f001 0xfffffffffffc3c00

def z833 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xff46d7eec8eecf33 0xffd1b5fbb23bb3cc

def z834 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x9ffff8010ffff03f 0xe7fffe0043fffc0f

def z835 : W := mkw 0x002f5ddda0000003 0x800bd77768000000 0xe00607fff0000000 0x380181fffc000000

def z836 : W := mkw 0x003ffddda4900003 0xc00fff7769240000 0xff7ffffff0f00001 0x3fdffffffc3c0000

def z837 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x7ffff9100ffff003 0xdffffe4403fffc00

def z838 : W := mkw 0x302502200db00e80 0x4c094088036c03a0 0x6fff06e00ff00fc1 0xdbffc1b803fc03f0

def z839 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x02fe06e00fe00fc0 0x00bf81b803f803f0

def z840 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xfffed6eecfeecb33 0xffffb5bbb3fbb2cc

def z841 : W := mkw 0x8810a00b020b0029 0x22042802c082c00a 0x92b8e00f0f0f003e 0x24ae3803c3c3c00f

def z842 : W := mkw 0x001afddda0000003 0x8006bf7768000000 0xfb06fffff0000000 0x3ec1bffffc000000

def z843 : W := mkw 0x000805dda0000003 0x8002017768000000 0xe00007fff0000c3c 0x380001fffc00030f

def z844 : W := mkw 0x8810a20b0a0b0829 0x22042882c282c20a 0xb7b8e60f0f0f083e 0xedee3983c3c3c20f

def z845 : W := mkw 0x403ffddda044a003 0x900fff7768112800 0xff3ffffff000f000 0x3fcffffffc003c00

def z846 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x1f47feee08fff003 0xc7d1ffbb823ffc00

def z847 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0x17b8e60e0f0f0c3e 0xc5ee398383c3c30f

def z848 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xff47fffff8efcf3f 0xffd1fffffe3bf3cf

def z849 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x02fe06e00ff003c1 0x00bf81b803fc00f0

def z850 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x1bfed0000ffff003 0xc6ffb40003fffc00

def z851 : W := mkw 0x302d05dda5900483 0xcc0b417769640120 0xe4b907fff71004c0 0xb92e41fffdc40130

def z852 : W := mkw 0x023ffdddf0005157 0x808fff777c001455 0x023ec6ee0011ffff 0xc08fb1bb80047fff

def z853 : W := mkw 0x001afddda0000003 0x8006bf7768000000 0xf738fffff0000000 0x3dce3ffffc000000

def z854 : W := mkw 0x0200000050005154 0x0080000014001455 0x4c013911f011ffff 0xd3004e447c047fff

def z855 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0xbffffe0e0ffff003 0xefffff8383fffc00

def z856 : W := mkw 0xc03daddda6992003 0xf00f6b7769a64800 0xe4b92ffff7113000 0xb92e4bfffdc44c00

def z857 : W := mkw 0x002f5dd4a0000002 0x800bd77528000000 0xff3fdffef0000000 0x3fcff7ffbc000000

def z858 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x0efff8000ffff001 0x83bffe0003fffc00

def z859 : W := mkw 0x000805dda0000003 0x8002017768000000 0xe4012ffff0000000 0x39004bfffc000000

def z860 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x6aff07f00ff00fc1 0x1abfc1fc03fc03f0

def z861 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x0cff38000ffff003 0xc33fce0003fffc00

def z862 : W := mkw 0x0002524688468820 0x80009491a211a208 0xfb46d6eec8eec833 0x7ed1b5bbb23bb20c

def z863 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x7fff17f00ff0cfc3 0xdfffc5fc03fc33f0

def z864 : W := mkw 0x8818a50b020b0029 0x22062942c082c00a 0xb7b8e70f0f0f003e 0xedee39c3c3c3c00f

def z865 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xff47d7fec8ffffff 0xffd1f5ffb23fffff

def z866 : W := mkw 0x8018a50902090001 0x2006294240824000 0xb7b8e70f0f0f0c3e 0xedee39c3c3c3c30f

def z867 : W := mkw 0x2c425266c966cf38 0x8b109499b259b3ce 0xfb46d6eec8eecf3f 0x7ed1b5bbb23bb3cf

def z868 : W := mkw 0x403ffddda4902003 0xd00fff7769240800 0xff3ffffff0103000 0x3fcffffffc040c00

def z869 : W := mkw 0xc010a00006dda000 0x7004280001b76800 0x02f8c0000ffff003 0xc0be300003fffc00

def z870 : W := mkw 0x4027580004d4a000 0x5009d60001352800 0x1fffd8000ffef003 0xc7fff60003ffbc00

def z871 : W := mkw 0x0002504480448000 0x8000941120112000 0xff47fffff8fff003 0xffd1fffffe3ffc00

def z872 : W := mkw 0x803ffddda2090003 0xa00fff7768824000 0xffbffffff7010000 0xbfeffffffdc04000

def z873 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xe63feffff0000000 0x398ffbfffc000000

def z874 : W := mkw 0xa818a72b0b2b0e29 0x2a0629cac2cac38a 0xffffe7ff0fff0fff 0xfffff9ffc3ffc3ff

def z875 : W := mkw 0xa818a50b030b0429 0x2a062942c0c2c10a 0xb5b8e10f070f0c3e 0xed6e3843c1c3c30f

def z876 : W := mkw 0x2e48076fd9225f7d 0x8b9201dbf64897df 0xe00007fff0000ffc 0x380001fffc0003ff

def z877 : W := mkw 0xc037f89026dda002 0x700dfe2409b76800 0x1ffff8103ffff003 0xc7fffe040ffffc00

def z878 : W := mkw 0x000a55dda0000003 0x8002957768000000 0xe206c7fff0000000 0x3881b1fffc000000

def z879 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x0fff06e00ff00fc1 0xc3ffc1b803fc03f0

def z880 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff0000c00 0xffcffffffc000300

def z881 : W := mkw 0x0200000050005154 0x0080000014001455 0x94013911f011ffff 0xe5004e447c047fff

def z882 : W := mkw 0xc012f84da24da001 0xb004be1368936800 0xfb46feeff8eff003 0x7ed1bfbbfe3bfc00

def z883 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xfb46d7fec8eecff3 0x7ed1b5ffb23bb3fc

def z884 : W := mkw 0x000805dda0000003 0x8002017768000000 0xf0003ffff0000000 0x3c000ffffc000000

def z885 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0xfffffffffffffc3f 0xffffffffffffff0f

def z886 : W := mkw 0x000805dda0000003 0x8002017768000000 0xf50027fff0000000 0x3d4009fffc000000

def z887 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xb7b9ef1f3f0f0c3e 0xedee7bc7cfc3c30f

def z888 : W := mkw 0xc035a80006dda000 0x700d6a0001b76800 0x0fff28000ffff003 0xc3ffca0003fffc00

def z889 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0x9ffffeeffffff003 0xe7ffffbbfffffc00

def z890 : W := mkw 0xe818af0b0b0b2c29 0x3a062bc2c2c2cb0a 0xb7b8ef0f0f0f3c3e 0xedee3bc3c3c3cf0f

def z891 : W := mkw 0x2808070b09020c29 0x0a0201c2c240830a 0xb7b8c70f0f0e0c3e 0xedee31c3c3c3830f

def z892 : W := mkw 0x2008070209020c20 0x080201c082408308 0xb7b8e70f0f0f0c3e 0xedee39c3c3c3c30f

def z893 : W := mkw 0x303ffddda5900483 0xcc0fff7769640120 0xffbffffff7000000 0x3feffffffdc00000

def z894 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x1bfef8000feff003 0x46ffbe0003fbfc00

def z895 : W := mkw 0x682f5f0b0dd6ac29 0x5a0bd7c2c375ab0a 0xa8471f0f00f0fc3d 0x2a11c7c3c03c3f0f

def z896 : W := mkw 0xa8275ad6ab0b0c2a 0xaa09d6b5aac2c30a 0x488718f0ff0f0c3e 0xd221c63c3fc3c30f

def z897 : W := mkw 0xc037f84486dda000 0xf00dfe1121b76800 0x1ffffeee0ffff003 0xc7ffffbb83fffc00

def z898 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xf23efffff0000000 0x3c8fbffffc000000

def z899 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x02fed8000feef000 0x00bfb60003fbbc00

def z900 : W := mkw 0x044002224866cb30 0x011000889219b2cc 0xfb46c6ee08eecb33 0x7ed1b1bb823bb2cc

def z901 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x1ffff9113ffff003 0xc7fffe444ffffc00

def z902 : W := mkw 0xc037f844a6dda000 0xf00dfe1129b76800 0x1ffff800fffff003 0xc7fffe003ffffc00

def z903 : W := mkw 0xa83ffddda309040b 0xaa0fff7768c24102 0xffbffffff7000000 0x3feffffffdc00000

def z904 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xb346d6eec8eec832 0x6cd1b5bbb23bb20c

def z905 : W := mkw 0xa818a50b030b0429 0x2a062942c0c2c10a 0xb7b8e70f070f043e 0xadee39c3c1c3c10f

def z906 : W := mkw 0x04425a66e866cb30 0x81109699ba19b2cc 0xfb46deeef8eecb33 0x7ed1b7bbbe3bb2cc

def z907 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x4a46c6ee08ee0301 0x1291b1bb823b80c0

def z908 : W := mkw 0x283ffddda100040b 0x8a0fff7768400102 0xff3ffffff000040c 0x3fcffffffc000103

def z909 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xb346c6ee08eecb33 0x6cd1b1bb823bb2cc

def z910 : W := mkw 0x000805dda0000003 0x8002017768000000 0xfd013ffff011f003 0xff404ffffc047c00

def z911 : W := mkw 0x000a55dda0000003 0x8002957768000000 0xe80617fff0000000 0x3a0185fffc000000

def z912 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0x9246feeff8eff03e 0x2491bfbbfe3bfc0f

def z913 : W := mkw 0x0018a5dda0000003 0x8006297768000000 0xe43827fff0000000 0x390e09fffc000000

def z914 : W := mkw 0xc000000006dda000 0x7000000001b76800 0x07f800000ffff003 0xc1fe000003fffc00

def z915 : W := mkw 0x422758d4f4d4f156 0xd089d6353d353c55 0x484718f0f0f0f3c1 0x1211c63c3c3c3cf0

def z916 : W := mkw 0x002502200cb00a00 0x40094088032c0280 0x6fff07f00ff00fc1 0xdbffc1fc03fc03f0

def z917 : W := mkw 0x382d07b90db00e8b 0x4e0b41ee436c03a2 0x6fff07f10ff00fcd 0xdbffc1fc43fc03f3

def z918 : W := mkw 0x000a55dda0000003 0x8002957768000000 0xff07fffff0000000 0x3fc1fffffc000000

def z919 : W := mkw 0xc03ffddda2092003 0xb00fff7768824800 0xff3ffffff0013000 0x3fcffffffc004c00

def z920 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0xe2fec7ffffee0000 0x38bfb1fffffb8000

def z921 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x6fff27f10ff10fcd 0xdbffc9fc43fc43f3

def z922 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0x4affdefefffef001 0x12bff7bfbfffbc00

def z923 : W := mkw 0xb818a72b0b2b0ea9 0x2e0629cac2cac3aa 0xb7b8e70f0f0f0ffe 0xedee39c3c3c3c3ff

def z924 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xa7b8c70f0f0e0c3c 0xe9ee31c3c3c3830f

def z925 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x0affd8000ffff003 0xc2bff60003fffc00

def z926 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xb7b8e70f0f0e0c3c 0x2dee39c3c3c3830f

def z927 : W := mkw 0x0002504480448000 0x8000941120112000 0x0246c6ee08ee0000 0x0091b1bb823b8000

def z928 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0x4a46d6eec8eecb33 0x5291b5bbb23bb2cc

def z929 : W := mkw 0x0037f8d4a0000002 0x800dfe3528000000 0xff3ffefef0000000 0x3fcfffbfbc000000

def z930 : W := mkw 0xf03dad9927992483 0x7c0f6b6649e64920 0x04b92911371134c0 0x812e4a444dc44d30

def z931 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x0246c6ee08ee0832 0x4091b1bb823b820c

def z932 : W := mkw 0x0000022208220a20 0x0000008882088288 0xb346c6ee08ee0832 0x6cd1b1bb823b820c

def z933 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0xffff3ff1fff10fff 0xffffcffc7ffc43ff

def z934 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0x06b8e70f0f0f0c3e 0xc1ae39c3c3c3c30f

def z935 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x4cff01f00ff00fc1 0xd33fc07c03fc03f0

def z936 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0x96b8e70f0f0f043e 0xa5ae39c3c3c3c10f

def z937 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0x02b8c60e0f0f003e 0x00ae318383c3c00f

def z938 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xff47fffff8fefbf3 0x7fd1fffffe3fbefc

def z939 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0x02b8c60e0f0e0c3c 0x00ae318383c3830f

def z940 : W := mkw 0x402758d4a4d4a002 0xd009d63529352800 0xfb47defef8fef003 0x7ed1f7bfbe3fbc00

def z941 : W := mkw 0xc037f84486dda000 0xf00dfe1121b76800 0xfffffffffffff003 0xfffffffffffffc00

def z942 : W := mkw 0xc037f84da6dda001 0xf00dfe1369b76800 0xfffff91ffffff003 0xfffffe47fffffc00

def z943 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x6fff07f00fe00fc0 0x1bffc1fc03f803f0

def z944 : W := mkw 0x0037f84da0000001 0x800dfe1368000000 0xff3ffeeff0000000 0x3fcfffbbfc000000

def z945 : W := mkw 0x203ffddda1000403 0x880fff7768400100 0xffbffffff7000400 0xbfeffffffdc00100

def z946 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x0b46c6ee08ee0001 0x42d1b1bb823b8000

def z947 : W := mkw 0xa818a79b0b0b0c2b 0x2a0629e6c2c2c30a 0xf7b8e7ff0f0f0c3e 0xfdee39ffc3c3c30f

def z948 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0xbffff8000ffff833 0xeffffe0003fffe0c

def z949 : W := mkw 0x303ffddda5900483 0xcc0fff7769640120 0xffbffffff7100fc1 0xffeffffffdc403f0

def z950 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xeb46c6eec8ee0b31 0x7ad1b1bbb23b82cc

def z951 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x06ff07f00ff00fc1 0xc1bfc1fc03fc03f0

def z952 : W := mkw 0xa818a72b0b2b0e29 0x2a0629cac2cac38a 0xb7f8e70f0fef0f3f 0xedfe39c3c3fbc3cf

def z953 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xfb46d6eec8effb3f 0x7ed1b5bbb23bfecf

def z954 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x1ffff9100ffff4c3 0xc7fffe4403fffd30

def z955 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0xfffffffffffef001 0x3fffffffffffbc00

def z956 : W := mkw 0x0442526688668a20 0x81109499a219a288 0xb746e7ef08ef0c3e 0xedd1b9fbc23bc30f

def z957 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0xbffff9010ffff003 0xeffffe4043fffc00

def z958 : W := mkw 0x000000d4a0000002 0x8000003528000000 0xe00006fef0000000 0x380001bfbc000000

def z959 : W := mkw 0x002d0ddda0000003 0x800b437768000000 0xe0010ffff0000000 0x380043fffc000000

def z960 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xfb46fffff8efffff 0x7ed1bffffe3bffff

def z961 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x1246d6ee08eec002 0x0491b5bb823bb000

def z962 : W := mkw 0x003ffddda0448003 0x800fff7768112000 0xff7ffffff0e0c001 0x3fdffffffc383000

def z963 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x4aff06f00ff00fc1 0xd2bfc1bc03fc03f0

def z964 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xda3ffefff0000000 0x368fffbffc000000

def z965 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xf246d6eec8eecb32 0x3c91b5bbb23bb2cc

def z966 : W := mkw 0x300807b009200e82 0x0c0201ec024803a0 0x6ffe07f00fe00fc1 0xdbff81fc03f803f0

def z967 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff0000fc0 0x3fcffffffc0003f0

def z968 : W := mkw 0x003ffddda4d48003 0xc00fff7769352000 0xfffffffffffec003 0xffffffffffffb000

def z969 : W := mkw 0x003daddda0000003 0x800f6b7768000000 0xfd393ffff0000000 0x3f4e4ffffc000000

def z970 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xffb9ff1fff1ffc3f 0xffee7fc7ffc7ff0f

def z971 : W := mkw 0x0000004da0000001 0x8000001368000000 0xe00006eff0000000 0x380001bbfc000000

def z972 : W := mkw 0xc027580006dda000 0x7009d60001b76800 0x0fff18000ffff003 0xc3ffc60003fffc00

def z973 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x6f47c7fe08fe0fc1 0xdbd1f1ff823f83f0

def z974 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xfb46d6eec8eec301 0x3ed1b5bbb23bb0c0

def z975 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x02fec0000feff002 0x00bfb00003fbfc00

def z976 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xfb3efeeff0000000 0x3ecfbfbbfc000000

def z977 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xb4b8e70f070f0c3e 0xad2e39c3c1c3c30f

def z978 : W := mkw 0x001af5dda0000003 0x8006bd7768000000 0xff3ef7fff0000000 0x3fcfbdfffc000000

def z979 : W := mkw 0x0442526688668a20 0x81109499a219a288 0xb346c6ee08ee0000 0x2cd1b1bb823b8000

def z980 : W := mkw 0xb818a7bb0b2b0eab 0x2e0629eec2cac3aa 0xfffee7ff0fef0fff 0xffffb9ffc3fbc3ff

def z981 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff010f001 0x3fcffffffc043c00

def z982 : W := mkw 0xc037f84da6dda001 0xf00dfe1369b76800 0x1ffff80e0ffff003 0xc7fffe0383fffc00

def z983 : W := mkw 0x04400266c8224b30 0x81100099b20892cc 0xfb46c6eec8ee0b33 0x7ed1b1bbb23b82cc

def z984 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0x94b8e10f0f0f0c3e 0xe52e3843c3c3c30f

def z985 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xff47fffff8eecfff 0x7fd1fffffe3bb3ff

def z986 : W := mkw 0xb83dad992799048b 0x6e0f6b6649e64122 0x04b92911371104cc 0x812e4a444dc44133

def z987 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xfb46d6eff8eecb3f 0x7ed1b5bbfe3bb2cf

def z988 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xfb46d6eec8fffb33 0xfed1b5bbb23ffecc

def z989 : W := mkw 0x000805dda0000003 0x8002017768000000 0xe00007fff0000fc0 0x380001fffc0003f0

def z990 : W := mkw 0xb83ffddda799048b 0xee0fff7769e64122 0xffbffffff71104cc 0xbfeffffffdc44133

def z991 : W := mkw 0x002d059004900002 0x400b416401240000 0x6fff07f00ff00fc1 0xdbffc1fc03fc03f0

def z992 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x4a46d6eec8ee0000 0x1291b5bbb23b8000

def z993 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xf73ee7fff0000000 0x3dcfb9fffc000000

def z994 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x5ffff810fffff003 0xd7fffe043ffffc00

def z995 : W := mkw 0x002f5ddda0000003 0x800bd77768000000 0x48071efef0000000 0x1201c7bfbc000000

def z996 : W := mkw 0x8012f000024d8000 0x2004bc0000936000 0x1ffff8000ffff003 0xc7fffe0003fffc00

def z997 : W := mkw 0x302d07b20db20ea2 0x4c0b41ec836c83a8 0x6fff07f00ffe0ff3 0xdbffc1fc03ff83fc

def z998 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xffb9ff1f0f1fffff 0xffee7fc7c3c7ffff

def z999 : W := mkw 0x002758d4a0000002 0x8009d63528000000 0xff07fffff0000000 0x3fc1fffffc000000

def z1000 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xff46ffeff8efff3f 0xffd1bffbfe3bffcf

def z1001 : W := mkw 0x803ffddda2090003 0xa00fff7768824000 0xffbfffffff1ff003 0xffefffffffc7fc00

def z1002 : W := mkw 0x0200000050005154 0x0080000014001455 0xff01f911f81fffff 0xffc07e447e07ffff

def z1003 : W := mkw 0x302d07b90db00e83 0x4c0b41ee436c03a0 0xefff07ff0ff00fc1 0xfbffc1ffc3fc03f0

def z1004 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0xffbffffff71ff002 0xbfeffffffdc7fc00

def z1005 : W := mkw 0x302d05b005b00682 0x4c0b416c016c01a0 0x4fff01f00ff007c1 0xd3ffc07c03fc01f0

def z1006 : W := mkw 0x064252225866db74 0x019094889619b6dd 0x1f47f80008ffffff 0xc7d1fe00023fffff

def z1007 : W := mkw 0x0002504480000000 0x8000941120000000 0xfb06feeff0000000 0x3ec1bfbbfc000000

def z1008 : W := mkw 0x001af54d80000001 0x8006bd5360000000 0xff3ffffff0000000 0x3fcffffffc000000

def z1009 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xff47ffefc8ffff3f 0xffd1fffbf23fffcf

def z1010 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0x97b8e60f0f0f003e 0xe5ee3983c3c3c00f

def z1011 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xfb3fdefef0000000 0x3ecff7bfbc000000

def z1012 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x42fe06f00fe003c0 0x10bf81bc03f800f0

def z1013 : W := mkw 0x000250d4a0000002 0x8000943528000000 0xfb06d6fef0000000 0x3ec1b5bfbc000000

def z1014 : W := mkw 0x0200000050005154 0x0080000014001455 0xec013911f011fffd 0xbb004e447c047fff

def z1015 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xff47d6eec8fecb33 0xffd1f5bbb23fb2cc

def z1016 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0x4a47defef8fef3c1 0x1291f7bfbe3fbcf0

def z1017 : W := mkw 0xb818a7bb0b2b0eab 0x2e0629eec2cac3aa 0xb7b8e7ef0f0f0c3e 0xedee39fbc3c3c30f

def z1018 : W := mkw 0x8010a2020a0b0820 0x200428808282c208 0xb7b8e70f0f0f0c3e 0xedee39c3c3c3c30f

def z1019 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xb7b9e71f0f1f0cfe 0xedee79c7c3c7c33f

def z1020 : W := mkw 0x000805dda0000003 0x8002017768000000 0xe8011ffff0000000 0x3a0047fffc000000

def z1021 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xbfb9ff0f0f0f0c3e 0xefee7fc3c3c3c30f

def z1022 : W := mkw 0x0640022258225b74 0x01900088960896dd 0x0000000000000ffc 0x00000000000003ff

def z1023 : W := mkw 0xa83ffddda309040b 0xaa0fff7768c24102 0xffbfffffff0f040e 0xffefffffffc3c103

def z1024 : W := mkw 0x8018a5dda2090003 0xa006297768824000 0xf7b8e7ffff0f0002 0xfdee39ffffc3c000

def z1025 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x6bff06f00ff00bc1 0x5affc1bc03fc02f0

def z1026 : W := mkw 0xba0002225fbb5ffc 0x6e80008897eed7ff 0x00c000000fffffff 0xc030000003ffffff

def z1027 : W := mkw 0x0002504da0000001 0x8000941368000000 0xfb06d6eff0000000 0x3ec1b5bbfc000000

def z1028 : W := mkw 0x102500b004b00282 0x4409402c012c00a0 0x6fff01f00ff00fc1 0xdbffc07c03fc03f0

def z1029 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xfb46d6eec8efcf3f 0xfed1b5bbb23bf3cf

def z1030 : W := mkw 0xc677fa225efffb74 0x719dfe8897bffedd 0x1ffff8000fffffff 0xc7fffe0003ffffff

def z1031 : W := mkw 0x0000022248224b30 0x00000088920892cc 0xfb46d6eec8eecb33 0x7ed1b5bbb23bb2cc

def z1032 : W := mkw 0x302d07b20db20ea2 0x4c0b41ec836c83a8 0xefff07fe0ff00ff1 0xfbffc1ff83fc03fc

def z1033 : W := mkw 0xa810a2020b0b0c28 0x2a04288082c2c30a 0xb7b8e60e0f0f0c3e 0xedee398383c3c30f

def z1034 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0xffffffffffeff002 0x3ffffffffffbfc00

def z1035 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0xfffff800cffff003 0xfffffe0033fffc00

def z1036 : W := mkw 0x166750f4d4f4d3d6 0xc599d43d353d34f5 0x484718f0f0f0f3c1 0x1211c63c3c3c3cf0

def z1037 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0x8246c6eec8ee0030 0x2091b1bbb23b800c

def z1038 : W := mkw 0x0002504480448000 0x8000941120112000 0x1b46d6ee08eec003 0x46d1b5bb823bb000

def z1039 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff001040c 0xbfcffffffc004103

def z1040 : W := mkw 0x0200000050005154 0x0080000014001455 0xff073ff1f011ffff 0xffc1cffc7c047fff

def z1041 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xfb46d6fef8eecbf3 0x7ed1b5bfbe3bb2fc

def z1042 : W := mkw 0x0012f84da0000001 0x8004be1368000000 0xf000feeff0000000 0x3c003fbbfc000000

def z1043 : W := mkw 0xba3da599579955df 0x6e8f696655e65577 0xfdb93911f711ffff 0xff6e4e447dc47fff

def z1044 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0x963ffffff0000000 0x258ffffffc000000

def z1045 : W := mkw 0xb83da5990799048b 0x6e0f696641e64122 0x04b821010701040c 0x812e084041c04103

def z1046 : W := mkw 0xc212f84df24df155 0xb084be137c937c55 0x9000f80ff00ff03e 0x24003e03fc03fc0f

def z1047 : W := mkw 0xf03ffddda7dda483 0xfc0fff7769f76920 0xfffffffffffff4c3 0xfffffffffffffd30

def z1048 : W := mkw 0xc64002225efffb74 0x7190008897bffedd 0x00c000000fffffff 0xc030000003ffffff

def z1049 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0xfffff9110fffffff 0xfffffe4443ffffff

def z1050 : W := mkw 0xf83dad990799248b 0x7e0f6b6641e64922 0x04b92911071134cc 0x812e4a4441c44d33

def z1051 : W := mkw 0x04425046c046c130 0x81109411b011b04c 0xfb46d6eec8eec033 0x7ed1b5bbb23bb00c

def z1052 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xfb47d6fec8fecbf3 0x7ed1f5bfb23fb2fc

def z1053 : W := mkw 0x064002225866db74 0x019000889619b6dd 0x0040000008fefbf3 0x40100000023fbefc

def z1054 : W := mkw 0xc012f800024da000 0x3004be0000936800 0x1ffef8000feff003 0xc7ffbe0003fbfc00

def z1055 : W := mkw 0xa818a72b0b2b0e29 0x2a0629cac2cac38a 0xb7fee7ef0fef0c3e 0xedffb9fbc3fbc30f

def z1056 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xb73effeff0000000 0x2dcfbffbfc000000

def z1057 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0x4246c6eec8ee0300 0x1091b1bbb23b80c0

def z1058 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xb3b8c60e0f0f0c3e 0xecee318383c3c30f

def z1059 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0xffffffffffff3000 0xbfffffffffffcc00

def z1060 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xff47fffec8fffff3 0xffd1ffffb23ffffc

def z1061 : W := mkw 0xa818a72b0b2b0e29 0x2a0629cac2cac38a 0xf7b8e7ef0f0f0f3e 0xfdee39fbc3c3c3cf

def z1062 : W := mkw 0x002d05dda0000003 0x800b417768000000 0xe80707fff0000000 0x3a01c1fffc000000

def z1063 : W := mkw 0xc025000006dda000 0x7009400001b76800 0x02fe00000ffff003 0xc0bf800003fffc00

def z1064 : W := mkw 0x0002504480000000 0x8000941120000000 0xfb06d7fff0000000 0x3ec1b5fffc000000

def z1065 : W := mkw 0x0442526688668a20 0x81109499a219a288 0xfb46d6eec8ee0832 0x7ed1b5bbb23b820c

def z1066 : W := mkw 0x000805dda0000003 0x8002017768000000 0xf50027fff0010c3e 0xfd4009fffc00430f

def z1067 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff000c003 0x7fcffffffc003000

def z1068 : W := mkw 0x102500b004b00282 0x4409402c012c00a0 0x4cff00f007f003c1 0x933fc03c01fc00f0

def z1069 : W := mkw 0x003ffddda4900003 0xc00fff7769240000 0xffffffffffe00000 0x3ffffffffff80000

def z1070 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff011fc3f 0xffcffffffc047f0f

def z1071 : W := mkw 0x003daddda0000003 0x800f6b7768000000 0xe03807fff0000000 0x380e01fffc000000

def z1072 : W := mkw 0x0442526688668a20 0x81109499a219a288 0xfb46c6ee08ee0b33 0x7ed1b1bb823b82cc

def z1073 : W := mkw 0x0037f8dda0000003 0x800dfe3768000000 0xfb07fefff0000000 0x3ec1ffbffc000000

def z1074 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0xffff3ff1fff1ffc3 0xffffcffc7ffc7ff0

def z1075 : W := mkw 0x0000004480000000 0x8000001120000000 0xfd013ffff0000000 0x3f404ffffc000000

def z1076 : W := mkw 0x403ffddda4d4a003 0xd00fff7769352800 0xff7ffffff0f1f003 0xffdffffffc3c7c00

def z1077 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x0246c6ee08ee0b01 0x4091b1bb823b82c0

def z1078 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xb7b8ff0fff0f0c3e 0xedee3fc3ffc3c30f

def z1079 : W := mkw 0xc037f8d4a6dda002 0xf00dfe3529b76800 0xfffff9f1fffff003 0xfffffe7c7ffffc00

def z1080 : W := mkw 0x002f5ddda0000003 0x800bd77768000000 0xfb07dffff0000000 0x3ec1f7fffc000000

def z1081 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x9ffff801fffff003 0xe7fffe007ffffc00

def z1082 : W := mkw 0x302d0fb02db00e82 0x4c0b43ec0b6c03a0 0x6fff0ff03ff00fc1 0xdbffc3fc0ffc03f0

def z1083 : W := mkw 0x003daddda0000003 0x800f6b7768000000 0xf739effff0000000 0x3dce7bfffc000000

def z1084 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0x92fefeefffeff002 0x24bfbfbbfffbfc00

def z1085 : W := mkw 0x0037f84480000000 0x800dfe1120000000 0xff3ffffff0000000 0x3fcffffffc000000

def z1086 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xf846d6eec0eecb33 0x3e11b5bbb03bb2cc

def z1087 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x6fff2ff13ff00fc1 0xdbffcbfc4ffc03f0

def z1088 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xff47fffff8fecff3 0xffd1fffffe3fb3fc

def z1089 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0xffffffffffffffc3 0xfffffffffffffff0

def z1090 : W := mkw 0xc035a80006dda000 0x700d6a0001b76800 0x00f800000ffff003 0xc03e000003fffc00

def z1091 : W := mkw 0x064002225866db74 0x019000889619b6dd 0x0040000008eecfff 0x40100000023bb3ff

def z1092 : W := mkw 0x803ffddda2090003 0xa00fff7768824000 0xffbfffffff0f0c3e 0xffefffffffc3c30f

def z1093 : W := mkw 0x000805dda0000003 0x8002017768000000 0xed0107fff0000000 0x3b4041fffc000000

def z1094 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0xfffffffff7f1f001 0xbffffffffdfc7c00

def z1095 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xfb46d6eec8fefbf3 0x7ed1b5bbb23fbefc

def z1096 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff001f002 0x3fcffffffc007c00

def z1097 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x66ff07f00ff00fc0 0x99bfc1fc03fc03f0

def z1098 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xe246c7fff8ee0ffc 0x3891b1fffe3b83ff

def z1099 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0x9b46d6eec8eec033 0x66d1b5bbb23bb00c

def z1100 : W := mkw 0xe83dad992799240b 0x7a0f6b6649e64902 0x04b929113711340c 0x812e4a444dc44d03

def z1101 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0x9f3ffeeff0000000 0x27cfffbbfc000000

def z1102 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xea3fdffff0000000 0x3a8ff7fffc000000

def z1103 : W := mkw 0x0200000050005154 0x0080000014001455 0xff01ff1ff011ffff 0xffc07fc7fc047fff

def z1104 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff0100001 0xffcffffffc040000

def z1105 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff0000832 0x7fcffffffc00020c

def z1106 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xbfb9e70f0f1f0c3f 0xefee79c3c3c7c30f

def z1107 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xef3fc7fff0000000 0x3bcff1fffc000000

def z1108 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0xff7ffffff0fff003 0x3fdffffffc3ffc00

def z1109 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0x0246c6ee08ee0b30 0x0091b1bb823b82cc

def z1110 : W := mkw 0x0000004480000000 0x8000001120000000 0xe00007fff0000000 0x380001fffc000000

def z1111 : W := mkw 0xb83da5990799048b 0x6e0f696641e64122 0x04b90110071004c0 0x812e404401c40130

def z1112 : W := mkw 0x0000022208220a20 0x0000008882088288 0x0246c6ee08ee0000 0x0091b1bb823b8000

def z1113 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0x5f3ffefef0000000 0x17cfffbfbc000000

def z1114 : W := mkw 0xc037f8d4a6dda002 0xf00dfe3529b76800 0x1ffff8e00ffff003 0xc7fffe3803fffc00

def z1115 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xbfb8f70f0f0fcc3f 0xefee3dc3c3c3f30f

def z1116 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x6fff2ff00ff13fc1 0xdbffcbfc03fc4ff0

def z1117 : W := mkw 0xc037f89006dda002 0x700dfe2401b76800 0x5ffff8f00ffff003 0xd7fffe3c03fffc00

def z1118 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x6bfe07f00fe00fc1 0x5aff81fc03f803f0

def z1119 : W := mkw 0x382d07bb0db20eab 0x4e0b41eec36c83aa 0xffff27ff0ff10fff 0xffffc9ffc3fc43ff

def z1120 : W := mkw 0xf03ffddda7992483 0xfc0fff7769e64920 0xffbffffff71134c0 0xbfeffffffdc44d30

def z1121 : W := mkw 0x000805dda0000003 0x8002017768000000 0xf90017fff0000000 0x3e4005fffc000000

def z1122 : W := mkw 0x003ffddda0448003 0x800fff7768112000 0xff7ffffff8ee0000 0x3fdffffffe3b8000

def z1123 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x6fff07f00ff10fff 0xdbffc1fc03fc43ff

def z1124 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x6fff1ff0fff00fc1 0xdbffc7fc3ffc03f0

def z1125 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0x5b46d6eec8eec303 0x56d1b5bbb23bb0c0

def z1126 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xff46f7efc8eecb33 0x7fd1bdfbf23bb2cc

def z1127 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xa2b8c70f0f0f0c3e 0xe8ae31c3c3c3c30f

def z1128 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xf807fffff0000000 0x3e01fffffc000000

def z1129 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x1346c6ee08ee0002 0x44d1b1bb823b8000

def z1130 : W := mkw 0x000805dda0000003 0x8002017768000000 0x800006eff0000000 0x200001bbfc000000

def z1131 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xb2b8e70f0f0f0c3e 0x2cae39c3c3c3c30f

def z1132 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xf346c6eec8ee0b32 0x7cd1b1bbb23b82cc

def z1133 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xfb46feeec8effb33 0x7ed1bfbbb23bfecc

def z1134 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xffb9e71f0f0f0c3e 0xffee79c7c3c3c30f

def z1135 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xfb3ed7fff0000000 0x3ecfb5fffc000000

def z1136 : W := mkw 0xa818a79b2b0b0c2b 0x2a0629e6cac2c30a 0xb7b8e71f3f0f0c3e 0xedee39c7cfc3c30f

def z1137 : W := mkw 0xc03ffddda6992003 0xf00fff7769a64800 0xffbffffff7000000 0x3feffffffdc00000

def z1138 : W := mkw 0x302d05b005b00682 0x4c0b416c016c01a0 0x6dff01f007f00fc1 0xdb7fc07c01fc03f0

def z1139 : W := mkw 0xc03dad9926992003 0x700f6b6649a64800 0x00b8000007000000 0x002e000001c00000

def z1140 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xfb46d6eec8eecfff 0x7ed1b5bbb23bb3ff

def z1141 : W := mkw 0xe83ffddda7dda40b 0xfa0fff7769f76902 0xfffffffffffff40f 0xfffffffffffffd03

def z1142 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff0113000 0xbfcffffffc044c00

def z1143 : W := mkw 0x002d05dda0000003 0x800b417768000000 0xe43907fff0000000 0x390e41fffc000000

def z1144 : W := mkw 0xc03dad9926992003 0x700f6b6649a64800 0x04b9291137000000 0x012e4a444dc00000

def z1145 : W := mkw 0x46675864d4f4f354 0xd199d619353d3cd5 0x484718f0f0f0f3c1 0x1211c63c3c3c3cf0

def z1146 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x7fff27f00ff10fc3 0xdfffc9fc03fc43f0

def z1147 : W := mkw 0x0018a5dda0000003 0x8006297768000000 0xff39fffff0000000 0x3fce7ffffc000000

def z1148 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xff47feeff8fffb3f 0xffd1ffbbfe3ffecf

def z1149 : W := mkw 0x803ffddda2090003 0xa00fff7768824000 0xffbfffffff0e0000 0x3fefffffffc38000

def z1150 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xda46d6eec8eec333 0x3691b5bbb23bb0cc

def z1151 : W := mkw 0x003da59900000003 0x000f696640000000 0xff3ffffff0000000 0x3fcffffffc000000

def z1152 : W := mkw 0x280805dda100040b 0x8a02017768400102 0xe00007fff000040c 0x380001fffc000103

def z1153 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0xffff3ff10ff1ffff 0xffffcffc43fc7fff

def z1154 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x9246c6ee08ee0032 0x2491b1bb823b800c

def z1155 : W := mkw 0xc037f80906dda001 0x700dfe0241b76800 0x9ffff80f0ffff003 0xe7fffe03c3fffc00

def z1156 : W := mkw 0x003ffddda4900003 0xc00fff7769240000 0xfffffffffff00fc1 0xfffffffffffc03f0

def z1157 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0x423ec6fef0000000 0x108fb1bfbc000000

def z1158 : W := mkw 0xc010a00006dda000 0x7004280001b76800 0x1ff9f8000ffff003 0xc7fe7e0003fffc00

def z1159 : W := mkw 0x8e52f04fd24fd17d 0xa394bc13f493f45f 0x9000f80ff00ff03e 0x24003e03fc03fc0f

def z1160 : W := mkw 0xc035a00006dda000 0x700d680001b76800 0x1fffe0000ffff003 0xc7fff80003fffc00

def z1161 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xff47feeec8eecb33 0x7fd1ffbbb23bb2cc

def z1162 : W := mkw 0xc012f00006dda000 0x7004bc0001b76800 0x1ffef0000ffff003 0xc7ffbc0003fffc00

def z1163 : W := mkw 0x0000022208220a20 0x0000008882088288 0xff47e7ff08ff0fff 0xffd1f9ffc23fc3ff

def z1164 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0x82b8c60f0f0e003c 0x20ae3183c3c3800f

def z1165 : W := mkw 0x302502b00db00e82 0x4c0940ac036c03a0 0x4fff00f00ff00fc1 0xd3ffc03c03fc03f0

def z1166 : W := mkw 0x000805dda0000003 0x8002017768000000 0xf300c7fff0000000 0x3cc031fffc000000

def z1167 : W := mkw 0x001afddda0000003 0x8006bf7768000000 0xfd01fffff0000000 0x3f407ffffc000000

def z1168 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xfb46feeff8eecb33 0x7ed1bfbbfe3bb2cc

def z1169 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0xefff07f1fff00fc1 0xfbffc1fc7ffc03f0

def z1170 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x0246c6ee08eec003 0x4091b1bb823bb000

def z1171 : W := mkw 0x8035a00006990000 0x600d680001a64000 0x1ffff8000ffff003 0xc7fffe0003fffc00

def z1172 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xe246c6eec8eecb33 0x7891b1bbb23bb2cc

def z1173 : W := mkw 0xb818a79b0b0b0cab 0x2e0629e6c2c2c32a 0xb7b8e71f0f0f0cfe 0xedee39c7c3c3c33f

def z1174 : W := mkw 0x0442526688668a20 0x81109499a219a288 0xff47fffff8ee0000 0x3fd1fffffe3b8000

def z1175 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x1ffff8000ffef001 0x07fffe0003ffbc00

def z1176 : W := mkw 0x002758d4a0000002 0x8009d63528000000 0x4a07defef0000000 0x1281f7bfbc000000

def z1177 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x6fff07f00ff003c1 0x1bffc1fc03fc00f0

def z1178 : W := mkw 0xa818a50b030b0429 0x2a062942c0c2c10a 0x90b8e00f070f003e 0x242e3803c1c3c00f

def z1179 : W := mkw 0x102500b004b00282 0x4409402c012c00a0 0x4aff00f00ff003c1 0x12bfc03c03fc00f0

def z1180 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x16fff8000ffff002 0x85bffe0003fffc00

def z1181 : W := mkw 0x000805dda0000003 0x8002017768000000 0xed0107fff0100fc1 0xfb4041fffc0403f0

def z1182 : W := mkw 0x0018a5dda0000003 0x8006297768000000 0xe238c7fff0000000 0x388e31fffc000000

def z1183 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xfb47fefff8fffbff 0x7ed1ffbffe3ffeff

def z1184 : W := mkw 0xc03dad9926992003 0x700f6b6649a64800 0xfdb93911f711f003 0xff6e4e447dc47c00

def z1185 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0x6f3fdffef0000000 0x1bcff7ffbc000000

def z1186 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0x6b46c6ee08eecb33 0x5ad1b1bb823bb2cc

def z1187 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x4eff07f00ff007c1 0x93bfc1fc03fc01f0

def z1188 : W := mkw 0x0200022258225b74 0x00800088960896dd 0xff47fffff8ffffff 0xffd1fffffe3fffff

def z1189 : W := mkw 0x003da5dda0000003 0x800f697768000000 0xff3fe7fff0000000 0x3fcff9fffc000000

def z1190 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff011ffc3 0xffcffffffc047ff0

def z1191 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xb7b8e70f0f1f0fff 0xedee39c3c3c7c3ff

def z1192 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xf7b8e71fff0f0c3e 0xfdee39c7ffc3c30f

def z1193 : W := mkw 0x001afddda0000003 0x8006bf7768000000 0x9000feeff0000000 0x24003fbbfc000000

def z1194 : W := mkw 0x002f55dda0000003 0x800bd57768000000 0xff3fd7fff0000000 0x3fcff5fffc000000

def z1195 : W := mkw 0x0200000050005154 0x0080000014001455 0xf8013911f011ffff 0x3e004e447c047fff

def z1196 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x7fff3ff00ff00fc1 0xdfffcffc03fc03f0

def z1197 : W := mkw 0x001afddda0000003 0x8006bf7768000000 0xe000c7fff0000000 0x380031fffc000000

def z1198 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xff47fefef8fffbf3 0xffd1ffbfbe3ffefc

def z1199 : W := mkw 0x0002504480448000 0x8000941120112000 0xfb46d6eec8ee0000 0x3ed1b5bbb23b8000

def z1200 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0xffffffffffeec003 0x7ffffffffffbb000

def z1201 : W := mkw 0x0200000050005154 0x0080000014001455 0xffb93911ff11ffff 0xffee4e447fc47fff

def z1202 : W := mkw 0x0442526688668a20 0x81109499a219a288 0xfb46d6eec8ee0b01 0x7ed1b5bbb23b82c0

def z1203 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xff46f7fff8efcfff 0xffd1bdfffe3bf3ff

def z1204 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xb7b9ef0f0f1f3c3e 0xedee7bc3c3c7cf0f

def z1205 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xf439fffff0000000 0x3d0e7ffffc000000

def z1206 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x7fffc7f00ffe0fc3 0xdffff1fc03ff83f0

def z1207 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0x4e3ffffff0000000 0x138ffffffc000000

def z1208 : W := mkw 0x003daddda0000003 0x800f6b7768000000 0xef3f2ffff0000000 0x3bcfcbfffc000000

def z1209 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xf7b8e71f0f0f0ffe 0xfdee39c7c3c3c3ff

def z1210 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0xefff07f10ff00ffd 0xfbffc1fc43fc03ff

def z1211 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0x823ec6eff0000000 0x208fb1bbfc000000

def z1212 : W := mkw 0xc037f84486dda000 0xf00dfe1121b76800 0x5ffff8e0cffff003 0xd7fffe3833fffc00

def z1213 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x7ffff8000ffffb03 0xdffffe0003fffec0

def z1214 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xff47f7ffc8ffcfff 0xffd1fdfff23ff3ff

def z1215 : W := mkw 0x0442526688668a20 0x81109499a219a288 0xe246c6eec8ee0000 0x3891b1bbb23b8000

def z1216 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff80e0002 0x7fcffffffe038000

def z1217 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xff47d7fec8eecb33 0x7fd1f5ffb23bb2cc

def z1218 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0xfffff911fffffc3f 0xfffffe447fffff0f

def z1219 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xfb47dffff8feffff 0x7ed1f7fffe3fbfff

def z1220 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x1bffd8000ffef003 0x46fff60003ffbc00

def z1221 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0xfffffffffffe0001 0xffffffffffff8000

def z1222 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff0010002 0xffcffffffc004000

def z1223 : W := mkw 0x403ffddda4d4a003 0xd00fff7769352800 0xff7ffffff0e00000 0x3fdffffffc380000

def z1224 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xffb8e70f0f0f0f3f 0xffee39c3c3c3c3cf

def z1225 : W := mkw 0x04425066c066c330 0x81109419b019b0cc 0xfb46d6eec0eec333 0x3ed1b5bbb03bb0cc

def z1226 : W := mkw 0x0442526688668a20 0x81109499a219a288 0xfb46d6eec8eec003 0x7ed1b5bbb23bb000

def z1227 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xfb46d7fff8eecb33 0x7ed1b5fffe3bb2cc

def z1228 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0x9246d6eec8eecb33 0x6491b5bbb23bb2cc

def z1229 : W := mkw 0x001afd4da0000001 0x8006bf5368000000 0xff3effeff0000000 0x3fcfbffbfc000000

def z1230 : W := mkw 0x103ffddda4900083 0xc40fff7769240020 0xff3ffffff01000c0 0x3fcffffffc040030

def z1231 : W := mkw 0xc03ffddda6992003 0xf00fff7769a64800 0xffbfffffff1f3002 0xffefffffffc7cc00

def z1232 : W := mkw 0xc03ffddda24da003 0xb00fff7768936800 0xffbfffffff0ff002 0xffefffffffc3fc00

def z1233 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0xffff27f10ff00fc1 0xffffc9fc43fc03f0

def z1234 : W := mkw 0x002f55d480000002 0x800bd57520000000 0xff3ffffff0000000 0x3fcffffffc000000

def z1235 : W := mkw 0xc03ffddda24da003 0xb00fff7768936800 0xff3ffffff01ff003 0xffcffffffc07fc00

def z1236 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xff47dffef8fefff3 0xffd1f7ffbe3fbffc

def z1237 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x6b46c6ee08ee0000 0x1ad1b1bb823b8000

def z1238 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x1ffff8000feff002 0x07fffe0003fbfc00

def z1239 : W := mkw 0x302d07b20db20ea2 0x4c0b41ec836c83a8 0xffffe7ff0fff0fff 0xfffff9ffc3ffc3ff

def z1240 : W := mkw 0x702d0fb00db02e82 0x5c0b43ec036c0ba0 0x6fff0ff00ff03fc1 0xdbffc3fc03fc0ff0

def z1241 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0xffffc7fe0ff00fc1 0xfffff1ff83fc03f0

def z1242 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff01003c1 0x3fcffffffc0400f0

def z1243 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xfb46d6eec8fecff3 0xfed1b5bbb23fb3fc

def z1244 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff001003e 0x3fcffffffc00400f

def z1245 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0x1b46d6ee08eecb33 0x46d1b5bb823bb2cc

def z1246 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xff3ffffff0000b01 0x7fcffffffc0002c0

def z1247 : W := mkw 0x382d07bb0db20eab 0x4e0b41eec36c83aa 0xffffc7ff0ffe0fff 0xfffff1ffc3ff83ff

def z1248 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x7ffffee00ffff003 0xdfffffb803fffc00

def z1249 : W := mkw 0xb83da5990799048b 0x6e0f696641e64122 0xfdb9211107110fff 0xff6e484441c443ff

def z1250 : W := mkw 0x02025044d044d154 0x8080941134113455 0xff47fffff8ffffff 0xffd1fffffe3fffff

def z1251 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x1ffff8000ffffc3f 0xc7fffe0003ffff0f

def z1252 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x4fff06f00ff003c1 0xd3ffc1bc03fc00f0

def z1253 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xfb47defef8eecb33 0x7ed1f7bfbe3bb2cc

def z1254 : W := mkw 0x0640022258225b74 0x01900088960896dd 0x000000000011ffff 0xc000000000047fff

def z1255 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0x0246c6ee08eec032 0x0091b1bb823bb00c

def z1256 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x1ffff9010ffff40f 0xc7fffe4043fffd03

def z1257 : W := mkw 0xc012f80006dda000 0x7004be0001b76800 0x17f8f8000ffff003 0xc5fe3e0003fffc00

def z1258 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0xfffff911ffffffc3 0xfffffe447ffffff0

def z1259 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xb3b8e60f0f0f083e 0x6cee3983c3c3c20f

def z1260 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x17fee0000ffff003 0xc5ffb80003fffc00

def z1261 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x0a46d6ee08eec001 0x0291b5bb823bb000

def z1262 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0xffff17f0cff00fc1 0xffffc5fc33fc03f0

def z1263 : W := mkw 0x8810a00b020b0029 0x22042802c082c00a 0xb7b8e10f0f0f0c3e 0xedee3843c3c3c30f

def z1264 : W := mkw 0x8810a00b020b0029 0x22042802c082c00a 0x94b8e00f070f003e 0xa52e3803c1c3c00f

def z1265 : W := mkw 0xc037f8dda6dda003 0xf00dfe3769b76800 0xdffff8fffffff003 0xf7fffe3ffffffc00

def z1266 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0x27b8c70e0f0f0c3e 0xc9ee31c383c3c30f

def z1267 : W := mkw 0x0018a5dda0000003 0x8006297768000000 0xf000e7fff0000000 0x3c0039fffc000000

def z1268 : W := mkw 0x3a0807bb59225fff 0x0e8201eed64897ff 0xe00007fff0000ffc 0x380001fffc0003ff

def z1269 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x27fe07e00ff00fc1 0xc9ff81f803fc03f0

def z1270 : W := mkw 0xb818a7bb0b2b0eab 0x2e0629eec2cac3aa 0xffb9e7ff0f1f0fff 0xffee79ffc3c7c3ff

def z1271 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0x92b8e60f0f0f0c3e 0xe4ae3983c3c3c30f

def z1272 : W := mkw 0x000a55dda0000003 0x8002957768000000 0xf000d7fff0000000 0x3c0035fffc000000

def z1273 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x9246d6eec8ee0000 0x2491b5bbb23b8000

def z1274 : W := mkw 0x0002522208668a20 0x000094888219a288 0xfb46d6ee08eecb33 0x7ed1b5bb823bb2cc

def z1275 : W := mkw 0xe83ffddda799240b 0xfa0fff7769e64902 0xffbffffff711340c 0xbfeffffffdc44d03

def z1276 : W := mkw 0xb83da5990799048b 0x6e0f696641e64122 0x00b8000007000000 0x002e000001c00000

def z1277 : W := mkw 0x102502b00cb00a82 0x440940ac032c02a0 0x6fff06f00ff00bc1 0xdbffc1bc03fc02f0

def z1278 : W := mkw 0x44425a66c866eb30 0x91109699b219bacc 0xfb46deeec8eefb33 0x7ed1b7bbb23bbecc

def z1279 : W := mkw 0x302d07b00db00e82 0x4c0b41ec036c03a0 0x6bfe06e00ff00fc1 0xdaff81b803fc03f0

def z1280 : W := mkw 0x003ffddda4900003 0xc00fff7769240000 0xfffffffffff1f003 0xfffffffffffc7c00

def z1281 : W := mkw 0x24425266c966cf30 0x89109499b259b3cc 0xfbc6d6eecfeecf33 0xfef1b5bbb3fbb3cc

def z1282 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xb7b8ff0f0f0ffc3e 0xedee3fc3c3c3ff0f

def z1283 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0x023edeeef0000000 0x008fb7bbbc000000

def z1284 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xfb46f6efc8efcb3f 0x7ed1bdbbf23bf2cf

def z1285 : W := mkw 0x002f5ddda0000003 0x800bd77768000000 0xef3f1ffff0000000 0x3bcfc7fffc000000

def z1286 : W := mkw 0x300807200db00e80 0x4c0201c8036c03a0 0x6ffe07e00ff00fc1 0xdbff81f803fc03f0

def z1287 : W := mkw 0xc23dad9976997157 0x708f6b665da65c55 0xfdb93911f711ffff 0xff6e4e447dc47fff

def z1288 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x0fffd8000ffef001 0xc3fff60003ffbc00

def z1289 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xbffee70f0fef0c3f 0xefffb9c3c3fbc30f

def z1290 : W := mkw 0xc027500006dda000 0x7009d40001b76800 0x1fffd0000ffff003 0xc7fff40003fffc00

def z1291 : W := mkw 0x0200000050005154 0x0080000014001455 0xf4013911f011fffe 0xbd004e447c047fff

def z1292 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xb3b8c70f0f0e0c3e 0x6cee31c3c3c3830f

def z1293 : W := mkw 0xc03ffddda6dda003 0xf00fff7769b76800 0xffffffffffef0002 0xfffffffffffbc000

def z1294 : W := mkw 0x0018addda0000003 0x80062b7768000000 0xe0002ffff0000000 0x38000bfffc000000

def z1295 : W := mkw 0xd037f89006dda082 0x740dfe2401b76820 0x1ffff8100ffff0c3 0xc7fffe0403fffc30

def z1296 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x1ffff8000fffffc3 0xc7fffe0003fffff0

def z1297 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xb7b8e70f0f1ffc3f 0xedee39c3c3c7ff0f

def z1298 : W := mkw 0x0442526688668a20 0x81109499a219a288 0x1b46d6ee08ee0000 0x06d1b5bb823b8000

def z1299 : W := mkw 0xa818a70b0b0b0c29 0x2a0629c2c2c2c30a 0xffb8f70fcf0f0c3e 0xffee3dc3f3c3c30f

def z1300 : W := mkw 0x04425266c866cb30 0x81109499b219b2cc 0xfb46d6eec8ee0b30 0x3ed1b5bbb23b82cc

def z1301 : W := mkw 0xc037f80926dda001 0x700dfe0249b76800 0x1ffff8013ffff003 0xc7fffe004ffffc00

def z1302 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xfb46feeff8ffffff 0xfed1bfbbfe3fffff

def z1303 : W := mkw 0x003ffddda0000003 0x800fff7768000000 0xffbfffffff000000 0xffefffffffc00000

def z1304 : W := mkw 0xc037f80006dda000 0x700dfe0001b76800 0x14f9f8000ffff003 0xc53e7e0003fffc00

def z1305 : W := mkw 0xa80807020b0b0c28 0x2a0201c082c2c30a 0xb7b8c70e0f0f0c3e 0xedee31c383c3c30f

def z1306 : W := mkw 0x06425266d866db74 0x81909499b619b6dd 0xfb46deeef8eefb33 0x7ed1b7bbbe3bbecc

def z1307 : W := mkw 0x002f5ddda0000003 0x800bd77768000000 0xfd073ffff0000000 0x3f41cffffc000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z6,z7,z0,z8,z2,z3,z9]),(0,[z10,z7,z0,z1,z2,z3,z9]),(0,[z11,z0,z1,z2,z12,z3,z9]),(0,[z7,z0,z1,z2,z13,z3,z9])],[(0,[z14,z15,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z16,z9]),(0,[z7,z0,z1,z17,z18,z3,z9]),(0,[z7,z0,z1,z19,z2,z3,z9]),(0,[z20,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z21,z2,z22,z3,z9]),(0,[z23,z7,z0,z24,z2,z3,z9]),(0,[z7,z25,z0,z1,z2,z3,z9])],[(0,[z7,z0,z26,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z2,z3,z9]),(1,[z27,z0,z21,z2,z3,z9]),(0,[z7,z0,z1,z28,z2,z3,z9]),(0,[z7,z29,z0,z1,z2,z3,z9]),(1,[z10,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z30,z3,z9])],[(0,[z7,z0,z1,z2,z3,z31,z9]),(0,[z0,z1,z2,z3,z32,z9,z4]),(0,[z23,z7,z0,z8,z2,z3,z9])],[(0,[z33,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z34,z2,z3,z9])],[(0,[z35,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z21,z36,z2,z3,z9]),(0,[z7,z0,z21,z37,z2,z3,z9]),(1,[z7,z0,z1,z38,z3,z9]),(0,[z23,z7,z1,z2,z3,z39,z9]),(0,[z7,z40,z0,z1,z2,z41,z9]),(0,[z7,z0,z1,z2,z3,z9,z42])],[(0,[z7,z43,z0,z1,z2,z3,z9]),(0,[z44,z7,z0,z8,z2,z3,z9]),(0,[z7,z45,z0,z1,z46,z3,z9]),(0,[z7,z0,z47,z1,z2,z3,z9]),(0,[z7,z0,z1,z22,z3,z48,z9]),(0,[z49,z0,z1,z2,z3,z50,z9])],[(0,[z7,z0,z1,z51,z2,z3,z9]),(0,[z7,z0,z1,z2,z52,z3,z9]),(0,[z7,z0,z21,z2,z41,z3,z9]),(1,[z0,z1,z53,z2,z3,z9]),(0,[z7,z0,z8,z2,z3,z9,z54]),(0,[z7,z0,z1,z55,z2,z3,z9]),(0,[z7,z0,z1,z2,z12,z48,z9]),(1,[z7,z0,z1,z56,z3,z9])]],
   [[(1,[z7,z0,z1,z57,z3,z9]),(0,[z7,z0,z1,z2,z3,z58,z9]),(0,[z7,z0,z59,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z60]),(0,[z61,z0,z1,z2,z3,z32,z9])],[(0,[z7,z62,z0,z1,z2,z3,z9]),(0,[z14,z7,z0,z8,z2,z3,z9]),(0,[z0,z1,z2,z3,z9,z4,z5]),(0,[z7,z0,z1,z2,z3,z9,z63]),(0,[z7,z0,z64,z1,z2,z3,z9]),(1,[z7,z0,z65,z2,z3,z9]),(0,[z7,z66,z0,z1,z2,z3,z9])],[(0,[z67,z7,z0,z1,z2,z3,z9]),(0,[z6,z0,z1,z2,z3,z68,z9]),(0,[z7,z0,z1,z2,z3,z69,z9]),(0,[z7,z0,z1,z2,z70,z3,z9]),(0,[z7,z0,z1,z2,z3,z50,z68]),(0,[z0,z1,z2,z71,z72,z3,z9])],[(0,[z7,z40,z1,z2,z41,z3,z9]),(0,[z7,z0,z1,z2,z73,z3,z9]),(0,[z74,z7,z0,z1,z75,z3,z9]),(0,[z7,z0,z1,z76,z2,z3,z9]),(0,[z7,z0,z1,z2,z77,z3,z9])],[(0,[z6,z78,z0,z1,z2,z3,z9]),(0,[z79,z6,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z80,z9]),(0,[z81,z7,z0,z21,z2,z3,z9]),(0,[z7,z82,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z83,z2,z3,z9]),(0,[z7,z0,z1,z3,z50,z9,z84]),(0,[z7,z0,z1,z2,z71,z3,z85]),(0,[z7,z0,z1,z56,z2,z3,z9])],[(0,[z7,z0,z1,z86,z2,z3,z9]),(0,[z87,z6,z0,z1,z2,z3,z9])],[(0,[z88,z7,z0,z1,z89,z3,z9]),(0,[z90,z0,z1,z2,z3,z9,z4]),(0,[z91,z7,z0,z21,z2,z3,z9]),(1,[z27,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z92,z3,z9]),(0,[z7,z0,z1,z18,z3,z48,z9]),(0,[z7,z0,z1,z93,z2,z3,z9])],[(0,[z7,z0,z94,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z95,z3,z9]),(0,[z74,z7,z0,z1,z2,z96,z9])]],
   [[(0,[z7,z0,z1,z97,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z98,z9]),(0,[z7,z0,z1,z99,z2,z3,z9])],[(1,[z7,z0,z1,z2,z3,z100]),(1,[z101,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z75,z3,z48,z9]),(0,[z7,z0,z1,z2,z102,z48,z9])],[(0,[z7,z0,z1,z2,z103,z3,z9]),(0,[z0,z1,z2,z3,z9,z4,z54]),(1,[z0,z1,z2,z71,z3,z4]),(0,[z7,z0,z104,z21,z2,z3,z9]),(0,[z7,z0,z1,z105,z2,z3,z9])],[(0,[z7,z0,z1,z106,z2,z3,z9]),(0,[z7,z0,z21,z17,z2,z3,z9]),(0,[z0,z8,z1,z2,z3,z9,z4]),(0,[z7,z107,z0,z1,z2,z3,z9])],[(0,[z108,z0,z1,z2,z3,z9,z4]),(0,[z91,z0,z1,z2,z3,z9,z4]),(0,[z6,z0,z8,z1,z2,z3,z9]),(0,[z7,z0,z1,z109,z2,z3,z9]),(0,[z7,z0,z1,z2,z110,z3,z9]),(0,[z7,z0,z111,z1,z2,z3,z9]),(1,[z112,z0,z1,z2,z3,z9]),(1,[z113,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z114,z2,z3,z9]),(0,[z7,z0,z104,z2,z3,z32,z9]),(0,[z7,z0,z1,z2,z71,z9,z85])],[(0,[z7,z0,z1,z115,z2,z3,z9]),(0,[z116,z7,z0,z1,z2,z3,z9])],[(0,[z117,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z118,z2,z3,z9]),(0,[z7,z0,z8,z17,z2,z3,z9]),(0,[z7,z0,z1,z2,z119,z3,z9]),(1,[z7,z0,z1,z2,z71,z85])],[(1,[z88,z120,z1,z2,z3,z9]),(0,[z20,z6,z0,z1,z2,z3,z9]),(0,[z7,z0,z21,z2,z3,z9,z121]),(0,[z74,z7,z0,z8,z2,z3,z9]),(0,[z7,z0,z1,z122,z2,z3,z9]),(0,[z7,z0,z1,z123,z2,z3,z9])]],
   [[(0,[z124,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z4]),(0,[z7,z125,z0,z1,z2,z3,z9]),(0,[z126,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z127,z3,z9])],[(0,[z7,z0,z1,z2,z128,z3,z9]),(0,[z7,z0,z1,z2,z3,z129,z9]),(0,[z6,z0,z1,z2,z3,z9,z84]),(0,[z7,z0,z1,z21,z2,z3,z9]),(0,[z130,z7,z0,z1,z2,z3,z9]),(0,[z131,z7,z0,z1,z2,z3,z9]),(0,[z44,z132,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z133,z2,z3,z9])],[(0,[z134,z7,z0,z1,z2,z3,z9])],[(1,[z35,z0,z135,z2,z3,z9]),(0,[z35,z6,z0,z1,z2,z3,z9]),(0,[z7,z0,z136,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z137,z3,z9]),(0,[z23,z7,z0,z1,z2,z3,z138]),(0,[z7,z0,z1,z2,z3,z32,z9]),(0,[z7,z0,z1,z2,z139,z3,z9])],[(0,[z88,z15,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z140,z9]),(0,[z141,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z142,z1,z2,z3,z9]),(0,[z7,z143,z0,z1,z2,z3,z9]),(0,[z7,z144,z0,z1,z2,z3,z9])],[(0,[z35,z7,z0,z1,z2,z3,z145]),(0,[z7,z0,z1,z146,z2,z3,z9]),(0,[z147,z7,z0,z1,z2,z3,z9]),(0,[z23,z148,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z105,z2,z41,z9]),(0,[z49,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z149,z3,z9])],[(0,[z0,z1,z2,z150,z3,z9,z4]),(0,[z0,z1,z151,z2,z152,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z153])],[(0,[z35,z7,z0,z135,z2,z3,z9]),(0,[z14,z7,z0,z1,z2,z3,z154]),(0,[z6,z0,z1,z2,z18,z3,z9]),(0,[z7,z0,z8,z2,z102,z3,z9]),(0,[z7,z0,z1,z2,z155,z3,z9])]],
   [[(1,[z7,z0,z1,z2,z3,z156]),(1,[z7,z0,z2,z3,z9,z157]),(0,[z6,z0,z1,z2,z3,z9,z5]),(0,[z7,z0,z1,z2,z3,z158,z9]),(0,[z7,z0,z1,z37,z2,z22,z9]),(0,[z7,z0,z159,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z3,z160,z9]),(0,[z161,z7,z0,z1,z2,z3,z9]),(0,[z162,z7,z0,z8,z2,z3,z9])],[(0,[z7,z163,z0,z1,z2,z3,z9]),(0,[z0,z1,z164,z2,z3,z9,z4]),(0,[z7,z40,z0,z1,z2,z39,z9]),(0,[z165,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z166,z3,z9])],[(0,[z88,z7,z0,z1,z2,z3,z9]),(0,[z7,z167,z0,z1,z2,z3,z9]),(0,[z168,z7,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z105,z2,z3,z169]),(1,[z7,z0,z170,z2,z3,z9])],[(0,[z7,z0,z1,z2,z171,z3,z9]),(0,[z172,z7,z0,z1,z150,z3,z9]),(0,[z173,z7,z0,z8,z2,z3,z9]),(0,[z7,z0,z1,z2,z174,z3,z9]),(0,[z6,z175,z0,z1,z2,z3,z9])],[(0,[z35,z0,z1,z135,z2,z3,z9]),(0,[z173,z7,z0,z1,z2,z176,z9]),(0,[z177,z7,z0,z1,z2,z3,z9]),(0,[z6,z0,z1,z2,z22,z3,z9]),(0,[z178,z7,z0,z1,z2,z3,z9]),(0,[z179,z7,z0,z8,z2,z3,z9]),(0,[z7,z0,z180,z8,z2,z3,z9]),(0,[z79,z7,z45,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z181])],[(0,[z182,z7,z0,z1,z2,z3,z9]),(0,[z6,z0,z1,z151,z2,z3,z9])]],
   [[(0,[z7,z90,z0,z8,z2,z3,z9]),(0,[z35,z0,z1,z2,z150,z3,z9]),(0,[z7,z0,z8,z8,z2,z3,z9]),(1,[z7,z0,z1,z76,z3,z9]),(0,[z7,z0,z1,z183,z2,z3,z84]),(0,[z7,z0,z1,z2,z12,z9,z85])],[(0,[z172,z7,z0,z1,z2,z3,z9]),(0,[z7,z184,z0,z1,z2,z3,z9]),(0,[z79,z7,z0,z1,z2,z185,z9]),(1,[z7,z0,z186,z2,z3,z9]),(0,[z0,z1,z2,z3,z50,z9,z187])],[(0,[z6,z0,z1,z37,z2,z3,z9]),(0,[z7,z188,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z138]),(0,[z7,z0,z1,z164,z151,z3,z9]),(0,[z7,z0,z1,z2,z3,z189,z9]),(0,[z7,z0,z1,z2,z3,z9,z85])],[(1,[z7,z0,z1,z2,z190,z9]),(0,[z74,z7,z0,z2,z75,z3,z9])],[(0,[z191,z7,z0,z1,z2,z3,z9]),(0,[z117,z6,z0,z1,z2,z3,z9]),(0,[z6,z0,z1,z2,z41,z3,z9]),(0,[z7,z0,z1,z192,z2,z3,z9]),(0,[z7,z0,z1,z2,z193,z3,z9])],[(0,[z88,z7,z0,z1,z2,z3,z194]),(0,[z78,z7,z0,z1,z2,z3,z9]),(0,[z79,z7,z0,z21,z2,z3,z9])],[(0,[z195,z7,z0,z1,z2,z3,z9]),(0,[z6,z14,z0,z1,z2,z3,z9]),(0,[z124,z6,z0,z1,z2,z3,z9]),(0,[z7,z0,z196,z21,z2,z3,z9])],[(0,[z88,z7,z0,z1,z2,z197,z9]),(0,[z7,z0,z0,z8,z2,z3,z9]),(0,[z7,z0,z1,z2,z198,z3,z9]),(0,[z7,z0,z1,z2,z199,z3,z9])]],
   [[(1,[z200,z0,z2,z3,z9,z4]),(1,[z0,z1,z2,z3,z9,z4]),(0,[z7,z0,z21,z2,z201,z3,z9]),(0,[z7,z0,z8,z2,z202,z3,z9]),(0,[z7,z0,z1,z2,z39,z48,z9]),(0,[z7,z0,z1,z2,z203,z3,z9])],[(0,[z7,z0,z1,z2,z204,z3,z9]),(0,[z6,z0,z1,z183,z2,z3,z9]),(0,[z7,z0,z1,z2,z205,z3,z9])],[(0,[z206,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z207,z9]),(0,[z7,z0,z1,z53,z2,z3,z9]),(0,[z7,z0,z8,z2,z3,z9,z208]),(0,[z7,z0,z1,z2,z209,z3,z9]),(0,[z7,z0,z1,z210,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z211,z9]),(0,[z212,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z213]),(0,[z7,z0,z214,z1,z2,z3,z9])],[(0,[z215,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z216]),(0,[z7,z0,z1,z2,z3,z169,z9]),(0,[z200,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z217,z2,z3,z9]),(0,[z7,z0,z104,z1,z2,z3,z32]),(0,[z81,z7,z0,z1,z2,z3,z84]),(0,[z7,z0,z218,z1,z2,z3,z9])],[(0,[z219,z7,z0,z1,z2,z3,z9]),(0,[z7,z220,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z221,z3,z9]),(0,[z78,z7,z0,z1,z2,z3,z4]),(0,[z87,z0,z1,z2,z3,z9,z4]),(0,[z222,z7,z0,z8,z2,z3,z9]),(0,[z179,z223,z0,z1,z2,z3,z9]),(0,[z224,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z164,z2,z22,z9])],[(0,[z7,z0,z225,z1,z2,z3,z9]),(0,[z226,z7,z0,z1,z2,z3,z9]),(1,[z0,z1,z2,z149,z3,z9])],[(0,[z0,z1,z135,z2,z3,z9,z4]),(0,[z227,z7,z0,z228,z2,z3,z9]),(0,[z7,z0,z228,z21,z2,z3,z9]),(0,[z6,z173,z0,z1,z2,z3,z9]),(0,[z6,z0,z1,z2,z176,z3,z9]),(0,[z6,z0,z229,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z230]),(0,[z7,z0,z1,z2,z3,z68,z85]),(0,[z7,z0,z1,z2,z71,z3,z9])],[(0,[z231,z7,z0,z1,z17,z3,z9]),(1,[z7,z0,z1,z2,z232,z9]),(0,[z7,z0,z2,z102,z3,z233,z9])]],
   [[(0,[z7,z0,z1,z2,z234,z3,z9]),(0,[z27,z7,z0,z21,z2,z3,z9]),(0,[z7,z0,z1,z235,z2,z3,z9]),(0,[z236,z7,z0,z1,z2,z3,z9]),(1,[z61,z0,z1,z2,z3,z9])],[(0,[z88,z0,z120,z1,z2,z3,z9]),(0,[z88,z6,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z237]),(0,[z7,z0,z1,z238,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z239]),(0,[z0,z1,z2,z3,z9,z9,z4]),(0,[z23,z7,z0,z21,z2,z3,z9]),(0,[z7,z0,z21,z2,z75,z3,z9]),(1,[z7,z175,z8,z2,z3,z9]),(0,[z7,z0,z240,z8,z2,z3,z9]),(0,[z241,z7,z0,z1,z2,z3,z9]),(1,[z7,z0,z2,z3,z242,z9]),(1,[z11,z0,z1,z2,z3,z9])],[(0,[z175,z0,z1,z2,z3,z9,z4]),(0,[z7,z0,z8,z2,z3,z9,z84]),(0,[z7,z0,z1,z105,z2,z39,z9]),(0,[z10,z81,z0,z1,z2,z3,z9]),(0,[z81,z7,z0,z1,z183,z3,z9])],[(0,[z6,z15,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z243,z3,z9]),(0,[z45,z0,z1,z2,z3,z9,z4]),(0,[z7,z0,z1,z65,z2,z3,z9]),(0,[z244,z7,z0,z1,z2,z3,z9]),(1,[z245,z7,z0,z2,z3,z9])],[(0,[z35,z7,z0,z21,z2,z3,z9]),(0,[z231,z0,z1,z17,z2,z3,z9]),(1,[z0,z1,z2,z3,z68,z4]),(0,[z44,z7,z0,z21,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z185,z9]),(0,[z7,z0,z246,z1,z2,z3,z9]),(0,[z7,z0,z1,z105,z193,z3,z9])],[(0,[z247,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z71,z3,z4]),(0,[z248,z7,z0,z1,z2,z3,z9]),(1,[z7,z0,z59,z2,z3,z9]),(0,[z79,z7,z1,z2,z18,z3,z9]),(0,[z7,z0,z1,z183,z18,z3,z9]),(0,[z7,z0,z1,z2,z3,z249,z9]),(0,[z7,z0,z1,z37,z2,z48,z9]),(0,[z245,z7,z0,z1,z2,z3,z9])],[(0,[z35,z7,z0,z2,z3,z32,z9]),(1,[z7,z0,z1,z2,z3,z250]),(0,[z6,z0,z1,z2,z3,z233,z9]),(0,[z6,z0,z1,z164,z2,z3,z9]),(0,[z7,z0,z1,z46,z3,z9,z84]),(0,[z7,z0,z251,z1,z2,z3,z9])],[(0,[z231,z15,z0,z1,z2,z3,z9]),(0,[z14,z0,z1,z2,z176,z3,z9]),(0,[z14,z7,z0,z21,z2,z3,z9]),(0,[z78,z7,z0,z1,z2,z3,z169]),(0,[z6,z0,z1,z252,z2,z3,z9]),(0,[z23,z7,z40,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z41,z48,z9])]],
   [[(0,[z7,z0,z8,z2,z18,z3,z9]),(0,[z7,z0,z104,z1,z2,z3,z5])],[(0,[z7,z0,z253,z1,z2,z3,z9]),(0,[z0,z1,z2,z22,z3,z9,z4]),(0,[z7,z0,z8,z2,z3,z9,z5]),(1,[z184,z0,z1,z2,z3,z9]),(0,[z7,z45,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z254,z9]),(0,[z162,z7,z0,z151,z2,z3,z9]),(0,[z7,z0,z229,z2,z102,z3,z9])],[(0,[z231,z7,z0,z1,z150,z3,z9]),(0,[z6,z7,z0,z1,z2,z3,z9]),(0,[z6,z0,z104,z1,z2,z3,z9]),(1,[z188,z0,z1,z2,z3,z9]),(0,[z255,z7,z0,z1,z2,z3,z9])],[(0,[z256,z7,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z257,z3,z9]),(0,[z27,z7,z0,z1,z2,z3,z9]),(0,[z258,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z259,z3,z9]),(0,[z7,z0,z1,z37,z3,z48,z9]),(0,[z7,z0,z1,z56,z105,z3,z9])],[(0,[z88,z7,z0,z1,z2,z3,z216]),(0,[z7,z0,z1,z2,z260,z39,z9]),(0,[z0,z1,z2,z3,z9,z4,z84]),(0,[z7,z0,z21,z151,z2,z3,z9]),(0,[z23,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z261,z9]),(0,[z262,z7,z0,z1,z2,z3,z9])],[(0,[z263,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z135,z21,z2,z3,z9]),(0,[z7,z0,z264,z1,z2,z3,z9]),(0,[z7,z0,z265,z1,z2,z3,z9]),(1,[z7,z0,z1,z2,z266,z9]),(0,[z7,z0,z1,z267,z2,z3,z9])],[(0,[z231,z7,z0,z8,z2,z3,z9]),(0,[z7,z0,z268,z1,z2,z3,z9]),(0,[z6,z0,z1,z2,z269,z3,z9]),(0,[z7,z0,z8,z2,z22,z3,z9]),(0,[z7,z270,z0,z1,z2,z3,z9]),(0,[z7,z0,z151,z2,z75,z3,z9]),(0,[z7,z0,z1,z2,z271,z3,z9]),(0,[z272,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z273,z9])]],
   [[(0,[z7,z0,z1,z2,z71,z3,z169]),(0,[z7,z0,z8,z151,z2,z3,z9]),(0,[z44,z7,z0,z1,z2,z3,z9]),(0,[z81,z7,z0,z1,z164,z3,z9]),(1,[z0,z1,z2,z72,z3,z9])],[(0,[z7,z0,z1,z274,z2,z3,z9]),(0,[z275,z7,z0,z1,z2,z3,z9]),(0,[z276,z7,z0,z1,z2,z3,z9]),(0,[z7,z277,z0,z1,z2,z3,z9]),(0,[z0,z1,z2,z18,z3,z9,z4]),(0,[z6,z7,z0,z1,z2,z3,z4]),(0,[z7,z0,z21,z2,z3,z50,z9]),(0,[z7,z0,z1,z183,z3,z50,z9])],[(0,[z7,z0,z1,z278,z2,z3,z9]),(0,[z7,z0,z229,z8,z2,z3,z9]),(0,[z7,z0,z1,z164,z18,z3,z9]),(0,[z7,z279,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z280,z2,z3,z9]),(0,[z7,z0,z196,z1,z151,z3,z9]),(0,[z7,z0,z1,z2,z22,z233,z9]),(0,[z7,z0,z1,z2,z12,z3,z9])],[(0,[z281,z7,z0,z1,z2,z3,z9]),(0,[z14,z7,z0,z1,z2,z3,z9]),(0,[z0,z1,z21,z2,z3,z9,z4]),(0,[z0,z1,z2,z3,z68,z9,z4]),(0,[z7,z0,z21,z2,z3,z48,z9]),(0,[z7,z0,z8,z37,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z282,z9]),(0,[z7,z0,z1,z2,z3,z9,z283]),(0,[z0,z1,z2,z12,z149,z3,z9])],[(0,[z7,z0,z1,z89,z2,z3,z9]),(0,[z172,z0,z1,z2,z150,z3,z9]),(0,[z7,z0,z1,z2,z3,z3,z9]),(0,[z7,z0,z8,z2,z3,z50,z9])],[(0,[z15,z7,z0,z8,z2,z3,z9]),(0,[z284,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z285,z9]),(0,[z74,z7,z0,z21,z2,z3,z9]),(0,[z7,z0,z8,z2,z41,z3,z9]),(0,[z7,z0,z1,z2,z3,z286,z9])],[(0,[z287,z7,z0,z1,z2,z3,z9]),(1,[z81,z7,z0,z1,z3,z84])],[(0,[z7,z0,z1,z150,z18,z3,z9]),(0,[z6,z0,z1,z288,z2,z3,z9]),(0,[z7,z0,z21,z183,z2,z3,z9]),(0,[z7,z66,z0,z1,z2,z3,z68]),(0,[z7,z0,z1,z2,z3,z9,z289])]],
   [[(0,[z88,z7,z90,z1,z2,z3,z9]),(0,[z290,z7,z0,z1,z2,z3,z9]),(0,[z231,z7,z0,z1,z2,z3,z291]),(0,[z23,z7,z0,z1,z2,z41,z9]),(0,[z7,z0,z1,z2,z292,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z293])],[(0,[z294,z7,z0,z1,z2,z3,z9]),(0,[z7,z295,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z296,z3,z9]),(0,[z7,z0,z1,z2,z39,z9,z85]),(0,[z7,z0,z1,z2,z3,z9,z297]),(0,[z7,z0,z1,z164,z22,z3,z9])],[(0,[z7,z0,z1,z298,z2,z3,z9]),(0,[z299,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z157]),(0,[z7,z0,z8,z183,z2,z3,z9]),(0,[z300,z7,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z17,z46,z3,z9]),(0,[z173,z14,z0,z1,z2,z3,z9]),(0,[z7,z0,z235,z21,z2,z3,z9]),(1,[z7,z0,z1,z2,z3,z301]),(0,[z302,z7,z0,z1,z2,z3,z9]),(0,[z7,z40,z0,z65,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z54,z85]),(0,[z7,z0,z303,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z304,z3,z9])],[(0,[z7,z0,z21,z2,z176,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z9]),(0,[z6,z7,z0,z1,z2,z3,z169]),(0,[z7,z0,z21,z105,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z305]),(0,[z7,z0,z1,z2,z102,z3,z9])],[(0,[z306,z7,z0,z1,z2,z3,z9]),(0,[z0,z228,z1,z2,z3,z260,z9]),(0,[z0,z228,z1,z2,z3,z9,z4]),(0,[z7,z0,z1,z2,z3,z291,z9]),(0,[z81,z0,z1,z2,z3,z9,z4]),(1,[z7,z0,z307,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z308]),(0,[z132,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z309,z3,z9])],[(0,[z7,z0,z1,z310,z2,z3,z9]),(0,[z6,z0,z1,z2,z3,z311,z9]),(0,[z7,z0,z21,z46,z2,z3,z9]),(0,[z7,z0,z1,z2,z232,z3,z9]),(0,[z7,z0,z1,z2,z312,z3,z9])],[(0,[z313,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z314]),(0,[z7,z0,z8,z2,z176,z3,z9]),(0,[z7,z0,z315,z21,z2,z3,z9]),(0,[z79,z101,z0,z1,z2,z3,z9]),(0,[z23,z7,z0,z1,z38,z3,z9]),(0,[z7,z0,z1,z2,z38,z3,z9]),(0,[z316,z7,z0,z1,z2,z3,z9])]],
   [[(0,[z6,z0,z120,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z317]),(0,[z6,z6,z0,z1,z2,z3,z9]),(0,[z162,z7,z0,z2,z3,z233,z9]),(0,[z7,z318,z0,z1,z2,z3,z9])],[(0,[z0,z120,z1,z2,z150,z3,z9]),(0,[z7,z90,z0,z319,z2,z3,z9]),(0,[z7,z0,z1,z320,z2,z3,z9]),(0,[z0,z1,z151,z2,z3,z9,z4]),(0,[z0,z1,z2,z3,z233,z9,z4]),(0,[z7,z0,z8,z46,z2,z3,z9]),(1,[z7,z0,z1,z2,z3,z321]),(0,[z74,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z322,z2,z3,z9])],[(0,[z7,z0,z1,z2,z57,z3,z9]),(0,[z88,z7,z0,z21,z2,z3,z9]),(0,[z14,z7,z0,z1,z2,z260,z9]),(0,[z323,z0,z1,z2,z3,z9,z4]),(0,[z7,z0,z324,z8,z2,z3,z9]),(0,[z325,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z326,z9]),(0,[z7,z0,z229,z1,z2,z233,z9])],[(0,[z327,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z260,z9]),(1,[z14,z0,z1,z2,z176,z9]),(0,[z7,z0,z1,z2,z328,z3,z9]),(0,[z23,z6,z0,z1,z2,z3,z9]),(0,[z7,z0,z21,z21,z2,z3,z9]),(0,[z7,z0,z1,z186,z2,z3,z9]),(0,[z162,z7,z0,z1,z2,z102,z9])],[(0,[z263,z6,z0,z1,z2,z3,z9]),(0,[z87,z7,z1,z21,z2,z3,z9]),(0,[z7,z0,z21,z164,z2,z3,z9]),(0,[z7,z0,z21,z2,z3,z233,z9]),(0,[z329,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z105,z2,z12,z3])],[(0,[z7,z0,z1,z2,z3,z9,z330]),(0,[z7,z0,z1,z331,z2,z3,z9]),(0,[z0,z1,z2,z3,z9,z157,z4]),(0,[z7,z0,z21,z2,z3,z32,z9]),(0,[z332,z7,z0,z1,z2,z3,z9]),(1,[z7,z66,z1,z2,z3,z68]),(0,[z44,z7,z0,z1,z2,z3,z32])],[(0,[z7,z0,z319,z1,z2,z3,z9]),(0,[z7,z90,z0,z21,z2,z3,z9]),(0,[z6,z0,z1,z2,z75,z3,z9]),(0,[z44,z6,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z169,z54]),(0,[z7,z0,z8,z2,z3,z333,z9]),(0,[z334,z7,z0,z1,z2,z3,z9]),(1,[z7,z0,z1,z2,z3,z335])],[(0,[z7,z0,z1,z2,z3,z9,z336]),(0,[z7,z0,z337,z1,z2,z3,z9]),(0,[z7,z0,z8,z164,z2,z3,z9]),(0,[z7,z0,z8,z2,z3,z233,z9])]],
   [[(0,[z7,z0,z1,z2,z338,z3,z9]),(0,[z7,z0,z339,z1,z2,z3,z9]),(0,[z172,z7,z0,z21,z2,z3,z9]),(0,[z7,z0,z1,z2,z340,z3,z9]),(0,[z7,z0,z1,z2,z3,z68,z9]),(0,[z162,z7,z0,z229,z2,z3,z9]),(0,[z341,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z342,z3,z9])],[(0,[z14,z0,z120,z1,z2,z3,z9]),(0,[z0,z1,z2,z176,z3,z260,z9]),(0,[z0,z1,z2,z176,z3,z9,z4]),(0,[z6,z40,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z343])],[(0,[z344,z7,z0,z1,z2,z3,z9]),(0,[z345,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z346,z9])],[(1,[z7,z0,z298,z2,z3,z9]),(0,[z6,z0,z1,z135,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z347]),(0,[z7,z0,z1,z2,z3,z348,z9]),(0,[z7,z0,z1,z2,z349,z3,z9]),(0,[z162,z7,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z3,z9,z350]),(0,[z78,z7,z0,z21,z2,z3,z9]),(0,[z287,z6,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z351,z2,z3,z9]),(0,[z7,z1,z2,z41,z3,z39,z9]),(0,[z245,z7,z0,z2,z3,z48,z9]),(0,[z352,z7,z0,z1,z2,z3,z9])],[(0,[z6,z0,z1,z2,z150,z3,z9]),(0,[z353,z7,z0,z1,z2,z3,z9])],[(0,[z35,z7,z0,z1,z2,z3,z100]),(1,[z7,z0,z1,z2,z96,z9]),(0,[z7,z0,z1,z183,z2,z354,z9])],[(0,[z173,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z68,z4]),(1,[z74,z7,z0,z75,z3,z9]),(0,[z7,z355,z0,z1,z2,z3,z9])]],
   [[(0,[z0,z1,z17,z2,z150,z3,z9]),(0,[z356,z7,z0,z1,z2,z3,z9]),(0,[z0,z1,z331,z2,z3,z9,z4]),(0,[z7,z0,z180,z1,z2,z3,z9]),(0,[z179,z7,z0,z1,z2,z3,z9]),(0,[z162,z74,z7,z0,z2,z3,z9]),(0,[z7,z0,z1,z2,z357,z3,z9])],[(0,[z7,z0,z1,z358,z2,z3,z9]),(0,[z0,z1,z2,z102,z3,z9,z4]),(0,[z200,z7,z0,z2,z3,z9,z4]),(0,[z7,z0,z1,z2,z359,z3,z9])],[(0,[z7,z90,z0,z1,z2,z3,z9]),(0,[z227,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z8,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z360,z3,z9]),(0,[z44,z7,z0,z1,z2,z3,z5]),(0,[z7,z0,z1,z2,z3,z9,z361]),(0,[z7,z0,z1,z2,z3,z9,z362]),(0,[z7,z363,z0,z1,z2,z3,z9])],[(0,[z227,z7,z0,z8,z2,z3,z9]),(0,[z7,z0,z1,z2,z364,z3,z9]),(0,[z7,z0,z1,z2,z3,z365,z9]),(0,[z179,z7,z0,z265,z2,z3,z9]),(0,[z7,z66,z0,z307,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z366,z9]),(0,[z7,z0,z1,z2,z3,z242,z9]),(0,[z7,z0,z1,z367,z2,z3,z9])],[(0,[z7,z0,z1,z2,z368,z3,z9]),(1,[z7,z0,z24,z2,z3,z9]),(0,[z369,z7,z0,z1,z2,z3,z9]),(1,[z0,z1,z2,z3,z9,z370])],[(0,[z313,z6,z0,z1,z2,z3,z9]),(0,[z7,z0,z371,z1,z2,z3,z9]),(0,[z23,z7,z0,z1,z2,z39,z9]),(0,[z7,z0,z1,z2,z372,z3,z9])],[(0,[z373,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z145,z9]),(0,[z7,z0,z1,z2,z374,z3,z9]),(0,[z6,z0,z1,z2,z3,z50,z9]),(1,[z7,z0,z8,z2,z3,z9]),(0,[z7,z0,z1,z2,z375,z3,z9]),(1,[z7,z0,z376,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z377,z9])],[(0,[z14,z0,z228,z1,z2,z3,z9]),(0,[z74,z6,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z378,z9]),(0,[z7,z0,z1,z2,z3,z9,z379])]],
   [[(0,[z7,z0,z1,z2,z3,z380,z9]),(0,[z200,z0,z1,z2,z3,z9,z4]),(0,[z6,z66,z0,z1,z2,z3,z9]),(0,[z6,z0,z1,z2,z3,z48,z9]),(0,[z7,z0,z1,z2,z3,z9,z381]),(0,[z7,z1,z2,z3,z68,z9,z54]),(0,[z7,z0,z1,z2,z233,z48,z9]),(1,[z0,z1,z2,z3,z9,z382])],[(0,[z7,z0,z0,z1,z2,z3,z9]),(0,[z7,z383,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z384,z3,z9]),(0,[z179,z7,z0,z1,z73,z3,z9]),(0,[z7,z0,z1,z2,z385,z3,z9]),(0,[z7,z0,z1,z2,z386,z3,z9])],[(0,[z7,z0,z1,z2,z3,z9,z100]),(0,[z0,z1,z105,z2,z3,z9,z4])],[(0,[z0,z120,z1,z2,z3,z260,z9]),(0,[z0,z120,z1,z2,z3,z9,z4]),(0,[z7,z0,z1,z2,z3,z387,z9]),(0,[z7,z0,z388,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z389,z9]),(0,[z7,z0,z390,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z391]),(0,[z7,z0,z1,z2,z72,z3,z9])],[(0,[z88,z35,z0,z1,z2,z3,z9]),(0,[z0,z1,z46,z2,z3,z9,z4]),(0,[z0,z229,z1,z2,z3,z9,z4]),(0,[z7,z0,z1,z2,z3,z39,z9]),(0,[z7,z0,z1,z392,z2,z3,z9]),(0,[z7,z0,z1,z2,z22,z102,z9]),(1,[z49,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z393,z2,z3,z9]),(0,[z7,z0,z1,z394,z2,z3,z9]),(0,[z7,z40,z0,z8,z2,z3,z9]),(0,[z7,z0,z1,z2,z12,z3,z54])],[(0,[z173,z7,z0,z1,z2,z260,z9]),(0,[z79,z0,z1,z2,z3,z9,z4]),(0,[z222,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z395,z3,z9]),(0,[z179,z7,z1,z2,z3,z9,z54]),(0,[z7,z0,z1,z396,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z5]),(0,[z7,z0,z1,z2,z3,z397,z9])],[(0,[z398,z7,z0,z1,z2,z3,z9]),(1,[z7,z0,z399,z2,z3,z9]),(1,[z7,z0,z1,z2,z3,z291]),(0,[z7,z0,z400,z1,z2,z3,z9]),(0,[z7,z0,z401,z1,z2,z3,z9])]],
   [[(0,[z7,z0,z1,z2,z3,z402,z9]),(0,[z7,z0,z1,z2,z403,z3,z9]),(0,[z7,z0,z404,z1,z2,z3,z9]),(0,[z14,z7,z0,z1,z2,z3,z156]),(0,[z7,z45,z0,z21,z2,z3,z9]),(0,[z405,z7,z0,z8,z2,z3,z9]),(0,[z7,z0,z1,z2,z406,z3,z9])],[(0,[z7,z0,z1,z407,z2,z3,z9]),(0,[z162,z6,z0,z1,z2,z3,z9]),(0,[z6,z0,z1,z105,z2,z3,z9]),(0,[z6,z7,z0,z21,z2,z3,z9]),(1,[z179,z7,z1,z2,z3,z54]),(0,[z7,z0,z1,z2,z408,z3,z9]),(0,[z409,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z410]),(0,[z7,z411,z0,z1,z2,z3,z9])],[(0,[z412,z7,z0,z1,z2,z3,z9]),(0,[z0,z1,z2,z3,z48,z9,z4]),(0,[z7,z413,z0,z1,z2,z3,z9])],[(0,[z88,z7,z0,z1,z57,z3,z9]),(0,[z7,z0,z240,z1,z2,z3,z9]),(0,[z7,z0,z1,z414,z2,z3,z9]),(0,[z6,z0,z1,z46,z2,z3,z9])],[(0,[z7,z0,z1,z2,z415,z3,z9]),(0,[z7,z0,z416,z1,z2,z3,z9]),(0,[z6,z81,z0,z1,z2,z3,z9]),(0,[z7,z175,z0,z8,z2,z3,z9]),(1,[z223,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z22,z3,z9])],[(0,[z231,z7,z0,z21,z2,z3,z9]),(0,[z417,z7,z0,z1,z2,z3,z9]),(0,[z418,z7,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z3,z419,z9]),(0,[z179,z6,z0,z1,z2,z3,z9]),(0,[z420,z7,z0,z1,z2,z3,z9]),(1,[z7,z0,z1,z55,z3,z9]),(0,[z7,z0,z421,z1,z2,z3,z9])],[(1,[z7,z0,z422,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z423]),(0,[z87,z7,z175,z1,z2,z3,z9]),(0,[z7,z0,z8,z2,z75,z3,z9]),(1,[z7,z0,z1,z2,z424,z9]),(0,[z7,z0,z1,z2,z3,z9,z425]),(0,[z426,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z54]),(0,[z427,z7,z0,z1,z2,z3,z9]),(0,[z7,z428,z0,z1,z2,z3,z9])]],
   [[(1,[z7,z0,z1,z2,z140,z9]),(0,[z7,z0,z1,z36,z2,z3,z9]),(0,[z35,z231,z0,z1,z2,z3,z9]),(0,[z7,z0,z429,z1,z2,z3,z9]),(0,[z0,z1,z2,z3,z260,z9,z4]),(0,[z6,z0,z1,z21,z2,z3,z9]),(0,[z430,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z37,z2,z3,z9]),(1,[z431,z0,z1,z2,z3,z9])],[(0,[z7,z0,z432,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z156]),(1,[z78,z0,z1,z2,z3,z4]),(0,[z7,z0,z1,z2,z96,z3,z9]),(1,[z132,z0,z1,z2,z3,z9])],[(0,[z23,z0,z1,z2,z3,z9,z4]),(0,[z6,z0,z1,z2,z3,z32,z9]),(0,[z27,z0,z1,z21,z2,z3,z9]),(0,[z7,z0,z433,z1,z2,z3,z9])],[(0,[z15,z7,z0,z21,z2,z3,z9]),(0,[z7,z0,z21,z2,z150,z3,z9]),(0,[z7,z0,z21,z2,z3,z434,z9]),(0,[z79,z7,z0,z59,z2,z3,z9]),(0,[z7,z0,z1,z2,z435,z3,z9]),(0,[z179,z7,z0,z1,z122,z3,z9]),(1,[z0,z1,z2,z3,z366,z9])],[(0,[z227,z7,z0,z135,z2,z3,z9]),(0,[z7,z0,z8,z135,z2,z3,z9]),(0,[z7,z0,z1,z2,z436,z3,z9]),(1,[z7,z0,z1,z2,z3,z154]),(1,[z0,z2,z3,z9,z157,z4]),(1,[z6,z0,z8,z2,z3,z9]),(0,[z7,z0,z1,z437,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z190,z9]),(0,[z7,z0,z438,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z439,z9]),(0,[z7,z0,z1,z151,z3,z48,z9]),(0,[z440,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z229,z1,z2,z102,z9])],[(0,[z35,z0,z1,z2,z3,z260,z9]),(0,[z35,z0,z1,z2,z3,z9,z4]),(0,[z44,z0,z1,z2,z3,z9,z4]),(0,[z7,z0,z1,z441,z2,z3,z9]),(1,[z7,z0,z392,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z442]),(0,[z81,z7,z0,z1,z3,z9,z84])],[(0,[z7,z0,z1,z2,z443,z3,z9]),(0,[z7,z0,z8,z2,z150,z3,z9]),(0,[z444,z7,z0,z1,z2,z3,z9]),(0,[z0,z1,z2,z3,z32,z9,z382])],[(0,[z7,z0,z1,z445,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z446]),(0,[z7,z0,z21,z28,z2,z3,z9]),(0,[z7,z0,z1,z447,z2,z3,z9]),(0,[z79,z184,z0,z1,z2,z3,z9]),(0,[z7,z0,z170,z1,z2,z3,z9]),(0,[z7,z0,z1,z307,z2,z3,z9]),(0,[z7,z448,z0,z1,z2,z3,z9])]],
   [[(0,[z14,z0,z1,z2,z3,z9,z4]),(1,[z148,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z449,z3,z9])],[(0,[z7,z0,z1,z450,z2,z3,z9]),(0,[z231,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z451,z3,z9]),(0,[z0,z1,z2,z12,z3,z9,z4]),(0,[z452,z7,z0,z1,z2,z3,z9]),(1,[z79,z7,z1,z18,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z453]),(0,[z7,z0,z1,z2,z454,z3,z9]),(0,[z7,z0,z1,z164,z75,z3,z9]),(0,[z7,z0,z1,z455,z2,z3,z9])],[(0,[z88,z0,z228,z1,z2,z3,z9]),(0,[z7,z0,z456,z1,z2,z3,z9]),(0,[z0,z1,z53,z21,z2,z3,z9]),(0,[z457,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z458,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z3,z459,z9]),(0,[z460,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z169,z32]),(0,[z461,z7,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z462,z2,z3,z9]),(0,[z7,z0,z229,z1,z2,z3,z9]),(0,[z431,z7,z0,z1,z2,z3,z9])],[(0,[z0,z1,z2,z41,z3,z9,z4]),(0,[z113,z0,z1,z151,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z463])],[(0,[z35,z7,z0,z228,z2,z3,z9]),(0,[z7,z0,z1,z17,z2,z3,z9]),(0,[z7,z0,z1,z183,z2,z3,z4]),(1,[z7,z0,z464,z2,z3,z9]),(0,[z7,z0,z1,z465,z2,z3,z9])],[(0,[z15,z7,z0,z1,z2,z3,z9]),(0,[z0,z1,z2,z75,z3,z9,z4]),(0,[z466,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z467,z2,z3,z9]),(0,[z7,z8,z1,z21,z2,z3,z9]),(0,[z7,z1,z46,z2,z18,z3,z9]),(0,[z7,z0,z1,z183,z46,z3,z9]),(1,[z7,z0,z1,z2,z354,z9])]],
   [[(0,[z468,z7,z0,z1,z2,z3,z9]),(0,[z0,z1,z2,z3,z9,z4,z469]),(0,[z7,z0,z1,z2,z12,z3,z68]),(0,[z162,z7,z0,z1,z198,z3,z9])],[(0,[z6,z0,z1,z2,z3,z9,z85]),(0,[z7,z0,z8,z2,z3,z48,z9]),(0,[z7,z470,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z471,z3,z9]),(0,[z7,z0,z1,z472,z2,z3,z9]),(0,[z11,z7,z0,z1,z2,z3,z9])],[(0,[z7,z473,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z121]),(0,[z7,z0,z1,z2,z474,z3,z9])],[(0,[z88,z7,z0,z298,z2,z3,z9]),(0,[z44,z227,z7,z0,z2,z3,z9]),(0,[z475,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z476]),(0,[z329,z7,z0,z21,z2,z3,z9]),(0,[z81,z7,z0,z8,z2,z3,z9]),(0,[z179,z7,z0,z1,z2,z3,z54]),(0,[z7,z0,z1,z2,z477,z3,z9]),(0,[z7,z0,z1,z2,z3,z478,z9])],[(0,[z35,z90,z0,z1,z2,z3,z9]),(0,[z35,z227,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z479,z3,z9]),(0,[z7,z0,z1,z2,z3,z480,z9]),(0,[z23,z188,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z164,z2,z48,z9])],[(0,[z7,z0,z1,z2,z197,z3,z9]),(0,[z7,z0,z481,z1,z2,z3,z9]),(0,[z482,z7,z0,z1,z2,z3,z9]),(0,[z91,z7,z0,z8,z2,z3,z9]),(0,[z7,z0,z1,z46,z3,z48,z9]),(0,[z7,z0,z1,z2,z483,z3,z9])],[(0,[z7,z0,z1,z2,z3,z484,z9]),(0,[z74,z0,z1,z2,z3,z9,z4])],[(0,[z7,z0,z1,z2,z3,z9,z370])]],
   [[(0,[z44,z35,z7,z0,z2,z3,z9]),(0,[z7,z0,z1,z485,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z169,z5]),(0,[z162,z7,z0,z1,z76,z3,z9])],[(0,[z7,z0,z1,z486,z2,z3,z9]),(0,[z7,z0,z53,z21,z2,z3,z9]),(0,[z7,z0,z104,z8,z2,z3,z9]),(0,[z79,z7,z0,z1,z2,z3,z301]),(0,[z81,z7,z0,z1,z3,z48,z9]),(0,[z7,z0,z1,z164,z3,z50,z9])],[(0,[z6,z0,z487,z1,z2,z3,z9]),(0,[z162,z7,z0,z21,z2,z3,z9]),(0,[z7,z0,z8,z105,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z488])],[(0,[z7,z0,z1,z489,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z382])],[(0,[z490,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z324,z1,z2,z3,z9]),(0,[z7,z0,z1,z164,z46,z3,z9]),(0,[z491,z7,z0,z1,z2,z3,z9])],[(0,[z7,z0,z21,z2,z3,z260,z9]),(0,[z7,z0,z21,z2,z3,z9,z4])],[(0,[z7,z323,z0,z1,z2,z3,z9]),(0,[z173,z7,z0,z21,z2,z3,z9]),(0,[z0,z1,z2,z3,z50,z9,z4]),(0,[z7,z0,z1,z2,z492,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z493])],[(0,[z231,z0,z120,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z250]),(0,[z0,z494,z1,z2,z3,z9,z4]),(0,[z179,z7,z0,z21,z2,z3,z9]),(0,[z79,z7,z0,z1,z2,z3,z321]),(0,[z7,z0,z1,z2,z3,z266,z9]),(1,[z448,z0,z1,z2,z3,z9])]],
   [[(0,[z7,z0,z21,z2,z137,z3,z9]),(0,[z7,z0,z1,z376,z2,z3,z9]),(0,[z7,z0,z2,z3,z242,z48,z9]),(0,[z7,z0,z1,z183,z2,z3,z50])],[(0,[z227,z7,z0,z21,z2,z3,z9]),(0,[z495,z7,z0,z1,z2,z3,z9]),(0,[z6,z0,z196,z1,z2,z3,z9]),(0,[z7,z0,z8,z21,z2,z3,z9]),(0,[z496,z7,z0,z1,z2,z3,z9]),(0,[z7,z45,z1,z46,z2,z3,z9]),(0,[z7,z0,z1,z497,z2,z3,z9])],[(0,[z7,z0,z1,z2,z498,z3,z9]),(0,[z7,z0,z1,z2,z3,z499,z9]),(1,[z7,z0,z1,z37,z48,z9]),(0,[z7,z0,z1,z2,z3,z9,z500]),(0,[z7,z0,z1,z105,z2,z71,z9])],[(0,[z88,z7,z120,z1,z2,z3,z9]),(0,[z88,z0,z1,z2,z3,z9,z4]),(0,[z227,z7,z0,z2,z3,z32,z9]),(0,[z7,z0,z1,z2,z3,z501,z9]),(0,[z7,z0,z8,z2,z3,z32,z9]),(0,[z7,z0,z1,z2,z41,z9,z85]),(0,[z7,z0,z1,z2,z3,z9,z502]),(0,[z7,z0,z1,z2,z3,z9,z187]),(0,[z7,z0,z1,z2,z3,z9,z503])],[(0,[z90,z0,z120,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z504,z9]),(0,[z7,z0,z505,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z3,z154,z9]),(0,[z7,z506,z0,z1,z2,z3,z9]),(0,[z373,z7,z0,z21,z2,z3,z9]),(0,[z7,z507,z0,z1,z2,z3,z9]),(1,[z7,z45,z1,z46,z3,z9]),(1,[z344,z0,z1,z2,z3,z9]),(1,[z7,z0,z229,z2,z102,z9]),(0,[z7,z0,z1,z2,z3,z9,z508])],[(0,[z7,z0,z1,z2,z509,z3,z9]),(1,[z0,z1,z183,z2,z3,z4])],[(0,[z510,z7,z0,z1,z2,z3,z9]),(0,[z7,z511,z0,z1,z2,z3,z9]),(0,[z6,z172,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z512,z2,z3,z9]),(0,[z7,z223,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z513,z2,z3,z9]),(0,[z7,z0,z1,z2,z12,z22,z9]),(0,[z7,z0,z1,z514,z2,z3,z9])]],
   [[(0,[z6,z45,z0,z1,z2,z3,z9]),(0,[z515,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z0,z21,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z516,z9]),(0,[z7,z0,z1,z2,z202,z3,z9]),(0,[z113,z7,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z399,z2,z3,z9]),(0,[z6,z0,z228,z1,z2,z3,z9]),(0,[z172,z0,z1,z2,z3,z9,z4]),(0,[z7,z0,z1,z2,z3,z9,z517]),(0,[z7,z0,z196,z1,z75,z3,z9]),(1,[z470,z0,z1,z2,z3,z9]),(1,[z7,z0,z104,z2,z3,z32]),(0,[z7,z0,z518,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z3,z9,z208]),(0,[z7,z0,z1,z2,z3,z301,z9])],[(0,[z231,z172,z0,z1,z2,z3,z9]),(0,[z0,z1,z2,z498,z3,z9,z4]),(0,[z0,z1,z2,z3,z9,z4,z4]),(0,[z7,z0,z1,z2,z201,z3,z9]),(0,[z81,z7,z0,z1,z2,z3,z50])],[(0,[z7,z0,z1,z2,z3,z311,z9]),(0,[z79,z7,z0,z1,z18,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z519]),(0,[z74,z7,z0,z1,z151,z3,z9]),(0,[z74,z7,z0,z1,z2,z266,z9]),(0,[z7,z0,z1,z2,z520,z3,z9])],[(0,[z7,z0,z521,z1,z2,z3,z9]),(0,[z231,z0,z228,z1,z2,z3,z9]),(0,[z78,z0,z1,z2,z3,z9,z4]),(0,[z7,z0,z1,z2,z3,z522,z9])],[(0,[z523,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z524,z9]),(0,[z179,z7,z0,z1,z2,z3,z68]),(1,[z7,z0,z47,z2,z3,z9]),(0,[z7,z0,z1,z525,z2,z3,z9])],[(0,[z88,z7,z0,z422,z2,z3,z9]),(0,[z7,z0,z120,z8,z2,z3,z9]),(0,[z0,z1,z2,z3,z9,z4,z336]),(0,[z7,z0,z2,z3,z9,z157,z4]),(0,[z7,z0,z21,z2,z3,z9,z85]),(0,[z7,z0,z1,z2,z526,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z527]),(1,[z162,z7,z0,z2,z233,z9]),(1,[z7,z0,z1,z105,z2,z12])]],
   [[(1,[z7,z0,z1,z2,z3,z9]),(0,[z6,z43,z0,z1,z2,z3,z9]),(0,[z23,z7,z0,z1,z2,z3,z335]),(0,[z7,z528,z0,z1,z2,z3,z9])],[(0,[z7,z0,z529,z1,z2,z3,z9]),(0,[z6,z0,z1,z2,z12,z3,z9]),(1,[z0,z53,z21,z2,z3,z9]),(0,[z530,z7,z0,z1,z2,z3,z9]),(0,[z531,z7,z0,z1,z2,z3,z9])],[(0,[z15,z0,z1,z2,z150,z3,z9]),(0,[z532,z7,z0,z1,z2,z3,z9]),(0,[z0,z1,z2,z3,z533,z9,z4]),(0,[z7,z175,z0,z21,z2,z3,z9]),(0,[z7,z0,z8,z2,z3,z9,z85]),(0,[z7,z0,z1,z2,z3,z9,z84]),(0,[z7,z0,z1,z2,z3,z9,z534])],[(0,[z7,z0,z1,z2,z3,z535,z9]),(1,[z173,z0,z1,z2,z260,z9]),(0,[z7,z0,z1,z2,z3,z9,z536]),(1,[z7,z0,z265,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z537,z9]),(0,[z7,z0,z2,z3,z32,z9,z5])],[(0,[z538,z7,z0,z1,z2,z3,z9]),(0,[z79,z7,z0,z8,z2,z3,z9]),(0,[z79,z7,z0,z376,z2,z3,z9]),(0,[z7,z45,z0,z1,z18,z3,z9]),(0,[z539,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z75,z3,z9])],[(0,[z7,z0,z1,z2,z3,z194,z9]),(1,[z0,z21,z2,z3,z9,z4]),(0,[z87,z7,z0,z8,z2,z3,z9]),(0,[z7,z0,z196,z8,z2,z3,z9]),(0,[z7,z0,z1,z540,z2,z3,z9]),(0,[z7,z45,z0,z170,z2,z3,z9])],[(0,[z541,z7,z0,z8,z2,z3,z9]),(0,[z7,z0,z8,z542,z2,z3,z9]),(0,[z543,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z544,z1,z2,z3,z9]),(0,[z545,z7,z0,z1,z2,z3,z9])],[(0,[z7,z175,z8,z1,z2,z3,z9]),(0,[z546,z7,z0,z8,z2,z3,z9]),(0,[z7,z0,z1,z18,z3,z9,z84]),(0,[z7,z40,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z547,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z548,z9]),(0,[z7,z0,z1,z549,z2,z3,z9]),(0,[z7,z0,z1,z550,z2,z3,z9])]],
   [[(0,[z7,z0,z1,z2,z3,z551,z9]),(1,[z0,z8,z2,z3,z9,z4]),(0,[z7,z0,z21,z2,z3,z169,z9]),(0,[z7,z0,z1,z2,z18,z3,z9]),(0,[z7,z0,z1,z552,z2,z3,z9])],[(1,[z7,z0,z1,z73,z3,z9])],[(1,[z7,z0,z1,z2,z3,z194]),(0,[z7,z0,z1,z2,z553,z3,z9]),(0,[z554,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z8,z2,z209,z3,z9]),(0,[z405,z7,z0,z1,z2,z3,z9]),(0,[z7,z45,z0,z186,z2,z3,z9]),(0,[z7,z555,z0,z1,z2,z3,z9])],[(0,[z6,z0,z1,z2,z3,z9,z9]),(0,[z7,z0,z21,z2,z71,z3,z9]),(0,[z79,z7,z0,z1,z46,z3,z9]),(0,[z112,z7,z0,z1,z2,z3,z9]),(0,[z556,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z557,z2,z3,z9]),(1,[z0,z1,z2,z3,z9,z187])],[(0,[z15,z7,z90,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z169,z68]),(0,[z7,z0,z1,z2,z558,z3,z9]),(0,[z0,z1,z2,z102,z3,z366,z9]),(0,[z7,z0,z1,z559,z2,z3,z9])],[(0,[z7,z0,z228,z8,z2,z3,z9]),(0,[z6,z231,z0,z1,z2,z3,z9]),(0,[z0,z1,z37,z2,z3,z9,z4]),(0,[z0,z1,z2,z3,z9,z4,z85]),(0,[z7,z0,z560,z21,z2,z3,z9]),(0,[z7,z0,z561,z8,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z562,z9])],[(0,[z7,z0,z1,z563,z2,z3,z9]),(0,[z7,z175,z0,z1,z2,z3,z9]),(0,[z7,z0,z8,z2,z71,z3,z9]),(0,[z564,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z565,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z68,z84]),(0,[z566,z7,z0,z1,z2,z3,z9])],[(0,[z7,z567,z0,z1,z2,z3,z9]),(1,[z7,z0,z1,z2,z342,z9])]],
   [[(0,[z7,z0,z1,z2,z568,z3,z9]),(0,[z6,z0,z1,z2,z119,z3,z9]),(0,[z7,z0,z1,z464,z2,z3,z9]),(0,[z7,z0,z1,z151,z2,z3,z9]),(0,[z7,z569,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z570,z2,z3,z9]),(0,[z7,z0,z21,z2,z3,z9,z54]),(0,[z457,z7,z0,z21,z2,z3,z9]),(1,[z7,z0,z196,z151,z3,z9]),(0,[z571,z7,z0,z1,z2,z3,z9]),(0,[z572,z7,z0,z1,z2,z3,z9]),(0,[z573,z7,z0,z1,z2,z3,z9]),(0,[z7,z574,z0,z1,z2,z3,z9])],[(0,[z575,z7,z0,z1,z2,z3,z9]),(0,[z576,z7,z0,z1,z2,z3,z9]),(0,[z6,z0,z1,z2,z3,z260,z9]),(0,[z6,z0,z1,z2,z3,z9,z4]),(0,[z577,z7,z0,z1,z2,z3,z9])],[(0,[z35,z7,z0,z8,z2,z3,z9]),(0,[z7,z0,z229,z21,z2,z3,z9]),(0,[z578,z7,z0,z1,z2,z3,z9]),(1,[z7,z0,z1,z164,z22,z9])],[(0,[z7,z0,z1,z579,z2,z3,z9]),(0,[z580,z7,z0,z1,z2,z3,z9]),(0,[z7,z66,z0,z47,z2,z3,z9]),(0,[z81,z448,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z50,z9]),(0,[z7,z0,z1,z2,z581,z3,z9])],[(0,[z0,z1,z17,z2,z3,z9,z4]),(0,[z79,z7,z0,z1,z2,z424,z9]),(0,[z7,z0,z1,z2,z41,z3,z9]),(0,[z7,z0,z1,z2,z582,z3,z9])],[(0,[z231,z0,z1,z2,z3,z9,z4]),(1,[z6,z0,z1,z2,z3,z9]),(1,[z0,z1,z2,z3,z4,z54]),(0,[z0,z1,z183,z2,z3,z9,z4]),(0,[z7,z0,z1,z2,z3,z9,z583]),(0,[z7,z0,z1,z2,z3,z48,z9]),(0,[z7,z0,z1,z584,z2,z3,z9])],[(0,[z585,z7,z0,z1,z2,z3,z9]),(0,[z14,z7,z0,z1,z2,z176,z9]),(0,[z586,z7,z0,z1,z2,z3,z9]),(0,[z7,z66,z0,z8,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z587])]],
   [[(1,[z7,z0,z1,z2,z3,z145]),(1,[z227,z0,z228,z2,z3,z9]),(1,[z23,z7,z1,z2,z39,z9]),(0,[z61,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z588])],[(0,[z66,z0,z1,z2,z3,z9,z4]),(1,[z7,z0,z1,z2,z3,z138]),(0,[z7,z0,z1,z589,z2,z3,z9]),(0,[z7,z0,z1,z164,z37,z3,z9]),(0,[z7,z0,z1,z2,z590,z3,z9])],[(0,[z7,z0,z1,z591,z2,z3,z9]),(0,[z7,z0,z1,z2,z22,z41,z9]),(0,[z0,z1,z2,z3,z68,z9,z370]),(0,[z7,z0,z1,z2,z592,z3,z9]),(0,[z7,z0,z1,z2,z3,z593,z9]),(0,[z7,z0,z1,z183,z2,z3,z9])],[(0,[z594,z7,z0,z1,z2,z3,z9]),(1,[z7,z0,z1,z122,z3,z9]),(0,[z74,z7,z0,z2,z102,z3,z9])],[(0,[z15,z7,z120,z1,z2,z3,z9]),(0,[z15,z0,z1,z2,z3,z260,z9]),(0,[z15,z0,z1,z2,z3,z9,z4]),(0,[z7,z0,z1,z595,z2,z3,z9]),(0,[z466,z0,z1,z2,z3,z9,z4]),(0,[z7,z0,z596,z1,z2,z3,z9]),(0,[z7,z0,z1,z597,z2,z3,z9]),(0,[z179,z112,z0,z1,z2,z3,z9]),(0,[z598,z7,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z3,z9,z599]),(0,[z7,z0,z1,z46,z150,z3,z9]),(1,[z6,z0,z1,z2,z3,z4])],[(0,[z600,z7,z0,z1,z2,z3,z9]),(1,[z172,z0,z1,z150,z3,z9]),(1,[z353,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z601,z2,z3,z9])],[(0,[z7,z0,z1,z2,z176,z3,z9]),(0,[z7,z0,z21,z2,z12,z3,z9]),(0,[z179,z7,z66,z1,z2,z3,z9]),(0,[z7,z0,z1,z602,z2,z3,z9])]],
   [[(0,[z603,z7,z0,z1,z2,z3,z9]),(1,[z87,z7,z21,z2,z3,z9]),(0,[z23,z7,z0,z1,z55,z3,z9]),(0,[z7,z604,z0,z1,z2,z3,z9])],[(0,[z6,z90,z0,z1,z2,z3,z9]),(0,[z227,z0,z228,z1,z2,z3,z9]),(0,[z6,z227,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z46,z2,z3,z9]),(0,[z7,z0,z24,z1,z2,z3,z9])],[(1,[z7,z0,z1,z2,z3,z216]),(0,[z7,z0,z1,z2,z3,z605,z9]),(0,[z7,z606,z0,z1,z2,z3,z9]),(0,[z7,z0,z607,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z533,z9]),(0,[z7,z0,z8,z2,z12,z3,z9]),(0,[z7,z0,z1,z608,z2,z3,z9])],[(0,[z609,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z610,z2,z3,z9]),(0,[z611,z7,z0,z1,z2,z3,z9])],[(0,[z231,z7,z0,z1,z2,z3,z250]),(0,[z7,z0,z1,z2,z41,z260,z9]),(0,[z0,z1,z320,z2,z3,z9,z4]),(0,[z74,z7,z0,z196,z2,z3,z9]),(0,[z7,z0,z1,z2,z612,z3,z9])],[(0,[z613,z7,z0,z1,z2,z3,z9]),(0,[z7,z614,z0,z1,z2,z3,z9]),(0,[z0,z1,z2,z3,z9,z423,z4]),(0,[z7,z0,z196,z151,z2,z3,z9]),(0,[z81,z7,z0,z1,z2,z3,z9]),(0,[z615,z7,z0,z1,z2,z3,z9])],[(1,[z15,z90,z1,z2,z3,z9]),(0,[z0,z1,z2,z3,z39,z9,z4]),(0,[z7,z0,z1,z105,z2,z3,z4]),(0,[z7,z0,z1,z560,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z333,z9]),(0,[z7,z0,z1,z2,z3,z9,z616]),(0,[z7,z0,z1,z2,z3,z617,z9]),(0,[z7,z0,z1,z2,z71,z22,z9])],[(0,[z91,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z618,z3,z9]),(0,[z172,z7,z0,z1,z17,z3,z9]),(0,[z108,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z424,z3,z9]),(0,[z7,z0,z1,z2,z3,z233,z9]),(0,[z7,z0,z1,z164,z2,z3,z9]),(0,[z7,z0,z1,z619,z2,z3,z9])]],
   [[(0,[z7,z620,z0,z1,z2,z3,z9]),(0,[z575,z6,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z252,z2,z3,z9]),(1,[z6,z0,z1,z2,z3,z169]),(0,[z496,z7,z0,z21,z2,z3,z9]),(0,[z7,z0,z1,z2,z621,z3,z9]),(0,[z622,z7,z0,z1,z2,z3,z9])],[(0,[z7,z623,z0,z1,z2,z3,z9]),(1,[z231,z0,z1,z17,z3,z9]),(0,[z7,z0,z1,z2,z3,z624,z9]),(0,[z7,z0,z21,z2,z102,z3,z9]),(0,[z7,z0,z1,z2,z3,z625,z9]),(1,[z44,z7,z0,z2,z3,z5]),(0,[z7,z0,z1,z626,z2,z3,z9]),(0,[z7,z0,z1,z183,z2,z342,z9])],[(0,[z7,z0,z1,z2,z176,z41,z9]),(1,[z7,z0,z1,z193,z3,z9])],[(0,[z7,z7,z0,z1,z2,z3,z9]),(0,[z15,z90,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z627,z3,z9]),(0,[z7,z0,z1,z2,z628,z3,z9]),(0,[z6,z0,z1,z2,z3,z39,z9]),(0,[z629,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z335,z9]),(0,[z7,z0,z1,z2,z3,z54,z84]),(0,[z7,z0,z1,z2,z3,z9,z630]),(0,[z7,z0,z104,z1,z2,z3,z9]),(0,[z7,z0,z1,z631,z2,z3,z9])],[(0,[z81,z7,z0,z1,z2,z3,z4]),(0,[z7,z0,z1,z183,z2,z3,z169]),(0,[z7,z0,z632,z1,z2,z3,z9]),(0,[z44,z7,z0,z2,z3,z9,z5])],[(0,[z6,z0,z1,z2,z3,z169,z9]),(0,[z7,z0,z1,z2,z633,z3,z9]),(0,[z7,z0,z1,z2,z152,z3,z9]),(1,[z7,z0,z1,z198,z3,z9])],[(1,[z7,z0,z1,z89,z3,z9]),(0,[z353,z0,z1,z2,z102,z3,z9])],[(0,[z7,z0,z1,z2,z3,z32,z4])]],
   [[(0,[z7,z0,z1,z2,z3,z634,z9]),(0,[z6,z0,z1,z2,z71,z3,z9]),(0,[z7,z0,z1,z2,z269,z3,z9]),(1,[z7,z8,z21,z2,z3,z9]),(0,[z23,z7,z0,z464,z2,z3,z9]),(0,[z7,z0,z635,z1,z2,z3,z9]),(0,[z7,z0,z636,z1,z2,z3,z9])],[(0,[z88,z7,z0,z8,z2,z3,z9]),(0,[z637,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z638,z1,z2,z3,z9]),(0,[z0,z104,z1,z2,z3,z9,z4]),(0,[z594,z6,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z639,z9]),(0,[z7,z0,z1,z640,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z641,z9])],[(1,[z7,z0,z319,z2,z3,z9]),(0,[z7,z0,z1,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z642,z9]),(0,[z7,z0,z1,z2,z643,z3,z9]),(0,[z644,z7,z0,z1,z2,z3,z9])],[(0,[z7,z0,z8,z2,z3,z260,z9]),(0,[z0,z196,z1,z2,z3,z9,z4]),(0,[z162,z0,z1,z2,z3,z9,z4]),(0,[z7,z0,z8,z2,z3,z9,z4]),(0,[z7,z0,z1,z2,z645,z3,z9]),(1,[z7,z0,z1,z2,z185,z9]),(0,[z179,z7,z0,z1,z2,z190,z9])],[(0,[z7,z0,z1,z2,z3,z646,z9]),(0,[z101,z7,z0,z1,z2,z3,z9])],[(0,[z7,z0,z120,z21,z2,z3,z9]),(0,[z647,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z21,z2,z3,z68,z9]),(0,[z7,z0,z1,z315,z2,z3,z9])],[(0,[z648,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z649,z9]),(0,[z7,z0,z1,z2,z3,z650,z9]),(0,[z6,z0,z1,z2,z3,z9,z54]),(0,[z7,z0,z1,z2,z3,z651,z9])],[(0,[z7,z0,z1,z2,z652,z3,z9]),(0,[z172,z7,z0,z8,z2,z3,z9]),(0,[z173,z0,z1,z2,z3,z260,z9]),(0,[z173,z0,z1,z2,z3,z9,z4]),(0,[z81,z7,z0,z1,z2,z3,z169]),(1,[z7,z0,z21,z2,z3,z9]),(0,[z7,z0,z1,z2,z22,z39,z9]),(0,[z344,z0,z1,z2,z3,z68,z9]),(0,[z7,z0,z151,z2,z102,z3,z9]),(0,[z7,z0,z1,z653,z2,z3,z9]),(0,[z654,z7,z0,z1,z2,z3,z9]),(0,[z431,z0,z1,z2,z71,z3,z9])]],
   [[(0,[z179,z0,z1,z2,z3,z9,z4]),(0,[z7,z0,z1,z2,z3,z4,z5]),(0,[z7,z0,z1,z288,z2,z3,z9]),(0,[z7,z0,z8,z2,z3,z68,z9]),(0,[z7,z0,z1,z2,z3,z354,z9]),(0,[z7,z0,z1,z105,z2,z3,z85])],[(0,[z7,z0,z494,z1,z2,z3,z9]),(0,[z44,z7,z0,z104,z2,z3,z9])],[(0,[z655,z7,z0,z1,z2,z3,z9]),(0,[z227,z0,z1,z2,z3,z9,z4]),(0,[z7,z0,z1,z2,z656,z3,z9]),(0,[z0,z1,z2,z3,z9,z4,z314])],[(0,[z7,z0,z1,z2,z3,z9,z657]),(0,[z78,z7,z0,z8,z2,z3,z9]),(0,[z87,z7,z0,z21,z2,z3,z9]),(0,[z7,z0,z8,z2,z3,z348,z9]),(0,[z7,z0,z1,z542,z2,z3,z9]),(0,[z148,z7,z0,z1,z2,z3,z9]),(0,[z658,z7,z0,z1,z2,z3,z9]),(0,[z659,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z660,z3,z9]),(0,[z661,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z662,z3,z9])],[(0,[z7,z0,z1,z2,z3,z663,z9]),(0,[z40,z0,z1,z2,z3,z9,z4]),(0,[z0,z1,z2,z645,z3,z9,z4])],[(0,[z91,z6,z0,z1,z2,z3,z9])],[(0,[z7,z0,z422,z1,z2,z3,z9]),(0,[z7,z90,z0,z399,z2,z3,z9]),(1,[z0,z1,z105,z2,z3,z4]),(0,[z7,z40,z0,z21,z2,z3,z9]),(0,[z162,z7,z0,z1,z2,z233,z9])],[(0,[z664,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z665,z3,z9]),(0,[z179,z7,z0,z1,z2,z232,z9]),(0,[z7,z0,z1,z2,z3,z50,z54])]],
   [[(0,[z7,z0,z1,z666,z2,z3,z9]),(0,[z7,z0,z1,z667,z2,z3,z9]),(0,[z0,z1,z2,z3,z169,z9,z4]),(0,[z6,z0,z264,z1,z2,z3,z9]),(0,[z7,z0,z487,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z668]),(0,[z669,z7,z0,z1,z2,z3,z9])],[(0,[z7,z0,z120,z1,z2,z3,z9]),(0,[z670,z7,z0,z1,z2,z3,z9]),(0,[z35,z14,z0,z1,z2,z3,z9]),(0,[z7,z0,z671,z1,z2,z3,z9]),(1,[z81,z0,z1,z2,z3,z4]),(0,[z7,z0,z1,z2,z3,z4,z54]),(0,[z7,z0,z1,z2,z3,z9,z672]),(0,[z7,z0,z1,z2,z673,z3,z9]),(0,[z7,z66,z0,z1,z2,z3,z54]),(0,[z7,z674,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z675,z3,z9])],[(0,[z0,z1,z2,z71,z3,z9,z4]),(0,[z7,z676,z0,z1,z2,z3,z9])],[(0,[z88,z7,z0,z1,z2,z140,z9]),(0,[z7,z0,z677,z1,z2,z3,z9]),(0,[z678,z7,z0,z1,z2,z3,z9]),(0,[z679,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z71,z48,z9])],[(0,[z7,z680,z0,z1,z2,z3,z9]),(0,[z681,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z682,z9]),(0,[z7,z0,z21,z2,z3,z378,z9]),(0,[z7,z0,z21,z2,z3,z9,z84])],[(0,[z90,z0,z228,z1,z2,z3,z9]),(0,[z6,z0,z1,z17,z2,z3,z9]),(1,[z7,z0,z565,z2,z3,z9]),(1,[z0,z1,z2,z152,z3,z9])],[(0,[z683,z7,z0,z1,z2,z3,z9]),(0,[z0,z228,z1,z135,z2,z3,z9]),(0,[z7,z0,z1,z684,z2,z3,z9]),(0,[z79,z7,z0,z1,z2,z3,z9])],[(0,[z685,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z176,z39,z9]),(0,[z0,z1,z2,z3,z9,z4,z350]),(1,[z0,z1,z2,z3,z32,z4]),(0,[z87,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z686,z3,z9]),(0,[z7,z0,z196,z1,z2,z3,z9])]],
   [[(0,[z541,z7,z0,z1,z2,z3,z9]),(0,[z0,z228,z1,z2,z150,z3,z9]),(1,[z7,z40,z1,z2,z41,z9]),(0,[z7,z66,z1,z2,z3,z68,z9]),(0,[z7,z0,z1,z687,z2,z3,z9])],[(1,[z200,z7,z0,z2,z3,z9]),(0,[z7,z0,z21,z2,z3,z39,z9]),(0,[z546,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z688,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z689,z9]),(0,[z7,z0,z1,z105,z2,z12,z9])],[(0,[z7,z0,z1,z2,z3,z9,z690]),(0,[z7,z0,z21,z2,z18,z3,z9]),(0,[z179,z7,z0,z392,z2,z3,z9]),(0,[z691,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z3,z48,z50,z9]),(0,[z7,z0,z1,z2,z12,z71,z3])],[(0,[z7,z692,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z693,z2,z3,z9]),(0,[z7,z0,z21,z2,z3,z9,z5]),(0,[z248,z7,z0,z8,z2,z3,z9]),(0,[z7,z694,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z695])],[(0,[z7,z0,z1,z135,z2,z3,z9]),(0,[z7,z0,z8,z2,z3,z39,z9]),(0,[z7,z40,z0,z565,z2,z3,z9])],[(0,[z7,z0,z1,z2,z3,z9,z469]),(1,[z6,z0,z21,z2,z3,z9]),(0,[z7,z66,z0,z21,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z9,z321]),(0,[z7,z0,z1,z2,z696,z3,z9]),(0,[z7,z0,z1,z2,z697,z3,z9])],[(0,[z7,z0,z1,z2,z150,z3,z9]),(0,[z6,z0,z1,z2,z102,z3,z9]),(0,[z7,z0,z8,z2,z3,z169,z9]),(0,[z7,z0,z1,z2,z3,z9,z698]),(0,[z7,z0,z1,z2,z3,z434,z9]),(0,[z7,z0,z8,z217,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z699,z9]),(0,[z7,z0,z1,z2,z3,z700,z9]),(0,[z7,z0,z1,z2,z3,z701,z9]),(0,[z44,z470,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z702,z2,z3,z9])],[(1,[z7,z0,z1,z2,z197,z9]),(0,[z7,z0,z1,z2,z703,z3,z9]),(0,[z704,z7,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z705,z9]),(0,[z7,z0,z228,z1,z2,z3,z9]),(0,[z7,z45,z0,z8,z2,z3,z9]),(0,[z7,z0,z561,z1,z2,z3,z9]),(0,[z7,z0,z1,z706,z2,z3,z9])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z7,z0,z8,z2,z3,z335]),(0,[z7,z632,z8,z2,z3,z9])],[(0,[z0,z1,z2,z3,z4,z476]),(0,[z7,z0,z1,z2,z707,z9]),(0,[z23,z7,z1,z38,z39,z9]),(0,[z112,z0,z1,z73,z3,z9]),(0,[z74,z7,z0,z75,z96,z9]),(0,[z7,z0,z1,z193,z3,z9])],[(0,[z0,z1,z2,z3,z705,z4]),(0,[z7,z0,z1,z2,z3,z708]),(0,[z7,z0,z315,z2,z3,z378]),(0,[z7,z0,z1,z38,z3,z138])],[(0,[z7,z0,z1,z105,z2,z645])],[(0,[z7,z0,z1,z2,z3,z156]),(0,[z7,z40,z1,z2,z709,z9])],[(0,[z7,z0,z1,z2,z197,z216]),(0,[z7,z0,z710,z2,z3,z9])],[(0,[z7,z0,z711,z2,z3,z9]),(0,[z7,z0,z1,z712,z3,z9])],[(0,[z35,z0,z570,z2,z3,z9]),(0,[z6,z0,z713,z2,z3,z9]),(0,[z7,z8,z21,z2,z3,z9]),(0,[z714,z7,z0,z2,z3,z9]),(0,[z7,z0,z715,z2,z3,z9])],[(0,[z7,z0,z1,z2,z3,z716]),(0,[z81,z7,z0,z1,z3,z717])],[(0,[z7,z0,z319,z2,z3,z9]),(0,[z0,z464,z2,z3,z9,z4]),(0,[z113,z0,z196,z151,z3,z9])],[(0,[z0,z376,z2,z3,z9,z4]),(1,[z7,z718,z2,z3,z9])],[(0,[z6,z0,z1,z2,z3,z100]),(0,[z108,z7,z1,z2,z3,z54]),(0,[z7,z0,z1,z2,z3,z717])],[(0,[z27,z0,z135,z2,z3,z9]),(0,[z81,z0,z21,z2,z3,z4]),(0,[z7,z0,z1,z2,z719,z3]),(0,[z720,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z3,z721]),(0,[z0,z1,z2,z3,z69,z4]),(0,[z200,z6,z0,z2,z3,z4]),(0,[z0,z1,z2,z3,z722,z9]),(0,[z0,z1,z2,z723,z3,z9])],[(0,[z7,z0,z21,z2,z3,z9]),(0,[z7,z569,z21,z2,z3,z9])],[(0,[z0,z1,z2,z3,z80,z4]),(0,[z0,z1,z2,z724,z3,z4]),(0,[z7,z0,z1,z725,z3,z9]),(0,[z726,z0,z1,z2,z3,z9])]],
   [[],[(0,[z7,z692,z8,z2,z3,z9]),(0,[z475,z0,z1,z2,z3,z4]),(0,[z466,z0,z1,z183,z3,z4]),(0,[z7,z0,z1,z2,z71,z698]),(0,[z0,z1,z2,z3,z9,z727]),(0,[z245,z7,z0,z37,z48,z9])],[(0,[z0,z494,z2,z3,z9,z157]),(0,[z0,z1,z2,z728,z3,z9]),(0,[z7,z0,z1,z105,z193,z12])],[(0,[z206,z0,z1,z150,z3,z9]),(0,[z14,z0,z1,z2,z176,z154]),(0,[z7,z40,z21,z2,z41,z9])],[(0,[z245,z7,z0,z75,z3,z9])],[(0,[z231,z0,z1,z445,z3,z9]),(0,[z7,z0,z1,z2,z3,z729]),(0,[z0,z2,z3,z157,z4,z5]),(0,[z7,z21,z2,z372,z3,z9]),(0,[z7,z411,z1,z2,z3,z68]),(0,[z0,z1,z2,z730,z3,z9]),(0,[z61,z0,z104,z2,z3,z32]),(0,[z0,z1,z183,z2,z3,z187])],[(0,[z731,z0,z1,z2,z3,z9]),(0,[z44,z470,z0,z2,z3,z5])],[(0,[z7,z0,z298,z2,z140,z9]),(0,[z35,z0,z135,z2,z3,z145]),(0,[z0,z1,z17,z3,z533,z9]),(0,[z6,z0,z1,z193,z3,z9])],[(0,[z7,z0,z732,z2,z3,z9]),(0,[z0,z21,z2,z733,z3,z9])],[(0,[z0,z1,z2,z149,z3,z9]),(0,[z0,z1,z55,z3,z9,z4]),(0,[z7,z0,z1,z734,z3,z9]),(0,[z0,z1,z2,z3,z9,z735])],[(0,[z7,z0,z21,z2,z197,z9]),(0,[z7,z0,z1,z736,z3,z9]),(0,[z6,z0,z1,z2,z3,z156]),(0,[z81,z7,z0,z21,z3,z84]),(0,[z7,z0,z737,z2,z3,z9]),(0,[z7,z1,z2,z3,z738,z54])],[(0,[z15,z0,z1,z2,z3,z250]),(0,[z327,z0,z1,z2,z3,z4]),(0,[z74,z0,z75,z3,z9,z4]),(0,[z0,z8,z2,z3,z9,z370])],[(0,[z61,z0,z1,z2,z3,z9]),(0,[z7,z0,z8,z2,z232,z9]),(0,[z7,z0,z1,z739,z3,z9]),(0,[z7,z0,z740,z2,z3,z9]),(0,[z11,z0,z1,z105,z2,z12])],[(0,[z0,z228,z1,z2,z3,z216]),(0,[z88,z120,z1,z2,z3,z216]),(0,[z741,z0,z2,z3,z9,z4]),(0,[z6,z8,z21,z2,z3,z9]),(0,[z7,z175,z8,z2,z3,z9]),(0,[z10,z0,z21,z2,z3,z9])],[(0,[z7,z167,z1,z46,z3,z9]),(0,[z117,z43,z1,z2,z3,z9]),(0,[z11,z0,z8,z2,z3,z9]),(0,[z7,z0,z24,z55,z3,z9]),(0,[z7,z0,z265,z2,z232,z9])],[(0,[z6,z0,z319,z2,z3,z9]),(1,[z0,z742,z2,z3,z9]),(0,[z0,z1,z2,z743,z3,z9]),(0,[z0,z8,z2,z3,z9,z382])]],
   [[(0,[z227,z0,z2,z3,z32,z4]),(0,[z7,z0,z8,z55,z3,z9]),(0,[z0,z1,z744,z2,z3,z9])],[(0,[z0,z2,z3,z32,z4,z5]),(0,[z7,z0,z59,z2,z3,z9]),(0,[z0,z8,z2,z3,z9,z745]),(0,[z7,z40,z565,z2,z41,z9])],[(0,[z573,z0,z1,z2,z3,z4]),(0,[z27,z8,z21,z2,z3,z9])],[(0,[z7,z0,z8,z2,z3,z250]),(0,[z7,z0,z1,z746,z3,z9]),(0,[z7,z0,z1,z2,z3,z747]),(0,[z7,z0,z1,z2,z3,z748]),(0,[z0,z1,z2,z749,z3,z9])],[(0,[z7,z0,z750,z2,z3,z9]),(0,[z7,z0,z1,z73,z232,z9])],[(0,[z7,z0,z1,z2,z3,z751]),(0,[z184,z0,z1,z2,z3,z9]),(0,[z0,z53,z399,z2,z3,z9]),(0,[z7,z0,z1,z752,z3,z9]),(0,[z35,z0,z2,z3,z32,z4]),(0,[z0,z2,z753,z3,z9,z4]),(0,[z0,z1,z2,z3,z754,z9]),(0,[z113,z0,z1,z2,z3,z755])],[(0,[z188,z0,z1,z2,z3,z9]),(1,[z0,z1,z756,z3,z9]),(0,[z0,z136,z1,z2,z260,z9]),(0,[z184,z0,z8,z2,z3,z9]),(0,[z757,z0,z8,z2,z3,z9]),(0,[z7,z0,z1,z37,z739,z9])],[(0,[z200,z0,z2,z3,z4,z5]),(0,[z179,z7,z1,z2,z232,z54]),(0,[z758,z0,z1,z2,z3,z9])],[(0,[z0,z1,z2,z354,z9,z4]),(0,[z148,z0,z24,z2,z3,z9])],[(0,[z15,z43,z1,z2,z3,z9]),(0,[z10,z0,z1,z2,z3,z9]),(0,[z27,z0,z21,z2,z3,z9]),(0,[z7,z0,z1,z759,z3,z9]),(0,[z7,z0,z1,z18,z354,z9]),(0,[z7,z0,z1,z193,z39,z9])],[(0,[z7,z0,z760,z2,z3,z9]),(0,[z761,z0,z1,z2,z3,z32]),(0,[z7,z0,z1,z122,z190,z9])],[(0,[z6,z0,z1,z2,z3,z642]),(0,[z27,z0,z2,z3,z32,z9]),(0,[z7,z1,z2,z3,z9,z738])],[(0,[z7,z0,z21,z2,z3,z100]),(0,[z172,z0,z21,z150,z3,z9]),(0,[z101,z0,z21,z2,z3,z9]),(0,[z539,z7,z0,z1,z3,z84]),(0,[z7,z0,z2,z3,z762,z9]),(0,[z0,z1,z2,z763,z3,z9])],[(0,[z7,z0,z764,z2,z3,z9])],[(0,[z0,z1,z53,z2,z3,z9]),(0,[z7,z0,z2,z3,z32,z100]),(0,[z0,z1,z2,z3,z145,z4]),(0,[z61,z0,z1,z2,z3,z169]),(0,[z7,z143,z8,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z765])],[(0,[z0,z21,z2,z3,z4,z54]),(0,[z0,z1,z2,z3,z378,z4]),(0,[z0,z1,z192,z2,z3,z4]),(0,[z112,z0,z21,z2,z3,z9]),(0,[z7,z0,z21,z3,z9,z766]),(0,[z767,z0,z1,z2,z3,z9]),(0,[z768,z0,z1,z2,z3,z9])]],
   [[(0,[z7,z0,z769,z2,z3,z9])],[(0,[z637,z0,z1,z2,z3,z4]),(0,[z7,z0,z8,z2,z354,z9]),(0,[z770,z0,z1,z2,z3,z9])],[(0,[z7,z0,z298,z89,z3,z9]),(0,[z88,z120,z21,z2,z3,z9]),(0,[z0,z1,z2,z3,z771,z9]),(0,[z179,z7,z392,z2,z3,z54]),(0,[z7,z772,z1,z2,z3,z9]),(0,[z81,z7,z0,z1,z3,z84])],[(0,[z7,z0,z422,z2,z140,z9]),(0,[z14,z0,z1,z2,z443,z9]),(0,[z6,z175,z8,z2,z3,z9]),(0,[z7,z0,z8,z773,z3,z9]),(0,[z0,z1,z2,z3,z9,z774])],[(0,[z7,z0,z1,z2,z3,z775]),(0,[z7,z0,z1,z2,z3,z776]),(0,[z777,z0,z1,z2,z3,z138])],[(0,[z7,z0,z778,z2,z3,z9]),(0,[z200,z7,z0,z2,z3,z32])],[(0,[z0,z1,z396,z2,z3,z4]),(0,[z200,z470,z0,z2,z3,z9]),(0,[z0,z1,z2,z779,z3,z9])],[(0,[z7,z0,z742,z2,z3,z9]),(0,[z6,z0,z59,z2,z3,z9]),(0,[z780,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z301]),(0,[z0,z1,z2,z3,z9,z781]),(0,[z7,z0,z1,z38,z41,z9]),(0,[z66,z1,z2,z3,z68,z370])],[(0,[z6,z0,z1,z2,z3,z250]),(0,[z7,z0,z8,z2,z3,z301]),(0,[z7,z8,z280,z2,z3,z9]),(0,[z7,z0,z1,z782,z3,z9]),(1,[z7,z0,z2,z3,z783])],[(0,[z7,z0,z1,z57,z3,z194]),(0,[z0,z1,z2,z3,z216,z4]),(0,[z0,z1,z2,z266,z9,z4]),(0,[z200,z0,z2,z71,z3,z4]),(0,[z0,z784,z2,z3,z9,z4])],[(0,[z0,z59,z2,z3,z9,z4]),(0,[z81,z0,z1,z183,z3,z4]),(0,[z20,z0,z1,z2,z269,z9]),(0,[z7,z0,z785,z2,z3,z9])],[(0,[z7,z0,z1,z786,z3,z9]),(0,[z7,z638,z21,z2,z3,z9]),(0,[z7,z0,z21,z2,z3,z156]),(0,[z10,z0,z1,z2,z3,z169]),(0,[z7,z0,z1,z3,z9,z766]),(0,[z787,z0,z1,z2,z3,z9])],[(0,[z200,z0,z2,z3,z9,z469]),(0,[z0,z1,z105,z2,z149,z3])],[(0,[z200,z227,z0,z2,z3,z9]),(0,[z0,z1,z151,z2,z3,z788]),(0,[z7,z0,z1,z2,z71,z85])],[(0,[z88,z120,z1,z2,z3,z9]),(0,[z7,z0,z1,z756,z3,z9]),(0,[z789,z0,z21,z2,z3,z9]),(0,[z7,z0,z8,z2,z3,z321]),(0,[z7,z0,z376,z2,z3,z321])],[(0,[z14,z0,z1,z2,z176,z9]),(0,[z23,z1,z2,z39,z9,z4]),(0,[z790,z7,z0,z1,z2,z3]),(0,[z7,z45,z1,z725,z3,z9]),(0,[z0,z1,z2,z791,z3,z9])]],
   [[(0,[z7,z0,z1,z2,z3,z792]),(0,[z0,z793,z2,z3,z9,z4]),(1,[z0,z1,z2,z3,z788])],[(0,[z448,z0,z8,z2,z3,z9])],[(0,[z0,z742,z135,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z335]),(0,[z7,z0,z1,z2,z3,z794])],[(0,[z0,z1,z2,z435,z3,z4]),(0,[z7,z0,z793,z2,z3,z9]),(0,[z7,z0,z21,z2,z719,z3])],[(0,[z795,z7,z0,z2,z3,z9]),(0,[z0,z1,z2,z3,z4,z616]),(0,[z0,z1,z796,z2,z3,z9]),(0,[z0,z1,z2,z149,z3,z54])],[(0,[z0,z120,z1,z57,z3,z9])],[(0,[z7,z0,z797,z2,z3,z9])],[(0,[z798,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z799,z9]),(0,[z0,z1,z800,z3,z9,z4]),(0,[z0,z1,z2,z3,z169,z801])],[(0,[z0,z1,z450,z2,z3,z4]),(0,[z0,z264,z1,z2,z3,z4]),(0,[z7,z0,z1,z802,z3,z9])],[(0,[z88,z120,z1,z2,z197,z9]),(0,[z7,z0,z2,z3,z9,z803]),(0,[z256,z0,z1,z2,z3,z4]),(0,[z789,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z471,z12])],[(0,[z470,z0,z8,z2,z3,z9]),(0,[z74,z7,z0,z75,z3,z9])],[(0,[z212,z0,z1,z2,z3,z4]),(0,[z0,z1,z183,z3,z50,z4]),(0,[z0,z1,z804,z3,z9,z4]),(0,[z7,z0,z805,z2,z3,z9])],[(0,[z7,z0,z1,z2,z806,z9]),(0,[z6,z0,z1,z2,z3,z301]),(0,[z44,z27,z0,z2,z3,z9]),(1,[z7,z1,z725,z3,z9])],[(0,[z7,z0,z422,z89,z3,z9]),(0,[z7,z0,z1,z2,z807,z9]),(0,[z0,z1,z465,z2,z3,z4]),(0,[z8,z53,z21,z2,z3,z9]),(0,[z808,z0,z21,z2,z3,z9]),(0,[z809,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z3,z810]),(0,[z0,z1,z183,z46,z3,z4]),(0,[z811,z0,z1,z2,z3,z9]),(0,[z7,z0,z812,z2,z3,z9])]],
   [[(0,[z7,z0,z1,z2,z3,z813]),(0,[z7,z0,z186,z2,z3,z9])],[(0,[z7,z0,z298,z2,z3,z194]),(0,[z7,z0,z814,z2,z3,z9]),(0,[z0,z1,z2,z471,z3,z4])],[(0,[z0,z2,z3,z9,z4,z815]),(0,[z200,z81,z0,z2,z3,z4]),(0,[z7,z0,z21,z2,z232,z9]),(0,[z816,z0,z1,z2,z3,z9]),(0,[z7,z0,z817,z2,z3,z9])],[(0,[z6,z0,z1,z2,z71,z85]),(0,[z61,z0,z21,z2,z3,z9])],[(0,[z818,z7,z0,z2,z3,z9]),(0,[z7,z0,z819,z2,z3,z9]),(0,[z0,z392,z2,z3,z9,z4]),(0,[z11,z0,z21,z2,z3,z9]),(0,[z7,z175,z718,z2,z3,z9]),(0,[z7,z0,z1,z441,z48,z9]),(0,[z7,z0,z1,z820,z3,z9]),(0,[z821,z0,z1,z2,z3,z9])],[(0,[z7,z51,z21,z2,z3,z9]),(0,[z0,z8,z183,z2,z3,z4]),(0,[z0,z1,z2,z102,z3,z822])],[(0,[z7,z0,z1,z823,z3,z9])],[(0,[z200,z0,z2,z3,z9,z4]),(0,[z457,z27,z0,z2,z3,z9]),(0,[z7,z0,z196,z824,z3,z9])],[(0,[z200,z14,z0,z2,z3,z9]),(0,[z6,z0,z1,z2,z3,z335]),(0,[z7,z0,z1,z2,z825,z9]),(0,[z7,z0,z1,z2,z3,z788]),(0,[z44,z7,z0,z2,z3,z783])],[(0,[z7,z0,z21,z2,z3,z250]),(0,[z826,z0,z2,z3,z242,z9])],[(0,[z7,z0,z1,z2,z827,z9]),(0,[z0,z1,z183,z3,z533,z4]),(0,[z808,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z828,z9])],[(0,[z7,z0,z399,z2,z3,z9]),(0,[z7,z0,z1,z2,z829,z9]),(0,[z200,z0,z2,z3,z9,z336]),(0,[z830,z0,z65,z2,z3,z9])],[(0,[z7,z26,z21,z2,z3,z9]),(0,[z7,z0,z8,z2,z3,z291]),(0,[z184,z0,z21,z2,z3,z9]),(0,[z7,z0,z831,z2,z3,z9]),(0,[z0,z1,z2,z832,z3,z9])],[(0,[z15,z0,z1,z2,z140,z9]),(0,[z0,z1,z2,z197,z9,z4]),(0,[z420,z0,z1,z150,z3,z9]),(0,[z188,z0,z21,z2,z3,z9]),(0,[z7,z0,z1,z322,z48,z9])],[(0,[z0,z1,z2,z328,z3,z4]),(0,[z0,z1,z2,z3,z4,z668]),(0,[z7,z0,z1,z2,z232,z9]),(0,[z7,z1,z2,z41,z709,z9])],[(0,[z124,z0,z1,z2,z3,z4])]],
   [[(0,[z11,z0,z1,z2,z3,z9]),(0,[z7,z0,z21,z759,z3,z9]),(0,[z7,z0,z833,z2,z3,z9]),(0,[z7,z0,z2,z3,z242,z9]),(0,[z353,z0,z1,z2,z3,z794]),(0,[z81,z0,z1,z2,z3,z187])],[(0,[z0,z1,z2,z232,z9,z4]),(0,[z223,z0,z8,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z834]),(0,[z835,z0,z1,z2,z3,z9]),(0,[z836,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z3,z837]),(0,[z7,z0,z1,z838,z3,z9]),(0,[z0,z1,z839,z3,z9,z4]),(0,[z0,z1,z105,z2,z71,z4]),(0,[z7,z0,z1,z55,z3,z9]),(0,[z245,z7,z0,z2,z3,z9]),(0,[z7,z0,z840,z2,z3,z9])],[(0,[z0,z8,z2,z3,z32,z4]),(0,[z0,z1,z2,z3,z68,z4]),(0,[z0,z1,z198,z3,z9,z4]),(0,[z6,z0,z1,z2,z806,z9]),(0,[z223,z0,z265,z2,z3,z9]),(0,[z7,z0,z1,z2,z841,z9]),(0,[z842,z0,z1,z2,z3,z9])],[(0,[z329,z7,z0,z137,z3,z9]),(0,[z7,z0,z8,z2,z424,z9]),(0,[z7,z0,z376,z2,z424,z9]),(0,[z7,z0,z1,z164,z739,z9])],[(0,[z7,z0,z8,z2,z140,z9]),(0,[z7,z0,z1,z2,z3,z250]),(0,[z843,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z844,z9]),(0,[z0,z1,z2,z845,z3,z9])],[(0,[z7,z0,z2,z3,z9,z815]),(0,[z6,z0,z1,z2,z3,z599]),(0,[z6,z0,z186,z2,z3,z9]),(0,[z87,z27,z21,z2,z3,z9]),(0,[z691,z7,z21,z2,z3,z9])],[(0,[z7,z0,z846,z2,z3,z9])],[(0,[z7,z0,z1,z2,z847,z9]),(0,[z14,z0,z1,z2,z221,z9]),(0,[z7,z0,z848,z2,z3,z9]),(0,[z7,z0,z1,z849,z3,z9]),(0,[z594,z0,z1,z252,z3,z9]),(0,[z757,z0,z1,z2,z3,z9]),(0,[z23,z7,z24,z2,z39,z9])],[(0,[z7,z0,z1,z2,z3,z850]),(0,[z0,z21,z2,z3,z4,z5]),(0,[z0,z1,z183,z2,z354,z4]),(0,[z7,z0,z392,z2,z3,z9]),(0,[z7,z0,z24,z2,z3,z138]),(0,[z223,z0,z1,z73,z3,z9])],[(0,[z7,z0,z8,z2,z3,z145]),(0,[z0,z1,z851,z2,z3,z9]),(0,[z23,z7,z8,z2,z39,z9]),(0,[z0,z8,z2,z3,z9,z187])],[(0,[z88,z852,z1,z2,z3,z9]),(0,[z0,z228,z1,z2,z3,z156]),(0,[z81,z0,z2,z3,z157,z4]),(0,[z0,z1,z2,z357,z3,z4]),(0,[z0,z1,z2,z342,z9,z4]),(0,[z431,z0,z1,z2,z3,z4]),(0,[z7,z0,z8,z2,z3,z138]),(0,[z853,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z22,z739,z9])],[(0,[z7,z854,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z855]),(0,[z0,z1,z2,z3,z9,z856]),(0,[z200,z0,z2,z3,z100,z4]),(0,[z6,z0,z1,z823,z3,z9]),(0,[z857,z0,z1,z2,z3,z9])],[(0,[z7,z0,z422,z2,z3,z194]),(0,[z0,z521,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z630,z4]),(0,[z7,z0,z1,z2,z3,z858]),(0,[z859,z0,z1,z2,z3,z9]),(0,[z148,z0,z8,z2,z3,z9]),(0,[z7,z0,z8,z122,z3,z9]),(0,[z7,z0,z1,z860,z3,z9]),(0,[z7,z0,z37,z242,z48,z9])],[(0,[z7,z0,z1,z2,z3,z861]),(0,[z862,z7,z0,z2,z3,z9]),(0,[z7,z0,z1,z863,z3,z9]),(0,[z7,z0,z21,z2,z3,z301]),(0,[z79,z7,z8,z18,z3,z9]),(0,[z79,z7,z376,z18,z3,z9])],[(0,[z313,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z72,z3,z9]),(0,[z7,z1,z46,z725,z3,z9]),(0,[z7,z0,z824,z75,z3,z9])]],
   [[(0,[z7,z0,z1,z2,z864,z9])],[(0,[z6,z0,z399,z2,z3,z9]),(0,[z0,z1,z2,z374,z3,z4])],[(0,[z7,z0,z865,z2,z3,z9]),(0,[z0,z1,z2,z866,z9,z4]),(0,[z0,z867,z2,z3,z9,z4]),(0,[z7,z0,z464,z2,z3,z9]),(0,[z7,z0,z392,z73,z3,z9]),(0,[z7,z0,z1,z601,z22,z9])],[(0,[z7,z0,z2,z3,z32,z690]),(0,[z227,z0,z53,z2,z3,z9]),(0,[z0,z1,z2,z868,z3,z9]),(0,[z7,z0,z1,z2,z354,z9]),(0,[z0,z1,z105,z2,z12,z149])],[(0,[z90,z1,z2,z3,z9,z423]),(0,[z6,z0,z1,z2,z232,z9]),(0,[z74,z6,z0,z75,z3,z9]),(0,[z7,z0,z21,z2,z71,z85]),(0,[z7,z0,z1,z2,z3,z869]),(0,[z7,z0,z1,z2,z870,z3])],[(0,[z0,z1,z2,z3,z260,z100]),(0,[z871,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z773,z3,z9])],[(0,[z14,z0,z21,z2,z176,z9]),(0,[z6,z0,z2,z3,z242,z9]),(0,[z0,z1,z2,z872,z3,z9]),(0,[z0,z1,z2,z71,z72,z85])],[(0,[z0,z1,z547,z2,z3,z4])],[(0,[z35,z0,z53,z2,z3,z9]),(0,[z0,z1,z394,z2,z3,z4]),(0,[z0,z265,z2,z3,z9,z4]),(0,[z6,z0,z1,z838,z3,z9]),(0,[z6,z0,z1,z55,z3,z9]),(0,[z873,z0,z1,z2,z3,z9]),(0,[z179,z7,z1,z122,z3,z54])],[(0,[z7,z0,z21,z2,z3,z335]),(0,[z7,z0,z21,z2,z874,z9]),(0,[z7,z0,z8,z2,z875,z9])],[(0,[z7,z0,z21,z876,z2,z3])],[(0,[z7,z0,z1,z2,z3,z877]),(0,[z27,z0,z228,z2,z3,z9]),(0,[z0,z21,z2,z71,z3,z4]),(0,[z0,z47,z2,z3,z9,z4]),(0,[z878,z0,z8,z2,z3,z9])],[],[(0,[z7,z0,z1,z18,z185,z9])],[(0,[z6,z0,z1,z2,z847,z9]),(0,[z248,z7,z0,z202,z3,z9])],[(0,[z7,z0,z1,z879,z3,z9]),(0,[z6,z0,z392,z2,z3,z9]),(0,[z27,z0,z2,z3,z378,z9]),(0,[z880,z0,z1,z2,z3,z9]),(0,[z112,z0,z1,z2,z232,z9])]],
   [[(0,[z35,z0,z1,z57,z3,z9]),(0,[z7,z0,z8,z89,z3,z9]),(0,[z7,z881,z1,z2,z3,z9]),(0,[z7,z0,z21,z802,z3,z9]),(0,[z7,z0,z1,z2,z3,z321])],[(0,[z15,z90,z399,z2,z3,z9]),(0,[z0,z1,z2,z3,z882,z9]),(1,[z0,z1,z2,z3,z822])],[(0,[z101,z0,z59,z2,z3,z9]),(0,[z7,z0,z883,z2,z3,z9])],[(0,[z448,z0,z1,z2,z3,z9]),(0,[z884,z0,z1,z2,z3,z9])],[(0,[z7,z339,z8,z2,z3,z9]),(0,[z6,z0,z1,z2,z3,z657]),(0,[z7,z0,z1,z3,z717,z84])],[(0,[z0,z21,z2,z3,z4,z121]),(0,[z7,z0,z1,z2,z874,z9]),(0,[z7,z0,z376,z2,z185,z9]),(0,[z0,z1,z2,z3,z138,z885])],[(0,[z7,z0,z1,z2,z140,z216]),(0,[z294,z0,z1,z150,z3,z9]),(0,[z7,z0,z1,z876,z2,z3]),(0,[z886,z0,z1,z2,z3,z9])],[(0,[z172,z0,z1,z2,z3,z250]),(0,[z0,z1,z437,z2,z3,z4])],[(0,[z7,z0,z1,z2,z887,z9]),(0,[z6,z0,z464,z2,z3,z9])],[(0,[z117,z0,z1,z2,z3,z4]),(0,[z7,z0,z1,z2,z3,z888]),(0,[z0,z228,z1,z2,z3,z250]),(0,[z6,z0,z1,z2,z354,z9]),(0,[z0,z1,z2,z3,z9,z889]),(0,[z7,z0,z1,z210,z2,z12]),(0,[z7,z0,z1,z2,z9,z890]),(0,[z7,z0,z1,z891,z2,z9])],[(0,[z7,z45,z8,z46,z3,z9]),(0,[z112,z0,z392,z2,z3,z9])],[(0,[z245,z6,z0,z2,z3,z9]),(0,[z7,z0,z1,z892,z2,z9]),(0,[z162,z7,z0,z2,z828,z9])],[(0,[z281,z120,z1,z2,z3,z9]),(0,[z0,z1,z2,z96,z9,z4]),(0,[z0,z1,z2,z893,z3,z9]),(0,[z7,z0,z1,z2,z3,z894]),(0,[z7,z0,z1,z2,z12,z895])],[(0,[z495,z120,z1,z2,z3,z9]),(0,[z470,z0,z1,z2,z3,z9]),(1,[z0,z1,z2,z896,z9])],[(0,[z7,z0,z8,z2,z3,z897]),(0,[z898,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z899])],[(0,[z7,z0,z1,z198,z233,z9])]],
   [[(0,[z7,z0,z900,z2,z3,z9]),(0,[z0,z1,z2,z3,z138,z4]),(0,[z344,z0,z1,z2,z3,z4]),(0,[z27,z0,z36,z2,z3,z9])],[(0,[z7,z0,z1,z2,z3,z901]),(0,[z0,z228,z2,z403,z3,z9]),(0,[z7,z0,z1,z2,z3,z902]),(0,[z0,z21,z2,z3,z903,z9]),(0,[z188,z0,z1,z2,z39,z9]),(0,[z7,z0,z1,z193,z71,z9]),(0,[z7,z0,z1,z2,z895,z3])],[(0,[z7,z0,z21,z2,z3,z291]),(0,[z87,z53,z21,z2,z3,z9]),(0,[z162,z7,z0,z2,z333,z9])],[(0,[z344,z0,z1,z2,z3,z194]),(0,[z88,z264,z1,z2,z3,z9]),(0,[z6,z0,z1,z2,z3,z690]),(0,[z0,z1,z2,z733,z3,z9]),(0,[z546,z7,z0,z2,z3,z208]),(0,[z7,z0,z904,z2,z3,z9]),(0,[z7,z0,z1,z99,z22,z9])],[(0,[z0,z1,z2,z612,z3,z4]),(0,[z23,z188,z1,z2,z39,z9])],[(0,[z7,z0,z1,z2,z905,z9]),(0,[z7,z0,z906,z2,z3,z9]),(1,[z0,z1,z2,z3,z801]),(0,[z6,z0,z1,z879,z3,z9]),(0,[z0,z8,z2,z3,z722,z9])],[(0,[z6,z0,z1,z2,z3,z321]),(0,[z7,z0,z907,z2,z3,z9])],[(0,[z223,z0,z21,z2,z3,z9]),(0,[z0,z1,z908,z2,z3,z9])],[(0,[z35,z0,z298,z2,z3,z9]),(0,[z7,z0,z909,z2,z3,z9]),(0,[z35,z0,z2,z3,z9,z157]),(0,[z173,z0,z8,z2,z260,z9]),(0,[z910,z0,z1,z2,z3,z9]),(0,[z0,z1,z193,z3,z9,z4]),(0,[z101,z0,z1,z2,z3,z301]),(0,[z7,z0,z1,z2,z190,z68]),(0,[z7,z0,z1,z164,z357,z9])],[(0,[z173,z0,z1,z2,z896,z9]),(0,[z0,z21,z2,z3,z9,z4]),(0,[z81,z0,z1,z3,z48,z4]),(0,[z0,z1,z183,z2,z342,z4]),(0,[z7,z0,z21,z55,z3,z9]),(0,[z911,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z822])],[(0,[z7,z0,z912,z2,z3,z9]),(0,[z7,z0,z21,z2,z424,z9]),(0,[z913,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z914]),(0,[z7,z0,z1,z559,z48,z9])],[(0,[z7,z0,z1,z2,z915,z9]),(0,[z916,z7,z0,z21,z3,z9]),(0,[z7,z0,z1,z917,z3,z9])],[(0,[z918,z0,z1,z2,z3,z9]),(0,[z0,z1,z2,z3,z9,z919]),(0,[z7,z0,z518,z151,z3,z9])],[(0,[z0,z8,z105,z2,z3,z4]),(0,[z0,z1,z2,z3,z9,z920]),(0,[z7,z0,z1,z921,z3,z9])],[(0,[z0,z228,z742,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z291]),(0,[z0,z1,z2,z3,z9,z922]),(0,[z0,z1,z2,z923,z9,z4]),(0,[z101,z0,z1,z2,z3,z321]),(0,[z7,z0,z1,z2,z924,z9]),(0,[z74,z7,z0,z824,z3,z9])],[(0,[z7,z0,z298,z57,z3,z9]),(0,[z7,z0,z8,z2,z3,z194]),(0,[z179,z1,z2,z3,z4,z54])]],
   [[(0,[z7,z0,z1,z2,z3,z925]),(0,[z7,z0,z1,z2,z926,z9]),(0,[z466,z0,z1,z3,z9,z469]),(0,[z0,z1,z2,z269,z3,z4])],[(0,[z7,z0,z1,z89,z3,z216]),(0,[z466,z0,z1,z150,z3,z9]),(0,[z927,z7,z0,z2,z3,z9]),(0,[z0,z8,z2,z149,z3,z9])],[(0,[z7,z0,z928,z2,z3,z9]),(0,[z0,z1,z2,z3,z347,z4]),(0,[z7,z0,z196,z217,z3,z9]),(0,[z929,z0,z1,z2,z3,z9])],[(0,[z223,z0,z1,z2,z3,z9]),(0,[z172,z0,z1,z756,z3,z9]),(0,[z0,z2,z3,z9,z4,z930]),(0,[z148,z0,z21,z2,z3,z9])],[(0,[z231,z0,z1,z252,z3,z9]),(0,[z7,z0,z931,z2,z3,z9]),(0,[z7,z0,z8,z2,z342,z9]),(0,[z0,z8,z2,z152,z3,z9]),(0,[z932,z7,z0,z2,z3,z9])],[(0,[z7,z0,z1,z2,z896,z9]),(0,[z7,z0,z1,z933,z3,z9]),(0,[z7,z8,z550,z2,z3,z9]),(0,[z7,z0,z24,z38,z3,z9]),(0,[z7,z0,z196,z151,z3,z9])],[(0,[z88,z200,z0,z2,z3,z9]),(0,[z7,z0,z1,z2,z424,z9])],[(0,[z7,z0,z1,z2,z140,z9]),(0,[z0,z1,z2,z3,z4,z239]),(0,[z418,z7,z1,z18,z3,z9]),(0,[z661,z7,z1,z2,z3,z54])],[(0,[z7,z0,z1,z2,z934,z9]),(0,[z7,z0,z1,z935,z3,z9]),(0,[z0,z1,z2,z3,z801,z4])],[(0,[z7,z0,z1,z2,z936,z9]),(0,[z7,z0,z8,z56,z3,z9])],[(0,[z7,z0,z1,z2,z937,z9]),(0,[z7,z0,z938,z2,z3,z9]),(0,[z7,z0,z21,z2,z354,z9]),(0,[z615,z7,z1,z18,z3,z9])],[(0,[z0,z1,z2,z896,z260,z9]),(0,[z200,z78,z0,z2,z3,z4]),(0,[z871,z0,z2,z3,z9,z4]),(0,[z1,z2,z3,z423,z4,z54]),(0,[z0,z2,z3,z9,z157,z4]),(0,[z7,z574,z1,z46,z3,z9]),(0,[z7,z0,z1,z93,z48,z9])],[(0,[z7,z0,z1,z2,z3,z145]),(0,[z871,z0,z21,z2,z3,z9]),(0,[z7,z0,z1,z2,z939,z9]),(0,[z23,z7,z1,z2,z39,z9])],[(0,[z7,z277,z21,z2,z3,z9]),(0,[z0,z1,z2,z498,z260,z9]),(0,[z7,z0,z1,z2,z3,z801]),(0,[z0,z1,z2,z940,z3,z9]),(0,[z0,z21,z2,z3,z9,z941]),(0,[z7,z0,z1,z2,z3,z942]),(0,[z7,z0,z1,z2,z3,z138])],[],[(0,[z148,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z943,z3,z9]),(0,[z14,z0,z1,z2,z176,z156]),(0,[z7,z0,z1,z122,z3,z9]),(0,[z7,z1,z725,z18,z3,z9]),(0,[z944,z0,z1,z2,z3,z9])]],
   [[(0,[z7,z21,z2,z582,z3,z9]),(0,[z79,z7,z1,z18,z3,z9]),(0,[z7,z363,z1,z2,z41,z9]),(0,[z0,z1,z945,z2,z3,z9]),(0,[z7,z0,z946,z2,z3,z9])],[(0,[z7,z0,z1,z2,z947,z9]),(0,[z6,z0,z1,z2,z3,z4])],[(0,[z6,z0,z8,z2,z3,z4]),(0,[z7,z0,z1,z2,z3,z948]),(0,[z0,z1,z2,z949,z3,z9]),(0,[z184,z0,z59,z2,z3,z9]),(0,[z7,z0,z950,z2,z3,z9]),(0,[z7,z0,z265,z122,z3,z9])],[(0,[z7,z0,z1,z951,z3,z9]),(0,[z231,z0,z1,z2,z3,z100]),(0,[z7,z0,z1,z2,z952,z9]),(0,[z916,z7,z0,z1,z3,z9]),(0,[z7,z0,z1,z602,z48,z9]),(0,[z81,z7,z0,z1,z354,z9])],[(0,[z7,z0,z953,z2,z3,z9]),(0,[z6,z0,z1,z2,z3,z291]),(0,[z263,z264,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z954])],[(0,[z87,z7,z718,z2,z3,z9]),(0,[z245,z7,z0,z151,z3,z9])],[(0,[z0,z8,z53,z2,z3,z9]),(0,[z0,z1,z2,z3,z9,z955])],[(0,[z7,z0,z2,z3,z9,z930]),(0,[z0,z1,z2,z3,z156,z4]),(0,[z7,z0,z21,z2,z3,z321]),(0,[z7,z0,z956,z2,z3,z9]),(0,[z353,z0,z1,z2,z3,z822])],[(0,[z7,z0,z1,z2,z3,z957]),(0,[z0,z1,z2,z724,z71,z3]),(0,[z958,z0,z1,z2,z3,z9]),(0,[z959,z0,z1,z2,z3,z9]),(0,[z7,z0,z960,z2,z3,z9])],[(0,[z231,z0,z1,z756,z3,z9]),(0,[z0,z170,z2,z3,z9,z4]),(0,[z7,z144,z8,z2,z3,z9])],[(0,[z0,z399,z2,z3,z9,z4]),(0,[z448,z0,z21,z2,z3,z9]),(0,[z7,z0,z151,z824,z3,z9]),(0,[z7,z0,z961,z2,z3,z9])],[(0,[z7,z0,z422,z57,z3,z9]),(0,[z0,z1,z693,z2,z3,z4]),(0,[z6,z0,z196,z151,z3,z9]),(0,[z7,z0,z1,z2,z875,z9]),(0,[z7,z528,z8,z2,z3,z9]),(0,[z7,z0,z151,z3,z282,z9]),(0,[z7,z0,z1,z455,z48,z9]),(0,[z962,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z895,z71])],[(0,[z7,z0,z1,z963,z3,z9]),(0,[z7,z606,z21,z2,z3,z9]),(0,[z575,z0,z288,z2,z3,z9]),(0,[z6,z0,z1,z2,z424,z9]),(0,[z964,z0,z1,z2,z3,z9]),(0,[z7,z0,z965,z2,z3,z9]),(0,[z7,z0,z1,z966,z3,z9])],[(0,[z6,z0,z1,z2,z140,z9]),(0,[z0,z1,z2,z697,z3,z4]),(0,[z878,z0,z1,z2,z3,z9]),(0,[z967,z0,z1,z2,z3,z9])],[(0,[z231,z0,z8,z17,z3,z9])],[(0,[z0,z1,z2,z3,z4,z297])]],
   [[(0,[z7,z45,z21,z46,z3,z9]),(0,[z162,z7,z0,z198,z233,z9])],[(0,[z0,z1,z2,z3,z16,z4]),(0,[z7,z8,z118,z2,z3,z9]),(0,[z7,z0,z1,z198,z3,z9]),(0,[z7,z0,z1,z2,z3,z755])],[(0,[z7,z0,z1,z89,z3,z9]),(0,[z0,z228,z399,z2,z3,z9]),(0,[z6,z0,z1,z2,z3,z145]),(0,[z313,z0,z2,z3,z157,z4]),(0,[z0,z1,z2,z30,z3,z4]),(0,[z7,z0,z21,z892,z2,z9]),(0,[z7,z0,z8,z198,z3,z9]),(0,[z968,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z56,z105,z12])],[(0,[z6,z0,z1,z2,z3,z138]),(0,[z6,z0,z1,z2,z3,z801]),(1,[z7,z0,z824,z3,z9]),(0,[z7,z0,z2,z3,z9,z783])],[(0,[z470,z0,z21,z2,z3,z9]),(0,[z969,z0,z1,z2,z3,z9]),(0,[z101,z0,z1,z2,z424,z9]),(0,[z7,z0,z59,z2,z3,z301]),(0,[z7,z0,z1,z2,z435,z85]),(0,[z7,z0,z2,z3,z828,z9])],[(0,[z7,z0,z1,z2,z970,z9]),(0,[z6,z0,z1,z122,z3,z9]),(0,[z971,z0,z1,z2,z3,z9]),(0,[z969,z0,z8,z2,z3,z9])],[(0,[z0,z1,z2,z3,z4,z317]),(0,[z7,z0,z1,z2,z3,z972]),(0,[z7,z0,z973,z2,z3,z9])],[(0,[z108,z1,z2,z3,z4,z54]),(0,[z6,z0,z1,z2,z947,z9])],[(0,[z7,z0,z974,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z975]),(0,[z976,z0,z1,z2,z3,z9]),(0,[z7,z0,z8,z2,z185,z9]),(0,[z184,z0,z1,z2,z3,z301])],[(0,[z7,z0,z1,z2,z977,z9]),(0,[z978,z0,z1,z2,z3,z9])],[(0,[z0,z1,z2,z140,z9,z4]),(0,[z227,z0,z487,z2,z3,z9]),(0,[z7,z0,z979,z2,z3,z9]),(0,[z0,z1,z2,z70,z3,z4]),(0,[z7,z0,z8,z76,z3,z9]),(0,[z7,z0,z59,z2,z3,z321]),(0,[z7,z0,z1,z2,z980,z9])],[(0,[z0,z228,z1,z2,z140,z9]),(0,[z0,z1,z2,z3,z4,z330])],[(0,[z0,z120,z1,z2,z3,z216]),(0,[z0,z1,z2,z590,z3,z4]),(0,[z7,z21,z2,z3,z639,z9]),(0,[z7,z45,z1,z46,z3,z9]),(0,[z7,z676,z1,z46,z3,z9]),(0,[z981,z0,z1,z2,z3,z9]),(0,[z7,z0,z2,z102,z828,z9])],[(0,[z200,z0,z183,z2,z3,z4])],[(0,[z7,z0,z1,z89,z197,z9]),(0,[z7,z0,z1,z2,z3,z982]),(0,[z200,z0,z2,z3,z533,z9]),(1,[z0,z21,z2,z3,z941]),(0,[z7,z355,z21,z2,z3,z9]),(0,[z184,z0,z1,z2,z3,z321]),(0,[z223,z0,z1,z2,z3,z54]),(0,[z7,z0,z983,z2,z3,z9])],[(0,[z7,z0,z1,z2,z984,z9]),(0,[z7,z0,z985,z2,z3,z9])]],
   [[(0,[z7,z0,z1,z2,z3,z897]),(0,[z90,z852,z1,z2,z3,z9]),(0,[z0,z1,z97,z2,z3,z4]),(0,[z0,z1,z99,z2,z3,z4])],[(0,[z7,z0,z2,z3,z986,z9]),(0,[z7,z0,z987,z2,z3,z9]),(0,[z0,z1,z2,z3,z9,z788])],[(0,[z6,z0,z1,z2,z3,z237]),(0,[z761,z0,z1,z2,z3,z9]),(0,[z0,z1,z2,z864,z9,z4])],[(0,[z7,z0,z988,z2,z3,z9]),(1,[z871,z0,z2,z3,z9]),(0,[z496,z7,z0,z2,z434,z9]),(0,[z918,z0,z21,z2,z3,z9]),(0,[z989,z0,z1,z2,z3,z9]),(0,[z0,z1,z2,z3,z990,z9])],[(0,[z991,z7,z0,z1,z3,z9]),(0,[z7,z0,z992,z2,z3,z9]),(0,[z0,z104,z2,z3,z32,z4]),(0,[z188,z0,z1,z2,z3,z335]),(0,[z993,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z3,z994]),(0,[z7,z0,z21,z2,z3,z194]),(0,[z0,z1,z2,z3,z4,z208]),(0,[z23,z6,z1,z2,z39,z9]),(0,[z7,z0,z1,z2,z39,z138]),(0,[z995,z0,z1,z2,z3,z9])],[],[(0,[z6,z0,z1,z198,z3,z9]),(0,[z7,z0,z1,z2,z996,z3])],[(0,[z6,z0,z1,z89,z3,z9]),(0,[z15,z473,z1,z2,z3,z9]),(0,[z7,z0,z1,z997,z3,z9]),(0,[z7,z0,z1,z164,z673,z9]),(0,[z7,z0,z1,z2,z998,z9])],[(0,[z287,z0,z1,z2,z3,z250]),(0,[z79,z6,z1,z18,z3,z9]),(0,[z999,z0,z21,z2,z3,z9]),(0,[z7,z0,z1,z739,z48,z9]),(0,[z7,z0,z1000,z2,z3,z9])],[(0,[z173,z0,z1,z2,z260,z9]),(1,[z0,z1,z2,z3,z941]),(0,[z0,z1,z2,z1001,z3,z9]),(0,[z7,z1002,z1,z2,z3,z9])],[(0,[z0,z1,z56,z3,z9,z4]),(0,[z7,z0,z1,z512,z48,z9]),(0,[z7,z0,z1,z2,z71,z588])],[(0,[z7,z0,z1,z1003,z3,z9]),(0,[z7,z0,z1,z75,z266,z9]),(1,[z7,z0,z1,z2,z895])],[(0,[z87,z6,z21,z2,z3,z9]),(0,[z6,z0,z1,z2,z185,z9]),(0,[z0,z1,z2,z3,z9,z1004]),(0,[z7,z0,z1,z1005,z3,z9])],[(0,[z7,z0,z21,z2,z140,z9]),(0,[z0,z1,z2,z3,z4,z381]),(0,[z1,z2,z3,z68,z4,z54]),(0,[z573,z7,z0,z1,z48,z9])],[(0,[z200,z0,z2,z645,z3,z9]),(0,[z0,z1,z320,z2,z645,z9])]],
   [[],[(0,[z7,z0,z1,z2,z3,z194]),(0,[z14,z0,z1,z2,z3,z100])],[(0,[z430,z0,z1,z17,z3,z9]),(0,[z0,z1,z1006,z2,z3,z9]),(0,[z6,z45,z1,z46,z3,z9]),(0,[z7,z0,z235,z2,z102,z9])],[(0,[z7,z0,z21,z2,z3,z145]),(0,[z23,z7,z21,z2,z39,z9]),(0,[z1007,z0,z1,z2,z3,z9])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z640,z2,z3,z4]),(0,[z0,z105,z2,z3,z157,z4]),(0,[z7,z0,z21,z2,z3,z138]),(0,[z1008,z0,z1,z2,z3,z9]),(0,[z7,z0,z1009,z2,z3,z9])],[(0,[z15,z0,z1,z57,z3,z9]),(0,[z999,z0,z1,z2,z3,z9]),(0,[z7,z1,z2,z3,z709,z9])],[(0,[z741,z7,z0,z2,z3,z9]),(0,[z0,z1,z331,z3,z533,z9]),(0,[z7,z0,z21,z2,z3,z941]),(0,[z7,z0,z21,z122,z3,z9]),(0,[z7,z0,z1,z2,z1010,z9]),(0,[z179,z7,z1,z2,z3,z738]),(0,[z7,z66,z307,z2,z3,z68]),(0,[z7,z0,z1,z2,z342,z9])],[(0,[z0,z196,z151,z3,z9,z4]),(0,[z79,z7,z21,z18,z3,z9]),(0,[z1011,z0,z1,z2,z3,z9]),(0,[z661,z7,z1,z2,z39,z9]),(0,[z7,z0,z1,z1012,z3,z9]),(0,[z1013,z0,z1,z2,z3,z9])],[(0,[z6,z0,z21,z2,z3,z4]),(0,[z7,z0,z8,z2,z266,z9]),(0,[z7,z1014,z1,z2,z3,z9])],[(0,[z162,z0,z2,z233,z9,z4])],[(0,[z7,z0,z8,z38,z3,z9]),(0,[z184,z0,z1,z46,z3,z9]),(0,[z7,z0,z1015,z2,z3,z9])],[(0,[z0,z8,z2,z3,z68,z4]),(0,[z0,z2,z3,z9,z157,z382]),(0,[z7,z0,z1,z56,z3,z9])],[(0,[z0,z1,z2,z498,z9,z314]),(0,[z7,z0,z1016,z2,z3,z9]),(0,[z0,z21,z2,z3,z366,z9])],[(0,[z7,z0,z8,z57,z3,z9]),(0,[z7,z0,z1,z2,z197,z194]),(0,[z0,z1,z2,z3,z4,z54]),(0,[z10,z0,z1,z2,z3,z4]),(0,[z7,z0,z1,z2,z1017,z9])],[(0,[z0,z1,z2,z660,z3,z4]),(0,[z7,z0,z596,z2,z3,z32]),(0,[z7,z0,z21,z2,z1018,z9]),(0,[z0,z1,z2,z3,z68,z187])],[(0,[z7,z0,z1,z2,z1019,z9]),(0,[z7,z0,z214,z1,z3,z84])]],
   [[(0,[z10,z0,z1,z2,z3,z291]),(0,[z81,z0,z1,z3,z4,z84]),(0,[z7,z0,z59,z2,z424,z9]),(0,[z1020,z0,z1,z2,z3,z9]),(0,[z7,z0,z392,z2,z232,z9])],[(0,[z7,z0,z1,z2,z1021,z9]),(0,[z61,z0,z1,z2,z3,z145]),(0,[z0,z1,z1022,z2,z3,z9]),(0,[z222,z7,z0,z2,z333,z9]),(0,[z44,z7,z0,z2,z3,z208]),(0,[z886,z0,z1,z2,z3,z335]),(0,[z0,z1,z2,z3,z1023,z9]),(0,[z7,z0,z1,z2,z739,z9])],[(0,[z6,z0,z1,z1003,z3,z9]),(0,[z7,z0,z1,z2,z3,z941]),(0,[z470,z0,z1,z2,z3,z5])],[],[(0,[z0,z1,z2,z1024,z3,z9]),(0,[z7,z0,z1,z1025,z3,z9]),(0,[z184,z0,z1,z2,z424,z9]),(0,[z0,z1,z2,z3,z1026,z9]),(0,[z188,z0,z1,z55,z3,z9]),(0,[z1027,z0,z1,z2,z3,z9])],[(0,[z6,z0,z1,z2,z3,z605]),(0,[z0,z183,z2,z3,z157,z4])],[(0,[z7,z0,z1,z1028,z3,z9])],[(0,[z6,z0,z1,z2,z3,z194]),(0,[z200,z90,z0,z2,z3,z9]),(0,[z87,z7,z21,z2,z3,z9]),(0,[z0,z8,z2,z72,z3,z9]),(0,[z7,z428,z8,z2,z3,z9])],[(0,[z7,z0,z1029,z2,z3,z9]),(0,[z0,z1,z2,z176,z3,z156]),(0,[z7,z0,z1,z2,z342,z169]),(0,[z0,z21,z2,z3,z9,z1030]),(0,[z7,z0,z21,z198,z3,z9])],[(0,[z7,z0,z21,z89,z3,z9]),(0,[z81,z7,z0,z1,z3,z230]),(0,[z113,z0,z8,z2,z3,z9]),(0,[z7,z107,z8,z2,z3,z9]),(0,[z1031,z7,z0,z2,z3,z9])],[(0,[z7,z163,z1,z2,z41,z9]),(0,[z7,z0,z1,z2,z1018,z9]),(0,[z79,z7,z59,z18,z3,z9]),(0,[z7,z0,z1,z1032,z3,z9])],[(0,[z7,z0,z1,z2,z1033,z9]),(0,[z0,z1,z2,z243,z3,z4]),(0,[z124,z0,z1,z2,z311,z9]),(0,[z0,z1,z2,z3,z9,z1034])],[(0,[z7,z0,z1,z2,z3,z1035]),(0,[z44,z7,z0,z2,z3,z100]),(0,[z7,z0,z1,z804,z3,z9]),(0,[z6,z0,z1,z2,z342,z9]),(0,[z7,z0,z1,z1036,z2,z9]),(0,[z7,z0,z1037,z2,z3,z9])],[(0,[z0,z1,z2,z3,z249,z4]),(0,[z7,z0,z1,z56,z3,z169])],[(0,[z7,z0,z21,z2,z185,z9])],[(0,[z1038,z7,z0,z2,z3,z9]),(0,[z6,z0,z1,z38,z3,z9])]],
   [[(0,[z7,z0,z1,z2,z866,z9]),(0,[z231,z0,z1,z17,z3,z9]),(0,[z0,z1,z2,z3,z4,z121]),(0,[z1039,z0,z1,z2,z3,z9]),(0,[z44,z7,z0,z2,z3,z5])],[(0,[z7,z1040,z1,z2,z3,z9]),(0,[z6,z0,z1,z56,z3,z9]),(0,[z241,z7,z21,z2,z3,z9]),(0,[z7,z0,z1041,z2,z3,z9]),(0,[z1042,z0,z1,z2,z3,z9])],[(0,[z7,z45,z186,z46,z3,z9]),(0,[z830,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z702,z48,z9]),(0,[z7,z0,z2,z3,z1043,z9])],[(0,[z0,z24,z2,z3,z9,z4])],[(0,[z7,z0,z2,z3,z9,z157]),(0,[z1044,z0,z1,z2,z3,z9]),(0,[z188,z0,z464,z2,z3,z9])],[(0,[z88,z120,z1,z2,z3,z194]),(0,[z7,z8,z123,z2,z3,z9]),(0,[z7,z0,z2,z3,z1045,z9])],[(0,[z0,z1,z3,z9,z4,z1046]),(0,[z200,z6,z0,z2,z3,z9]),(0,[z7,z0,z1,z2,z424,z301])],[(0,[z352,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z724,z3,z9]),(0,[z7,z0,z170,z2,z3,z9])],[(0,[z0,z1,z2,z3,z9,z885]),(0,[z0,z229,z2,z102,z9,z4]),(0,[z7,z21,z2,z3,z9,z343])],[(0,[z108,z120,z1,z2,z3,z9]),(0,[z0,z1,z2,z3,z9,z1047]),(0,[z0,z21,z2,z3,z9,z1048]),(0,[z457,z7,z0,z2,z3,z5]),(0,[z7,z0,z1,z2,z185,z9]),(0,[z7,z0,z1,z2,z709,z9]),(0,[z7,z0,z1,z2,z3,z1049])],[(0,[z162,z7,z0,z76,z233,z9]),(0,[z7,z0,z2,z3,z9,z1050])],[(0,[z15,z62,z1,z2,z3,z9]),(0,[z0,z1051,z2,z3,z9,z4]),(0,[z0,z1,z2,z3,z903,z9]),(0,[z7,z0,z1052,z2,z3,z9]),(0,[z7,z0,z1,z193,z41,z9]),(0,[z7,z0,z1,z76,z3,z9])],[(0,[z172,z0,z1,z119,z3,z9]),(0,[z27,z0,z1,z2,z3,z941]),(0,[z0,z1,z1053,z2,z3,z9]),(0,[z179,z223,z1,z2,z3,z54])],[(0,[z7,z0,z1,z57,z3,z216]),(0,[z88,z120,z1,z2,z140,z9]),(0,[z7,z0,z21,z2,z996,z3])],[(0,[z0,z21,z183,z2,z3,z4]),(0,[z7,z0,z1,z2,z190,z9]),(0,[z7,z0,z1,z2,z3,z1054]),(0,[z44,z132,z0,z2,z3,z5])]],
   [[(0,[z226,z7,z21,z2,z3,z9]),(0,[z7,z0,z8,z2,z190,z9]),(0,[z7,z0,z8,z2,z1055,z9]),(0,[z1056,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z55,z3,z335]),(0,[z7,z0,z1057,z2,z3,z9])],[(0,[z173,z0,z21,z2,z260,z9]),(0,[z6,z0,z1,z2,z1033,z9])],[(0,[z7,z0,z1,z2,z1058,z9]),(0,[z0,z1,z2,z3,z9,z1059]),(0,[z7,z0,z265,z2,z190,z9]),(0,[z0,z1,z2,z3,z9,z822])],[(0,[z112,z0,z1,z122,z3,z9]),(0,[z81,z7,z0,z1,z3,z293])],[(0,[z0,z1,z2,z3,z9,z4]),(0,[z7,z0,z1060,z2,z3,z9])],[(0,[z200,z0,z105,z2,z3,z4]),(0,[z7,z0,z561,z2,z3,z348])],[(0,[z0,z1,z135,z2,z3,z100]),(0,[z40,z1,z2,z41,z9,z4]),(0,[z7,z0,z1,z2,z1061,z9]),(0,[z1062,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z3,z1063]),(0,[z1064,z0,z307,z2,z3,z9])],[(0,[z7,z0,z1065,z2,z3,z9]),(0,[z281,z7,z1,z18,z3,z9]),(0,[z1066,z0,z1,z2,z3,z9]),(0,[z0,z21,z2,z3,z9,z370]),(0,[z7,z29,z21,z2,z3,z9]),(0,[z7,z0,z1,z73,z190,z9])],[(0,[z1067,z0,z1,z2,z3,z9]),(0,[z7,z318,z21,z2,z3,z9])],[(0,[z0,z852,z1,z2,z3,z9]),(0,[z0,z120,z1,z2,z3,z156]),(0,[z6,z0,z2,z3,z9,z157]),(0,[z148,z0,z1,z2,z3,z335]),(0,[z7,z0,z1,z1068,z3,z9]),(0,[z7,z0,z1,z3,z9,z717])],[(0,[z1008,z0,z21,z2,z3,z9]),(0,[z1069,z0,z1,z2,z3,z9]),(0,[z179,z7,z1,z2,z190,z54]),(0,[z1070,z0,z1,z2,z3,z9])],[(0,[z1071,z0,z21,z2,z3,z9]),(0,[z0,z21,z2,z3,z9,z382]),(0,[z7,z0,z1,z608,z22,z9])],[(0,[z0,z1,z756,z150,z3,z9]),(0,[z0,z1,z2,z185,z9,z4]),(0,[z0,z1,z76,z3,z9,z4]),(0,[z7,z0,z21,z2,z342,z9]),(0,[z7,z0,z1072,z2,z3,z9]),(0,[z1073,z0,z1,z2,z3,z9])],[(0,[z200,z0,z2,z3,z32,z4]),(0,[z6,z0,z170,z2,z3,z9]),(0,[z7,z0,z560,z151,z3,z9])],[(0,[z88,z0,z1,z2,z3,z100]),(0,[z0,z796,z186,z2,z3,z9]),(0,[z615,z7,z1,z2,z3,z54])]],
   [[(0,[z200,z7,z0,z2,z3,z9]),(0,[z0,z1,z105,z2,z41,z4]),(0,[z0,z1,z2,z342,z3,z4]),(0,[z7,z0,z21,z38,z3,z9]),(0,[z7,z0,z464,z2,z3,z335])],[(0,[z0,z2,z71,z3,z157,z4])],[(0,[z0,z1,z2,z3,z250,z4]),(0,[z0,z1,z1074,z3,z9,z4]),(0,[z6,z0,z1,z76,z3,z9]),(0,[z7,z0,z21,z56,z3,z9]),(0,[z431,z0,z8,z2,z3,z9]),(0,[z1075,z0,z1,z2,z3,z9])],[(0,[z78,z0,z8,z2,z3,z4]),(0,[z0,z1,z2,z3,z348,z4]),(0,[z61,z0,z1,z2,z3,z4])],[(0,[z168,z0,z1,z2,z3,z4]),(0,[z0,z21,z2,z3,z9,z187]),(0,[z0,z1,z2,z1076,z3,z9])],[(0,[z6,z0,z1,z2,z190,z9])],[(0,[z7,z0,z298,z2,z3,z216]),(0,[z7,z0,z1077,z2,z3,z9]),(0,[z457,z7,z0,z2,z3,z121]),(0,[z7,z0,z1,z73,z3,z68])],[(0,[z7,z0,z1,z2,z1078,z9])],[(0,[z0,z1,z2,z3,z9,z941]),(0,[z1071,z0,z1,z2,z3,z9]),(0,[z101,z0,z1,z2,z185,z9]),(0,[z7,z0,z1,z2,z3,z1079]),(0,[z7,z0,z1,z105,z2,z696])],[(0,[z88,z120,z1,z89,z3,z9]),(0,[z647,z0,z1,z2,z260,z9]),(0,[z0,z1,z2,z3,z100,z4]),(0,[z532,z0,z1,z2,z3,z4]),(0,[z0,z1,z122,z3,z9,z4]),(0,[z44,z6,z0,z2,z3,z5]),(0,[z81,z7,z0,z8,z3,z84])],[(0,[z6,z0,z1,z2,z3,z129]),(0,[z223,z0,z1,z2,z232,z9]),(0,[z7,z0,z1,z2,z266,z9]),(0,[z1080,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z3,z1081]),(0,[z7,z0,z1,z1082,z3,z9]),(0,[z0,z1,z367,z2,z3,z4]),(0,[z1083,z0,z1,z2,z3,z9])],[(0,[z405,z0,z228,z2,z3,z9]),(0,[z0,z1,z2,z3,z9,z1084]),(0,[z7,z0,z1,z38,z3,z9])],[(0,[z1085,z0,z1,z2,z3,z9]),(0,[z7,z0,z1086,z2,z3,z9])],[(0,[z35,z0,z288,z2,z3,z9]),(0,[z79,z184,z1,z18,z3,z9])],[(0,[z7,z0,z1,z57,z3,z9]),(0,[z113,z0,z21,z2,z3,z9])]],
   [[(0,[z7,z0,z1,z1087,z3,z9]),(0,[z7,z0,z65,z2,z3,z9])],[(0,[z35,z0,z542,z2,z3,z9]),(0,[z7,z0,z1088,z2,z3,z9]),(0,[z0,z1,z2,z384,z3,z4]),(0,[z179,z112,z1,z2,z3,z54])],[(0,[z0,z1022,z21,z2,z3,z9]),(0,[z0,z1,z2,z3,z9,z1089]),(0,[z7,z0,z21,z2,z3,z1090]),(0,[z7,z0,z315,z2,z3,z32]),(0,[z0,z1,z1091,z2,z3,z9])],[(0,[z0,z1,z2,z203,z3,z4]),(0,[z7,z0,z21,z1036,z2,z9])],[(0,[z0,z1,z2,z205,z3,z4]),(0,[z0,z1,z2,z1092,z3,z9])],[(0,[z7,z0,z1,z3,z9,z1046]),(0,[z7,z40,z65,z2,z41,z9]),(0,[z223,z0,z392,z2,z3,z9])],[(0,[z0,z298,z2,z3,z9,z4]),(0,[z655,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z397,z4]),(0,[z0,z1,z2,z3,z4,z588]),(0,[z1093,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z122,z232,z9]),(0,[z344,z66,z1,z2,z3,z68])],[(0,[z231,z0,z21,z17,z3,z9]),(0,[z7,z1,z2,z3,z68,z738])],[(0,[z0,z120,z1,z2,z3,z250]),(0,[z6,z0,z1,z2,z3,z207]),(0,[z431,z0,z1,z2,z3,z154]),(0,[z7,z0,z1,z46,z354,z9])],[(0,[z0,z1,z2,z3,z771,z4]),(0,[z0,z1,z2,z71,z3,z4]),(0,[z7,z0,z307,z2,z3,z9]),(0,[z0,z1,z2,z3,z9,z1094])],[(0,[z15,z852,z1,z2,z3,z9]),(0,[z7,z0,z1095,z2,z3,z9]),(0,[z7,z25,z21,z2,z3,z9]),(0,[z0,z8,z2,z949,z3,z9]),(0,[z148,z0,z1,z55,z3,z9]),(0,[z7,z0,z1,z2,z190,z54])],[(0,[z7,z0,z1,z57,z197,z9]),(0,[z113,z0,z1,z2,z3,z9]),(0,[z0,z1,z38,z3,z9,z4]),(0,[z1096,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z1097,z3,z9]),(0,[z7,z0,z1098,z2,z3,z9]),(0,[z7,z0,z1099,z2,z3,z9])],[(0,[z0,z2,z3,z9,z4,z1100]),(0,[z7,z1,z718,z2,z3,z9]),(0,[z0,z1,z2,z3,z335,z955])],[(0,[z200,z7,z0,z2,z3,z100]),(0,[z7,z0,z1,z2,z3,z1090]),(0,[z1101,z0,z1,z2,z3,z9]),(0,[z1102,z0,z1,z2,z3,z9])],[(0,[z7,z1103,z1,z2,z3,z9]),(0,[z74,z7,z0,z202,z3,z9]),(0,[z1104,z0,z1,z2,z3,z9]),(0,[z188,z0,z1,z2,z3,z138]),(0,[z7,z66,z47,z2,z3,z68])]],
   [[(0,[z0,z1,z183,z18,z3,z4]),(0,[z6,z0,z1,z2,z266,z9]),(0,[z1105,z0,z1,z2,z3,z9]),(0,[z7,z0,z464,z55,z3,z9])],[(0,[z7,z0,z1,z2,z1106,z9]),(0,[z1107,z0,z1,z2,z3,z9]),(1,[z7,z0,z2,z828,z9]),(0,[z0,z1,z2,z3,z9,z1108])],[(0,[z0,z1,z57,z3,z9,z4]),(0,[z35,z0,z135,z2,z3,z9]),(0,[z200,z7,z0,z2,z3,z5]),(0,[z27,z0,z53,z2,z3,z9]),(0,[z7,z66,z8,z2,z3,z68]),(0,[z7,z0,z1,z48,z499,z9])],[(0,[z0,z1109,z2,z3,z9,z4]),(0,[z1110,z0,z1,z2,z3,z9]),(0,[z7,z0,z21,z76,z3,z9]),(0,[z7,z0,z2,z3,z1111,z9])],[(0,[z27,z0,z21,z2,z3,z941]),(0,[z7,z0,z8,z37,z48,z9])],[(0,[z6,z0,z1,z57,z3,z9]),(0,[z7,z0,z1,z46,z3,z321])],[(0,[z6,z0,z65,z2,z3,z9]),(0,[z7,z0,z21,z2,z190,z9]),(0,[z1112,z7,z0,z2,z3,z9])],[(0,[z7,z0,z298,z2,z3,z9]),(0,[z6,z0,z2,z3,z157,z4]),(0,[z0,z1,z56,z105,z3,z4]),(0,[z7,z0,z1,z2,z895,z85])],[(0,[z81,z0,z1,z164,z3,z4]),(0,[z1113,z0,z1,z2,z3,z9]),(1,[z7,z1,z2,z709,z9]),(0,[z7,z0,z1,z2,z3,z738])],[(0,[z7,z0,z1,z2,z3,z1114]),(0,[z7,z0,z2,z753,z3,z9]),(0,[z0,z1,z267,z2,z3,z4]),(0,[z7,z0,z1,z2,z1115,z9]),(0,[z7,z718,z21,z2,z3,z9]),(0,[z7,z0,z1,z1116,z3,z9])],[(0,[z35,z0,z1,z2,z3,z216]),(0,[z7,z0,z1,z2,z3,z1117]),(0,[z7,z0,z1,z1118,z3,z9]),(0,[z148,z0,z464,z2,z3,z9]),(0,[z7,z0,z1,z1119,z3,z9]),(0,[z0,z1,z2,z3,z9,z1120])],[(0,[z7,z0,z8,z2,z96,z9])],[(0,[z1121,z0,z1,z2,z3,z9]),(0,[z1122,z0,z8,z2,z3,z9]),(0,[z81,z448,z0,z1,z3,z84])],[(0,[z7,z0,z1,z1123,z3,z9])],[(0,[z14,z0,z1,z2,z896,z9]),(0,[z200,z0,z2,z3,z9,z157])],[(0,[z0,z1,z2,z190,z9,z4]),(0,[z6,z0,z307,z2,z3,z9]),(0,[z7,z0,z1,z2,z424,z321])]],
   [[(0,[z7,z0,z1,z1124,z3,z9]),(0,[z7,z0,z1125,z2,z3,z9])],[(0,[z7,z0,z1126,z2,z3,z9]),(0,[z7,z0,z2,z3,z9,z1100]),(0,[z7,z0,z8,z105,z2,z12]),(0,[z0,z1,z2,z3,z301,z1034]),(0,[z7,z0,z1,z2,z3,z783])],[(0,[z7,z0,z1,z2,z1127,z9]),(0,[z287,z0,z1,z2,z3,z4]),(0,[z7,z0,z1,z800,z3,z9]),(0,[z8,z21,z2,z3,z9,z4]),(0,[z313,z0,z487,z2,z3,z9]),(0,[z7,z0,z1,z2,z1055,z9]),(0,[z1128,z0,z1,z2,z3,z9]),(0,[z7,z0,z1129,z2,z3,z9])],[(0,[z7,z0,z298,z2,z197,z9]),(0,[z0,z228,z1,z57,z3,z9]),(0,[z79,z7,z1,z18,z3,z301])],[(0,[z255,z0,z1,z2,z3,z4]),(0,[z1130,z0,z1,z2,z3,z9]),(0,[z7,z0,z59,z2,z185,z9]),(0,[z7,z0,z1,z2,z1131,z9]),(0,[z7,z0,z1,z38,z39,z9]),(0,[z7,z0,z1132,z2,z3,z9])],[],[(0,[z0,z1,z2,z304,z3,z4]),(0,[z7,z0,z1133,z2,z3,z9])],[(0,[z7,z0,z1,z2,z1134,z9]),(0,[z200,z0,z2,z3,z260,z9]),(0,[z0,z21,z105,z2,z3,z4]),(0,[z1135,z0,z1,z2,z3,z9]),(0,[z7,z0,z229,z2,z828,z9]),(0,[z0,z104,z2,z3,z32,z382])],[(0,[z7,z0,z1,z2,z1136,z9]),(0,[z0,z1,z2,z3,z291,z4]),(0,[z184,z0,z1,z2,z185,z9])],[(0,[z27,z0,z1,z2,z3,z1090]),(0,[z49,z0,z8,z2,z3,z9]),(0,[z79,z7,z1,z18,z3,z321])],[(0,[z0,z21,z2,z3,z9,z1137]),(0,[z7,z0,z104,z2,z3,z348]),(0,[z23,z7,z1,z2,z39,z335]),(0,[z245,z7,z0,z2,z102,z9])],[(0,[z0,z1,z2,z150,z3,z100]),(0,[z0,z1,z2,z645,z176,z9]),(0,[z7,z0,z8,z73,z3,z9]),(0,[z162,z7,z0,z2,z266,z9])],[(0,[z910,z0,z1,z2,z3,z4]),(0,[z0,z1,z164,z22,z9,z4]),(0,[z7,z0,z8,z1138,z3,z9]),(0,[z1007,z0,z186,z2,z3,z9]),(0,[z418,z7,z1,z2,z39,z9]),(0,[z0,z229,z2,z102,z366,z9])],[(0,[z6,z0,z298,z2,z3,z9]),(0,[z0,z1,z2,z3,z4,z213]),(0,[z7,z0,z2,z3,z9,z1139])],[(0,[z0,z1,z89,z3,z9,z4]),(0,[z200,z231,z0,z2,z3,z9]),(0,[z0,z1,z2,z492,z3,z4]),(0,[z777,z0,z1,z2,z3,z9]),(0,[z0,z21,z2,z152,z3,z9]),(0,[z405,z0,z240,z2,z3,z9]),(0,[z179,z7,z8,z2,z3,z54]),(0,[z7,z0,z229,z2,z209,z9]),(0,[z79,z101,z1,z18,z3,z9])],[(0,[z7,z0,z1140,z2,z3,z9]),(0,[z287,z0,z1,z119,z3,z9]),(0,[z0,z1,z2,z149,z3,z68])]],
   [[(0,[z35,z0,z135,z2,z3,z100]),(0,[z0,z21,z2,z3,z32,z4]),(0,[z7,z0,z180,z2,z209,z9]),(0,[z179,z7,z265,z2,z3,z54])],[(0,[z117,z0,z1,z2,z3,z216]),(0,[z0,z1,z2,z3,z9,z1141]),(0,[z7,z0,z21,z2,z266,z9]),(0,[z1142,z0,z1,z2,z3,z9]),(0,[z1143,z0,z1,z2,z3,z9])],[(0,[z27,z0,z298,z2,z3,z9]),(0,[z0,z2,z3,z9,z1144,z370])],[(0,[z7,z0,z422,z2,z3,z9]),(0,[z0,z422,z2,z3,z9,z4]),(0,[z200,z0,z2,z3,z68,z4]),(0,[z7,z0,z1,z2,z1145,z9]),(0,[z7,z0,z1,z1146,z3,z9]),(0,[z1147,z0,z1,z2,z3,z9]),(0,[z7,z0,z1148,z2,z3,z9])],[(0,[z0,z1,z756,z2,z3,z9]),(0,[z431,z0,z1,z2,z3,z9]),(0,[z1085,z0,z21,z2,z3,z9]),(0,[z0,z1,z2,z1149,z3,z9])],[(0,[z78,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z346,z4]),(0,[z7,z0,z8,z164,z22,z9]),(0,[z7,z0,z1150,z2,z3,z9]),(0,[z1151,z0,z1,z2,z3,z9]),(0,[z0,z1,z1152,z2,z3,z9])],[(0,[z7,z0,z21,z57,z3,z9]),(0,[z132,z0,z8,z2,z3,z9]),(0,[z179,z7,z1,z73,z3,z54]),(0,[z7,z0,z1,z1153,z3,z9])],[(0,[z0,z1,z2,z3,z366,z9]),(0,[z244,z0,z1,z2,z176,z9]),(0,[z571,z0,z1,z2,z3,z4]),(0,[z7,z0,z1154,z2,z3,z9])],[(0,[z7,z0,z1,z2,z3,z1155])],[(0,[z7,z0,z8,z2,z3,z154]),(0,[z1156,z0,z1,z2,z3,z9]),(0,[z1157,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z105,z2,z895])],[(0,[z7,z0,z1,z2,z3,z1158]),(0,[z0,z1,z2,z3,z301,z4]),(0,[z7,z0,z1,z2,z185,z301]),(0,[z7,z0,z1,z354,z50,z9])],[(0,[z0,z228,z298,z2,z3,z9]),(0,[z0,z228,z2,z3,z9,z157]),(0,[z7,z0,z21,z1159,z3,z9])],[(1,[z852,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z1160])],[(0,[z7,z0,z1161,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z1162]),(0,[z0,z1140,z2,z3,z9,z4]),(0,[z1163,z7,z0,z2,z3,z9]),(0,[z7,z0,z1,z2,z1164,z9])],[(0,[z173,z0,z1,z2,z311,z9]),(0,[z6,z0,z1,z2,z1136,z9])],[(0,[z7,z0,z422,z2,z197,z9])]],
   [[(0,[z7,z0,z1,z1165,z3,z9]),(0,[z1166,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z895,z9])],[(0,[z108,z200,z0,z2,z3,z9]),(0,[z1167,z0,z1,z2,z3,z9]),(0,[z1064,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1168,z2,z3,z9]),(0,[z112,z0,z1,z2,z190,z9])],[(0,[z7,z0,z8,z2,z3,z216]),(0,[z7,z0,z1,z1169,z3,z9]),(0,[z0,z1,z105,z2,z498,z4]),(0,[z871,z7,z0,z2,z3,z9]),(0,[z188,z0,z1,z2,z41,z9])],[(0,[z7,z136,z21,z2,z3,z9]),(0,[z0,z8,z2,z3,z4,z54]),(0,[z0,z2,z3,z32,z157,z4]),(0,[z7,z0,z1170,z2,z3,z9]),(0,[z79,z7,z1,z725,z3,z9]),(0,[z7,z0,z1,z2,z384,z85])],[(0,[z431,z0,z1,z2,z3,z169]),(0,[z7,z0,z1,z2,z1171,z3]),(0,[z7,z0,z1,z2,z70,z85])],[(0,[z7,z0,z1172,z2,z3,z9]),(0,[z0,z1,z2,z368,z260,z9]),(0,[z78,z0,z1,z2,z3,z801]),(0,[z7,z0,z1,z1159,z3,z9]),(0,[z7,z0,z1,z2,z1173,z9])],[(0,[z0,z1,z2,z970,z9,z4]),(0,[z7,z66,z21,z2,z3,z68])],[(0,[z6,z0,z422,z2,z3,z9]),(0,[z7,z0,z1174,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z1175]),(0,[z0,z1006,z21,z2,z3,z9])],[(0,[z1110,z0,z21,z2,z3,z9]),(0,[z1176,z0,z1,z2,z3,z9]),(0,[z23,z7,z1,z55,z39,z9]),(0,[z7,z1,z2,z709,z39,z9])],[(0,[z227,z470,z0,z2,z3,z9]),(0,[z1176,z0,z8,z2,z3,z9]),(0,[z188,z0,z1,z38,z3,z9]),(0,[z7,z0,z1,z55,z3,z138]),(0,[z223,z0,z1,z122,z3,z9])],[(0,[z0,z1,z407,z2,z3,z4]),(0,[z6,z81,z0,z1,z3,z84])],[(0,[z7,z0,z1,z1177,z3,z9]),(0,[z108,z1,z2,z3,z9,z350]),(0,[z7,z0,z1,z1074,z3,z9]),(0,[z7,z0,z1,z151,z266,z9])],[(0,[z7,z0,z21,z2,z1178,z9]),(0,[z7,z0,z2,z828,z233,z9])],[(0,[z79,z7,z1,z18,z424,z9]),(0,[z0,z1,z2,z3,z187,z54])]],
   [[(0,[z35,z470,z0,z2,z3,z9]),(0,[z7,z0,z251,z2,z102,z9])],[(0,[z0,z1,z742,z2,z3,z9]),(0,[z7,z0,z21,z2,z96,z9]),(0,[z168,z7,z0,z1,z3,z84]),(0,[z7,z0,z1,z1179,z3,z9]),(0,[z7,z0,z151,z102,z48,z9])],[(0,[z7,z0,z1051,z2,z3,z9]),(0,[z0,z1,z2,z71,z4,z85]),(0,[z7,z0,z1,z2,z3,z1180])],[(0,[z231,z0,z1,z115,z3,z9]),(0,[z7,z0,z1109,z2,z3,z9])],[(0,[z7,z852,z1,z2,z3,z9]),(0,[z90,z0,z1,z2,z3,z100]),(0,[z227,z0,z1,z2,z3,z100]),(0,[z1181,z0,z1,z2,z3,z9]),(0,[z7,z604,z8,z2,z3,z9]),(0,[z1182,z0,z1,z2,z3,z9]),(0,[z7,z66,z1,z2,z3,z68]),(0,[z7,z0,z392,z122,z3,z9]),(0,[z7,z555,z1,z2,z3,z68])],[(0,[z7,z0,z422,z2,z3,z216]),(0,[z148,z0,z1,z2,z3,z138]),(0,[z7,z0,z2,z3,z9,z1144]),(0,[z7,z0,z1183,z2,z3,z9])],[(0,[z290,z0,z1,z2,z3,z4]),(0,[z0,z2,z3,z9,z1184,z4]),(0,[z6,z0,z1,z1165,z3,z9]),(1,[z7,z1,z2,z3,z738]),(0,[z7,z0,z1,z37,z48,z9])],[(0,[z1185,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1186,z2,z3,z9]),(0,[z7,z0,z784,z2,z3,z9]),(0,[z7,z0,z1,z1187,z3,z9])],[(0,[z0,z228,z2,z3,z380,z9]),(0,[z7,z0,z229,z2,z102,z9]),(0,[z7,z0,z1188,z2,z3,z9]),(0,[z1189,z0,z1,z2,z3,z9]),(0,[z1190,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z1191,z9]),(0,[z200,z323,z0,z2,z3,z9]),(0,[z0,z1,z183,z2,z3,z4]),(0,[z6,z0,z1,z1169,z3,z9]),(0,[z7,z0,z1,z2,z1178,z9]),(0,[z344,z0,z8,z2,z3,z9]),(0,[z23,z7,z464,z2,z39,z9]),(0,[z7,z0,z2,z3,z32,z783])],[(0,[z818,z0,z2,z3,z9,z4]),(0,[z7,z0,z464,z2,z3,z138])],[(0,[z7,z0,z867,z2,z3,z9]),(0,[z0,z1,z2,z3,z4,z343]),(0,[z7,z214,z21,z2,z3,z9]),(0,[z7,z0,z1,z46,z185,z9]),(0,[z7,z0,z2,z3,z783,z5])],[(0,[z7,z0,z1,z2,z1192,z9]),(0,[z7,z0,z1,z2,z96,z9]),(0,[z7,z0,z104,z2,z3,z32])],[(0,[z231,z0,z1,z17,z3,z250]),(0,[z1122,z0,z1,z2,z3,z9]),(0,[z23,z148,z1,z2,z39,z9])],[(0,[z7,z0,z1,z688,z48,z9]),(0,[z245,z7,z0,z198,z3,z9])]],
   [[(0,[z0,z319,z2,z3,z9,z4]),(0,[z27,z0,z21,z2,z3,z1090]),(0,[z1193,z0,z1,z2,z3,z9]),(0,[z1194,z0,z1,z2,z3,z9])],[(0,[z7,z1195,z1,z2,z3,z9])],[(0,[z7,z0,z1,z89,z140,z9]),(0,[z7,z0,z1,z1196,z3,z9])],[(0,[z0,z1,z2,z3,z9,z370]),(0,[z81,z0,z8,z2,z3,z4]),(0,[z79,z1,z18,z3,z9,z4]),(0,[z7,z0,z24,z2,z3,z9]),(0,[z1197,z0,z1,z2,z3,z9]),(0,[z162,z7,z0,z2,z233,z9]),(0,[z7,z0,z1,z105,z2,z12]),(0,[z7,z0,z1198,z2,z3,z9])],[(0,[z1199,z0,z2,z3,z9,z370])],[(0,[z7,z0,z8,z2,z3,z9]),(0,[z0,z1,z2,z939,z9,z4]),(0,[z0,z53,z21,z2,z3,z9]),(0,[z7,z0,z376,z2,z3,z9]),(0,[z0,z1,z2,z3,z9,z1200]),(0,[z7,z1201,z1,z2,z3,z9])],[(0,[z88,z120,z1,z57,z3,z9]),(0,[z0,z638,z1,z150,z3,z9]),(0,[z87,z21,z2,z3,z9,z4]),(0,[z0,z1,z2,z477,z3,z4]),(0,[z200,z0,z2,z3,z9,z314]),(0,[z0,z1,z2,z71,z22,z4]),(0,[z1093,z0,z1,z2,z3,z301])],[(0,[z0,z1,z2,z3,z9,z382]),(0,[z7,z0,z265,z2,z3,z9]),(0,[z7,z0,z1,z38,z3,z335])],[(0,[z35,z0,z1,z2,z3,z156]),(0,[z0,z1,z252,z2,z3,z4]),(0,[z7,z21,z2,z3,z9,z668])],[(0,[z7,z0,z1,z2,z923,z9]),(0,[z0,z1,z2,z176,z896,z9]),(0,[z245,z0,z2,z3,z9,z4]),(0,[z0,z1,z2,z3,z9,z745])],[(0,[z7,z0,z1202,z2,z3,z9]),(0,[z7,z0,z1,z839,z3,z9]),(0,[z6,z66,z1,z2,z3,z68]),(0,[z7,z0,z21,z2,z1145,z9])],[(0,[z49,z0,z1,z2,z3,z9]),(0,[z0,z1,z2,z3,z335,z4]),(0,[z344,z0,z1,z2,z3,z169]),(0,[z431,z0,z21,z2,z3,z9])],[(0,[z78,z0,z21,z2,z3,z4]),(0,[z0,z307,z2,z3,z9,z4]),(0,[z6,z0,z1,z37,z48,z9]),(0,[z132,z0,z21,z2,z3,z9]),(0,[z7,z0,z2,z102,z266,z9]),(0,[z7,z0,z1203,z2,z3,z9])],[(0,[z7,z0,z560,z28,z3,z9]),(0,[z7,z0,z1,z2,z1204,z9]),(0,[z7,z0,z1,z73,z3,z9]),(0,[z1205,z0,z1,z2,z3,z9])],[(0,[z0,z1,z489,z2,z3,z4]),(0,[z0,z21,z2,z149,z3,z9]),(0,[z7,z0,z1,z1138,z3,z9]),(0,[z7,z0,z1,z1206,z3,z9])],[(0,[z0,z1,z2,z3,z9,z187]),(0,[z7,z0,z21,z2,z3,z154]),(0,[z0,z1,z105,z2,z645,z4]),(0,[z6,z0,z229,z2,z102,z9]),(0,[z1207,z0,z1,z2,z3,z9]),(0,[z1208,z0,z1,z2,z3,z9]),(0,[z7,z0,z151,z198,z3,z9])]],
   [[(0,[z0,z8,z2,z3,z4,z208]),(0,[z0,z1,z37,z48,z9,z4]),(0,[z7,z0,z1,z2,z1209,z9]),(0,[z7,z1,z2,z725,z3,z9]),(0,[z7,z0,z1,z1210,z3,z9]),(0,[z179,z7,z1,z2,z3,z54]),(0,[z7,z0,z265,z73,z3,z9])],[(0,[z7,z0,z8,z2,z197,z9]),(0,[z7,z220,z8,z2,z3,z9]),(0,[z0,z1,z2,z3,z801,z9])],[(0,[z44,z0,z2,z3,z4,z5]),(0,[z1211,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z3,z1212]),(0,[z0,z186,z2,z3,z9,z4]),(0,[z6,z0,z1,z2,z1192,z9]),(0,[z6,z0,z1,z2,z96,z9]),(0,[z6,z0,z104,z2,z3,z32]),(0,[z7,z0,z1,z2,z3,z1213])],[(0,[z0,z65,z2,z3,z9,z4])],[(0,[z0,z1,z667,z150,z3,z9]),(0,[z0,z21,z2,z3,z68,z4]),(0,[z862,z0,z2,z3,z9,z4])],[(0,[z7,z433,z8,z2,z3,z9])],[(0,[z353,z0,z229,z2,z102,z9]),(0,[z7,z0,z1,z164,z22,z9]),(0,[z7,z0,z1214,z2,z3,z9])],[(0,[z132,z0,z1,z2,z3,z9]),(0,[z0,z1,z2,z3,z154,z4]),(0,[z323,z1,z2,z3,z9,z423]),(0,[z0,z1,z288,z2,z3,z4])],[(0,[z6,z0,z24,z2,z3,z9]),(0,[z6,z0,z1,z105,z2,z12]),(0,[z7,z0,z1215,z2,z3,z9]),(0,[z373,z0,z53,z2,z3,z9]),(0,[z1216,z0,z1,z2,z3,z9])],[(0,[z0,z21,z2,z3,z754,z9])],[(0,[z7,z0,z1217,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z154]),(0,[z7,z0,z1,z2,z3,z1218]),(0,[z6,z0,z8,z2,z3,z9]),(0,[z0,z1,z2,z3,z516,z4]),(0,[z0,z8,z2,z3,z348,z4]),(0,[z81,z0,z1,z2,z3,z771]),(0,[z6,z0,z376,z2,z3,z9]),(0,[z7,z0,z1219,z2,z3,z9])],[(0,[z227,z0,z228,z2,z3,z9]),(0,[z496,z7,z0,z2,z233,z9]),(0,[z7,z0,z1,z2,z3,z1220]),(0,[z0,z1,z2,z3,z9,z1221]),(0,[z0,z196,z151,z152,z3,z9])],[(0,[z88,z339,z1,z2,z3,z9]),(0,[z6,z0,z265,z2,z3,z9]),(0,[z0,z2,z3,z242,z990,z9])],[(0,[z88,z120,z298,z2,z3,z9]),(0,[z1222,z0,z1,z2,z3,z9]),(0,[z0,z1,z2,z1223,z3,z9])],[(0,[z15,z0,z1,z2,z3,z216]),(0,[z0,z8,z2,z3,z4,z5]),(0,[z7,z0,z1,z2,z1224,z9]),(0,[z7,z66,z1,z2,z3,z738])]],
   [[(0,[z7,z0,z1225,z2,z3,z9]),(0,[z0,z2,z3,z9,z1139,z4]),(0,[z0,z1226,z2,z3,z9,z4]),(0,[z27,z0,z8,z2,z3,z9]),(0,[z7,z0,z1,z34,z48,z9])],[(0,[z7,z0,z1,z2,z140,z194]),(0,[z7,z0,z1227,z2,z3,z9]),(0,[z14,z0,z1,z2,z269,z9]),(0,[z0,z1,z2,z915,z9,z4]),(0,[z0,z21,z2,z72,z3,z9]),(0,[z255,z7,z0,z1,z3,z84])],[(0,[z7,z0,z1228,z2,z3,z9]),(0,[z398,z0,z1,z2,z260,z9]),(0,[z1229,z0,z1,z2,z3,z9])],[(0,[z172,z0,z8,z150,z3,z9]),(0,[z45,z1,z46,z3,z9,z4]),(0,[z0,z1,z2,z71,z48,z4]),(0,[z6,z0,z1,z73,z3,z9]),(0,[z101,z0,z8,z2,z3,z9]),(0,[z353,z0,z8,z2,z3,z9]),(0,[z101,z0,z376,z2,z3,z9]),(0,[z7,z0,z1,z2,z185,z321]),(0,[z7,z0,z2,z102,z389,z9])],[(0,[z0,z21,z2,z3,z378,z4])],[(0,[z245,z7,z0,z2,z266,z9]),(0,[z0,z1,z1230,z2,z3,z9]),(0,[z0,z1,z2,z3,z9,z1231]),(0,[z0,z1,z2,z3,z9,z1232])],[(0,[z7,z0,z1,z2,z3,z216]),(0,[z7,z0,z1,z1233,z3,z9]),(0,[z35,z0,z1,z2,z3,z250]),(0,[z1234,z0,z21,z2,z3,z9]),(0,[z0,z1,z2,z3,z9,z1030]),(0,[z112,z0,z8,z2,z3,z9]),(0,[z0,z1091,z307,z2,z3,z9])],[],[(0,[z0,z1,z2,z3,z194,z4]),(0,[z78,z0,z2,z3,z157,z4]),(0,[z0,z1,z73,z3,z9,z4]),(0,[z66,z1,z2,z3,z68,z4]),(0,[z0,z1,z687,z2,z3,z4]),(0,[z0,z1,z2,z3,z9,z1235]),(0,[z7,z0,z1,z2,z41,z138]),(0,[z0,z1053,z65,z2,z3,z9]),(0,[z10,z81,z0,z1,z3,z84])],[(0,[z578,z0,z1,z2,z260,z9]),(0,[z7,z0,z1236,z2,z3,z9])],[(0,[z15,z90,z1,z2,z3,z9]),(0,[z7,z0,z1237,z2,z3,z9])],[(0,[z35,z0,z393,z2,z3,z9]),(0,[z0,z1,z552,z2,z3,z4])],[(0,[z852,z120,z1,z2,z3,z9]),(0,[z162,z6,z0,z2,z233,z9]),(0,[z113,z0,z1,z2,z3,z788])],[(0,[z0,z120,z1,z2,z140,z9]),(0,[z0,z2,z3,z68,z157,z4]),(0,[z6,z0,z1,z164,z22,z9]),(0,[z6,z0,z8,z2,z3,z169]),(0,[z7,z0,z21,z37,z48,z9])],[(0,[z7,z0,z1,z2,z3,z1238]),(0,[z0,z1,z2,z3,z4,z293]),(0,[z7,z0,z21,z1239,z3,z9]),(0,[z7,z0,z1,z1240,z3,z9])],[(0,[z6,z0,z1215,z2,z3,z9]),(0,[z7,z0,z8,z193,z3,z9])]],
   [[(0,[z7,z0,z1,z1241,z3,z9]),(0,[z344,z0,z21,z2,z3,z9]),(0,[z1242,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1243,z2,z3,z9]),(0,[z678,z7,z21,z2,z3,z9]),(0,[z6,z0,z1,z2,z3,z154]),(0,[z0,z8,z2,z71,z3,z4]),(0,[z1244,z0,z1,z2,z3,z9]),(0,[z148,z0,z1,z38,z3,z9])],[(0,[z7,z0,z8,z2,z3,z156]),(0,[z7,z0,z235,z2,z201,z9]),(0,[z1234,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1245,z2,z3,z9])],[],[(0,[z1246,z0,z1,z2,z3,z9]),(0,[z7,z8,z718,z2,z3,z9]),(0,[z23,z7,z1,z2,z39,z138])],[(0,[z227,z0,z742,z2,z3,z9]),(0,[z74,z7,z0,z198,z3,z9])],[(0,[z231,z0,z1,z17,z3,z291]),(0,[z6,z0,z1227,z2,z3,z9]),(0,[z7,z0,z464,z38,z3,z9])],[(0,[z90,z1,z118,z2,z3,z9]),(0,[z124,z0,z1,z2,z3,z156]),(0,[z0,z1,z2,z3,z9,z1048]),(0,[z7,z0,z1,z73,z3,z54]),(0,[z7,z0,z1,z1247,z3,z9])],[(0,[z313,z0,z1,z2,z3,z100]),(0,[z179,z6,z1,z2,z3,z54]),(0,[z0,z1,z2,z149,z71,z3])],[(0,[z88,z120,z422,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z1248]),(0,[z7,z0,z21,z105,z2,z12]),(0,[z7,z0,z1,z1239,z3,z9]),(0,[z7,z0,z2,z3,z1249,z9]),(0,[z431,z0,z1,z2,z71,z85])],[(0,[z35,z0,z742,z2,z3,z9]),(0,[z0,z1250,z2,z3,z9,z4])],[(0,[z7,z0,z1,z89,z3,z194]),(0,[z6,z0,z1,z2,z3,z216]),(0,[z344,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z1251]),(0,[z0,z1,z83,z2,z3,z4]),(0,[z0,z1,z56,z2,z3,z4]),(0,[z7,z0,z718,z2,z3,z9]),(0,[z7,z0,z1,z1252,z3,z9])],[(0,[z7,z0,z1253,z2,z3,z9]),(0,[z0,z1,z2,z3,z593,z4]),(0,[z0,z1,z1254,z2,z3,z9])],[(0,[z495,z7,z1,z2,z39,z9]),(0,[z0,z1,z2,z3,z321,z4]),(0,[z0,z21,z2,z893,z3,z9])],[(0,[z539,z0,z1,z2,z3,z4])]],
   [[(0,[z491,z0,z1,z2,z3,z4]),(0,[z826,z0,z1,z2,z3,z9])],[],[(0,[z7,z0,z1255,z2,z3,z9]),(0,[z0,z1,z2,z3,z410,z4]),(0,[z0,z1,z105,z2,z3,z4]),(0,[z49,z0,z21,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z1256])],[(0,[z7,z0,z1,z2,z3,z1257]),(0,[z0,z1,z2,z3,z896,z9]),(0,[z7,z0,z324,z217,z3,z9])],[(0,[z7,z0,z1,z2,z3,z1258]),(0,[z0,z1,z2,z110,z3,z4]),(0,[z0,z1,z2,z3,z4,z517]),(0,[z7,z0,z21,z73,z3,z9]),(0,[z7,z0,z1,z2,z1259,z9])],[(0,[z7,z0,z1,z2,z3,z1260]),(0,[z0,z1,z17,z2,z3,z250]),(0,[z81,z0,z1,z2,z3,z4]),(1,[z0,z1,z2,z342,z4]),(0,[z7,z0,z47,z2,z3,z9]),(0,[z0,z1,z2,z3,z9,z1137]),(0,[z7,z0,z1261,z2,z3,z9])],[(0,[z7,z0,z1,z1262,z3,z9])],[(0,[z7,z0,z1,z2,z3,z9]),(0,[z179,z7,z21,z2,z3,z54]),(0,[z7,z0,z1,z2,z1263,z9])],[(0,[z927,z0,z2,z3,z9,z4]),(0,[z7,z0,z1,z2,z1264,z9]),(0,[z7,z0,z1,z2,z3,z1265])],[(0,[z0,z1,z2,z152,z3,z9]),(0,[z761,z0,z1,z2,z3,z4]),(0,[z6,z0,z1245,z2,z3,z9]),(0,[z7,z0,z565,z2,z3,z9]),(0,[z7,z21,z2,z205,z3,z9])],[(1,[z0,z1,z56,z3,z4]),(0,[z7,z544,z8,z2,z3,z9]),(0,[z61,z0,z8,z2,z3,z9])],[(0,[z7,z0,z1,z2,z1266,z9]),(0,[z0,z2,z3,z157,z4,z54]),(0,[z0,z1,z2,z3,z32,z4]),(0,[z184,z0,z1,z18,z3,z9]),(0,[z223,z0,z1,z2,z190,z9]),(0,[z1267,z0,z1,z2,z3,z9])],[(0,[z227,z0,z2,z3,z9,z382]),(0,[z0,z142,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z625,z4]),(0,[z7,z0,z1,z2,z1268,z3]),(0,[z7,z40,z1,z2,z41,z9]),(0,[z7,z0,z1,z824,z3,z9])],[(0,[z7,z0,z1,z1269,z3,z9]),(0,[z7,z0,z1,z2,z1270,z9])],[(0,[z910,z0,z1,z2,z3,z68]),(0,[z7,z0,z21,z164,z22,z9]),(0,[z1199,z7,z0,z2,z3,z9])],[(0,[z7,z0,z1,z2,z1271,z9]),(0,[z0,z8,z2,z3,z9,z4]),(1,[z7,z0,z1,z739,z9])]],
   [[],[(0,[z35,z0,z2,z3,z9,z382]),(0,[z6,z0,z21,z2,z3,z9]),(0,[z74,z7,z0,z75,z266,z9]),(0,[z7,z0,z1,z2,z205,z85])],[(0,[z0,z1,z2,z424,z9,z4]),(0,[z188,z0,z24,z2,z3,z9]),(0,[z1272,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z197,z9]),(0,[z184,z0,z376,z2,z3,z9]),(0,[z79,z7,z1,z18,z185,z9])],[(0,[z7,z0,z1273,z2,z3,z9]),(0,[z991,z0,z1,z3,z9,z4]),(0,[z7,z0,z1250,z2,z3,z9]),(0,[z790,z7,z0,z21,z2,z3]),(0,[z188,z0,z8,z2,z3,z9]),(0,[z7,z0,z392,z2,z190,z9]),(0,[z1274,z7,z0,z2,z3,z9]),(0,[z0,z1,z2,z3,z9,z1275])],[(0,[z7,z0,z2,z3,z1276,z9]),(0,[z7,z0,z1,z1277,z3,z9]),(0,[z470,z0,z1,z2,z3,z32]),(0,[z7,z0,z2,z1278,z3,z9])],[(0,[z7,z0,z1,z1279,z3,z9])],[(0,[z10,z0,z8,z2,z3,z9]),(0,[z1280,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1281,z2,z3,z9]),(0,[z7,z0,z1,z2,z1282,z9]),(0,[z1283,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z193,z12,z9])],[(0,[z7,z0,z1226,z2,z3,z9]),(0,[z0,z1,z2,z3,z650,z4]),(0,[z175,z8,z2,z3,z9,z4]),(0,[z7,z21,z2,z3,z701,z9]),(0,[z353,z0,z21,z2,z3,z9]),(0,[z7,z0,z1284,z2,z3,z9]),(0,[z223,z0,z1,z2,z3,z68]),(0,[z1285,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z1286,z3,z9]),(0,[z126,z0,z1,z2,z3,z4])],[(0,[z0,z2,z3,z9,z4,z1287]),(0,[z6,z0,z47,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z1288]),(0,[z7,z0,z1,z2,z1289,z9])],[(0,[z15,z90,z319,z2,z3,z9]),(0,[z7,z511,z21,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z1290]),(0,[z0,z1,z2,z3,z321,z1089])],[(0,[z6,z0,z1,z2,z3,z9]),(0,[z7,z0,z21,z2,z3,z216]),(0,[z200,z0,z2,z3,z4,z54]),(0,[z7,z0,z1,z2,z342,z4]),(0,[z0,z1,z21,z2,z3,z941]),(0,[z7,z1291,z1,z2,z3,z9]),(0,[z245,z7,z0,z2,z233,z9])],[(0,[z177,z0,z1,z2,z3,z4]),(0,[z0,z2,z3,z242,z9,z4])],[(0,[z35,z0,z399,z2,z3,z9]),(0,[z6,z0,z565,z2,z3,z9]),(0,[z0,z8,z2,z3,z366,z9])]],
   [[(0,[z0,z565,z2,z3,z9,z4])],[(0,[z15,z90,z21,z2,z3,z9]),(0,[z0,z1,z17,z756,z3,z9]),(0,[z7,z0,z713,z2,z3,z9]),(0,[z7,z0,z1,z2,z1292,z9]),(0,[z0,z1,z2,z3,z9,z1293]),(0,[z1294,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z164,z271,z9])],[(0,[z27,z0,z1,z2,z3,z9]),(0,[z0,z1,z210,z2,z3,z4]),(0,[z0,z1,z2,z3,z211,z4]),(0,[z0,z214,z1,z2,z3,z4]),(0,[z7,z0,z1,z56,z3,z4]),(0,[z6,z40,z1,z2,z41,z9]),(0,[z7,z0,z8,z2,z3,z775]),(0,[z7,z0,z1,z2,z3,z1295]),(0,[z7,z0,z104,z2,z3,z783])],[(0,[z0,z1,z2,z3,z4,z442]),(0,[z6,z0,z21,z2,z3,z169]),(0,[z7,z506,z1,z2,z3,z68]),(0,[z7,z0,z1,z18,z3,z321])],[(0,[z541,z0,z542,z2,z3,z9])],[(0,[z101,z0,z1,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z1296]),(0,[z7,z0,z1,z2,z1297,z9]),(0,[z7,z0,z1,z2,z3,z100]),(0,[z353,z0,z1,z2,z3,z9]),(0,[z172,z0,z1,z150,z3,z9]),(0,[z7,z0,z1298,z2,z3,z9]),(0,[z7,z0,z21,z193,z3,z9]),(0,[z7,z0,z376,z2,z3,z301])],[(0,[z7,z0,z1,z2,z1299,z9]),(0,[z7,z0,z8,z2,z3,z100]),(0,[z7,z0,z2,z3,z9,z1184])],[(0,[z7,z0,z1300,z2,z3,z9]),(0,[z7,z0,z1,z2,z3,z1301]),(0,[z7,z0,z1302,z2,z3,z9]),(0,[z0,z1,z2,z3,z4,z453])],[(0,[z35,z0,z1,z2,z140,z9]),(0,[z112,z0,z1,z2,z3,z9]),(0,[z200,z0,z135,z2,z3,z9]),(0,[z173,z0,z1,z2,z3,z156])],[(0,[z6,z0,z1,z2,z197,z9]),(0,[z0,z1,z684,z2,z3,z4]),(0,[z1303,z0,z1,z2,z3,z9])],[(0,[z7,z0,z1,z2,z3,z1304]),(0,[z7,z0,z1,z2,z1305,z9]),(0,[z200,z0,z2,z150,z3,z9]),(0,[z0,z1,z105,z2,z39,z4]),(0,[z316,z0,z1,z2,z3,z4]),(0,[z23,z7,z1,z2,z709,z9])],[(0,[z7,z0,z8,z2,z71,z85]),(0,[z7,z0,z1306,z2,z3,z9]),(0,[z112,z0,z265,z2,z3,z9])],[(0,[z88,z120,z8,z2,z3,z9]),(0,[z0,z1,z105,z193,z3,z4]),(0,[z0,z1,z105,z2,z12,z4]),(0,[z7,z0,z2,z824,z3,z9]),(0,[z7,z0,z1,z198,z102,z9])],[(0,[z15,z0,z1,z2,z3,z156]),(0,[z14,z0,z8,z2,z176,z9]),(0,[z329,z7,z0,z75,z3,z9]),(0,[z1130,z0,z1,z2,z3,z321]),(0,[z7,z45,z170,z46,z3,z9]),(0,[z1307,z0,z1,z2,z3,z9])],[(0,[z7,z0,z24,z2,z3,z335]),(0,[z7,z413,z1,z2,z41,z9])],[(0,[z7,z0,z1,z57,z140,z9]),(0,[z6,z0,z1,z2,z3,z169]),(0,[z7,z0,z2,z3,z9,z1287])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 493) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 493).take 498) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 991).take 438) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1429)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [493, 498, 438] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 127).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 127).take 113).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 240).take 135).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 375).take 126).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 501).take 11).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [127, 113, 135, 126, 11] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_37579

theorem PEqualNP.Outside.L_meta_37579 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276791968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276791968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37579.solve
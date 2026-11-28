import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37865

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
  Nat.testBit (4277074664 * 2 ^ 32 + 4274846336) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x4008c10dc1984561#64 ++ 0x020046086e0cc22b#64 ++ 0xa059c71fc3984ffb#64 ++ 0xfd02ce38fe1cc27f#64 : BitVec 256),
   (0x80822462842b8ca8#64 ++ 0x3404112314215c65#64 ++ 0x71a624e38cff8cff#64 ++ 0x7b8d31271c67fc67#64 : BitVec 256),
   (0x023808b450e0d0d1#64 ++ 0x9811c045a2870686#64 ++ 0xee3838fc70e1f0f7#64 ++ 0xd771c1c7e3870f87#64 : BitVec 256),
   (0x05c036002e012a02#64 ++ 0x202e01b001700950#64 ++ 0xefc03f007f01ff1e#64 ++ 0xcf7e01f803f80ff8#64 : BitVec 256),
   (0x077d40007bd40003#64 ++ 0xc03bea0003dea000#64 ++ 0xf7ffc0007ffe000e#64 ++ 0x3fbffe0003fff000#64 : BitVec 256),
   (0x0ff7bfdb0000001c#64 ++ 0x007fbdfed8000000#64 ++ 0xffffffff80000001#64 ++ 0xfffffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 2]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [9, 1]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0008002450e0d0c1 0x9800400122870686 0x0000000070e1f0f6 0x0000000003870f87

def z1 : W := mkw 0x0230089000000010 0x0011804480000000 0xee3838fc00000001 0xd771c1c7e0000000

def z2 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xefc03f007f01ff1e 0xcf7e01f803f80ff8

def z3 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xf7ffc0007ffe000e 0x3fbffe0003fff000

def z4 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffffffff80000001 0xfffffffffc000000

def z5 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xa059c71fc3984ffb 0xfd02ce38fe1cc27f

def z6 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x71a624e38cff8cff 0x7b8d31271c67fc67

def z7 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xee3838fc70e1f0f7 0xd771c1c7e3870f87

def z8 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x118604038cff8cfe 0x288c30201c67fc67

def z9 : W := mkw 0x0008400041900001 0x00004200020c8000 0xa059c0004398000a 0x3d02ce00021cc000

def z10 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0xffffffffff01ff1f 0xfffffffffff80ff8

def z11 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0x0019c01f809800e1 0x3000ce00fc04c007

def z12 : W := mkw 0x023d400051d40001 0xc011ea00028ea000 0x71bfc0000cfe000e 0x3b8dfe000067f000

def z13 : W := mkw 0x054012002a002202 0x002a009001500110 0x8e401b0073007300 0x847200d803980398

def z14 : W := mkw 0x0775000000000000 0x003ba80000000000 0xf7ffc0000cfe000e 0x3fbffe000067f000

def z15 : W := mkw 0x8ff7bffb842b8cbc 0x347fbdffdc215c65 0xffffffff8cff8cff 0xfffffffffc67fc67

def z16 : W := mkw 0x0000000000000000 0x0000000000000000 0xee00380000000000 0xc77001c000000000

def z17 : W := mkw 0x0000810900000000 0x0000040848000000 0x0019c01f80000001 0x3000ce00fc000000

def z18 : W := mkw 0x054000002e012a02 0x202a000001700950 0xe7c000007f01ff1e 0x0f3e000003f80ff8

def z19 : W := mkw 0x0000000000000000 0x0000000000000000 0x080038000001f010 0xc04001c000000f80

def z20 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0x0041c703c3984ffa 0x28020e381e1cc27f

def z21 : W := mkw 0x0dc7b74b0000000c 0x006e3dba58000000 0xb1dfc71f80000001 0xfd8efe38fc000000

def z22 : W := mkw 0x000808b440a0d0d1 0x18004045a2050686 0xa81838fc4081f0f3 0xd540c1c7e2040f87

def z23 : W := mkw 0x0000000000000000 0x0000000000000000 0x71a600000cfe000e 0x3b8d30000067f000

def z24 : W := mkw 0x87ff6462ffff8cab 0xf43ffb2317fffc65 0xf7ffe4e3ffff8cff 0x7fbfff271ffffc67

def z25 : W := mkw 0x023d400051d40001 0xc011ea00028ea000 0x0019c00000000000 0x0000ce0000000000

def z26 : W := mkw 0x4080b70d84096f60 0x220405b86c204b7b 0x08003f1f8001fff1 0xc04001f8fc000fff

def z27 : W := mkw 0x80020062802a84a8 0x1400100314015425 0x102600e380fe00e1 0x308130071c07f007

def z28 : W := mkw 0x85c23662ae2baeaa 0x342e11b315715d75 0xffe63fe3ffffffff 0xffff31ff1fffffff

def z29 : W := mkw 0x07f7244200000008 0x003fb92210000000 0xf7ffe4e380000001 0x7fbfff271c000000

def z30 : W := mkw 0x0f751a9000000014 0x007ba8d480000000 0x0e00180000000000 0x007000c000000000

def z31 : W := mkw 0x023008b000208090 0x1011804580010404 0xee3838fc00e180f7 0xd771c1c7e0070c07

def z32 : W := mkw 0x0238000050c00001 0x8011c00002860000 0xe638000070e00006 0x1731c00003870000

def z33 : W := mkw 0x077d48b47bf4d0d3 0xd83bea45a3dfa686 0xfffff8fc7ffff0ff 0xffffffc7e3ffff87

def z34 : W := mkw 0x0080360004012a00 0x200401b000200950 0xee003f007001ff16 0xc77001f803800ff8

def z35 : W := mkw 0x0082246200208088 0x1004112310010404 0x71a624e380e180f7 0x7b8d31271c070c07

def z36 : W := mkw 0x40084004c1984561 0x02004200260cc22b 0xa018001c43984ffb 0xd500c000e21cc27f

def z37 : W := mkw 0x0000002000208080 0x1000000100010404 0x602020e000e180f7 0x5301010700070c07

def z38 : W := mkw 0x82ba2cf6d4ebdcf9 0xbc15d167b6a75ee7 0xffbe3cfffcfffcff 0xfffdf1e7ffe7ffe7

def z39 : W := mkw 0x4000810d80084560 0x020004086c00422b 0x0000071f80004ff1 0xc0000038fc00027f

def z40 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000040000000c1a 0x4900002000000060

def z41 : W := mkw 0x077500003a440002 0xc03ba80001d22000 0x57a600003c660004 0x02bd300001e33000

def z42 : W := mkw 0x0fff3ef650e0d0dd 0x987ff9f7b2870686 0xffbe38fc70e1f0f7 0xd7fdf1c7e3870f87

def z43 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0x09c03f000f01ff18 0xc84e01f800780ff8

def z44 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0x8659c00073000000 0x0432ce0003980000

def z45 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0x103fc0ff80000001 0x3081fe07fc000000

def z46 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0x57bfc0003cfe0004 0x32bdfe0001e7f000

def z47 : W := mkw 0x023d400051d40001 0xc011ea00028ea000 0xb07fc00043fe000a 0x3d83fe00021ff000

def z48 : W := mkw 0x0fffffff7bf4d0df 0xd87ffffffbdfa686 0xfffffffffffff0ff 0xffffffffffffff87

def z49 : W := mkw 0x07f83e947ec17a53 0xa83fc1f4a3f60bd2 0xefd83f1c7f01ff1e 0xcf7ec1f8e3f80ff8

def z50 : W := mkw 0x0238089450c05051 0x8811c044a2860282 0x8e18181c70007000 0x8470c0c0e3800380

def z51 : W := mkw 0x077d48947bd45053 0xc83bea44a3dea282 0xffffd81c7ffe700e 0xbffffec0e3fff380

def z52 : W := mkw 0x0000000000000000 0x0000000000000000 0xee0038007001f016 0xc77001c003800f80

def z53 : W := mkw 0x07f83eb47ee1fad3 0xb83fc1f5a3f70fd6 0xeff83ffc7fe1ffff 0xdf7fc1ffe3ff0fff

def z54 : W := mkw 0x05c0360000000000 0x002e01b000000000 0x4f80380000000000 0x027c01c000000000

def z55 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0xf1e627e3cfffcfff 0xff8f313f1e7ffe7f

def z56 : W := mkw 0x00000020802884a0 0x1000000104014425 0x602024e380f98cff 0x7b0101271c07cc67

def z57 : W := mkw 0x40084004c1984561 0x02004200260cc22b 0x00000000009800e0 0x000000000004c007

def z58 : W := mkw 0x0fffffdb7bd4001f 0xc07ffffedbdea000 0xfffffffffffe000f 0xfffffffffffff000

def z59 : W := mkw 0x40084004c1984561 0x02004200260cc22b 0x0000000043984ffa 0x00000000021cc27f

def z60 : W := mkw 0x0882bfdb0000001c 0x004415fed8000000 0x08003fff80000001 0xc04001fffc000000

def z61 : W := mkw 0x0f759b9900000014 0x007bacdcc8000000 0x8e59db1c00000000 0x8472ced8e0000000

def z62 : W := mkw 0x0ff7bfdb3a44001e 0xc07fbdfed9d22000 0xffffffffbc660005 0xfffffffffde33000

def z63 : W := mkw 0x0ff5bf992e012a16 0x207fadfcc9700950 0xefd9ff1c7f01ff1e 0xcf7ecff8e3f80ff8

def z64 : W := mkw 0x4548d30d6b906343 0x022a46986b5c831a 0x8e59db1c73007300 0x8472ced8e3980398

def z65 : W := mkw 0x07fd76007fd52a03 0xe03febb003fea950 0xfffff8007fffb00e 0x3fffffc003fffd80

def z66 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x51a624e38c678cf5 0x428d31271c633c67

def z67 : W := mkw 0x07f536003e452a02 0xe03fa9b001f22950 0xffe63f007f67ff1e 0xcfff31f803fb3ff8

def z68 : W := mkw 0x40084024d1f8d5e1 0x9a004201268fc6af 0x0000000073f9fffe 0x00000000039fcfff

def z69 : W := mkw 0x4238c9bdd1f8d5f1 0x9a11c64dee8fc6af 0xee79fffff3f9ffff 0xff73cfffff9fcfff

def z70 : W := mkw 0x4000c10981180520 0x020006084c08c029 0x0041c70383180f08 0x28020e381c18c078

def z71 : W := mkw 0x80822442840b0c28 0x2404112214205861 0x118604038c1e0c08 0x288c30201c60f060

def z72 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x000024e380018cf1 0x400001271c000c67

def z73 : W := mkw 0x80000020842b8ca0 0x3400000104215c65 0x000000000cff8cfe 0x000000000067fc67

def z74 : W := mkw 0x4008c10d41904141 0x020046086a0c820a 0xa059c31c4398430a 0xbd02ce18e21cc218

def z75 : W := mkw 0x4f7ddb9dc1984575 0x027beedcee0cc22b 0xae59df1fc3984ffb 0xfd72cef8fe1cc27f

def z76 : W := mkw 0x023008b010609090 0x9811804580830484 0x6e2038e030e1b0f7 0x537101c701870d87

def z77 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0xffa63ce3fcfffcff 0xfffd31e71fe7ffe7

def z78 : W := mkw 0x077d48907bd40013 0xc03bea4483dea000 0xfffff8fc7ffe000f 0xffffffc7e3fff000

def z79 : W := mkw 0x0000810900000000 0x0000040848000000 0xa059c71f80000001 0xfd02ce38fc000000

def z80 : W := mkw 0x0882bfdb04012a1c 0x204415fed8200950 0x08003fff8001ff11 0xc04001fffc000ff8

def z81 : W := mkw 0x477dc10dc1984561 0x023bee086e0cc22b 0xf7ffc71fc3984ffb 0xffbffe38fe1cc27f

def z82 : W := mkw 0x0000000000000000 0x0000000000000000 0x8e00180070007000 0x847000c003800380

def z83 : W := mkw 0x0230000000000000 0x0011800000000000 0xe638000000000000 0x1731c00000000000

def z84 : W := mkw 0x4238c9bdd1f8d5f1 0x9a11c64dee8fc6af 0x0039c0ff80f800e1 0x3001ce07fc07c007

def z85 : W := mkw 0x0082244200000008 0x0004112210000000 0x71a624e380000001 0x7b8d31271c000000

def z86 : W := mkw 0x0000000000000000 0x0000000000000000 0x6020000000e00006 0x1301000000070000

def z87 : W := mkw 0x0000000000000000 0x0000000000000000 0x1026000000fe0000 0x308130000007f000

def z88 : W := mkw 0x05c0360000000000 0x002e01b000000000 0xefc03f0000000000 0xcf7e01f800000000

def z89 : W := mkw 0x85c236622e23aa8a 0x342e11b311711d54 0x5fa638e03c67b004 0x02fd31c701e33d80

def z90 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0x0059c71f83980fe9 0x3802ce38fc1cc07f

def z91 : W := mkw 0x000000240020d0c0 0x1800000120010686 0x000000000001f0f0 0x0000000000000f87

def z92 : W := mkw 0x0008002450e0d0c1 0x9800400122870686 0x0000000000e000e0 0x0000000000070007

def z93 : W := mkw 0x4000810d00004140 0x020004086800020a 0x0000031c00004300 0x80000018e0000218

def z94 : W := mkw 0x477dc109fbdc0523 0xc23bee084fdee029 0xf7ffc703fffe0f0e 0x3fbffe381ffff078

def z95 : W := mkw 0x8ff7bfdb840b0c3c 0x247fbdfedc205861 0xffffffff8c1e0c09 0xfffffffffc60f060

def z96 : W := mkw 0x0000000000000000 0x0000000000000000 0xa040070043004f1a 0xcd02003802180278

def z97 : W := mkw 0x45c8f70def996f63 0x222e47b86f7ccb7b 0xefd9ff1fff99ffff 0xff7ecff8fffccfff

def z98 : W := mkw 0x0080360004012a00 0x200401b000200950 0x0000070000000f00 0x0000003800000078

def z99 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0x0019c71f80984ff1 0xf000ce38fc04c27f

def z100 : W := mkw 0x80823662842baea8 0x340411b314215d75 0x79a63fe38cffffff 0xfbcd31ff1c67ffff

def z101 : W := mkw 0x8fffbfffd4ebdcfd 0xbc7ffdfffea75ee7 0xfffffffffcfffcff 0xffffffffffe7ffe7

def z102 : W := mkw 0x023d400051d40001 0xc011ea00028ea000 0x103fc00000fe0000 0x3081fe000007f000

def z103 : W := mkw 0x4008c10d41904141 0x020046086a0c820a 0x8059c31c43004300 0x8402ce18e2180218

def z104 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffffffff8cfe000f 0xfffffffffc67f000

def z105 : W := mkw 0x80020042800a0428 0x0400100214005021 0x10060003801e0000 0x208030001c00f000

def z106 : W := mkw 0x47fdf70dffdd6f63 0xe23fefb86ffeeb7b 0xffffff1fffffffff 0xfffffff8ffffffff

def z107 : W := mkw 0x0000000000000000 0x0000000000000000 0x602020e000000001 0x5301010700000000

def z108 : W := mkw 0x0000000004012a00 0x2000000000200950 0x000000000001ff10 0x0000000000000ff8

def z109 : W := mkw 0x80020062802a84a8 0x1400100314015425 0x71a600e38cfe00ef 0x3b8d30071c67f007

def z110 : W := mkw 0x0000000080080420 0x0000000004004021 0x2000040380980cfb 0x790000201c04c067

def z111 : W := mkw 0x054840007bd40003 0xc02a420003dea000 0xe7c000007ffe000e 0x0f3e000003fff000

def z112 : W := mkw 0x80822442840b0c28 0x2404112214205861 0x71a624e38c1e0c09 0x7b8d31271c60f060

def z113 : W := mkw 0x4dcff74fc198456d 0x026e7fba7e0cc22b 0xb1dfc71fc3984ffb 0xfd8efe38fe1cc27f

def z114 : W := mkw 0x07f03eb03e61ba92 0xb83f81f581f30dd4 0xefe03fe07f61ff1e 0xcf7f01ff03fb0ff8

def z115 : W := mkw 0x023008b010609090 0x9811804580830484 0x4e2038e03061b004 0x027101c701830d80

def z116 : W := mkw 0x077d48947bd45053 0xc83bea44a3dea282 0x8e59d81c73007000 0x8472cec0e3980380

def z117 : W := mkw 0x077d40047bd44043 0xc03bea0023dea202 0xf7ffc01c7ffe40ff 0xffbffe00e3fff207

def z118 : W := mkw 0x0008002450e0d0c1 0x9800400122870686 0xee00380070e1f0f6 0xc77001c003870f87

def z119 : W := mkw 0x05c03600ae092e22 0x202e01b005704971 0xefc03f03ff99ffff 0xff7e01f81ffccfff

def z120 : W := mkw 0x80020062802a84a8 0x1400100314015425 0x000000e3800000e1 0x000000071c000007

def z121 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xee783ffc73e1ffff 0xdf73c1ffe39f0fff

def z122 : W := mkw 0x05c0360004012a00 0x202e01b000200950 0xefc03f000001ff10 0xcf7e01f800000ff8

def z123 : W := mkw 0x08823ed20000001c 0x004411f690000000 0x080038e000000000 0x004001c700000000

def z124 : W := mkw 0x80000000840b0c20 0x2400000004205861 0x000000000c1e0c08 0x000000000060f060

def z125 : W := mkw 0x077500002a000002 0x003ba80001500000 0xf7ffc0007f00000e 0x3fbffe0003f80000

def z126 : W := mkw 0x0002004200000008 0x0000100210000000 0x102600e380000001 0x308130071c000000

def z127 : W := mkw 0x0a35899900000014 0x0051ac4cc8000000 0x0019c01c00000000 0x0000ce00e0000000

def z128 : W := mkw 0x07fd76007fd52a03 0xe03febb003fea950 0xefd9ff007f01ff1e 0xcf7ecff803f80ff8

def z129 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xd7ffc0007f660004 0x06bffe0003fb3000

def z130 : W := mkw 0x423dc10dd1dc4561 0xc211ee086e8ee22b 0x103fc01f80fe00e1 0x3081fe00fc07f007

def z131 : W := mkw 0x02ba2cf650e0d0d9 0x9815d167b2870686 0xffbe3cfff0e1f0f7 0xfffdf1e7ff870f87

def z132 : W := mkw 0x0dc7b74b0000000c 0x006e3dba58000000 0x11c7c70380000000 0x288e3e381c000000

def z133 : W := mkw 0x0230089000000010 0x0011804480000000 0xee3838fc7001f017 0xd771c1c7e3800f80

def z134 : W := mkw 0x8a3789fb802a84bc 0x1451bc4fdc015425 0x103fc0ff80fe00e1 0x3081fe07fc07f007

def z135 : W := mkw 0xc082e54b851b0d28 0x2604172a5c28d869 0x11c7c7038f1e0f08 0x288e3e381c78f078

def z136 : W := mkw 0x0008400041900001 0x00004200020c8000 0xf1ffc0004ffe000e 0x3f8ffe00027ff000

def z137 : W := mkw 0x4000c10981180520 0x020006084c08c029 0x2041c70383980ffb 0x79020e381c1cc07f

def z138 : W := mkw 0x477dc10dfbdc4563 0xc23bee086fdee22b 0xf7ffc71ffffe4fff 0xffbffe38fffff27f

def z139 : W := mkw 0x8082246204238888 0x3404112310211c44 0x51a620e00c678004 0x028d310700633c00

def z140 : W := mkw 0xc00ac16fc1bac5e9 0x1600560b7e0dd62f 0x103fc0ff80fe00e1 0x3081fe07fc07f007

def z141 : W := mkw 0x0238000050c00001 0x8011c00002860000 0x0038000000e00000 0x1001c00000070000

def z142 : W := mkw 0x077808b47ae0d0d3 0x983bc045a3d70686 0xeff838fc7fe1f0ff 0xdf7fc1c7e3ff0f87

def z143 : W := mkw 0x023008b40020d0d0 0x18118045a0010686 0xee3838fc0001f0f1 0xd771c1c7e0000f87

def z144 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0x61c027000f018f1e 0x4b0e013800780c78

def z145 : W := mkw 0x87ff6442ffdf0c2b 0xe43ffb2217fef861 0xf7ffc403fffe0c0e 0x3fbffe201ffff060

def z146 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0x4e3838fc30e1b0e5 0x1271c1c7e1870d87

def z147 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0x5fbff8ff80000001 0x32fdffc7fc000000

def z148 : W := mkw 0x000008b40020d0d0 0x18000045a0010686 0x682038fc00e1f0f7 0xd34101c7e0070f87

def z149 : W := mkw 0x054d40007bd40003 0xc02a6a0003dea000 0x11c7c0007ffe000e 0x288e3e0003fff000

def z150 : W := mkw 0x0ff73ed20000001c 0x007fb9f690000000 0x5fa638e000000000 0x02fd31c700000000

def z151 : W := mkw 0x05c236422e012a0a 0x202e11b211700950 0xffe63fe3ff01ff1f 0xffff31ff1ff80ff8

def z152 : W := mkw 0x80822442840b0c28 0x2404112214205861 0x71a604038cfe0c0e 0x3b8d30201c67f060

def z153 : W := mkw 0x0fffffdb51d4001d 0xc07ffffeda8ea000 0xffffffff80fe0001 0xfffffffffc07f000

def z154 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0x2019c41f80980cfb 0x7900ce20fc04c067

def z155 : W := mkw 0x000000002e012a02 0x2000000001700950 0x000000007f01ff1e 0x0000000003f80ff8

def z156 : W := mkw 0x077d40207bf48083 0xd03bea0103dfa404 0xf7ffe0e07fff80ff 0x7fbfff0703fffc07

def z157 : W := mkw 0x0ff73ed22e012a1e 0x207fb9f691700950 0x5fa638e03c01b004 0x02fd31c701e00d80

def z158 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0xffffffffbc01b005 0xfffffffffde00d80

def z159 : W := mkw 0x80822442840b0c28 0x2404112214205861 0x0000040380000c00 0x000000201c000060

def z160 : W := mkw 0x0ff73ed20000001c 0x007fb9f690000000 0xffbe38fc00000001 0xd7fdf1c7e0000000

def z161 : W := mkw 0x0ff7bfdb04012a1c 0x207fbdfed8200950 0xffffffff8001ff11 0xfffffffffc000ff8

def z162 : W := mkw 0x0dc7f74b2b14000e 0x406e3fba5958a000 0x11c7c7038f1e0008 0x288e3e381c78f000

def z163 : W := mkw 0x4a3fc9dfc198457d 0x0251fe4efe0cc22b 0x103fc0ff809800e1 0x3081fe07fc04c007

def z164 : W := mkw 0x054540002b140002 0x402a2a000158a000 0x71e7c0000ffe000e 0x3b8f3e00007ff000

def z165 : W := mkw 0x07fd76007fd52a03 0xe03febb003fea950 0xffffff007fffff1e 0xfffffff803fffff8

def z166 : W := mkw 0x0000120000002200 0x0000009000000110 0x08001b0000007300 0x804000d800000398

def z167 : W := mkw 0x077d52007bd42203 0xc03bea9003dea110 0xffffdb007ffe730e 0xbffffed803fff398

def z168 : W := mkw 0x0000000080080420 0x0000000004004021 0x0000040380000cf1 0x400000201c000067

def z169 : W := mkw 0x077d400041900001 0x003bea00020c8000 0xf7ffc0004398000a 0x3fbffe00021cc000

def z170 : W := mkw 0x82ba2cf654e3d8d9 0xbc15d167b2a71ec6 0xffbe38fc7ce7f0f7 0xd7fdf1c7e3e73f87

def z171 : W := mkw 0x0f7789db0000001c 0x007bbc4ed8000000 0xf7ffc0ff80000001 0x3fbffe07fc000000

def z172 : W := mkw 0x0080240000000000 0x0004012000000000 0x6180240000000000 0x4b0c012000000000

def z173 : W := mkw 0x0fffbfff7ee1fadf 0xb87ffdfffbf70fd6 0xffffffffffe1ffff 0xffffffffffff0fff

def z174 : W := mkw 0x05c876007fd52a03 0xe02e43b003fea950 0xefc03f007fffff1e 0xcf7e01f803fffff8

def z175 : W := mkw 0x05c836046e816a43 0x202e41b023740b52 0xefd83f1c7f81ffff 0xdf7ec1f8e3fc0fff

def z176 : W := mkw 0x80802420842b8ca0 0x3404012104215c65 0x618024000cff8cfe 0x4b0c01200067fc67

def z177 : W := mkw 0x000840007bd40003 0xc000420003dea000 0x000000007ffe000e 0x0000000003fff000

def z178 : W := mkw 0x054540002b140002 0x402a2a000158a000 0x11c7c0000f1e0008 0x288e3e000078f000

def z179 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xa059c71f809800e1 0xfd02ce38fc04c007

def z180 : W := mkw 0x0080240004010800 0x2004012000200840 0x618024000c018c1e 0x4b0c012000600c60

def z181 : W := mkw 0x47f8ffbdfff9fff3 0xba3fc7fdefffcfff 0xeff9fffffff9ffff 0xff7fcfffffffcfff

def z182 : W := mkw 0x000008b40020d0d0 0x18000045a0010686 0x080038fc0001f0f1 0xc04001c7e0000f87

def z183 : W := mkw 0x0000810900000000 0x0000040848000000 0xa059c71fc3004f1b 0xfd02ce38fe180278

def z184 : W := mkw 0xc5caf76fefbbefeb 0x362e57bb7f7ddf7f 0xffffffffffffffff 0xffffffffffffffff

def z185 : W := mkw 0x077d40007fd52a03 0xe03bea0003fea950 0xf7ffc0007fffff1e 0x3fbffe0003fffff8

def z186 : W := mkw 0x0a3708d20000001c 0x0051b84690000000 0x102600e000000000 0x0081300700000000

def z187 : W := mkw 0xc082a56f842bcde8 0x3604152b7c215e6f 0x71a627ff8cffcfff 0xfb8d313ffc67fe7f

def z188 : W := mkw 0x85c76462af3f8caa 0x742e3b231579fc65 0x71e7e4e38fff8cff 0x7b8f3f271c7ffc67

def z189 : W := mkw 0x054000002a000002 0x002a000001500000 0xe7c000007f00000e 0x0f3e000003f80000

def z190 : W := mkw 0x0008400051d40001 0xc0004200028ea000 0x0000000000fe0000 0x000000000007f000

def z191 : W := mkw 0x0080360004012a00 0x200401b000200950 0xa8403f004301ff1a 0xcd4201f802180ff8

def z192 : W := mkw 0x0082244200000008 0x0004112210000000 0x51a620e000000000 0x028d310700000000

def z193 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0x8059c71fc3004ff1 0xc402ce38fe18027f

def z194 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0x083838fc00e1f0f1 0xd041c1c7e0070f87

def z195 : W := mkw 0x000000002a002202 0x0000000001500110 0x0000000073007300 0x0000000003980398

def z196 : W := mkw 0x45c8f70d6f916b43 0x222e47b86b7c8b5a 0xefd9ff1c7f01ff1e 0xcf7ecff8e3f80ff8

def z197 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0x4f8038003c01b004 0x027c01c001e00d80

def z198 : W := mkw 0x0ff7bfdb8008043c 0x007fbdfedc004021 0xffffffff80980cfb 0xfffffffffc04c067

def z199 : W := mkw 0x4548d30deb986763 0x022a46986f5cc33b 0xae59df1ff3987ffb 0xfd72cef8ff9cc3ff

def z200 : W := mkw 0x023848b47bf4d0d3 0xd811c245a3dfa686 0xee3838fc7ffff0ff 0xd771c1c7e3ffff87

def z201 : W := mkw 0x0000002000208080 0x1000000100010404 0xee2038e070e1f0f7 0xd77101c703870f87

def z202 : W := mkw 0xc082a56f842bcde8 0x3604152b7c215e6f 0x000027ff8001cff1 0xc000013ffc000e7f

def z203 : W := mkw 0xc08ae56fc5bbcde9 0x3604572b7e2dde6f 0xf1ffe7ffcfffcfff 0xff8fff3ffe7ffe7f

def z204 : W := mkw 0x0080240004010800 0x2004012000200840 0x0000240000018c10 0x4000012000000c60

def z205 : W := mkw 0x0235000010440000 0xc011a80000822000 0x1026000000660000 0x0081300000033000

def z206 : W := mkw 0x82bf6462d5ff8ca9 0xf415fb2316affc65 0x71bfe4e38cff8cff 0x7b8dff271c67fc67

def z207 : W := mkw 0x808a2466c4abcce9 0x3404512336255e67 0xf1be24ffccffccff 0xff8df127fe67fe67

def z208 : W := mkw 0xc0084024c5bbcde1 0x36004201262dde6f 0x000000004fffcffe 0x00000000027ffe7f

def z209 : W := mkw 0x077540003b540002 0xc03baa0001daa000 0x57e7c0003f7e000c 0x2abf3e0001fbf000

def z210 : W := mkw 0x0080360004012a00 0x200401b000200950 0x08003f000001ff10 0xc04001f800000ff8

def z211 : W := mkw 0x054012002e012a02 0x202a009001700950 0x8e401b007f01ff1e 0x847200d803f80ff8

def z212 : W := mkw 0x054012002a002202 0x002a009001500110 0xae401f0073007f1a 0xcd7200f8039803f8

def z213 : W := mkw 0x0000810900000000 0x0000040848000000 0x0041c70380000000 0x28020e381c000000

def z214 : W := mkw 0x8082246204238888 0x3404112310211c44 0x71a620e00cff800e 0x3b8d31070067fc00

def z215 : W := mkw 0x0008000440804041 0x0000400022040202 0x00000000408040f2 0x0000000002040207

def z216 : W := mkw 0x0f7fc9db7bd4001f 0xc07bfe4edbdea000 0xf7ffc0fffffe000f 0x3fbffe07fffff000

def z217 : W := mkw 0x80822442840b0c28 0x2404112214205861 0x718624038c1f8c1e 0x6b8c31201c60fc60

def z218 : W := mkw 0x0080360004012a00 0x200401b000200950 0x080038000001b000 0x004001c000000d80

def z219 : W := mkw 0x077d400051d40001 0xc03bea00028ea000 0xf7ffc00000fe0000 0x3fbffe000007f000

def z220 : W := mkw 0x05c876006f912a03 0x202e43b0037c8950 0xefd9ff007f99ff1e 0xff7ecff803fccff8

def z221 : W := mkw 0x8882bffb842b8cbc 0x344415ffdc215c65 0x08003fff80018cf1 0xc04001fffc000c67

def z222 : W := mkw 0x023d48b451f4d0d1 0xd811ea45a28fa686 0x103fc0fc00fe00e1 0x3081fe07e007f007

def z223 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000000008000f3 0x5100000000040007

def z224 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0x01c007000f000f08 0x080e003800780078

def z225 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0xffffffff8f000f09 0xfffffffffc780078

def z226 : W := mkw 0x0000000000000000 0x0000000000000000 0xee403f007301ff1e 0xcf7201f803980ff8

def z227 : W := mkw 0x82b22cf2946b9cb8 0xbc15916794a35ce5 0x7fa63ce3bcffbcff 0x7bfd31e71de7fde7

def z228 : W := mkw 0x85c23642ae0b2e2a 0x242e11b215705971 0x11c607038f1e0f08 0x288e30381c78f078

def z229 : W := mkw 0x0f759b9900000014 0x007bacdcc8000000 0xffffdb1c00000000 0xbffffed8e0000000

def z230 : W := mkw 0x054540002b140002 0x402a2a000158a000 0xf7c7c0007f1e000e 0x2fbe3e0003f8f000

def z231 : W := mkw 0x0230089000000010 0x0011804480000000 0x4e2038e000000000 0x027101c700000000

def z232 : W := mkw 0x4fffffdfc198457d 0x027ffffefe0cc22b 0xffffffffc3984ffb 0xfffffffffe1cc27f

def z233 : W := mkw 0x0008810d40804041 0x000044086a040202 0xa059c71fc08040f3 0xfd02ce38fe040207

def z234 : W := mkw 0x80000020802a84a0 0x1400000104015425 0x0000000000fe00e0 0x000000000007f007

def z235 : W := mkw 0x40084004ef996f63 0x22004200277ccb7b 0x000000007f99fffe 0x0000000003fccfff

def z236 : W := mkw 0x0ff7bfdb0401081c 0x207fbdfed8200840 0xffffffff8c018c1f 0xfffffffffc600c60

def z237 : W := mkw 0x4008c9bdc1b8d5f1 0x1a00464dee0dc6af 0xa859ffffc399fffb 0xfd42cffffe1ccfff

def z238 : W := mkw 0x0000002000208080 0x1000000100010404 0x000020e0000180f1 0x4000010700000c07

def z239 : W := mkw 0x0230899900000010 0x0011844cc8000000 0xee79ffff80000001 0xff73cffffc000000

def z240 : W := mkw 0x8082244204030808 0x2404112210201840 0x118600000c060000 0x008c300000603000

def z241 : W := mkw 0x0000000400004040 0x0000000020000202 0x0000001c000040f1 0xc0000000e0000207

def z242 : W := mkw 0x0ffff74b7bd4000f 0xc07fffba5bdea000 0xf7ffc703fffe000e 0x3fbffe381ffff000

def z243 : W := mkw 0x0080360000000000 0x000401b000000000 0x08003f0000000000 0xc04001f800000000

def z244 : W := mkw 0x4088f70dc5996f61 0x220447b86e2ccb7b 0xa859ff1fc399fffb 0xfd42cff8fe1ccfff

def z245 : W := mkw 0x0a3f89ff50e0d0dd 0x9851fc4ffa870686 0xfe3ff8fff0e1f0f7 0xf7f1ffc7ff870f87

def z246 : W := mkw 0x8082a56b842b8ca8 0x3404152b5c215c65 0xf1ffe7ff8cff8cff 0xff8fff3ffc67fc67

def z247 : W := mkw 0x000840007bd40003 0xc000420003dea000 0xa059c0007ffe000e 0x3d02ce0003fff000

def z248 : W := mkw 0x0ab7bfdb0000001c 0x0055bdfed8000000 0x183fffff80000001 0xf0c1fffffc000000

def z249 : W := mkw 0x0238089450c05051 0x8811c044a2860282 0xee18381c7001f016 0xc770c1c0e3800f80

def z250 : W := mkw 0x0fffbfff50e0d0dd 0x987ffdfffa870686 0xfffffffff0e1f0f7 0xffffffffff870f87

def z251 : W := mkw 0x423dc10dd1dc4561 0xc211ee086e8ee22b 0xb07fc71fc3fe4ffb 0xfd83fe38fe1ff27f

def z252 : W := mkw 0x87f72462be6f8caa 0xf43fb92315f37c65 0x77a624e3bcff8cff 0x7bbd31271de7fc67

def z253 : W := mkw 0x0238089440804051 0x0011c044a2040202 0xee3838fc408040f3 0xd771c1c7e2040207

def z254 : W := mkw 0x4238c9bd51f0d1d1 0x9a11c64dea8f868e 0xee79fbfc73e1f3f7 0xd773cfdfe39f0f9f

def z255 : W := mkw 0x0008000440804041 0x0000400022040202 0xa018001c408040f3 0xd500c000e2040207

def z256 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x71a624e380018cf1 0x7b8d31271c000c67

def z257 : W := mkw 0x80000020842b8ca0 0x3400000104215c65 0x71a600000cff8cfe 0x3b8d30000067fc67

def z258 : W := mkw 0x82b22cf214639898 0xbc15916790a31cc4 0x5fa638e03c67b004 0x02fd31c701e33d80

def z259 : W := mkw 0x054000002a000002 0x002a000001500000 0xf7e600007ffe000e 0x3fbf300003fff000

def z260 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xce3838fc7061f004 0x8671c1c7e3830f80

def z261 : W := mkw 0x4000400081180520 0x020002000408c029 0x0000000003180f08 0x000000000018c078

def z262 : W := mkw 0x80084020ffff8ca3 0xf400420107fffc65 0x000000007fff8cfe 0x0000000003fffc67

def z263 : W := mkw 0x477d4004fbdc4563 0xc23bea0027dee22b 0xf7ffc0007ffe4ffe 0x3fbffe0003fff27f

def z264 : W := mkw 0x077d4000fbdc0423 0xc03bea0007dee021 0xf7ffc403fffe0cff 0x7fbffe201ffff067

def z265 : W := mkw 0x0775089000000010 0x003ba84480000000 0xfffff8fc00000001 0xffffffc7e0000000

def z266 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0x0019c01fc3984ffb 0x3000ce00fe1cc27f

def z267 : W := mkw 0x0f779bdb0000001c 0x007bbcded8000000 0x9e7fdbff80000001 0xb4f3fedffc000000

def z268 : W := mkw 0x80000020842b8ca0 0x3400000104215c65 0x0000000000018cf0 0x0000000000000c67

def z269 : W := mkw 0x000840007bd40003 0xc000420003dea000 0x0000000073000000 0x0000000003980000

def z270 : W := mkw 0x40084004c1984561 0x02004200260cc22b 0x20000403c3984ffb 0x790000201e1cc27f

def z271 : W := mkw 0x0ab7addb0000001c 0x0055bd6ed8000000 0x71bfe4ff80000001 0x7b8dff27fc000000

def z272 : W := mkw 0x0fffbfdb50c0001d 0x807ffdfeda860000 0xfffffffff0e00007 0xffffffffff870000

def z273 : W := mkw 0x8dc7b76b842b8cac 0x346e3dbb5c215c65 0x71e7e7e38cff8cff 0x7b8f3f3f1c67fc67

def z274 : W := mkw 0x0807814b0000000c 0x00403c0a58000000 0x1007c00380000000 0x20803e001c000000

def z275 : W := mkw 0x0000000000000000 0x0000000000000000 0x71a6000000000000 0x3b8d300000000000

def z276 : W := mkw 0x023008b010609090 0x9811804580830484 0x002000e000600000 0x0001000700030000

def z277 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0x8059c71fc3184f08 0xac02ce38fe18c278

def z278 : W := mkw 0x4a3fc9dfc198457d 0x0251fe4efe0cc22b 0xb07fc7ffc3984ffb 0xfd83fe3ffe1cc27f

def z279 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0x5fa63fff80000001 0xc2fd31fffc000000

def z280 : W := mkw 0x07f536002e012a02 0x203fa9b001700950 0xffffff007f01ff1e 0xfffffff803f80ff8

def z281 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000cfe000e 0x000000000067f000

def z282 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xdffffbfc00000000 0x86ffffdfe0000000

def z283 : W := mkw 0x0238089450c05051 0x8811c044a2860282 0x0018001c00000000 0x0000c000e0000000

def z284 : W := mkw 0x0dc2bfdb0000001c 0x006e15fed8000000 0xefc03fff80000001 0xcf7e01fffc000000

def z285 : W := mkw 0x87f724623e67888a 0xf43fb92311f33c44 0x57a620e03c678004 0x02bd310701e33c00

def z286 : W := mkw 0x0882bfdb0000001c 0x004415fed8000000 0x79a63fff80000001 0xfbcd31fffc000000

def z287 : W := mkw 0x4fffffffd1f8d5fd 0x9a7ffffffe8fc6af 0xfffffffff3f9ffff 0xffffffffff9fcfff

def z288 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0x8059c31fc39843e1 0xb402ce18fe1cc21f

def z289 : W := mkw 0x85c236622e23aa8a 0x342e11b311711d54 0xffe63fe07f67ff1e 0xcfff31ff03fb3ff8

def z290 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z291 : W := mkw 0x05c03eb42e21fad2 0x382e01f5a1710fd6 0xefc03ffc7f01ffff 0xcf7e01ffe3f80fff

def z292 : W := mkw 0x0ab2bfdb0000001c 0x005595fed8000000 0xee383fff80000001 0xd771c1fffc000000

def z293 : W := mkw 0x07fd7eb47ff5fad3 0xf83febf5a3ffafd6 0xfffffffc7fffffff 0xffffffffe3ffffff

def z294 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0xfe3ff8ff80000001 0xf7f1ffc7fc000000

def z295 : W := mkw 0x0f759b9900000014 0x007bacdcc8000000 0xee79fbfc00000001 0xd773cfdfe0000000

def z296 : W := mkw 0x4008c10def996f63 0x220046086f7ccb7b 0xa059c71fff99ffff 0xfd02ce38fffccfff

def z297 : W := mkw 0x0000000080080420 0x0000000004004021 0x0000000000980cfa 0x000000000004c067

def z298 : W := mkw 0x0fffffdb7fd52a1f 0xe07ffffedbfea950 0xffffffffffffff1f 0xfffffffffffffff8

def z299 : W := mkw 0x0000000004010800 0x2000000000200840 0x000000000c018c1e 0x0000000000600c60

def z300 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xcfc03b007f01f304 0x867e01d803f80f98

def z301 : W := mkw 0x8ff7bffb0423889c 0x347fbdffd8211c44 0xffffffff8c678005 0xfffffffffc633c00

def z302 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xa03800fc40e040f3 0xd501c007e2070207

def z303 : W := mkw 0x0080242004218880 0x3004012100210c44 0x61a024e00ce18cff 0x5b0d012700670c67

def z304 : W := mkw 0x0008400041900001 0x00004200020c8000 0xa059c70043984f1a 0xfd02ce38021cc278

def z305 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xe7d9c0007f00000e 0x0f3ece0003f80000

def z306 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0x11ffc7ff80000001 0x388ffe3ffc000000

def z307 : W := mkw 0x0238000050c00001 0x8011c00002860000 0xf7be00007cfe000e 0x3fbdf00003e7f000

def z308 : W := mkw 0x0775810900000000 0x003bac0848000000 0xf7ffc71f80000001 0xffbffe38fc000000

def z309 : W := mkw 0xcfffffffc5bbcdfd 0x367ffffffe2dde6f 0xffffffffcfffcfff 0xfffffffffe7ffe7f

def z310 : W := mkw 0x85c03620ae2baea2 0x342e01b105715d75 0xefc03f007ffffffe 0xcf7e01f803ffffff

def z311 : W := mkw 0x4238c9bdd1f8d5f1 0x9a11c64dee8fc6af 0xa079c7ffc3f84ffb 0xfd03ce3ffe1fc27f

def z312 : W := mkw 0x054000002a000002 0x002a000001500000 0x8640000073000000 0x0432000003980000

def z313 : W := mkw 0x023848b451f0d0d1 0x9811c245a28f8686 0xee79f8fc73f9f0ff 0xff73cfc7e39fcf87

def z314 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0x97dfc0007f1e0008 0x2cbefe0003f8f000

def z315 : W := mkw 0x8082246204238888 0x3404112310211c44 0x71a624e38c678005 0x7b8d31271c633c00

def z316 : W := mkw 0x4000c10981180520 0x020006084c08c029 0xa041c703c3184f1a 0xed020e381e18c278

def z317 : W := mkw 0x0ff7bfdb2a00221e 0x007fbdfed9500110 0xfffffffff3007301 0xffffffffff980398

def z318 : W := mkw 0x054000002a000002 0x002a000001500000 0xe7c007007f004f1e 0xcf3e003803f80278

def z319 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xf1ffc71fcffe4fff 0xff8ffe38fe7ff27f

def z320 : W := mkw 0x0082a54b00000008 0x0004152a58000000 0xf1ffe7ff80000001 0xff8fff3ffc000000

def z321 : W := mkw 0x054840006b900003 0x002a4200035c8000 0xe7d9c0007f98000e 0x3f3ece0003fcc000

def z322 : W := mkw 0x077d48b47bf4d0d3 0xd83bea45a3dfa686 0xee79f8fc73e1f0f7 0xd773cfc7e39f0f87

def z323 : W := mkw 0x0fffffdb4190001d 0x007ffffeda0c8000 0xffffffffc398000b 0xfffffffffe1cc000

def z324 : W := mkw 0x00084000c1980421 0x00004200060cc021 0xa059c403c3980cfb 0x7d02ce201e1cc067

def z325 : W := mkw 0x8000002004238880 0x3400000100211c44 0x000000000c678004 0x0000000000633c00

def z326 : W := mkw 0x0082244200000008 0x0004112210000000 0x71a624e38cfe000f 0x7b8d31271c67f000

def z327 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0x8659c0007ffe000e 0x0432ce0003fff000

def z328 : W := mkw 0x4238c99dd1d85571 0x8a11c64cee8ec2ab 0xae59df1ff3987ffb 0xfd72cef8ff9cc3ff

def z329 : W := mkw 0x077540002b140002 0x403baa000158a000 0xf7ffc0000f1e0008 0x3fbffe000078f000

def z330 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0x5fe7ffe380000000 0x2aff3fff1c000000

def z331 : W := mkw 0xc00ac16fc1bac5e9 0x1600560b7e0dd62f 0xb07fc7ffc3fe4ffb 0xfd83fe3ffe1ff27f

def z332 : W := mkw 0x0882bfdb0000001c 0x004415fed8000000 0xa859ffff80000001 0xfd42cffffc000000

def z333 : W := mkw 0x077800007ac00003 0x803bc00003d60000 0xe7f800007fe0000e 0x1f3fc00003ff0000

def z334 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xa059c01fc39800eb 0x3d02ce00fe1cc007

def z335 : W := mkw 0x808a6462ffff8cab 0xf404532317fffc65 0x71a624e3ffff8cff 0x7b8d31271ffffc67

def z336 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xf7ffc7007ffe4f1e 0xffbffe3803fff278

def z337 : W := mkw 0x08009b9900000014 0x004004dcc8000000 0x08001b1c00000000 0x804000d8e0000000

def z338 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x11a604e38cfe0ce9 0x388d30271c67f067

def z339 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xa019c01fc09840f3 0xf500ce00fe04c207

def z340 : W := mkw 0x80020062802a84a8 0x1400100314015425 0x702620e380ff80f7 0x738131071c07fc07

def z341 : W := mkw 0x080289db0000001c 0x0040144ed8000000 0x000000ff80000001 0x00000007fc000000

def z342 : W := mkw 0x0008400041900001 0x00004200020c8000 0x0019c00000980000 0x3000ce000004c000

def z343 : W := mkw 0x054012002a002202 0x002a009001500110 0x0e00180030003000 0x007000c001800180

def z344 : W := mkw 0x0082244280080428 0x0004112214004021 0x71a624e380980cfb 0x7b8d31271c04c067

def z345 : W := mkw 0x0fffbfff50e0d0dd 0x987ffdfffa870686 0xffffffff80e000e1 0xfffffffffc070007

def z346 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0x003800fc00e000e1 0x1001c007e0070007

def z347 : W := mkw 0x0082244204010808 0x2004112210200840 0x71a624e38c018c1f 0x7b8d31271c600c60

def z348 : W := mkw 0x0ff73ed22e012a1e 0x207fb9f691700950 0xffe63fe07f01ff1e 0xcfff31ff03f80ff8

def z349 : W := mkw 0x00803eb40421fad0 0x380401f5a0210fd6 0x08003ffc0001fff1 0xc04001ffe0000fff

def z350 : W := mkw 0x80822442840b0c28 0x2404112214205861 0x318604038c9e0cfb 0x798c30201c64f067

def z351 : W := mkw 0x4000810d80084560 0x020004086c00422b 0x0000001f800000e1 0x00000000fc000007

def z352 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x000024e38cff8cff 0x400001271c67fc67

def z353 : W := mkw 0x0a3fc9db51d4001d 0xc051fe4eda8ea000 0x103fc0ff80fe0001 0x3081fe07fc07f000

def z354 : W := mkw 0x8882bffb842b8cbc 0x344415ffdc215c65 0x79a63fff8cff8cff 0xfbcd31fffc67fc67

def z355 : W := mkw 0x077d08b47ae4d0d3 0xd83be845a3d72686 0xffbe38fc7ce7f0f7 0xd7fdf1c7e3e73f87

def z356 : W := mkw 0x0000810900000000 0x0000040848000000 0x8059c31c00000000 0x8402ce18e0000000

def z357 : W := mkw 0x4000c10981180520 0x020006084c08c029 0xa059c71f83180f09 0xfd02ce38fc18c078

def z358 : W := mkw 0x0ff7bffb1060909c 0x987fbdffd8830484 0xffffffffb061b005 0xfffffffffd830d80

def z359 : W := mkw 0x07781ab47ae0f2d3 0x983bc0d5a3d70796 0xee783bfc73e1f3f7 0xd773c1dfe39f0f9f

def z360 : W := mkw 0x0082244200000008 0x0004112210000000 0x000024e380000001 0x400001271c000000

def z361 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0x4fc03f003f01bf0c 0x0a7e01f801f80df8

def z362 : W := mkw 0x0235000000000000 0x0011a80000000000 0x103fc00000000000 0x3081fe0000000000

def z363 : W := mkw 0x0ff73ed23a44001e 0xc07fb9f691d22000 0x5fa638e03c660004 0x02fd31c701e33000

def z364 : W := mkw 0x0008400041900001 0x00004200020c8000 0x8059c00043000000 0x0402ce0002180000

def z365 : W := mkw 0x85c76442af1f0c2a 0x642e3b221578f861 0x11c7c4038f1e0c08 0x288e3e201c78f060

def z366 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0x11ffc0000ffe0008 0x388ffe00007ff000

def z367 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0x018000000c000000 0x000c000000600000

def z368 : W := mkw 0x0dc7b74b0000000c 0x006e3dba58000000 0xffc7ff0380000000 0xeffe3ff81c000000

def z369 : W := mkw 0x85c23662842b8ca8 0x342e11b314215c65 0xffe63fe38cff8cff 0xffff31ff1c67fc67

def z370 : W := mkw 0x4fffffdfef996f7f 0x227ffffeff7ccb7b 0xffffffffff99ffff 0xfffffffffffccfff

def z371 : W := mkw 0x077500003a440002 0xc03ba80001d22000 0x0600000030000000 0x0030000001800000

def z372 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0x8e18181c70e1f0f6 0x8470c0c0e3870f87

def z373 : W := mkw 0x0080240004010800 0x2004012000200840 0xe1c027004f01cf1e 0xcf0e013802780e78

def z374 : W := mkw 0x8ff7bffbae2baebe 0x347fbdffdd715d75 0xffffffffffffffff 0xffffffffffffffff

def z375 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0x8e403f007301ff10 0xc47201f803980ff8

def z376 : W := mkw 0x054000002a000002 0x002a000001500000 0x01c000000f000008 0x080e000000780000

def z377 : W := mkw 0x000000002a000002 0x0000000001500000 0x000000007f00000e 0x0000000003f80000

def z378 : W := mkw 0x40084004c1984561 0x02004200260cc22b 0xa059c00043984ffa 0x3d02ce00021cc27f

def z379 : W := mkw 0x077500003a440002 0xc03ba80001d22000 0x77a600003cfe000e 0x3bbd300001e7f000

def z380 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000000040004012 0xc500000002000200

def z381 : W := mkw 0x0000000000000000 0x0000000000000000 0x4e0038003001b004 0x027001c001800d80

def z382 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0x8e1838fc7001f0f1 0xc470c1c7e3800f87

def z383 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xffe63f007fffff1e 0xffff31f803fffff8

def z384 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040070003000f08 0x0802003800180078

def z385 : W := mkw 0x80822cf6842bdcf8 0x3c041167b4215ee7 0x79a63cff8cfffcff 0xfbcd31e7fc67ffe7

def z386 : W := mkw 0x0000400001100000 0x0000020000088000 0x0041c00003180008 0x28020e000018c000

def z387 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x102624e380ff8cf1 0x708131271c07fc67

def z388 : W := mkw 0x4008810dc0884561 0x020044086e04422b 0xa018071fc0804ff3 0xd500c038fe04027f

def z389 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0x9fdfdf1f80000000 0xacfefef8fc000000

def z390 : W := mkw 0x4000000480084560 0x020000002400422b 0x0000000000004ff0 0x000000000000027f

def z391 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xefc038007f01b00e 0x0f7e01c003f80d80

def z392 : W := mkw 0x4000c10901100100 0x0200060848088008 0x0041c30003000300 0x00020e1800180018

def z393 : W := mkw 0x0775000000000000 0x003ba80000000000 0x57a6000000000000 0x02bd300000000000

def z394 : W := mkw 0x4548c10deb984563 0x022a46086f5cc22b 0xe7d9c71fff984fff 0xff3ece38fffcc27f

def z395 : W := mkw 0x023d48b451f4d0d1 0xd811ea45a28fa686 0xfe3ff8fc70fff0f7 0xf7f1ffc7e387ff87

def z396 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0xb07fc7ff80000001 0xfd83fe3ffc000000

def z397 : W := mkw 0x423889bdd0e8d5f1 0x9a11c44dee8746af 0xee383ffff0e1fff7 0xd771c1ffff870fff

def z398 : W := mkw 0x07f836007ec12a03 0xa03fc1b003f60950 0xeff83f007fe1ff1e 0xdf7fc1f803ff0ff8

def z399 : W := mkw 0x4fffffdffbdc457f 0xc27ffffeffdee22b 0xfffffffffffe4fff 0xfffffffffffff27f

def z400 : W := mkw 0x023808b4d0e8d4f1 0x9811c045a68746a7 0xee383cfff0f9fcff 0xff71c1e7ff87cfe7

def z401 : W := mkw 0x000800247ee1fac3 0xb800400123f70fd6 0x000000007fe1fffe 0x0000000003ff0fff

def z402 : W := mkw 0x823a08f6d0ead4f9 0x9c11d047b68756a7 0x103e00ff80fe00e1 0x3081f007fc07f007

def z403 : W := mkw 0x0fffbfdf50c0505d 0x887ffdfefa860282 0xfffffffff0007001 0xffffffffff800380

def z404 : W := mkw 0x0008000440804041 0x0000400022040202 0xee18381c7081f0f7 0xd770c1c0e3840f87

def z405 : W := mkw 0x07f83eb47ee1fad3 0xb83fc1f5a3f70fd6 0xefb838fc7ce1f0f7 0xd77dc1c7e3e70f87

def z406 : W := mkw 0x4008c10d41904141 0x020046086a0c820a 0x0019c01c00000000 0x0000ce00e0000000

def z407 : W := mkw 0x4ff7bfdf8008457c 0x027fbdfefc00422b 0xffffffff80004ff1 0xfffffffffc00027f

def z408 : W := mkw 0x0f759b9900000014 0x007bacdcc8000000 0xae59df1f80000001 0xfd72cef8fc000000

def z409 : W := mkw 0x0008000440804041 0x0000400022040202 0xa058071c43804ffb 0xdd02c038e21c027f

def z410 : W := mkw 0x4000c10d81184560 0x020006086c08c22b 0x0041c71f83184ff9 0xe8020e38fc18c27f

def z411 : W := mkw 0x077d48b07bf49093 0xd83bea4583dfa484 0xfffff8e07fffb00e 0x3fffffc703fffd80

def z412 : W := mkw 0x0ff7bffb0020809c 0x107fbdffd8010404 0xffffffff80e180f7 0xfffffffffc070c07

def z413 : W := mkw 0x07fd76007bd40003 0xc03febb003dea000 0xffffff007ffe000e 0xfffffff803fff000

def z414 : W := mkw 0x0080240004010800 0x2004012000200840 0x418020000c018004 0x020c010000600c00

def z415 : W := mkw 0x05c2364200000008 0x002e11b210000000 0xffe63fe380000001 0xffff31ff1c000000

def z416 : W := mkw 0x0008400441904041 0x00004200220c8202 0xa059c01c439840fb 0xfd02ce00e21cc207

def z417 : W := mkw 0x0540120000000000 0x002a009000000000 0x8e401b0000000000 0x847200d800000000

def z418 : W := mkw 0x85c23642ae0b2e2a 0x242e11b215705971 0xffc63f03ff1fff1e 0xeffe31f81ff8fff8

def z419 : W := mkw 0x40084004c1984561 0x02004200260cc22b 0xa040070043984ffa 0xcd020038021cc27f

def z420 : W := mkw 0x8002006200228088 0x1400100310011404 0x102600e000660000 0x0081300700033000

def z421 : W := mkw 0x0ff5bf9900000014 0x007fadfcc8000000 0xefd9ff1c00000000 0xcf7ecff8e0000000

def z422 : W := mkw 0x077d08b450e0d0d1 0x983be845a2870686 0xfffff8fc70e1f0f7 0xffffffc7e3870f87

def z423 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0x8059c31c43984ffa 0x8402ce18e21cc27f

def z424 : W := mkw 0x07fd64007fd50803 0xe03feb2003fea840 0xf7ffe4007fff8c1e 0x7fbfff2003fffc60

def z425 : W := mkw 0x8082246204238888 0x3404112310211c44 0x000020e000018000 0x0000010700000c00

def z426 : W := mkw 0x82ba2cf6d4ebdcf9 0xbc15d167b6a75ee7 0xee383cfff0e1fcf7 0xd771c1e7ff870fe7

def z427 : W := mkw 0x0008000450c05041 0x8800400022860282 0x0000000070007000 0x0000000003800380

def z428 : W := mkw 0x877d4020ffff8ca3 0xf43bea0107fffc65 0xf7ffc0007fff8cfe 0x3fbffe0003fffc67

def z429 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xe63800fc70e000e7 0x1731c007e3870007

def z430 : W := mkw 0x0000002010609080 0x9800000100830484 0x000000003061b004 0x0000000001830d80

def z431 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xa1c007004f004f1a 0xcd0e003802780278

def z432 : W := mkw 0x05c036202e21aa82 0x302e01b101710d54 0xefe03fe07fe1ffff 0xdf7f01ff03ff0fff

def z433 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x618024e38c018cff 0x4b0c01271c600c67

def z434 : W := mkw 0x0540000000000000 0x002a000000000000 0xe7c0000000000000 0x0f3e000000000000

def z435 : W := mkw 0x0000002000208080 0x1000000100010404 0x002000e000e000e1 0x1001000700070007

def z436 : W := mkw 0x45c0f709af192f22 0x222e07b84d78c979 0xefc1ff03ff19ff1e 0xef7e0ff81ff8cff8

def z437 : W := mkw 0x0230089000000010 0x0011804480000000 0x003800fc00000001 0x1001c007e0000000

def z438 : W := mkw 0x87ff64627ff7888b 0xf43ffb2313ffbc44 0xf7ffe0e07fff800e 0x3fbfff0703fffc00

def z439 : W := mkw 0x0a3f89ff50e0d0dd 0x9851fc4ffa870686 0x103fc0ff80e000e1 0x3081fe07fc070007

def z440 : W := mkw 0x077d40247bf4d0c3 0xd83bea0123dfa686 0xf7ffc0007ffff0fe 0x3fbffe0003ffff87

def z441 : W := mkw 0x8ab7adfb842b8cbc 0x3455bd6fdc215c65 0x71bfe4ff8cff8cff 0x7b8dff27fc67fc67

def z442 : W := mkw 0x0008000440804041 0x0000400022040202 0x0018001c008000e1 0x1000c000e0040007

def z443 : W := mkw 0x80822cf6842bdcf8 0x3c041167b4215ee7 0x08003cff8001fcf1 0xc04001e7fc000fe7

def z444 : W := mkw 0xc08ae56fc5bbcde9 0x3604572b7e2dde6f 0x71bfe4ff8cff8cff 0x7b8dff27fc67fc67

def z445 : W := mkw 0x023808b050e09091 0x9811c04582870484 0xee3838e070e1b006 0x1771c1c703870d80

def z446 : W := mkw 0x0775000000000000 0x003ba80000000000 0x8659c00000000000 0x0432ce0000000000

def z447 : W := mkw 0x023008b41060d0d0 0x98118045a0830686 0x4e2038fc3061f0f5 0xc27101c7e1830f87

def z448 : W := mkw 0x0238089450c05051 0x8811c044a2860282 0xee38181c70e07006 0x9771c0c0e3870380

def z449 : W := mkw 0x05c0360000000000 0x002e01b000000000 0x01c0070000000000 0x080e003800000000

def z450 : W := mkw 0x0fffbfdf4080405d 0x007ffdfefa040202 0xffffffffc08040f3 0xfffffffffe040207

def z451 : W := mkw 0x4088e50dc5994d61 0x220447286e2cca6b 0xe1d9e71fcf99cfff 0xff0ecf38fe7cce7f

def z452 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xffbe38fc7cfff0ff 0xfffdf1c7e3e7ff87

def z453 : W := mkw 0x0dc7bfdb0000001c 0x006e3dfed8000000 0x19c7ffff80000001 0xe8ce3ffffc000000

def z454 : W := mkw 0x054012002a002202 0x002a009001500110 0x0040030003000300 0x0002001800180018

def z455 : W := mkw 0x4008c12dd1f8d5e1 0x9a0046096e8fc6af 0xa059c71ff3f9ffff 0xfd02ce38ff9fcfff

def z456 : W := mkw 0x4ff7ffdb8118053c 0x027fbffedc08c029 0xffffffff83180f09 0xfffffffffc18c078

def z457 : W := mkw 0x0008002450e0d0c1 0x9800400122870686 0xa018001c70e1f0f7 0xd500c000e3870f87

def z458 : W := mkw 0x054000002a000002 0x002a000001500000 0x478000003c000004 0x023c000001e00000

def z459 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0x8e59ffff80000001 0xc472cffffc000000

def z460 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000040380000001 0x790000201c000000

def z461 : W := mkw 0x8dc7b74b840b0c2c 0x246e3dba5c205861 0x11c7c7038c1e0c08 0x288e3e381c60f060

def z462 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0x4f8038007f01ff1e 0x027c01c003f80ff8

def z463 : W := mkw 0x0238089450c05051 0x8811c044a2860282 0xee3838fc70007001 0xd771c1c7e3800380

def z464 : W := mkw 0x808a2466d4ebdce9 0xbc04512336a75ee7 0x71a624e3fcfffcff 0x7b8d31271fe7ffe7

def z465 : W := mkw 0x0000000000000000 0x0000000000000000 0x118600000c1e0008 0x288c30000060f000

def z466 : W := mkw 0x0000000000000000 0x0000000000000000 0x618000000c00000e 0x0b0c000000600000

def z467 : W := mkw 0x023008b010609090 0x9811804580830484 0xee3838fc3061b005 0xd771c1c7e1830d80

def z468 : W := mkw 0x8082246204238888 0x3404112310211c44 0x71a620e00ce780f7 0x538d310700673c07

def z469 : W := mkw 0x0775000000000000 0x003ba80000000000 0xf7ffc00000000000 0x3fbffe0000000000

def z470 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0x57a600007ffe000e 0x02bd300003fff000

def z471 : W := mkw 0x0f7d9b9d50c05055 0x887becdcea860282 0x8e59db1c70007000 0x8472ced8e3800380

def z472 : W := mkw 0x4000810d80084560 0x020004086c00422b 0xa059c71f80004ff1 0xfd02ce38fc00027f

def z473 : W := mkw 0x0dc736420000000c 0x006e39b210000000 0x1186000000000000 0x008c300000000000

def z474 : W := mkw 0x0000000000000000 0x0000000000000000 0xa059c00000000000 0x3d02ce0000000000

def z475 : W := mkw 0x0f7ddb997bd40017 0xc07beedccbdea000 0x8e59db1c73000000 0x8472ced8e3980000

def z476 : W := mkw 0x0fffffdb7bd4001f 0xc07ffffedbdea000 0xfffffffff3000001 0xffffffffff980000

def z477 : W := mkw 0x40084004fbdc4563 0xc200420027dee22b 0x000000007ffe4ffe 0x0000000003fff27f

def z478 : W := mkw 0x0000000000000000 0x0000000000000000 0xe600000070000006 0x0730000003800000

def z479 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xfffffffff001f017 0xffffffffff800f80

def z480 : W := mkw 0x4238c99dc1984571 0x0211c64cee0cc22b 0xee79ffffc3984ffb 0xff73cffffe1cc27f

def z481 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xf7ffc00073000000 0x3fbffe0003980000

def z482 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xee59ff1ff399ffff 0xff72cff8ff9ccfff

def z483 : W := mkw 0x000008b40020d0d0 0x18000045a0010686 0xee0038fc7001f0f7 0xc77001c7e3800f87

def z484 : W := mkw 0x0fff7ed27bd4001f 0xc07ffbf693dea000 0xfffff8e07ffe000e 0x3fffffc703fff000

def z485 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0x0000071fc3984ffb 0xc0000038fe1cc27f

def z486 : W := mkw 0x000000002e012a02 0x2000000001700950 0xee0038007f01ff1e 0xc77001c003f80ff8

def z487 : W := mkw 0x023840007bd40003 0xc011c20003dea000 0xe63800007ffe000e 0x1731c00003fff000

def z488 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xe679c00073e00006 0x1733ce00039f0000

def z489 : W := mkw 0x054d40006b940003 0x402a6a00035ca000 0xb1dfc0004f9e000a 0x3d8efe00027cf000

def z490 : W := mkw 0x054540002b140002 0x402a2a000158a000 0x0041c00003000000 0x00020e0000180000

def z491 : W := mkw 0x05c836247ee1fac3 0xb82e41b123f70fd6 0xefc03f007fe1fffe 0xcf7e01f803ff0fff

def z492 : W := mkw 0x8082246204238888 0x3404112310211c44 0x71a624e00c678c1e 0x4b8d312700633c60

def z493 : W := mkw 0x0000810980080420 0x000004084c004021 0xa059c71f80980cfb 0xfd02ce38fc04c067

def z494 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xe7c007007f000f0e 0x0f3e003803f80078

def z495 : W := mkw 0x0082244200000008 0x0004112210000000 0x1186040380000000 0x288c30201c000000

def z496 : W := mkw 0x4008400441904141 0x02004200220c820a 0x0000000043004300 0x0000000002180218

def z497 : W := mkw 0x4545c109ab1c0522 0x422a2e084d58e029 0x11c7c7038f1e0f08 0x288e3e381c78f078

def z498 : W := mkw 0x0080240004010800 0x2004012000200840 0xef803c007c01fc1e 0xcf7c01e003e00fe0

def z499 : W := mkw 0x0000810900000000 0x0000040848000000 0x0000071f80000001 0xc0000038fc000000

def z500 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x200024e380998cfb 0x790001271c04cc67

def z501 : W := mkw 0x4fffffdf4190415d 0x027ffffefa0c820a 0xffffffffc3004301 0xfffffffffe180218

def z502 : W := mkw 0x877f4062fbfe84ab 0xd43bfa0317dff425 0xf7ffc0e3fffe00ef 0x3fbffe071ffff007

def z503 : W := mkw 0x0000000000000000 0x0000000000000000 0x51a600000c660004 0x028d300000633000

def z504 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x51a620e38cff80e5 0x328d31071c67fc07

def z505 : W := mkw 0x408ae54fc1984569 0x0204572a7e0cc22b 0xf1ffe7ffc3984ffb 0xff8fff3ffe1cc27f

def z506 : W := mkw 0x0000000080080420 0x0000000004004021 0x0000040380180c08 0x280000201c00c060

def z507 : W := mkw 0x45c8f70dc1984561 0x022e47b86e0cc22b 0xefd9ff1fc3984ffb 0xff7ecff8fe1cc27f

def z508 : W := mkw 0x07f03e9000000010 0x003f81f480000000 0xeff83ffc00000001 0xdf7fc1ffe0000000

def z509 : W := mkw 0x0238000050c00001 0x8011c00002860000 0x8618000070000000 0x0430c00003800000

def z510 : W := mkw 0x8ffffffbffff8cbf 0xf47fffffdffffc65 0xffffffffffff8cff 0xfffffffffffffc67

def z511 : W := mkw 0x0008000050c00001 0x8000400002860000 0x0000000070e00006 0x0000000003870000

def z512 : W := mkw 0xc2baedffd5fbddf9 0xbe15d76ffeafdeef 0xffffffffffffffff 0xffffffffffffffff

def z513 : W := mkw 0x0230089010401010 0x8811804480820080 0x0e00180030003000 0x007000c001800180

def z514 : W := mkw 0x4000c10981180520 0x020006084c08c029 0x0001c00380180000 0x20000e001c00c000

def z515 : W := mkw 0x0882bfff0020d0dc 0x184415fff8010686 0x08003fff8001f0f1 0xc04001fffc000f87

def z516 : W := mkw 0x4882bfdf8008457c 0x024415fefc00422b 0x08003fff80004ff1 0xc04001fffc00027f

def z517 : W := mkw 0x45c87604ef996f63 0x222e43b0277ccb7b 0xefc03f007f99fffe 0xcf7e01f803fccfff

def z518 : W := mkw 0x0dc7b74b2e012a0e 0x206e3dba59700950 0x11c7c7038f000f08 0x288e3e381c780078

def z519 : W := mkw 0x077d00007ac40003 0xc03be80003d62000 0xf7be00007ce60006 0x17bdf00003e73000

def z520 : W := mkw 0x4008c10dfbdc4563 0xc20046086fdee22b 0xa059c71ffffe4fff 0xfd02ce38fffff27f

def z521 : W := mkw 0x80000020842b8ca0 0x3400000104215c65 0x602020e00cff8cff 0x530101070067fc67

def z522 : W := mkw 0x05c576002f152a02 0x602e2bb00178a950 0xffc7ff007f1fff1e 0xeffe3ff803f8fff8

def z523 : W := mkw 0x00080004c0884461 0x0000400026044223 0xa018041fc0984cfb 0xfd00c020fe04c267

def z524 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000043004f1a 0x0000000002180278

def z525 : W := mkw 0x80822462802a84a8 0x1404112314015425 0x71a624e380fe00e1 0x7b8d31271c07f007

def z526 : W := mkw 0x80823662842baea8 0x340411b314215d75 0x08003fe38001fff1 0xc04001ff1c000fff

def z527 : W := mkw 0x0080240084090c20 0x2004012004204861 0x618024038c998cff 0x7b0c01201c64cc67

def z528 : W := mkw 0xc7ffe56fffffcdeb 0xf63fff2b7ffffe6f 0xf7ffe7ffffffcfff 0xffbfff3ffffffe7f

def z529 : W := mkw 0x05c024002e010802 0x202e012001700840 0xe7c024007f018c1e 0x4f3e012003f80c60

def z530 : W := mkw 0x0dc7b74b0000000c 0x006e3dba58000000 0x71e7e7e380000001 0x7b8f3f3f1c000000

def z531 : W := mkw 0x07fd76007fd52a03 0xe03febb003fea950 0xf7ffc7007ffe0f0e 0x3fbffe3803fff078

def z532 : W := mkw 0x05c576002f152a02 0x602e2bb00178a950 0x11c7c7000f1e0f08 0x288e3e380078f078

def z533 : W := mkw 0xc08ae56fc5bbcde9 0x3604572b7e2dde6f 0xa059e7ffc399cffb 0xfd02cf3ffe1cce7f

def z534 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x51a624e38c7f8c0c 0x2a8d31271c63fc60

def z535 : W := mkw 0x0238089050c00011 0x8011c04482860000 0xee3838fc70e00007 0xd771c1c7e3870000

def z536 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x602024e380e18cf7 0x530101271c070c67

def z537 : W := mkw 0x0f759b992a002216 0x007bacdcc9500110 0x8e59db1c73007300 0x8472ced8e3980398

def z538 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0x603820fc00e180f7 0x5301c107e0070c07

def z539 : W := mkw 0x000808b450e0d0d1 0x98004045a2870686 0x080038fc70e1f0f7 0xc04001c7e3870f87

def z540 : W := mkw 0x45c0f709af192f22 0x222e07b84d78c979 0x01c1c7038f180f08 0x280e0e381c78c078

def z541 : W := mkw 0x000008b000209090 0x1800004580010484 0x080038e00001b000 0x004001c700000d80

def z542 : W := mkw 0x0008000440804041 0x0000400022040202 0x8018001c40004000 0x8400c000e2000200

def z543 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffffffffc3004f1b 0xfffffffffe180278

def z544 : W := mkw 0x0000089400005050 0x08000044a0000282 0x0800181c00007000 0x804000c0e0000380

def z545 : W := mkw 0x0ff7bfdb2a00001e 0x007fbdfed9500000 0xffffffffff00000f 0xfffffffffff80000

def z546 : W := mkw 0x0005400001140000 0x40002a000008a000 0x1007c000001e0000 0x20803e000000f000

def z547 : W := mkw 0x0000000000000000 0x0000000000000000 0xa018001c00000001 0xd500c000e0000000

def z548 : W := mkw 0x07ff64427bd4000b 0xc03ffb2213dea000 0xf7ffe4e3fffe000f 0x7fbfff271ffff000

def z549 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xfffff8007ffff01e 0xffffffc003ffff80

def z550 : W := mkw 0x85c23662ae2baeaa 0x342e11b315715d75 0x71e627e38fff8fff 0x7b8f313f1c7ffc7f

def z551 : W := mkw 0x45c0b70dae096f62 0x222e05b86d704b7b 0xefc03f1fff01ffff 0xcf7e01f8fff80fff

def z552 : W := mkw 0x423848b4d1f8d5f1 0x9a11c245a68fc6af 0xee3838fc73f9ffff 0xd771c1c7e39fcfff

def z553 : W := mkw 0x0000000000000000 0x0000000000000000 0xa04000004300000a 0x0d02000002180000

def z554 : W := mkw 0x077d000050c00001 0x803be80002860000 0xf7ffc00070e00006 0x3fbffe0003870000

def z555 : W := mkw 0x400089bd8028d5f0 0x1a00044dec0146af 0x08003fff8001fff1 0xc04001fffc000fff

def z556 : W := mkw 0x4008c10d41904141 0x020046086a0c820a 0xa059c71fc3004301 0xfd02ce38fe180218

def z557 : W := mkw 0x05c0360000000000 0x002e01b000000000 0xefc03f007001f016 0xcf7e01f803800f80

def z558 : W := mkw 0x000840247bf4d0c3 0xd800420123dfa686 0x000000007ffff0fe 0x0000000003ffff87

def z559 : W := mkw 0x0882b74b0000000c 0x004415ba58000000 0x0000070380000000 0x000000381c000000

def z560 : W := mkw 0x4008c12dc1b8c5e1 0x120046096e0dc62f 0xe079e7ffc3f9cfff 0xff03cf3ffe1fce7f

def z561 : W := mkw 0x07f5360000000000 0x003fa9b000000000 0xffffff0000000000 0xfffffff800000000

def z562 : W := mkw 0x85c23662ae2baeaa 0x342e11b315715d75 0x7fa63ce3bcffbcff 0x7bfd31e71de7fde7

def z563 : W := mkw 0x0230000010400000 0x8011800000820000 0x4620000030600004 0x0231000001830000

def z564 : W := mkw 0x0ff73ef21060909c 0x987fb9f790830484 0x5fa638e03061b004 0x02fd31c701830d80

def z565 : W := mkw 0x0d45930900000004 0x006a2c9848000000 0x0041c30000000000 0x00020e1800000000

def z566 : W := mkw 0x054012002a002202 0x002a009001500110 0xee403b007301f316 0xc77201d803980f98

def z567 : W := mkw 0x077dc1097bd40003 0xc03bee084bdea000 0xf7ffc71ffffe000f 0xffbffe38fffff000

def z568 : W := mkw 0x008024002e012a02 0x2004012001700950 0x618024007f01ff1e 0x4b0c012003f80ff8

def z569 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0x003800fc70e1f0f7 0x1001c007e3870f87

def z570 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0x01c007007f01ff1e 0x080e003803f80ff8

def z571 : W := mkw 0x0238400051d00001 0x8011c200028e8000 0xe679c00073f8000e 0x3f33ce00039fc000

def z572 : W := mkw 0x077d52007bd42203 0xc03bea9003dea110 0x8e59db0073007300 0x8472ced803980398

def z573 : W := mkw 0x85c23662ae2baeaa 0x342e11b315715d75 0xefc03fe3ff01ffff 0xcf7e01ff1ff80fff

def z574 : W := mkw 0x80000020842b8ca0 0x3400000104215c65 0x200004038cff8cff 0x790000201c67fc67

def z575 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xefc03f003c01b004 0xcf7e01f801e00d80

def z576 : W := mkw 0x87fa3ef6feebfefb 0xbc3fd1f7b7f75ff7 0xfffe3fffffffffff 0xfffff1ffffffffff

def z577 : W := mkw 0x000840007fd52a03 0xe000420003fea950 0x000000007fffff1e 0x0000000003fffff8

def z578 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0x4e2038e070e1f0f6 0x027101c703870f87

def z579 : W := mkw 0x823808b4d4ebdcf1 0xbc11c045a6a75ee7 0xee3838fc7cfffcff 0xd771c1c7e3e7ffe7

def z580 : W := mkw 0x000000003a440002 0xc000000001d22000 0x000000003c660004 0x0000000001e33000

def z581 : W := mkw 0x0238002050e08081 0x9011c00102870404 0xe63820e070e180f7 0x5731c10703870c07

def z582 : W := mkw 0x477dc10d7bd44143 0xc23bee086bdea20a 0xf7ffc31c7ffe430e 0xbfbffe18e3fff218

def z583 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0x8fc01f007f007f08 0x8c7e00f803f803f8

def z584 : W := mkw 0x0238000450c04041 0x8011c00022860202 0xe638001c70e040f7 0xd731c000e3870207

def z585 : W := mkw 0x07781a947ac07253 0x883bc0d4a3d60392 0x8e581b1c73007300 0x8472c0d8e3980398

def z586 : W := mkw 0x054500002a040002 0x402a280001502000 0x118600000c060000 0x008c300000603000

def z587 : W := mkw 0x07f536003e452a02 0xe03fa9b001f22950 0x5fa638003c67b004 0x02fd31c001e33d80

def z588 : W := mkw 0x05c036002a000002 0x002e01b001500000 0xefc03f007f00000e 0xcf7e01f803f80000

def z589 : W := mkw 0x077508b03a649092 0xd83ba84581d32484 0x5fa638e03c67b004 0x02fd31c701e33d80

def z590 : W := mkw 0x87f72462842b8ca8 0x343fb92314215c65 0xf7ffe4e38cff8cff 0x7fbfff271c67fc67

def z591 : W := mkw 0x477dc10d7bd44143 0xc23bee086bdea20a 0x8659c31c73004300 0x8432ce18e3980218

def z592 : W := mkw 0x000000002e012a02 0x2000000001700950 0xa04007007f01ff1e 0xcd02003803f80ff8

def z593 : W := mkw 0x023d40007bd40003 0xc011ea0003dea000 0x103fc0007ffe000e 0x3081fe0003fff000

def z594 : W := mkw 0x0000000080080420 0x0000000004004021 0xa0400703c3984ffb 0xfd0200381e1cc27f

def z595 : W := mkw 0x823f4062d1fe84a9 0xd411fa03168ff425 0x103fc0e380fe00e1 0x3081fe071c07f007

def z596 : W := mkw 0x05c0360004010800 0x202e01b000200840 0xefc03f000c018c1e 0xcf7e01f800600c60

def z597 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000200000018016 0x4300010000000c00

def z598 : W := mkw 0x0ff7ffdb2b14001e 0x407fbffed958a000 0xffffffff8f1e0009 0xfffffffffc78f000

def z599 : W := mkw 0x0238000050c00001 0x8011c00002860000 0xee38380070e1f016 0xd771c1c003870f80

def z600 : W := mkw 0x477dc9bdfbfcd5f3 0xda3bee4defdfe6af 0xffffffffffffffff 0xffffffffffffffff

def z601 : W := mkw 0x0008400041900001 0x00004200020c8000 0x000000004398000a 0x00000000021cc000

def z602 : W := mkw 0xc08a6466c5bbcde9 0x36045323362dde6f 0x71a624e3cfffcfff 0x7b8d31271e7ffe7f

def z603 : W := mkw 0x023889bd50e0d0d1 0x9811c44dea870686 0xee79fffff0e1f0f7 0xff73cfffff870f87

def z604 : W := mkw 0x0000002000208080 0x1000000100010404 0x402020e000618004 0x0201010700030c00

def z605 : W := mkw 0x477dc10dfbdc4563 0xc23bee086fdee22b 0xf7ffc01ffffe00ef 0x3fbffe00fffff007

def z606 : W := mkw 0x0ababfff50e0d0dd 0x9855d5fffa870686 0xee383ffff0e1f0f7 0xd771c1ffff870f87

def z607 : W := mkw 0x05c036002a002202 0x002e01b001500110 0xefc03f0073007300 0xcf7e01f803980398

def z608 : W := mkw 0x0f7d9bbd50e0d0d5 0x987becddea870686 0xee79fbfc70e1f0f7 0xd773cfdfe3870f87

def z609 : W := mkw 0x02b83eb454e1fad1 0xb815c1f5a2a70fd6 0xee383ffc70e1fff7 0xd771c1ffe3870fff

def z610 : W := mkw 0x077500003a440002 0xc03ba80001d22000 0xf7e600007f66000e 0x0fbf300003fb3000

def z611 : W := mkw 0x0ff73ed20000001c 0x007fb9f690000000 0xffe63fe000000000 0xcfff31ff00000000

def z612 : W := mkw 0x07f03eb03e61ba92 0xb83f81f581f30dd4 0x4fa038e03c61b004 0x027d01c701e30d80

def z613 : W := mkw 0x4000810d80084560 0x020004086c00422b 0xa040071fc3004ffb 0xcd020038fe18027f

def z614 : W := mkw 0x000000002e012a02 0x2000000001700950 0x000000003c01b004 0x0000000001e00d80

def z615 : W := mkw 0x454dc10deb9c4563 0x422a6e086f5ce22b 0xb1dfc71fcf9e4ffb 0xfd8efe38fe7cf27f

def z616 : W := mkw 0x0000000000000000 0x0000000000000000 0x8040030043004300 0x8402001802180218

def z617 : W := mkw 0x0000000080080420 0x0000000004004021 0x00000003809800e1 0x300000001c04c007

def z618 : W := mkw 0x0008c10941900001 0x000046084a0c8000 0xa059c71fc398000b 0xfd02ce38fe1cc000

def z619 : W := mkw 0x87ff7662ffffaeab 0xf43ffbb317fffd75 0xffffffe3ffffffff 0xffffffff1fffffff

def z620 : W := mkw 0x0000000080080420 0x0000000004004021 0x71a604038cfe0cff 0x7b8d30201c67f067

def z621 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000007001f016 0x0000000003800f80

def z622 : W := mkw 0x80020062842b8ca8 0x3400100314215c65 0x102600e38cff8cff 0x308130071c67fc67

def z623 : W := mkw 0x0238002450e0d0c1 0x9811c00122870686 0xe638000070e1f0f6 0x1731c00003870f87

def z624 : W := mkw 0x054012002a002202 0x002a009001500110 0xefc01b007f00730e 0x8f7e00d803f80398

def z625 : W := mkw 0x05c0360000000000 0x002e01b000000000 0xefc03f0043004f1a 0xcf7e01f802180278

def z626 : W := mkw 0x0008002440a0c0c1 0x1000400122050606 0xe03820fc40e1c0f7 0xd701c107e2070e07

def z627 : W := mkw 0x82ba2cf6d4ebdcf9 0xbc15d167b6a75ee7 0x71be24ff8cff8cff 0x7b8df127fc67fc67

def z628 : W := mkw 0x8ff7bffb802a84bc 0x147fbdffdc015425 0xffffffff80fe00e1 0xfffffffffc07f007

def z629 : W := mkw 0x008036002e012a02 0x200401b001700950 0x08003f007f01ff1e 0xc04001f803f80ff8

def z630 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xa659c0007398000a 0x3d32ce00039cc000

def z631 : W := mkw 0x0ff7b74b0000000c 0x007fbdba58000000 0xf7ffc70380000000 0x3fbffe381c000000

def z632 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000070000004f10 0xc000003800000278

def z633 : W := mkw 0x023d400051d40001 0xc011ea00028ea000 0xf63fc00070fe0006 0x37b1fe000387f000

def z634 : W := mkw 0x4238c10dd1d84561 0x8211c6086e8ec22b 0xe679c71ff3f84fff 0xff33ce38ff9fc27f

def z635 : W := mkw 0xc082e56b853b8da8 0x3604172b5c29dc6d 0x71e7e7e38fff8fff 0x7b8f3f3f1c7ffc7f

def z636 : W := mkw 0x0dc2bfdb2e012a1e 0x206e15fed9700950 0xefc03fffff01ff1f 0xcf7e01fffff80ff8

def z637 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0x4f803f003c01ff14 0xc27c01f801e00ff8

def z638 : W := mkw 0x4dc7f74b8118052c 0x026e3fba5c08c029 0x11c7c70383180f08 0x288e3e381c18c078

def z639 : W := mkw 0xc008c12dc5bbcde1 0x360046096e2dde6f 0xa059c71fcfffcfff 0xfd02ce38fe7ffe7f

def z640 : W := mkw 0x0230089000000010 0x0011804480000000 0x8e18181c00000000 0x8470c0c0e0000000

def z641 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xefc03f000f000f08 0xcf7e01f800780078

def z642 : W := mkw 0x8ff7bffb842b8cbc 0x347fbdffdc215c65 0xffffffff80018cf1 0xfffffffffc000c67

def z643 : W := mkw 0x07f83eb450e0d0d1 0x983fc1f5a2870686 0xeff83ffc70e1f0f7 0xdf7fc1ffe3870f87

def z644 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0x967fc00073fe0000 0x34b3fe00039ff000

def z645 : W := mkw 0x80020062802a84a8 0x1400100314015425 0x302604e380fe0cfb 0x798130271c07f067

def z646 : W := mkw 0x80000020ae2baea2 0x3400000105715d75 0x000000007ffffffe 0x0000000003ffffff

def z647 : W := mkw 0x0008002450e0d0c1 0x9800400122870686 0x602020e070e1f0f7 0x5301010703870f87

def z648 : W := mkw 0x0ff7bfff0020d0dc 0x187fbdfff8010686 0xffffffff8001f0f1 0xfffffffffc000f87

def z649 : W := mkw 0x82b22cf2842b8cb8 0x3415916794215c65 0xffbe3cff8cff8cff 0xfffdf1e7fc67fc67

def z650 : W := mkw 0x80080024d4ebdce1 0xbc00400126a75ee7 0x000000007cfffcfe 0x0000000003e7ffe7

def z651 : W := mkw 0x0080240004010800 0x2004012000200840 0x71a624000cff8c1e 0x7b8d31200067fc60

def z652 : W := mkw 0x80822462ae2baeaa 0x3404112315715d75 0x71a624e3ffffffff 0x7b8d31271fffffff

def z653 : W := mkw 0x488affdfc198457d 0x024457fefe0cc22b 0xa859ffffc3984ffb 0xfd42cffffe1cc27f

def z654 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xef8038007c01f016 0xc77c01c003e00f80

def z655 : W := mkw 0x05c0b70900000000 0x002e05b848000000 0xefd9ff1f80000001 0xff7ecff8fc000000

def z656 : W := mkw 0x4008c10d41904141 0x020046086a0c820a 0xa059c71c43004f1a 0xcd02ce38e2180278

def z657 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x51a620e00cff8cfe 0x028d31070067fc67

def z658 : W := mkw 0x4f7ddb9d41904155 0x027beedcea0c820a 0x8e59db1c43004300 0x8472ced8e2180218

def z659 : W := mkw 0x808a6462c5bb8ca9 0x34045323162ddc65 0xf1ffe4e3cfff8cff 0x7f8fff271e7ffc67

def z660 : W := mkw 0x0000089000000010 0x0000004480000000 0x080038fc00000001 0xc04001c7e0000000

def z661 : W := mkw 0x054000002a000002 0x002a000001500000 0xefc038007f01f01e 0xcf7e01c003f80f80

def z662 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xee3838fc00e000e1 0xd771c1c7e0070007

def z663 : W := mkw 0x4008c10d41904141 0x020046086a0c820a 0xa059c31c438043f3 0xd502ce18e21c021f

def z664 : W := mkw 0x4fffffdfc198457d 0x027ffffefe0cc22b 0xffffffff809800e1 0xfffffffffc04c007

def z665 : W := mkw 0x000000002e012a02 0x2000000001700950 0x000000000f000f08 0x0000000000780078

def z666 : W := mkw 0x077d48b47bf4d0d3 0xd83bea45a3dfa686 0xf7ffc0fc7ffe00ef 0x3fbffe07e3fff007

def z667 : W := mkw 0x0000000000000000 0x0000000000000000 0xa040070000000000 0xcd02003800000000

def z668 : W := mkw 0x8ff73ef2842b8cbc 0x347fb9f794215c65 0x7fa63ce38cff8cff 0x7bfd31e71c67fc67

def z669 : W := mkw 0x45c8f70def996f63 0x222e47b86f7ccb7b 0xa1d9c71fcf984ffb 0xfd0ece38fe7cc27f

def z670 : W := mkw 0x477dc10dfbdc4563 0xc23bee086fdee22b 0xa659c71ff3984ffb 0xfd32ce38ff9cc27f

def z671 : W := mkw 0x0080240004010800 0x2004012000200840 0x018004000c000c08 0x080c002000600060

def z672 : W := mkw 0x07f03e902e012a12 0x203f81f481700950 0xeff83ffc7f01ff1f 0xdf7fc1ffe3f80ff8

def z673 : W := mkw 0x0238089450c05051 0x8811c044a2860282 0xae18181c708070f3 0xd570c0c0e3840387

def z674 : W := mkw 0x0ff73ed20000001c 0x007fb9f690000000 0x7fa63ce380000001 0x7bfd31e71c000000

def z675 : W := mkw 0x0008000040800001 0x0000400002040000 0xa018000040800002 0x1500c00002040000

def z676 : W := mkw 0x0000002000208080 0x1000000100010404 0x71a620e00cff80ff 0x7b8d31070067fc07

def z677 : W := mkw 0x87ff6cf6ffffdcfb 0xfc3ffb67b7fffee7 0xfffffcfffffffcff 0xffffffe7ffffffe7

def z678 : W := mkw 0x0545000000000000 0x002a280000000000 0x11c7c00000000000 0x288e3e0000000000

def z679 : W := mkw 0x000040002b140002 0x400002000158a000 0x000000000f1e0008 0x000000000078f000

def z680 : W := mkw 0x0ff73ed20000001c 0x007fb9f690000000 0xfffff8e000000000 0x3fffffc700000000

def z681 : W := mkw 0x0f7ddb997bd40017 0xc07beedccbdea000 0xffffdb1c7ffe000e 0xbffffed8e3fff000

def z682 : W := mkw 0x4008c109c1980521 0x020046084e0cc029 0xa059c703c3980f0a 0x3d02ce381e1cc078

def z683 : W := mkw 0x05c0b7092e012a02 0x202e05b849700950 0xefd9ff1fff01ff1f 0xff7ecff8fff80ff8

def z684 : W := mkw 0x000008b40020d0d0 0x18000045a0010686 0x000000fc000000e1 0x00000007e0000007

def z685 : W := mkw 0x0000002000208080 0x1000000100010404 0x0000000000e180f6 0x0000000000070c07

def z686 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0x8e3818fc70e070e1 0x9471c0c7e3870387

def z687 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x118624e38c1f8cf9 0x688c31271c60fc67

def z688 : W := mkw 0x4238c99d51d05151 0x8a11c64cea8e828a 0x8e59db1c73007300 0x8472ced8e3980398

def z689 : W := mkw 0x823a08f6d0ead4f9 0x9c11d047b68756a7 0xfe3e38fff0fff0f7 0xf7f1f1c7ff87ff87

def z690 : W := mkw 0x4000810980080520 0x020004084c004029 0x0000070380000f00 0x000000381c000078

def z691 : W := mkw 0x077500003a440002 0xc03ba80001d22000 0xf7ffc0003c660004 0x3fbffe0001e33000

def z692 : W := mkw 0x0dc7b74b2e012a0e 0x206e3dba59700950 0xffc7ff03ff01ff1e 0xeffe3ff81ff80ff8

def z693 : W := mkw 0xc08ae54fc59b4d69 0x2604572a7e2cda6b 0xb1dfc71fcf9e4ffb 0xfd8efe38fe7cf27f

def z694 : W := mkw 0x85c22462ae2b8caa 0x342e112315715c65 0xf7e624e3ffff8cff 0x7fbf31271ffffc67

def z695 : W := mkw 0x4238c9bdd1f8d5f1 0x9a11c64dee8fc6af 0xee39f8fff0f9f0f7 0xf771cfc7ff87cf87

def z696 : W := mkw 0x0000000000000000 0x0000000000000000 0x200000000098000a 0x390000000004c000

def z697 : W := mkw 0x8ff73ef20423889c 0x347fb9f790211c44 0x5fa638e00c678004 0x02fd31c700633c00

def z698 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0x6f803c003c01bc1e 0x4b7c01e001e00de0

def z699 : W := mkw 0x02b22cd200000018 0x0015916690000000 0xffbe3cff80000001 0xfffdf1e7fc000000

def z700 : W := mkw 0x0080360004012a00 0x200401b000200950 0x69803f000c01ff1e 0xcb4c01f800600ff8

def z701 : W := mkw 0x000840007bd40003 0xc000420003dea000 0x71a600007ffe000e 0x3b8d300003fff000

def z702 : W := mkw 0x023008b010609090 0x9811804580830484 0xee2038e07061f016 0xc77101c703830f80

def z703 : W := mkw 0x02b82cb454e1d8d1 0xb815c165a2a70ec6 0xefb83cfc7ce1fcff 0xdf7dc1e7e3e70fe7

def z704 : W := mkw 0x4000810d80084560 0x020004086c00422b 0x2000071f80984ffb 0xf9000038fc04c27f

def z705 : W := mkw 0x82ba2462d4eb8ca9 0xb415d12316a75c65 0xf7be24e3fcff8cff 0x7fbdf1271fe7fc67

def z706 : W := mkw 0x023808b47ee1fad3 0xb811c045a3f70fd6 0xee3838fc7fe1ffff 0xd771c1c7e3ff0fff

def z707 : W := mkw 0x4fff7ed6c198457d 0x027ffbf6b60cc22b 0x5fa638e043984ffa 0x02fd31c7021cc27f

def z708 : W := mkw 0x0000810900000000 0x0000040848000000 0xe079e7ff80000001 0xff03cf3ffc000000

def z709 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xf7ffe0007fff801e 0x7fbfff0003fffc00

def z710 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0xffffffffff000f0f 0xfffffffffff80078

def z711 : W := mkw 0x0dcfb76f50e0d0cd 0x986e7dbb7a870686 0x11c7c703f0e1f0f6 0x288e3e381f870f87

def z712 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xdfffffff80000001 0xc6fffffffc000000

def z713 : W := mkw 0x477d40047bd44143 0xc23bea0023dea20a 0xf7ffc0007ffe430e 0x3fbffe0003fff218

def z714 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0x4e3838fc30e1f0f5 0xd271c1c7e1870f87

def z715 : W := mkw 0x023008b41060d0d0 0x98118045a0830686 0x0e0038fc3001f0f1 0xc07001c7e1800f87

def z716 : W := mkw 0xc0084024efbbefe3 0x36004201277ddf7f 0x000000007ffffffe 0x0000000003ffffff

def z717 : W := mkw 0x87ff6462ffff8cab 0xf43ffb2317fffc65 0x8659e4e3f3018cf1 0x4432cf271f980c67

def z718 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0x71bfc0ff8cfe000f 0x3b8dfe07fc67f000

def z719 : W := mkw 0x40084024c1b8c5e1 0x12004201260dc62f 0x0000000043f9cffe 0x00000000021fce7f

def z720 : W := mkw 0x054d40007bd40003 0xc02a6a0003dea000 0x11c7c0000ffe0008 0x288e3e00007ff000

def z721 : W := mkw 0x0082a54b00000008 0x0004152a58000000 0x71bfe4ff80000001 0x7b8dff27fc000000

def z722 : W := mkw 0x0f779bdb0000001c 0x007bbcded8000000 0x1e3fd8ff80000001 0x30f1fec7fc000000

def z723 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xefe03fe07f01ff1f 0xdf7f01ff03f80ff8

def z724 : W := mkw 0xc0084024d5fbdde1 0xbe00420126afdeef 0x000000007ffffffe 0x0000000003ffffff

def z725 : W := mkw 0x080289db0000001c 0x0040144ed8000000 0xa059c7ff80000001 0xfd02ce3ffc000000

def z726 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xee79ffff80000001 0xd773cffffc000000

def z727 : W := mkw 0x023008b000208090 0x1011804580010404 0xee3838fc70e1f0f7 0xd771c1c7e3870f87

def z728 : W := mkw 0x0ff7bfdb04012a1c 0x207fbdfed8200950 0xffffffffc301ff1b 0xfffffffffe180ff8

def z729 : W := mkw 0x0f7789db0000001c 0x007bbc4ed8000000 0xfffff8ff80000001 0xffffffc7fc000000

def z730 : W := mkw 0x054d40007bd40003 0xc02a6a0003dea000 0x71e7c0007ffe000e 0x3b8f3e0003fff000

def z731 : W := mkw 0x0ff7bfdb2a00001e 0x007fbdfed9500000 0xfffffffff3000001 0xffffffffff980000

def z732 : W := mkw 0xc08ae56f45b3c9c9 0x3604572b7a2d9e4e 0xd1ffe3fc4f67c304 0x868fff1fe27b3e18

def z733 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0x8e59fffff301ff11 0xc472cfffff980ff8

def z734 : W := mkw 0x0f7ddb9d7bd45057 0xc87beedcebdea282 0x8e59db1c73007000 0x8472ced8e3980380

def z735 : W := mkw 0x0230899900000010 0x0011844cc8000000 0xa079c7ff80000001 0xfd03ce3ffc000000

def z736 : W := mkw 0x45c8f70def996f63 0x222e47b86f7ccb7b 0x4f99f81fbc99b0e5 0x327ccfc0fde4cd87

def z737 : W := mkw 0x0a3789db2e012a1e 0x2051bc4ed9700950 0x103fc0ffff01ff1f 0x3081fe07fff80ff8

def z738 : W := mkw 0x054548b42b34d0d2 0x582a2a45a159a686 0x19c7f8fc0f1ff0f9 0xe8ce3fc7e078ff87

def z739 : W := mkw 0x077d48907bd40013 0xc03bea4483dea000 0xfffff8fc7ffff01f 0xffffffc7e3ffff80

def z740 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xee383cfc70e1fcff 0xdf71c1e7e3870fe7

def z741 : W := mkw 0x088affdb7bd4001f 0xc04457fedbdea000 0x08003ffffffe000f 0xc04001fffffff000

def z742 : W := mkw 0x05c236422e012a0a 0x202e11b211700950 0xefc03fe3ff01ff1f 0xcf7e01ff1ff80ff8

def z743 : W := mkw 0x0ff7bfdb04012a1c 0x207fbdfed8200950 0xffffffff8c01ff1f 0xfffffffffc600ff8

def z744 : W := mkw 0x0ff7bfdb2a00001e 0x007fbdfed9500000 0xffffffffbc000005 0xfffffffffde00000

def z745 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xfffff8007fffb00e 0x3fffffc003fffd80

def z746 : W := mkw 0x077d52007bd42203 0xc03bea9003dea110 0xffffdf007ffe7f1e 0xfffffef803fff3f8

def z747 : W := mkw 0x0ab7bfdb0000001c 0x0055bdfed8000000 0xfe3fffff80000001 0xf7f1fffffc000000

def z748 : W := mkw 0x0082246200208088 0x1004112310010404 0x71a624e38cff80ff 0x7b8d31271c67fc07

def z749 : W := mkw 0x054d40007bd40003 0xc02a6a0003dea000 0xf7c7c0007ffe000e 0x2fbe3e0003fff000

def z750 : W := mkw 0x02bd760055d52a01 0xe015ebb002aea950 0x183fff0000ffff10 0xf0c1fff80007fff8

def z751 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0x5fbff8ffbc01b005 0x32fdffc7fde00d80

def z752 : W := mkw 0xc0084024c5bbcde1 0x36004201262dde6f 0x000000000cff8cfe 0x000000000067fc67

def z753 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0xf1ffe4e38cff8cff 0x7f8fff271c67fc67

def z754 : W := mkw 0x4008c10dd1dc4561 0xc20046086e8ee22b 0xa059c71fc3fe4ffb 0xfd02ce38fe1ff27f

def z755 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0x4e2038fc70e1f0f7 0xc27101c7e3870f87

def z756 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xffffd8007ffe700e 0xbffffec003fff380

def z757 : W := mkw 0x0ff7bfdb1044001c 0xc07fbdfed8822000 0xffffffff80660001 0xfffffffffc033000

def z758 : W := mkw 0x077d400041900001 0x003bea00020c8000 0xf7ffc0004ffe000e 0x3fbffe00027ff000

def z759 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffffffff8001f011 0xfffffffffc000f80

def z760 : W := mkw 0x000808b440a0d0d1 0x18004045a2050686 0xee1838fc7081f0f7 0xd770c1c7e3840f87

def z761 : W := mkw 0x023848b451f0d0d1 0x9811c245a28f8686 0xee39f8fc70f9f0f7 0xf771cfc7e387cf87

def z762 : W := mkw 0x0ab7addb0401081c 0x2055bd6ed8200840 0x71bfe4ff8c018c1f 0x7b8dff27fc600c60

def z763 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0x71bfc0ff80000001 0x3b8dfe07fc000000

def z764 : W := mkw 0xc082a56b842b8da8 0x3604152b5c215c6d 0x000027e380018ff1 0x4000013f1c000c7f

def z765 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0xffffffff8f018f1f 0xfffffffffc780c78

def z766 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0x8e1838fc70e1f0f7 0xc470c1c7e3870f87

def z767 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0xfe3ff8fff001f017 0xf7f1ffc7ff800f80

def z768 : W := mkw 0x0f7789db0000001c 0x007bbc4ed8000000 0x11ffc0ff80000001 0x388ffe07fc000000

def z769 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xa859ff1fc399fffb 0xfd42cff8fe1ccfff

def z770 : W := mkw 0x82ba2cd6d4cb5c79 0xac15d166b6a65ae3 0x9f9e1c1ffc1e7c08 0xacfcf0e0ffe0f3e0

def z771 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xce3838fc7061f0f5 0xc671c1c7e3830f87

def z772 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xae403f007301ff1a 0xcd7201f803980ff8

def z773 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xfffffffff0000007 0xffffffffff800000

def z774 : W := mkw 0x077d40047bd45043 0xc83bea0023dea282 0xf7ffc0007ffe700e 0x3fbffe0003fff380

def z775 : W := mkw 0x4f7ddb9d7bd44157 0xc27beedcebdea20a 0x8e59db1c73004300 0x8472ced8e3980218

def z776 : W := mkw 0x05c2b74b2e012a0a 0x202e15ba59700950 0xffffffffff01ff1f 0xfffffffffff80ff8

def z777 : W := mkw 0x4008c10dd1d85561 0x8a0046086e8ec2ab 0xa059c71ff3987ffb 0xfd02ce38ff9cc3ff

def z778 : W := mkw 0x0230899900000010 0x0011844cc8000000 0x0039c0ff80000001 0x3001ce07fc000000

def z779 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xefb838fc7ce1f0ff 0xdf7dc1c7e3e70f87

def z780 : W := mkw 0x8882bfff842bdcfc 0x3c4415fffc215ee7 0x08003fff8001fcf1 0xc04001fffc000fe7

def z781 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0x11ffc0007ffe000e 0x388ffe0003fff000

def z782 : W := mkw 0x0ab7bfdb0000001c 0x0055bdfed8000000 0x103fc7ff80000001 0x3081fe3ffc000000

def z783 : W := mkw 0x0775899900000010 0x003bac4cc8000000 0xffffffff80000001 0xfffffffffc000000

def z784 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xa059c71fc3004ffb 0xcd02ce38fe18027f

def z785 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xee783ffc70e1f0f7 0xdf73c1ffe3870f87

def z786 : W := mkw 0x077d48907bd40013 0xc03bea4483dea000 0xf7ffc0fc7ffe000f 0x3fbffe07e3fff000

def z787 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0xfe7fffff80000001 0xfff3fffffc000000

def z788 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0x8e403f007f01ff1e 0xc47201f803f80ff8

def z789 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xefd83f1c7f01ff1f 0xdf7ec1f8e3f80ff8

def z790 : W := mkw 0x0238089440804051 0x0011c044a2040202 0xee3838fc7081f0f7 0xd771c1c7e3840f87

def z791 : W := mkw 0x0882bfdb0000001c 0x004415fed8000000 0x0819ffff80000001 0xf040cffffc000000

def z792 : W := mkw 0x80823662842baea8 0x340411b314215d75 0xffa63fe3fcffffff 0xfffd31ff1fe7ffff

def z793 : W := mkw 0x077540003b540002 0xc03baa0001daa000 0xf7ffc0003f7e000c 0x3fbffe0001fbf000

def z794 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xefc03f03ff01ff1f 0xff7e01f81ff80ff8

def z795 : W := mkw 0x8882bffb842baebc 0x344415ffdc215d75 0x08003fff8001fff1 0xc04001fffc000fff

def z796 : W := mkw 0x0005400001140000 0x40002a000008a000 0x71a7c0000cfe000e 0x3b8d3e000067f000

def z797 : W := mkw 0x077d48907bd41013 0xc83bea4483dea080 0xffffd8007ffe300e 0x3ffffec003fff180

def z798 : W := mkw 0x0002814b00000008 0x0000140a58000000 0x103fc0ff80000001 0x3081fe07fc000000

def z799 : W := mkw 0x0ff7bfdb2a00221e 0x007fbdfed9500110 0xffffffffb0003001 0xfffffffffd800180

def z800 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xefd9ff007f01ff1e 0xff7ecff803f80ff8

def z801 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0x71ffc0000ffe000e 0x3b8ffe00007ff000

def z802 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xffffff007fffff1e 0xfffffff803fffff8

def z803 : W := mkw 0x4775810dba4c4562 0xc23bac086dd2622b 0x57a6071fbc664ff5 0xc2bd3038fde3327f

def z804 : W := mkw 0x0235000000000000 0x0011a80000000000 0x71bfc0000cfe000e 0x3b8dfe000067f000

def z805 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0xefd9ffffff01ff1f 0xcf7ecffffff80ff8

def z806 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xffc63f007f1fff1e 0xeffe31f803f8fff8

def z807 : W := mkw 0x8f759bb9842b8cb4 0x347bacddcc215c65 0x8e59db1c0cff8cfe 0x8472ced8e067fc67

def z808 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffffffff80e00007 0xfffffffffc070000

def z809 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xae59ffff80000001 0xfd72cffffc000000

def z810 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0x0059c71f83984ff9 0xf802ce38fc1cc27f

def z811 : W := mkw 0x000000002e012a02 0x2000000001700950 0xee403f007f01ff1e 0xcf7201f803f80ff8

def z812 : W := mkw 0x0002814b00000008 0x0000140a58000000 0xb07fc7ff80000001 0xfd83fe3ffc000000

def z813 : W := mkw 0x07f72cd200000018 0x003fb96690000000 0xfffffcff80000001 0xffffffe7fc000000

def z814 : W := mkw 0x054012002e012a02 0x202a009001700950 0xee403b007f01ff1e 0xc77201d803f80ff8

def z815 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0xffffffffbf01bf0d 0xfffffffffdf80df8

def z816 : W := mkw 0x0f779bdb0000001c 0x007bbcded8000000 0x8e59dbff80000001 0x8472cedffc000000

def z817 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xf1ffc71fc3984ffb 0xff8ffe38fe1cc27f

def z818 : W := mkw 0x4000c10981180520 0x020006084c08c029 0xa059c71f83980ffb 0xfd02ce38fc1cc07f

def z819 : W := mkw 0x80823662842baea8 0x340411b314215d75 0x79a63ce38cffbcff 0x7bcd31e71c67fde7

def z820 : W := mkw 0x077500002a000002 0x003ba80001500000 0xf7ffc0007ffe000e 0x3fbffe0003fff000

def z821 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0x57ffc0003ffe000c 0x3abffe0001fff000

def z822 : W := mkw 0x077d52007bd42203 0xc03bea9003dea110 0xf7ffc3007ffe030e 0x3fbffe1803fff018

def z823 : W := mkw 0x077540003b540002 0xc03baa0001daa000 0x77e7c0003ffe000e 0x3bbf3e0001fff000

def z824 : W := mkw 0x0882bfdb0000001c 0x004415fed8000000 0x8859ffff80000001 0xc442cffffc000000

def z825 : W := mkw 0x02b2addb00000018 0x0015956ed8000000 0xffffffff80000001 0xfffffffffc000000

def z826 : W := mkw 0x023d08b450e0d0d1 0x9811e845a2870686 0xfe3ff8fc70e1f0f7 0xf7f1ffc7e3870f87

def z827 : W := mkw 0x054d40007bd40003 0xc02a6a0003dea000 0xb1dfc0007ffe000e 0x3d8efe0003fff000

def z828 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0x9e7fffff80000001 0xf4f3fffffc000000

def z829 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffffffff80018017 0xfffffffffc000c00

def z830 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0x107fc7ff80000001 0x3883fe3ffc000000

def z831 : W := mkw 0x0082244280080428 0x0004112214004021 0x71a624e38cfe0cff 0x7b8d31271c67f067

def z832 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffbff8ff80000001 0xf7fdffc7fc000000

def z833 : W := mkw 0x000808b450e0d0d1 0x98004045a2870686 0xee0038fc70e1f0f7 0xc77001c7e3870f87

def z834 : W := mkw 0x0ff7bfdb1040001c 0x807fbdfed8820000 0xffffffffb0600005 0xfffffffffd830000

def z835 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0xb07fc0ff80000001 0x3d83fe07fc000000

def z836 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xee79f8fc70e1f0f7 0xff73cfc7e3870f87

def z837 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0x303fc4ff80000001 0x7981fe27fc000000

def z838 : W := mkw 0x0000400001100000 0x0000020000088000 0x71e7c0000ffe000e 0x3b8f3e00007ff000

def z839 : W := mkw 0x023848b451f4d0d1 0xd811c245a28fa686 0xee3838fc70fff0f7 0xd771c1c7e387ff87

def z840 : W := mkw 0x0008002440a0c0c1 0x1000400122050606 0xee3838fc70e1f0f7 0xd771c1c7e3870f87

def z841 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0xffffffffff01b00f 0xfffffffffff80d80

def z842 : W := mkw 0x0ab7bfdb0000001c 0x0055bdfed8000000 0x79bfffff80000001 0xfbcdfffffc000000

def z843 : W := mkw 0x4230c9b9917895b0 0x9a11864dcc8bc4ad 0x4e61ffe3b379bf0c 0x2a730fff1d9bcdf8

def z844 : W := mkw 0x077d48947bd45053 0xc83bea44a3dea282 0xfffff81c7ffff01e 0xffffffc0e3ffff80

def z845 : W := mkw 0xc0084024c5bbcde1 0x36004201262dde6f 0x000000004399cffa 0x00000000021cce7f

def z846 : W := mkw 0x054540002b140002 0x402a2a000158a000 0x11c7c0000ffe000e 0x288e3e00007ff000

def z847 : W := mkw 0x077d40047bd44043 0xc03bea0023dea202 0xf7ffc01c7ffe00ef 0x3fbffe00e3fff007

def z848 : W := mkw 0x0ab7addb0000001c 0x0055bd6ed8000000 0x51bfe0ff80000001 0x328dff07fc000000

def z849 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x11a604e38cff8cff 0x388d30271c67fc67

def z850 : W := mkw 0x0ff7bfdb2a00001e 0x007fbdfed9500000 0xffffffff8f000009 0xfffffffffc780000

def z851 : W := mkw 0x80020062802a84a8 0x1400100314015425 0x11a600e38cfe00e9 0x388d30071c67f007

def z852 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xf7ffc0007ffe4f1e 0x3fbffe0003fff278

def z853 : W := mkw 0x8ff7bfdb0403081c 0x247fbdfed8201840 0xffffffff8c060001 0xfffffffffc603000

def z854 : W := mkw 0x80823662842baea8 0x340411b314215d75 0x71a627e38cff8fff 0x7b8d313f1c67fc7f

def z855 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xf7bfc0007cfe0006 0x37bdfe0003e7f000

def z856 : W := mkw 0x0f759b9900000014 0x007bacdcc8000000 0xee79ffff80000001 0xff73cffffc000000

def z857 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffffffff83000f09 0xfffffffffc180078

def z858 : W := mkw 0x0ff7bfdb2a00221e 0x007fbdfed9500110 0xffffffff83000301 0xfffffffffc180018

def z859 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xf7ffc0007ffe401e 0xffbffe0003fff200

def z860 : W := mkw 0x05c536002e052a02 0x602e29b001702950 0xffc63f007f07ff1e 0xcffe31f803f83ff8

def z861 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xa059c71fc3804ff3 0xd502ce38fe1c027f

def z862 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0x11bfc0ff80000001 0x308dfe07fc000000

def z863 : W := mkw 0x0ff7bfdb3e452a1e 0xe07fbdfed9f22950 0xffffffffff67ff1f 0xfffffffffffb3ff8

def z864 : W := mkw 0x077d48947bd44053 0xc03bea44a3dea202 0xfffff8fc7ffe40ff 0xffffffc7e3fff207

def z865 : W := mkw 0x0ab7addb0000001c 0x0055bd6ed8000000 0xffbffcff80000001 0xfffdffe7fc000000

def z866 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xefc03f007f99ff1e 0xff7e01f803fccff8

def z867 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xee403f007301ff16 0xc77201f803980ff8

def z868 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0xb07fc7ffc3004f1b 0xfd83fe3ffe180278

def z869 : W := mkw 0x8882adfb842b8cbc 0x3444156fdc215c65 0x000024ff80018cf1 0x40000127fc000c67

def z870 : W := mkw 0x054012002e012a02 0x202a009001700950 0xefc01b007f01ff1e 0x8f7e00d803f80ff8

def z871 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xf7ffc7ff80000001 0x3fbffe3ffc000000

def z872 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffffffffb001b005 0xfffffffffd800d80

def z873 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0x9fffdfff80000001 0xbcfffefffc000000

def z874 : W := mkw 0x077540003b540002 0xc03baa0001daa000 0x57a7c0003c7e0004 0x22bd3e0001e3f000

def z875 : W := mkw 0x023d48b451f4d0d1 0xd811ea45a28fa686 0xee39f8fc70e1f0f7 0xd771cfc7e3870f87

def z876 : W := mkw 0x4dc7f74baf192f2e 0x226e3fba5d78c979 0x11c7c7038f180f08 0x288e3e381c78c078

def z877 : W := mkw 0x07f83eb47ee1fad3 0xb83fc1f5a3f70fd6 0x01f807fc0fe00fe9 0x180fc03fe07f007f

def z878 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffffffffc300000b 0xfffffffffe180000

def z879 : W := mkw 0x0dc2bfdb0000001c 0x006e15fed8000000 0xefd9ffff80000001 0xff7ecffffc000000

def z880 : W := mkw 0xc082a56f842bcde8 0x3604152b7c215e6f 0x000024ff80018cf1 0x40000127fc000c67

def z881 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x51a624e38cff8cff 0x428d31271c67fc67

def z882 : W := mkw 0x40084024d1f8d5e1 0x9a004201268fc6af 0x0000000000f800e0 0x000000000007c007

def z883 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x71a627e38cffcfff 0xfb8d313f1c67fe7f

def z884 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffffffff80000c1b 0xfffffffffc000060

def z885 : W := mkw 0x023d48b451f4d0d1 0xd811ea45a28fa686 0xffbff8fc7cfff0ff 0xfffdffc7e3e7ff87

def z886 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffffffff80fe0001 0xfffffffffc07f000

def z887 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xf7ffc3007ffe430e 0xbfbffe1803fff218

def z888 : W := mkw 0x0dc7bfdb0000001c 0x006e3dfed8000000 0xb9dfffff80000001 0xfdcefffffc000000

def z889 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xa059c71fc3004ff1 0xfd02ce38fe18027f

def z890 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffffffff8c00000f 0xfffffffffc600000

def z891 : W := mkw 0x0082a54b04010808 0x2004152a58200840 0xf1ffe7ffcf01cf1f 0xff8fff3ffe780e78

def z892 : W := mkw 0x0ff7bfdb2a00001e 0x007fbdfed9500000 0xffffffffff004f1f 0xfffffffffff80278

def z893 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xe1d9c71fcf984fff 0xff0ece38fe7cc27f

def z894 : W := mkw 0x0ab7bfdb0000001c 0x0055bdfed8000000 0x183ff8ff80000001 0x30c1ffc7fc000000

def z895 : W := mkw 0x0ff7bfdb0401081c 0x207fbdfed8200840 0xffffffff80018c11 0xfffffffffc000c60

def z896 : W := mkw 0x077d40047bd44043 0xc03bea0023dea202 0xf7ffc71c7ffe4fff 0xffbffe38e3fff27f

def z897 : W := mkw 0x0a3789db1044001c 0xc051bc4ed8822000 0x103fc0ff80660001 0x3081fe07fc033000

def z898 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x31a604e38cfe0cfb 0x798d30271c67f067

def z899 : W := mkw 0x07f7a54b00000008 0x003fbd2a58000000 0xf7ffe7ff80000001 0xffbfff3ffc000000

def z900 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0xf1be24ff8cff8cff 0xff8df127fc67fc67

def z901 : W := mkw 0x023008b40020d0d0 0x18118045a0010686 0xee3838fc7001f0f7 0xd771c1c7e3800f87

def z902 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0x19ffffff80000001 0xf8cffffffc000000

def z903 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x51a624e38cff8cf5 0x728d31271c67fc67

def z904 : W := mkw 0x023848b451f0d0d1 0x9811c245a28f8686 0xee79f8fc73e1f0f7 0xd773cfc7e39f0f87

def z905 : W := mkw 0x8882b76b842b8cac 0x344415bb5c215c65 0x000027e380018cf1 0x4000013f1c000c67

def z906 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xf7ffc4007ffe0c1e 0x7fbffe2003fff060

def z907 : W := mkw 0x077d400051d40001 0xc03bea00028ea000 0xf7ffc0000cfe000e 0x3fbffe000067f000

def z908 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffffffff8c660005 0xfffffffffc633000

def z909 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xee3838fc73e1ffff 0xd771c1c7e39f0fff

def z910 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xd7ffc0007ffe000e 0x06bffe0003fff000

def z911 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0x9fdfffff80000001 0xecfefffffc000000

def z912 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xe079c71fc3f84fff 0xff03ce38fe1fc27f

def z913 : W := mkw 0x054000002a000002 0x002a000001500000 0xefc03f007f01ff1e 0xcf7e01f803f80ff8

def z914 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0x11bfc0000cfe0000 0x308dfe000067f000

def z915 : W := mkw 0x0ff7bfdb0401081c 0x207fbdfed8200840 0xffffffff8cff8c1f 0xfffffffffc67fc60

def z916 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x71a604e38cfe0cef 0x3b8d30271c67f067

def z917 : W := mkw 0x0ab7addb0000001c 0x0055bd6ed8000000 0xf1ffe7ff80000001 0xff8fff3ffc000000

def z918 : W := mkw 0x85421262aa2aa6aa 0x142a109315515535 0x9e661be3f3fe73e1 0xb4f330df1f9ff39f

def z919 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xce3838fc70e1f0f6 0x8671c1c7e3870f87

def z920 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0xf1e624e3cfff8cff 0x7f8f31271e7ffc67

def z921 : W := mkw 0x05c236422e012a0a 0x202e11b211700950 0xffe63fe07f01ff1e 0xcfff31ff03f80ff8

def z922 : W := mkw 0x054540002b140002 0x402a2a000158a000 0xf7e7c0007ffe000e 0x3fbf3e0003fff000

def z923 : W := mkw 0x000008b40020d0d0 0x18000045a0010686 0x4e0038fc3001f0f5 0xc27001c7e1800f87

def z924 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xf7ffc0007ffff01e 0x3fbffe0003ffff80

def z925 : W := mkw 0x054d40006b940003 0x402a6a00035ca000 0xf1ffc0004ffe000e 0x3f8ffe00027ff000

def z926 : W := mkw 0x054540002b140002 0x402a2a000158a000 0x11e7c0000ffe0008 0x388f3e00007ff000

def z927 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xa059c71ff399ffff 0xfd02ce38ff9ccfff

def z928 : W := mkw 0x054012002e012a02 0x202a009001700950 0x8e401b007301ff10 0x847200d803980ff8

def z929 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xb1ffc7ff80000001 0xfd8ffe3ffc000000

def z930 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xee3838fc7cfff0ff 0xd771c1c7e3e7ff87

def z931 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x51a620e38cff8cff 0x328d31071c67fc67

def z932 : W := mkw 0x0ff7bfdb2a00221e 0x007fbdfed9500110 0xfffffffff3007f1b 0xffffffffff9803f8

def z933 : W := mkw 0x077d5a947bd47253 0xc83bead4a3dea392 0xffffdb1c7ffe730e 0xbffffed8e3fff398

def z934 : W := mkw 0x0082a54b00000008 0x0004152a58000000 0xa059e7ff80000001 0xfd02cf3ffc000000

def z935 : W := mkw 0x077540003b540002 0xc03baa0001daa000 0xf7e7c0007f7e000e 0x2fbf3e0003fbf000

def z936 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xd7ffc0007f7e000c 0x2ebffe0003fbf000

def z937 : W := mkw 0x05c236422e012a0a 0x202e11b211700950 0xffe63fe3ffffff1f 0xffff31ff1ffffff8

def z938 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xee3838fc70e1b0e7 0x1771c1c7e3870d87

def z939 : W := mkw 0x023848b451f0d0d1 0x9811c245a28f8686 0xfffff8fc7ffff0ff 0xffffffc7e3ffff87

def z940 : W := mkw 0x80020062802a84a8 0x1400100314015425 0x71a604e38cfe0cff 0x7b8d30271c67f067

def z941 : W := mkw 0x0a379bdb0000001c 0x0051bcded8000000 0x183fdbff80000001 0xb0c1fedffc000000

def z942 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xf7ffe0e07ffe000f 0x7fbfff0703fff000

def z943 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0xfffffffff301ff11 0xffffffffff980ff8

def z944 : W := mkw 0x0ff7bfdb0401081c 0x207fbdfed8200840 0xffffffff8c000c09 0xfffffffffc600060

def z945 : W := mkw 0x0ab2bfdb0000001c 0x005595fed8000000 0xee79ffff80000001 0xff73cffffc000000

def z946 : W := mkw 0x80020062842b8ca8 0x3400100314215c65 0x71a600e38cff8cff 0x3b8d30071c67fc67

def z947 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0xffffffff8c000001 0xfffffffffc600000

def z948 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffffffff8c1e0009 0xfffffffffc60f000

def z949 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xefc03f007f81ffff 0xdf7e01f803fc0fff

def z950 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xee783bfc73e1f3f7 0xd773c1dfe39f0f9f

def z951 : W := mkw 0x07f0bf9900000010 0x003f85fcc8000000 0xeff9ffff80000001 0xff7fcffffc000000

def z952 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0x8e3838fc70e1f0f1 0xd471c1c7e3870f87

def z953 : W := mkw 0x8ff73ef22e23aa9e 0x347fb9f791711d54 0x5fa638e03c67b004 0x02fd31c701e33d80

def z954 : W := mkw 0x0ff7bfdb04012a1c 0x207fbdfed8200950 0xffffffff80000f01 0xfffffffffc000078

def z955 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0x57e7c0007ffe000e 0x2abf3e0003fff000

def z956 : W := mkw 0x0ab7bfdb0000001c 0x0055bdfed8000000 0xb87fffff80000001 0xfdc3fffffc000000

def z957 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xefc03f007fffff1e 0xcf7e01f803fffff8

def z958 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0xffffffffbc01ff15 0xfffffffffde00ff8

def z959 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xee59ff1fc3984ffb 0xff72cff8fe1cc27f

def z960 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0x5fffffff80000001 0x3afffffffc000000

def z961 : W := mkw 0x000008b40020d0d0 0x18000045a0010686 0x8e0038fc7001f0f1 0xc47001c7e3800f87

def z962 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0xf7a624e3fcff8cff 0x7fbd31271fe7fc67

def z963 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0x0019c0ff80000001 0x0000ce07fc000000

def z964 : W := mkw 0x0f7d5a907bd40017 0xc07bead483dea000 0xffffd8007ffe000e 0x3ffffec003fff000

def z965 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0x8fc01f007f01ff1e 0x8c7e00f803f80ff8

def z966 : W := mkw 0x077500003a440002 0xc03ba80001d22000 0xf7ffc0003cfe000e 0x3fbffe0001e7f000

def z967 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xfffff8ff80000001 0x3fffffc7fc000000

def z968 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xffe63f007f01ff1e 0xffff31f803f80ff8

def z969 : W := mkw 0x0dc2bfdb2e012a1e 0x206e15fed9700950 0xefd9ffffff01ff1f 0xff7ecffffff80ff8

def z970 : W := mkw 0x40084024fff9ffe3 0xba00420127ffcfff 0x000000007ff9fffe 0x0000000003ffcfff

def z971 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xee1838fc7001f0f7 0xc770c1c7e3800f87

def z972 : W := mkw 0x000008b40020d0d0 0x18000045a0010686 0xee2038fc70e1f0f7 0xd77101c7e3870f87

def z973 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0x7fbffcff80000001 0x7bfdffe7fc000000

def z974 : W := mkw 0x0ff7bfdb3a44001e 0xc07fbdfed9d22000 0xffffffffbcfe000f 0xfffffffffde7f000

def z975 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0x11ffc7ff8f000f09 0x388ffe3ffc780078

def z976 : W := mkw 0x00000020802884a0 0x1000000104014425 0x71a624e38cff8cff 0x7b8d31271c67fc67

def z977 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffffffff8098000b 0xfffffffffc04c000

def z978 : W := mkw 0x0ab7addb0000001c 0x0055bd6ed8000000 0x103fe4ff80000001 0x7081ff27fc000000

def z979 : W := mkw 0x008036002e012a02 0x200401b001700950 0xee003f007f01ff1e 0xc77001f803f80ff8

def z980 : W := mkw 0x054012002a002202 0x002a009001500110 0xee403f007301ff1e 0xcf7201f803980ff8

def z981 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0xffffffffffffff1f 0xfffffffffffffff8

def z982 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xb1dfc71fcf9e4ffb 0xfd8efe38fe7cf27f

def z983 : W := mkw 0x023d400051d40001 0xc011ea00028ea000 0xf1ffc0004ffe000e 0x3f8ffe00027ff000

def z984 : W := mkw 0x023008b41060d0d0 0x98118045a0830686 0x4e2038fc3061b0e5 0x027101c7e1830d87

def z985 : W := mkw 0x4000810d80084560 0x020004086c00422b 0xa059c71fc3004ffb 0xfd02ce38fe18027f

def z986 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0x0059c71fc3984ffb 0x3802ce38fe1cc27f

def z987 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x71a624e3fcfffcff 0x7b8d31271fe7ffe7

def z988 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xae59df1ff3987ffb 0xfd72cef8ff9cc3ff

def z989 : W := mkw 0x05c236422e012a0a 0x202e11b211700950 0xffc63f03ff01ff1e 0xeffe31f81ff80ff8

def z990 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xdfffffff80000000 0xaefffffffc000000

def z991 : W := mkw 0x05c2b74b00000008 0x002e15ba58000000 0xffffffff80000001 0xfffffffffc000000

def z992 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xffbe38fc7ce7f0f7 0xd7fdf1c7e3e73f87

def z993 : W := mkw 0x023d400051d40001 0xc011ea00028ea000 0x11bfc0000cfe0008 0x388dfe000067f000

def z994 : W := mkw 0x077d40007bd42203 0xc03bea0003dea110 0xf7ffc0007ffe730e 0x3fbffe0003fff398

def z995 : W := mkw 0x0230899900000010 0x0011844cc8000000 0xee39f8ff80000001 0xf771cfc7fc000000

def z996 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0x8059c71fc3984fe9 0xbc02ce38fe1cc27f

def z997 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0x4fc03f007f01ff1e 0x0a7e01f803f80ff8

def z998 : W := mkw 0x0dc736422e012a0e 0x206e39b211700950 0xffc63f007f01ff1e 0xcffe31f803f80ff8

def z999 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xf7ffc0007ffe00ff 0x7fbffe0003fff007

def z1000 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0xffe63fe3ffffffff 0xffff31ff1fffffff

def z1001 : W := mkw 0xc082adff842bddf8 0x3e04156ffc215eef 0x08003fff8001fff1 0xc04001fffc000fff

def z1002 : W := mkw 0x0ff7bfdb3a44001e 0xc07fbdfed9d22000 0xffffffffff66000f 0xfffffffffffb3000

def z1003 : W := mkw 0x0ff7bfdb2a00001e 0x007fbdfed9500000 0xffffffffff01f01f 0xfffffffffff80f80

def z1004 : W := mkw 0xc0084024ffffcde3 0xf600420127fffe6f 0x000000007fffcffe 0x0000000003fffe7f

def z1005 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xf7ffc403fffe000f 0x7fbffe201ffff000

def z1006 : W := mkw 0x054540003b540002 0xc02a2a0001daa000 0x11c7c0003f7e000c 0x288e3e0001fbf000

def z1007 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0x2059c71f83980ffb 0x7902ce38fc1cc07f

def z1008 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xfffffffff301ff1f 0xffffffffff980ff8

def z1009 : W := mkw 0x0ff7bfdb2a00221e 0x007fbdfed9500110 0xfffffffff301f317 0xffffffffff980f98

def z1010 : W := mkw 0x077540003b540002 0xc03baa0001daa000 0x11e7c0000f7e0008 0x288f3e00007bf000

def z1011 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x71a620e38cff80f7 0x738d31071c67fc07

def z1012 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xe079e7ffc3984ffb 0xff03cf3ffe1cc27f

def z1013 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xb07fc71fc3fe4ffb 0xfd83fe38fe1ff27f

def z1014 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xa059c71f83980fe9 0xfd02ce38fc1cc07f

def z1015 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xf7ffc01c7ffe000f 0xffbffe00e3fff000

def z1016 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xee3838fc30e1b0e5 0xd771c1c7e1870d87

def z1017 : W := mkw 0x80822462842baea8 0x3404112314215d75 0x71a624e38cffffff 0x7b8d31271c67ffff

def z1018 : W := mkw 0x023008b010609090 0x9811804580830484 0xee3838fc30e1b0f7 0xd771c1c7e1870d87

def z1019 : W := mkw 0x8dc7b74bae0b2e2e 0x246e3dba5d705971 0x11c7c7038f1e0f08 0x288e3e381c78f078

def z1020 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xf7ffc0000ffe0008 0x3fbffe00007ff000

def z1021 : W := mkw 0x80084024ffffdce3 0xfc00420127fffee7 0x000000007ffffcfe 0x0000000003ffffe7

def z1022 : W := mkw 0x077d48907bd40013 0xc03bea4483dea000 0xfffff8e07ffe000e 0x3fffffc703fff000

def z1023 : W := mkw 0x40084024d1f8d5e1 0x9a004201268fc6af 0xee403f0073f9fffe 0xcf7201f8039fcfff

def z1024 : W := mkw 0x0ab7addb0000001c 0x0055bd6ed8000000 0x11bfc4ff80000001 0x388dfe27fc000000

def z1025 : W := mkw 0x0f779bdb0000001c 0x007bbcded8000000 0xffffdbff80000001 0xbffffedffc000000

def z1026 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0xf1e627e38cff8cff 0xff8f313f1c67fc67

def z1027 : W := mkw 0x0ff7bfdb0401081c 0x207fbdfed8200840 0xffffffff8c018005 0xfffffffffc600c00

def z1028 : W := mkw 0x40084024d1f8d5e1 0x9a004201268fc6af 0x0000000070f9f0f6 0x000000000387cf87

def z1029 : W := mkw 0x80823662842b8ca8 0x340411b314215c65 0x79a63fe38cff8cff 0xfbcd31ff1c67fc67

def z1030 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xd7ffc0007ffe0004 0x36bffe0003fff000

def z1031 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0x907fc3ff80000001 0xb483fe1ffc000000

def z1032 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0x71ffe7ff80000001 0x7b8fff3ffc000000

def z1033 : W := mkw 0x0882bfdb0000001c 0x004415fed8000000 0xf9ffffff80000001 0xffcffffffc000000

def z1034 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0x103fc7ff80000001 0xf081fe3ffc000000

def z1035 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xe059e71fc399cfff 0xff02cf38fe1cce7f

def z1036 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0xb03fc0ff80000001 0xf581fe07fc000000

def z1037 : W := mkw 0x8082a56b842b8ca8 0x3404152b5c215c65 0x000027ff80018cf1 0xc000013ffc000c67

def z1038 : W := mkw 0x077d52007bd42203 0xc03bea9003dea110 0xfffffb007ffff31e 0xffffffd803ffff98

def z1039 : W := mkw 0x0f7789db0000001c 0x007bbc4ed8000000 0x57bfc0ff80000001 0x32bdfe07fc000000

def z1040 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0x57bfc0007ffe000e 0x32bdfe0003fff000

def z1041 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xee3838fc70f9f0ff 0xff71c1c7e387cf87

def z1042 : W := mkw 0x077d40047bd44043 0xc03bea0023dea202 0xf7ffc0007ffe40fe 0x3fbffe0003fff207

def z1043 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0xf1a624e3ccffccff 0xff8d31271e67fe67

def z1044 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0x8059c71fc3184ff9 0xec02ce38fe18c27f

def z1045 : W := mkw 0x0000810980080420 0x000004084c004021 0xa059c71fc3984ffb 0xfd02ce38fe1cc27f

def z1046 : W := mkw 0x45c87624fff9ffe3 0xba2e43b127ffcfff 0xefc03f007ff9fffe 0xcf7e01f803ffcfff

def z1047 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xee7838fc73e1f0ff 0xdf73c1c7e39f0f87

def z1048 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0x97dfc0007ffe000e 0x2cbefe0003fff000

def z1049 : W := mkw 0x07f0bf992e012a12 0x203f85fcc9700950 0xeff9ffffff01ff1f 0xff7fcffffff80ff8

def z1050 : W := mkw 0x0ff7addb0000001c 0x007fbd6ed8000000 0xf7ffe4ff80000001 0x7fbfff27fc000000

def z1051 : W := mkw 0x023008b41060d0d0 0x98118045a0830686 0xee2038fc7061f0f7 0xc77101c7e3830f87

def z1052 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xf7ffc7007ffe0f0e 0x3fbffe3803fff078

def z1053 : W := mkw 0xc0084024c1bac5e1 0x16004201260dd62f 0x0000000000fe00e0 0x000000000007f007

def z1054 : W := mkw 0xc0886424c5bbcde1 0x36044321262dde6f 0xe1c027004fffcffe 0xcf0e0138027ffe7f

def z1055 : W := mkw 0x077d40047bd44043 0xc03bea0023dea202 0xf7ffc01c7ffe400e 0xbfbffe00e3fff200

def z1056 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x11a600e38cfe00e1 0x308d30071c67f007

def z1057 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0x8fc03f007f01ff18 0xcc7e01f803f80ff8

def z1058 : W := mkw 0x077d40047bd44043 0xc03bea0023dea202 0xfffff81c7ffff0ff 0xffffffc0e3ffff87

def z1059 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xfffffffff0007001 0xffffffffff800380

def z1060 : W := mkw 0x477dc99d7bd45153 0xca3bee4cebdea28a 0x8e59db1c73007300 0x8472ced8e3980398

def z1061 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xf7ffc7007ffe000e 0xffbffe3803fff000

def z1062 : W := mkw 0x077d52007bd40003 0xc03bea9003dea000 0xffffdb007ffe000e 0xbffffed803fff000

def z1063 : W := mkw 0x0ff7bfdb2a00221e 0x007fbdfed9500110 0xffffffffff00730f 0xfffffffffff80398

def z1064 : W := mkw 0x077d48947bd45053 0xc83bea44a3dea282 0xfffff8fc7ffe700f 0xffffffc7e3fff380

def z1065 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x71a624e38cfe0ce9 0x7b8d31271c67f067

def z1066 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xffe63f007f67ff1e 0xcfff31f803fb3ff8

def z1067 : W := mkw 0x0ff7bfdb3a44001e 0xc07fbdfed9d22000 0xffffffffb0000001 0xfffffffffd800000

def z1068 : W := mkw 0x0ff7bfdb3e452a1e 0xe07fbdfed9f22950 0xffffffffbc67b005 0xfffffffffde33d80

def z1069 : W := mkw 0x0ff7bfdb04012a1c 0x207fbdfed8200950 0xffffffff8001b001 0xfffffffffc000d80

def z1070 : W := mkw 0x05c536002e012a02 0x202e29b001700950 0xffc7ff007f01ff1e 0xeffe3ff803f80ff8

def z1071 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xcfc03b007f01ff1e 0x867e01d803f80ff8

def z1072 : W := mkw 0x023d400051d40001 0xc011ea00028ea000 0x51bfc0000cfe0004 0x328dfe000067f000

def z1073 : W := mkw 0x023848b451f0d0d1 0x9811c245a28f8686 0xee79fffc73f9ffff 0xff73cfffe39fcfff

def z1074 : W := mkw 0x0000000000000000 0x0000000000000000 0xf1ffc0000cfe000e 0x3f8ffe000067f000

def z1075 : W := mkw 0xc5c87624efbbefe3 0x362e43b1277ddf7f 0xefc03f007ffffffe 0xcf7e01f803ffffff

def z1076 : W := mkw 0x077d48907bd40013 0xc03bea4483dea000 0xffffd81c7ffe000e 0xbffffec0e3fff000

def z1077 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xa059c71fcffe4fff 0xfd02ce38fe7ff27f

def z1078 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0xffffffffff01f305 0xfffffffffff80f98

def z1079 : W := mkw 0x077d000050c00001 0x803be80002860000 0xf7ffc0007cfe000e 0x3fbffe0003e7f000

def z1080 : W := mkw 0x0008810d40804041 0x000044086a040202 0xa059c71fc3804ffb 0xfd02ce38fe1c027f

def z1081 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x71a624e38cff80e5 0x7b8d31271c67fc07

def z1082 : W := mkw 0xc0084024c1bac5e1 0x16004201260dd62f 0x0000000043fe4ffa 0x00000000021ff27f

def z1083 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0xffffffffcf004f1b 0xfffffffffe780278

def z1084 : W := mkw 0xc5c2f74baf1b2f2a 0x262e17ba5d78d979 0x11c7c7038f1e0f08 0x288e3e381c78f078

def z1085 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xffbe38fc70e1f0f7 0xfffdf1c7e3870f87

def z1086 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0xf63fc0ff80000001 0x37b1fe07fc000000

def z1087 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0x9e3fd8ff80000001 0xb4f1fec7fc000000

def z1088 : W := mkw 0x0f7789db2a00001e 0x007bbc4ed9500000 0xf7ffc0ffff00000f 0x3fbffe07fff80000

def z1089 : W := mkw 0x077d48947bd45053 0xc83bea44a3dea282 0xf7ffc01c7ffe000e 0x3fbffe00e3fff000

def z1090 : W := mkw 0x0080240004010800 0x2004012000200840 0xefc03f007f01ff1e 0xcf7e01f803f80ff8

def z1091 : W := mkw 0x0008400041900001 0x00004200020c8000 0x71bfc0000cfe000e 0x3b8dfe000067f000

def z1092 : W := mkw 0x0ab7bfdb0000001c 0x0055bdfed8000000 0x0819ffff80000001 0xc040cffffc000000

def z1093 : W := mkw 0x023d08b450e4d0d1 0xd811e845a2872686 0xfe3e38fc70e7f0f7 0xd7f1f1c7e3873f87

def z1094 : W := mkw 0x80823662842baea8 0x340411b314215d75 0xf9e63fe3cfffffff 0xffcf31ff1e7fffff

def z1095 : W := mkw 0x0f779bdb0000001c 0x007bbcded8000000 0xfe7ffbff80000001 0xf7f3ffdffc000000

def z1096 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x71e627e38fff8fff 0x7b8f313f1c7ffc7f

def z1097 : W := mkw 0x0ff7bfdb0401081c 0x207fbdfed8200840 0xfffffffffc01fc1f 0xffffffffffe00fe0

def z1098 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xf7ffc0003cfe0004 0x3fbffe0001e7f000

def z1099 : W := mkw 0x80020062802a84a8 0x1400100314015425 0x51a600e38cfe00e5 0x328d30071c67f007

def z1100 : W := mkw 0x4000c10d81184560 0x020006086c08c22b 0xa059c71f83184ff9 0xfd02ce38fc18c27f

def z1101 : W := mkw 0x0545000000000000 0x002a280000000000 0x71e7c0000cfe000e 0x3b8f3e000067f000

def z1102 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0xfffffffffc01f017 0xffffffffffe00f80

def z1103 : W := mkw 0x80822462802a84a8 0x1404112314015425 0x71a624e38cfe00ef 0x7b8d31271c67f007

def z1104 : W := mkw 0x054540002b140002 0x402a2a000158a000 0x51e7c0000f7e000c 0x2a8f3e00007bf000

def z1105 : W := mkw 0x023d400051d40001 0xc011ea00028ea000 0xf7bfc0007cfe000e 0x3fbdfe0003e7f000

def z1106 : W := mkw 0x0f7789db0000001c 0x007bbc4ed8000000 0xf7ffc7ff80000001 0xffbffe3ffc000000

def z1107 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xce3838fc70e1f0e5 0x9671c1c7e3870f87

def z1108 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xb1ffc0004ffe000a 0x3d8ffe00027ff000

def z1109 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x7fa63ce3bcffbcff 0x7bfd31e71de7fde7

def z1110 : W := mkw 0x0000899900000010 0x0000044cc8000000 0xa859ffff80000001 0xfd42cffffc000000

def z1111 : W := mkw 0x0ff7bfdb04012a1c 0x207fbdfed8200950 0xfffffffff001ff17 0xffffffffff800ff8

def z1112 : W := mkw 0x0ff7bfdb2a00001e 0x007fbdfed9500000 0xfffffffffffe000f 0xfffffffffffff000

def z1113 : W := mkw 0x023848b451f0d0d1 0x9811c245a28f8686 0xee3838fc73f9f0ff 0xd771c1c7e39fcf87

def z1114 : W := mkw 0x077d48947bd45053 0xc83bea44a3dea282 0xffffd81c7ffe70ff 0xfffffec0e3fff387

def z1115 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0x8059c71fc3984ff1 0xf402ce38fe1cc27f

def z1116 : W := mkw 0x000840007bd40003 0xc000420003dea000 0xf1ffc0007ffe000e 0x3f8ffe0003fff000

def z1117 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0x77bfc0003cfe000e 0x3bbdfe0001e7f000

def z1118 : W := mkw 0x0080360004012a00 0x200401b000200950 0xee403f007301ff1e 0xcf7201f803980ff8

def z1119 : W := mkw 0x077540002b140002 0x403baa000158a000 0xf7ffc0000ffe000e 0x3fbffe00007ff000

def z1120 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x71a620e38cff80ef 0x3b8d31071c67fc07

def z1121 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xfe3e38fc70fff0f7 0xf7f1f1c7e387ff87

def z1122 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xe659c71ff3984fff 0xff32ce38ff9cc27f

def z1123 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x11a624e38cff8cf9 0x788d31271c67fc67

def z1124 : W := mkw 0x4a3fc9ffd1f8d5fd 0x9a51fe4ffe8fc6af 0x103fc0ff80f800e1 0x3081fe07fc07c007

def z1125 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffffffffc3004301 0xfffffffffe180218

def z1126 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x71a624e3cfffcfff 0x7b8d31271e7ffe7f

def z1127 : W := mkw 0x0ab7bfdb04012a1c 0x2055bdfed8200950 0x183fffff8001ff11 0xf0c1fffffc000ff8

def z1128 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xee383ffc70e1fff7 0xd771c1ffe3870fff

def z1129 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffffffff80004f11 0xfffffffffc000278

def z1130 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xefe03f007fe1ff1e 0xdf7f01f803ff0ff8

def z1131 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0x4e3838fc70e1f0f7 0x1271c1c7e3870f87

def z1132 : W := mkw 0x0ff7bfdb2e01081e 0x207fbdfed9700840 0xffffffffff018c1f 0xfffffffffff80c60

def z1133 : W := mkw 0x423848b451f0d1d1 0x9a11c245a28f868e 0xee3838fc73e1f3f7 0xd771c1c7e39f0f9f

def z1134 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0x97ffc0007ffe0008 0x3cbffe0003fff000

def z1135 : W := mkw 0x423dc9bdd1fcd5f1 0xda11ee4dee8fe6af 0x103fc0ff80fe00e1 0x3081fe07fc07f007

def z1136 : W := mkw 0x054840006b900003 0x002a4200035c8000 0xf7ffc0007ffe000e 0x3fbffe0003fff000

def z1137 : W := mkw 0x023008b41060d0d0 0x98118045a0830686 0x6e2038fc30e1f0f7 0xd37101c7e1870f87

def z1138 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0x183ff8ff80000001 0xf0c1ffc7fc000000

def z1139 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0x703fe0ff80000001 0x7381ff07fc000000

def z1140 : W := mkw 0x85c236422e032a0a 0x242e11b211701950 0xffc63f007f07ff1e 0xcffe31f803f83ff8

def z1141 : W := mkw 0x080289db0000001c 0x0040144ed8000000 0x0019c0ff80000001 0x3000ce07fc000000

def z1142 : W := mkw 0x40084024d1f8d5e1 0x9a004201268fc6af 0x0000000043f84ffa 0x00000000021fc27f

def z1143 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0xffffffffff007f09 0xfffffffffff803f8

def z1144 : W := mkw 0x0f779bdb0000001c 0x007bbcded8000000 0x107fc3ff80000001 0x3083fe1ffc000000

def z1145 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xefc03f007301ff10 0xcf7e01f803980ff8

def z1146 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0x103fc0ff80fe0001 0x3081fe07fc07f000

def z1147 : W := mkw 0xc23ac9ffd1fad5f9 0x9e11d64ffe8fd6af 0x103fc0ff80fe00e1 0x3081fe07fc07f007

def z1148 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x51a624e38cff8ced 0x3a8d31271c67fc67

def z1149 : W := mkw 0x05c0360000000000 0x002e01b000000000 0xefc03f007301ff1e 0xcf7e01f803980ff8

def z1150 : W := mkw 0x0ff73ef23e61ba9e 0xb87fb9f791f30dd4 0x5fa638e03c61b004 0x02fd31c701e30d80

def z1151 : W := mkw 0x023008b41060d0d0 0x98118045a0830686 0xee3838fc3061f0f5 0xd771c1c7e1830f87

def z1152 : W := mkw 0x80020062802a84a8 0x1400100314015425 0x71a620e38cff80ff 0x7b8d31071c67fc07

def z1153 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0x8059c71fc3984ffb 0xc402ce38fe1cc27f

def z1154 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffffffffc0004013 0xfffffffffe000200

def z1155 : W := mkw 0x0ff7bfdb1040101c 0x887fbdfed8820080 0xffffffffb0003001 0xfffffffffd800180

def z1156 : W := mkw 0x077d40007bd40003 0xc03bea0003dea000 0xfffff8007ffe000e 0xffffffc003fff000

def z1157 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0x8059c71fc3984ffa 0xac02ce38fe1cc27f

def z1158 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xcfc03f007f01ff0c 0x8e7e01f803f80ff8

def z1159 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0x6e3838fc30e1b0f7 0x5371c1c7e1870d87

def z1160 : W := mkw 0x0f779bdb0000001c 0x007bbcded8000000 0xbe7fdfff80000001 0xfdf3fefffc000000

def z1161 : W := mkw 0x0230899900000010 0x0011844cc8000000 0xee79fffff301ff1f 0xff73cfffff980ff8

def z1162 : W := mkw 0x0dc7b74b0000000c 0x006e3dba58000000 0xf1ffe7ff80000001 0xff8fff3ffc000000

def z1163 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0xcfc03f007f01ff14 0xc67e01f803f80ff8

def z1164 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xee383cfff0e1f0f7 0xff71c1e7ff870f87

def z1165 : W := mkw 0x0ff7bfdb2a04001e 0x407fbdfed9502000 0xffffffff8c060001 0xfffffffffc603000

def z1166 : W := mkw 0x0f779bdb2a00221e 0x007bbcded9500110 0x9e7fdbfff3007301 0xb4f3fedfff980398

def z1167 : W := mkw 0x0f7789db3a44001e 0xc07bbc4ed9d22000 0x57bfc0ffbc660005 0x32bdfe07fde33000

def z1168 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xae1838fc7081f0f3 0xd570c1c7e3840f87

def z1169 : W := mkw 0x0ff7bfdb0401081c 0x207fbdfed8200840 0xffffffffcf01cf1f 0xfffffffffe780e78

def z1170 : W := mkw 0x023808b450e0d0d1 0x9811c045a2870686 0xee3838fc7001f0f1 0xd771c1c7e3800f87

def z1171 : W := mkw 0x0f7789db0000001c 0x007bbc4ed8000000 0x967fc0ff80000001 0x34b3fe07fc000000

def z1172 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xdffffbff80000001 0xb6ffffdffc000000

def z1173 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0x5fbfffff80000001 0xf2fdfffffc000000

def z1174 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0xffa63ce38cff8cff 0xfffd31e71c67fc67

def z1175 : W := mkw 0x40084024fbfcd5e3 0xda00420127dfe6af 0x000000007ffffffe 0x0000000003ffffff

def z1176 : W := mkw 0x40084024c1b8d5e1 0x1a004201260dc6af 0x000000004399fffa 0x00000000021ccfff

def z1177 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x51a624e38cff8cfe 0x2a8d31271c67fc67

def z1178 : W := mkw 0xc082b76f842befe8 0x360415bb7c215f7f 0x08003fff8001fff1 0xc04001fffc000fff

def z1179 : W := mkw 0x077d52007bd42203 0xc03bea9003dea110 0xffffd8007ffe300e 0x3ffffec003fff180

def z1180 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xffffffff808000f3 0xfffffffffc040007

def z1181 : W := mkw 0x054012002e012a02 0x202a009001700950 0xae401f007f01ff1e 0xcd7200f803f80ff8

def z1182 : W := mkw 0x4008c10dd1d84561 0x820046086e8ec22b 0xa059c71ff3f84fff 0xfd02ce38ff9fc27f

def z1183 : W := mkw 0x0238400051d00001 0x8011c200028e8000 0xf7ffc0007ffe000e 0x3fbffe0003fff000

def z1184 : W := mkw 0x0ff7bfdb0000001c 0x007fbdfed8000000 0xefd9ffff80000001 0xcf7ecffffc000000

def z1185 : W := mkw 0x023d48b451f4d0d1 0xd811ea45a28fa686 0xfe7ff8fc73fff0ff 0xfff3ffc7e39fff87

def z1186 : W := mkw 0xc882bfff842bcdfc 0x364415fffc215e6f 0x08003fff8001cff1 0xc04001fffc000e7f

def z1187 : W := mkw 0x0ff7bfdb0000221c 0x007fbdfed8000110 0xffffffff80007301 0xfffffffffc000398

def z1188 : W := mkw 0x0882bfdb04012a1c 0x204415fed8200950 0xa859ffffc301ff1b 0xfd42cffffe180ff8

def z1189 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0xffffffff8f01ff19 0xfffffffffc780ff8

def z1190 : W := mkw 0x05c036002e012a02 0x202e01b001700950 0x4f803f007f01ff1e 0xc27c01f803f80ff8

def z1191 : W := mkw 0x4008c10dc1984561 0x020046086e0cc22b 0xa059c71fc3980feb 0x3d02ce38fe1cc07f

def z1192 : W := mkw 0x023d40007bd40003 0xc011ea0003dea000 0x71bfc0007ffe000e 0x3b8dfe0003fff000

def z1193 : W := mkw 0x0ff7bfdb2e012a1e 0x207fbdfed9700950 0xffffffffbc01bc1f 0xfffffffffde00de0

def z1194 : W := mkw 0x80822462842b8ca8 0x3404112314215c65 0x79a63ce38cfffcff 0xfbcd31e71c67ffe7

def z1195 : W := mkw 0x0a3789db0000001c 0x0051bc4ed8000000 0x5e3ff8ff80000001 0x32f1ffc7fc000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z8,z6]),(0,[z9,z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z11,z5,z6]),(0,[z7,z12,z13,z2,z4,z5,z6]),(0,[z7,z2,z14,z4,z5,z6,z15])],[(0,[z16,z7,z2,z3,z4,z5,z6]),(0,[z17,z7,z2,z3,z4,z5,z6]),(0,[z7,z18,z2,z3,z4,z5,z6])],[(0,[z19,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z20,z5,z6]),(0,[z7,z2,z3,z21,z4,z5,z6]),(0,[z22,z7,z2,z3,z4,z5,z6]),(0,[z23,z7,z2,z4,z5,z6,z24])],[(0,[z7,z25,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z26,z6]),(0,[z7,z3,z4,z5,z27,z6,z28]),(0,[z7,z2,z3,z29,z4,z5,z6]),(0,[z7,z2,z3,z30,z4,z5,z6]),(0,[z31,z7,z2,z3,z4,z5,z6])],[(0,[z32,z7,z2,z33,z4,z5,z6]),(0,[z34,z7,z2,z3,z4,z5,z6]),(0,[z35,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z36,z5,z6]),(0,[z37,z2,z3,z4,z5,z6,z38]),(0,[z7,z2,z3,z10,z39,z5,z6]),(0,[z40,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z41,z4,z39,z5,z6]),(0,[z7,z2,z3,z4,z42,z5,z6])],[(0,[z7,z43,z2,z3,z4,z5,z6]),(0,[z7,z2,z44,z3,z45,z5,z6]),(1,[z7,z2,z46,z4,z5,z6]),(0,[z7,z47,z2,z3,z4,z5,z6]),(0,[z23,z9,z7,z2,z4,z5,z6])],[],[(0,[z7,z2,z3,z4,z48,z5,z6]),(0,[z7,z2,z3,z49,z4,z5,z6]),(0,[z50,z7,z2,z51,z4,z5,z6])]],
   [[(1,[z52,z3,z53,z4,z5,z6]),(0,[z7,z2,z3,z10,z5,z6,z38]),(0,[z7,z54,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z55])],[(0,[z56,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z57,z5,z6]),(0,[z7,z2,z3,z58,z59,z5,z6]),(0,[z7,z2,z3,z60,z61,z5,z6]),(0,[z7,z2,z41,z3,z62,z5,z6]),(0,[z7,z2,z3,z63,z4,z5,z6])],[(0,[z50,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z64,z6]),(0,[z7,z2,z3,z65,z4,z5,z6]),(0,[z7,z2,z41,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z66,z6]),(0,[z7,z2,z3,z67,z4,z5,z6])],[(0,[z7,z2,z3,z68,z5,z69,z6]),(0,[z7,z2,z3,z45,z70,z5,z6]),(0,[z37,z50,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z71,z28]),(0,[z7,z2,z3,z45,z5,z72,z6]),(0,[z7,z2,z3,z45,z5,z73,z6]),(0,[z7,z2,z3,z4,z74,z5,z6]),(0,[z7,z2,z3,z4,z5,z75,z6]),(0,[z76,z7,z2,z3,z4,z5,z6])],[(1,[z7,z2,z3,z4,z5,z77]),(1,[z7,z2,z78,z4,z5,z6]),(0,[z79,z1,z7,z2,z3,z5,z6]),(0,[z7,z2,z3,z80,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z81,z6])],[(0,[z82,z7,z2,z3,z4,z5,z6]),(0,[z83,z7,z2,z3,z4,z5,z6]),(1,[z7,z3,z4,z5,z84,z6]),(0,[z85,z7,z2,z3,z61,z5,z6])],[(0,[z86,z7,z2,z3,z4,z5,z6]),(0,[z87,z7,z2,z3,z4,z5,z6]),(0,[z7,z88,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z89])],[(0,[z7,z2,z3,z4,z90,z5,z6]),(0,[z32,z2,z3,z33,z4,z5,z6]),(0,[z91,z7,z2,z3,z4,z5,z6]),(0,[z92,z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z93,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z94,z6]),(0,[z7,z2,z3,z4,z5,z6,z95]),(1,[z96,z7,z3,z4,z97,z6])],[(0,[z98,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z99,z5,z6]),(1,[z7,z2,z3,z4,z5,z100])],[(0,[z7,z2,z3,z4,z5,z6,z101]),(0,[z7,z102,z2,z41,z4,z5,z6]),(0,[z7,z2,z3,z10,z103,z5,z6]),(0,[z23,z7,z2,z3,z104,z5,z6])],[(0,[z7,z2,z44,z3,z4,z5,z27])],[(0,[z7,z2,z3,z4,z5,z105,z6]),(0,[z7,z2,z3,z4,z5,z106,z6]),(0,[z85,z7,z2,z3,z4,z5,z73])],[(0,[z107,z7,z2,z3,z4,z5,z6]),(0,[z108,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z109,z6]),(0,[z110,z7,z2,z3,z45,z5,z6]),(0,[z7,z111,z2,z3,z4,z5,z6]),(0,[z7,z3,z4,z11,z5,z97,z6])],[(0,[z7,z2,z3,z4,z5,z112,z6]),(0,[z7,z2,z3,z4,z5,z113,z6]),(0,[z7,z2,z3,z114,z4,z5,z6]),(0,[z7,z13,z3,z4,z10,z5,z6])],[(0,[z115,z2,z3,z33,z4,z5,z6]),(0,[z7,z2,z3,z116,z4,z5,z6]),(1,[z7,z2,z117,z4,z5,z6]),(0,[z118,z7,z2,z3,z45,z5,z6]),(0,[z96,z7,z2,z3,z4,z97,z6]),(0,[z7,z2,z119,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z53,z10,z5,z6]),(0,[z7,z2,z3,z4,z5,z120,z6]),(1,[z121,z2,z3,z4,z5,z6]),(0,[z7,z122,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z123,z4,z5,z6])],[(0,[z7,z2,z3,z78,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z124,z6]),(0,[z7,z2,z125,z3,z10,z5,z6]),(0,[z7,z2,z3,z45,z45,z5,z6]),(0,[z126,z7,z2,z3,z45,z5,z6]),(0,[z7,z2,z3,z127,z45,z5,z6]),(0,[z7,z2,z3,z128,z4,z5,z6]),(0,[z7,z2,z129,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z130,z6]),(0,[z79,z7,z2,z3,z5,z73,z6]),(0,[z7,z131,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z132,z10,z5,z6]),(0,[z133,z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z134]),(0,[z7,z2,z3,z4,z5,z6,z135]),(0,[z136,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z137,z5,z6]),(0,[z7,z102,z2,z4,z5,z138,z6]),(0,[z7,z2,z3,z10,z5,z139,z6]),(0,[z7,z2,z2,z3,z45,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z140])],[(0,[z141,z7,z2,z3,z4,z5,z6]),(0,[z32,z7,z2,z3,z4,z5,z6]),(0,[z115,z7,z2,z3,z4,z69,z6]),(0,[z7,z2,z142,z3,z4,z5,z6]),(0,[z96,z7,z2,z3,z4,z11,z6]),(0,[z143,z7,z2,z3,z4,z5,z6])],[(0,[z7,z144,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z145]),(0,[z7,z2,z3,z10,z5,z27,z6]),(0,[z96,z146,z2,z3,z4,z5,z6]),(0,[z96,z7,z2,z3,z147,z5,z6]),(0,[z148,z7,z2,z3,z4,z5,z6])],[(0,[z0,z7,z2,z3,z4,z5,z6]),(1,[z7,z149,z2,z4,z5,z6]),(1,[z7,z2,z3,z150,z59,z6]),(1,[z7,z151,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z152,z6]),(0,[z7,z2,z3,z4,z153,z5,z6]),(0,[z96,z7,z2,z46,z4,z5,z6]),(0,[z7,z2,z3,z4,z154,z5,z6]),(1,[z7,z2,z44,z4,z5,z72])],[(0,[z155,z7,z88,z3,z4,z5,z6]),(0,[z110,z7,z2,z3,z4,z103,z6])],[(0,[z7,z2,z3,z45,z132,z5,z6]),(0,[z7,z2,z3,z156,z4,z5,z6]),(0,[z7,z2,z3,z157,z4,z5,z6]),(0,[z7,z2,z3,z4,z158,z5,z6])],[(0,[z7,z2,z3,z4,z5,z159,z6]),(0,[z7,z2,z3,z160,z4,z5,z6]),(0,[z96,z7,z2,z3,z4,z5,z55])],[(0,[z7,z2,z3,z117,z4,z5,z6]),(1,[z7,z2,z3,z161,z5,z6]),(0,[z7,z2,z3,z162,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z163,z6])],[(0,[z115,z7,z2,z3,z4,z5,z6]),(1,[z7,z164,z2,z4,z5,z6]),(0,[z7,z2,z3,z165,z4,z5,z6]),(0,[z166,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z167,z4,z5,z6]),(0,[z168,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z169,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z170])],[(1,[z7,z2,z3,z171,z5,z6]),(0,[z172,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z10,z173,z5,z6]),(0,[z7,z3,z4,z10,z5,z6,z28]),(0,[z7,z2,z174,z3,z4,z5,z6])],[(0,[z7,z2,z175,z3,z4,z5,z6]),(1,[z115,z2,z3,z4,z70,z6]),(0,[z7,z2,z165,z4,z5,z72,z6]),(0,[z7,z2,z3,z45,z5,z176,z6]),(0,[z177,z7,z2,z60,z4,z5,z6])]],
   [[(0,[z7,z178,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z179,z5,z6]),(0,[z79,z7,z2,z3,z45,z5,z6]),(0,[z180,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z181,z6]),(0,[z182,z178,z2,z3,z4,z5,z6]),(0,[z183,z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z184])],[(0,[z7,z2,z3,z185,z4,z5,z6]),(0,[z7,z2,z3,z186,z4,z5,z6]),(0,[z23,z7,z2,z60,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z187])],[(0,[z7,z2,z3,z4,z5,z6,z188]),(0,[z7,z189,z2,z3,z10,z5,z6]),(0,[z190,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z10,z5,z6,z28]),(1,[z7,z13,z3,z4,z5,z27]),(0,[z191,z7,z2,z3,z4,z5,z6]),(0,[z192,z7,z2,z3,z4,z5,z6])],[(0,[z7,z88,z3,z4,z10,z5,z6]),(0,[z7,z13,z2,z3,z10,z5,z6]),(0,[z155,z7,z3,z45,z4,z5,z6]),(0,[z7,z2,z3,z4,z193,z5,z6])],[(0,[z7,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z53,z45,z5,z6]),(0,[z194,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z10,z58,z5,z6]),(0,[z195,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z196,z6])],[(0,[z7,z178,z2,z4,z5,z72,z6]),(0,[z7,z197,z3,z4,z11,z5,z6]),(0,[z7,z2,z3,z4,z198,z5,z6])],[(0,[z7,z2,z3,z4,z5,z84,z6]),(0,[z155,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z199,z6]),(0,[z7,z200,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z165,z4,z5,z138,z6]),(0,[z201,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z4,z5,z6,z202]),(0,[z7,z2,z3,z4,z103,z5,z203])],[(0,[z204,z7,z2,z3,z4,z5,z6]),(0,[z205,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z206])],[],[(0,[z7,z2,z3,z4,z5,z6,z207]),(0,[z7,z2,z3,z5,z6,z208,z203])],[(1,[z7,z2,z209,z4,z5,z6]),(1,[z210,z7,z102,z4,z5,z6]),(0,[z180,z7,z3,z4,z5,z6,z28]),(0,[z7,z2,z3,z4,z5,z139,z28]),(0,[z7,z2,z4,z5,z72,z6,z24]),(0,[z85,z7,z211,z3,z4,z5,z6]),(0,[z110,z7,z2,z3,z4,z6,z203]),(0,[z7,z212,z2,z3,z4,z5,z6])],[(0,[z213,z7,z2,z3,z4,z5,z6]),(0,[z7,z12,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z214,z6]),(0,[z7,z2,z3,z4,z5,z6,z24])],[(0,[z215,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z216,z4,z5,z6])],[(0,[z52,z2,z3,z33,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z217,z6]),(0,[z218,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z219,z3,z4,z5,z6]),(0,[z7,z2,z220,z3,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z221,z15])]],
   [[(0,[z7,z222,z2,z3,z4,z5,z6]),(0,[z223,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z104,z5,z6])],[(0,[z7,z224,z2,z3,z225,z5,z6]),(0,[z7,z2,z3,z45,z61,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z15])],[(0,[z7,z102,z2,z33,z4,z5,z6]),(0,[z0,z7,z2,z3,z59,z5,z6]),(0,[z226,z7,z3,z4,z5,z69,z6])],[(0,[z7,z2,z3,z10,z5,z69,z6]),(0,[z7,z2,z3,z4,z5,z6,z227]),(0,[z7,z2,z3,z4,z5,z6,z228]),(0,[z7,z2,z3,z229,z4,z5,z6])],[(0,[z7,z230,z2,z3,z4,z5,z6]),(0,[z231,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z150,z10,z5,z6]),(0,[z7,z2,z3,z4,z5,z232,z6])],[(0,[z7,z178,z2,z3,z45,z5,z6]),(0,[z233,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z10,z10,z5,z6]),(0,[z7,z2,z3,z10,z5,z234,z6]),(0,[z7,z2,z3,z4,z235,z5,z6]),(0,[z180,z7,z2,z3,z236,z5,z6])],[(0,[z50,z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z41,z3,z10,z5,z6])],[(0,[z7,z2,z3,z4,z5,z237,z6]),(0,[z238,z7,z2,z3,z4,z5,z6]),(1,[z239,z7,z2,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z240,z6])]],
   [[(0,[z241,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z80,z10,z5,z6]),(1,[z7,z2,z3,z236,z5,z6])],[(0,[z1,z7,z2,z78,z4,z5,z6]),(0,[z7,z2,z3,z4,z242,z5,z6]),(0,[z243,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z244,z6]),(0,[z7,z2,z3,z45,z245,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z246]),(0,[z247,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z151,z3,z4,z5,z6])],[(1,[z7,z2,z3,z248,z5,z6]),(0,[z23,z7,z102,z2,z4,z5,z6]),(0,[z7,z88,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z5,z97,z6]),(0,[z249,z7,z2,z3,z4,z5,z6]),(0,[z23,z7,z2,z4,z39,z5,z6]),(0,[z7,z2,z14,z3,z4,z5,z6])],[(0,[z7,z2,z3,z10,z250,z5,z6]),(0,[z239,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z251,z6]),(0,[z7,z2,z3,z4,z5,z6,z252])],[(0,[z37,z7,z2,z3,z45,z5,z6]),(0,[z7,z2,z3,z10,z5,z73,z6]),(0,[z7,z2,z3,z4,z5,z138,z6]),(0,[z7,z2,z3,z4,z104,z5,z6]),(0,[z253,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z254,z6])],[(0,[z52,z7,z2,z3,z4,z5,z6]),(1,[z7,z12,z2,z4,z5,z6]),(0,[z177,z7,z2,z3,z4,z5,z6])],[(0,[z255,z7,z2,z117,z4,z5,z6]),(1,[z146,z2,z3,z4,z5,z6]),(0,[z96,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z147,z5,z6]),(0,[z7,z2,z3,z4,z5,z256,z6]),(0,[z7,z2,z3,z4,z5,z257,z6])],[(0,[z7,z2,z3,z4,z5,z6,z258]),(0,[z50,z7,z2,z3,z4,z5,z71]),(0,[z7,z259,z2,z3,z4,z5,z6]),(0,[z260,z7,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z261,z5,z6]),(0,[z23,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z262,z6]),(0,[z7,z2,z3,z4,z5,z263,z6]),(0,[z7,z2,z3,z264,z4,z5,z6])],[(0,[z182,z7,z2,z33,z4,z5,z6]),(0,[z2,z3,z33,z4,z5,z69,z6]),(0,[z7,z2,z265,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z266,z5,z6]),(0,[z7,z2,z3,z267,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z268,z6]),(0,[z269,z7,z2,z3,z4,z5,z6]),(0,[z9,z7,z2,z4,z5,z72,z6]),(0,[z7,z2,z3,z4,z270,z5,z6])],[(0,[z7,z197,z2,z3,z45,z5,z6]),(0,[z7,z13,z2,z3,z271,z5,z6]),(0,[z7,z2,z4,z39,z5,z72,z6])],[(0,[z52,z7,z224,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z272,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z273]),(0,[z180,z7,z13,z3,z4,z5,z6])],[(0,[z7,z3,z165,z4,z5,z6,z28]),(0,[z7,z2,z3,z274,z45,z5,z6]),(0,[z7,z2,z3,z4,z236,z5,z6]),(0,[z275,z7,z2,z3,z4,z5,z6]),(1,[z79,z7,z2,z3,z232,z6])],[(0,[z276,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z277,z5,z6]),(0,[z210,z7,z2,z3,z45,z5,z6]),(0,[z7,z2,z3,z4,z5,z278,z6]),(0,[z7,z2,z3,z279,z4,z5,z6])],[(0,[z7,z2,z3,z280,z4,z5,z6]),(0,[z281,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z282,z4,z5,z6])],[(0,[z283,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z284,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z285]),(0,[z7,z2,z3,z286,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z39,z103,z6])],[(1,[z7,z2,z3,z225,z5,z6]),(0,[z32,z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z5,z287,z6]),(0,[z7,z2,z3,z4,z288,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z289])],[(0,[z290,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z291,z3,z4,z5,z6]),(0,[z7,z2,z3,z292,z4,z5,z6]),(0,[z155,z7,z13,z3,z4,z5,z6]),(0,[z9,z7,z2,z4,z5,z138,z6]),(0,[z7,z2,z3,z4,z59,z5,z6])],[(0,[z7,z2,z3,z293,z4,z5,z6]),(0,[z7,z2,z3,z294,z4,z5,z6]),(0,[z0,z7,z2,z3,z10,z5,z6]),(0,[z50,z7,z2,z3,z45,z5,z6]),(0,[z7,z2,z3,z295,z4,z5,z6]),(0,[z7,z102,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z296,z6]),(0,[z7,z2,z41,z3,z45,z5,z6]),(0,[z7,z2,z4,z39,z5,z138,z6]),(0,[z297,z7,z2,z3,z4,z5,z6])],[(0,[z1,z7,z149,z2,z4,z5,z6]),(0,[z7,z2,z3,z4,z298,z5,z6]),(0,[z299,z7,z2,z3,z4,z5,z6]),(0,[z7,z300,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z301])],[(0,[z7,z2,z3,z4,z5,z6,z100]),(0,[z146,z7,z2,z3,z4,z5,z6]),(0,[z302,z7,z2,z3,z4,z5,z6]),(0,[z85,z7,z151,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z103,z139])],[(0,[z7,z224,z2,z3,z4,z5,z6]),(0,[z303,z7,z2,z3,z4,z5,z6]),(0,[z79,z0,z7,z2,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z27,z38]),(0,[z304,z7,z2,z3,z4,z5,z6]),(0,[z210,z7,z102,z3,z4,z5,z6]),(0,[z7,z2,z3,z157,z10,z5,z6]),(0,[z7,z2,z3,z45,z11,z5,z6]),(0,[z7,z2,z305,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z103,z138,z6])],[(0,[z52,z7,z2,z3,z306,z5,z6]),(0,[z307,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z45,z5,z138,z6]),(0,[z7,z2,z308,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z309]),(0,[z7,z2,z3,z4,z5,z6,z310])]],
   [[(0,[z7,z2,z3,z4,z5,z311,z6]),(0,[z7,z312,z2,z3,z4,z5,z6]),(0,[z9,z7,z2,z3,z45,z5,z6]),(0,[z7,z313,z2,z3,z4,z5,z6])],[(0,[z2,z3,z33,z4,z5,z6,z38]),(0,[z0,z7,z2,z3,z250,z5,z6]),(0,[z115,z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z314,z3,z4,z5,z6]),(0,[z7,z2,z3,z165,z10,z5,z6]),(1,[z7,z2,z3,z158,z5,z6]),(0,[z7,z2,z3,z4,z5,z315,z6])],[(0,[z7,z2,z3,z4,z316,z5,z6]),(0,[z7,z13,z2,z3,z317,z5,z6]),(0,[z7,z318,z2,z3,z4,z5,z6]),(0,[z23,z7,z2,z3,z4,z319,z6]),(0,[z320,z7,z2,z3,z5,z6,z203])],[(0,[z7,z2,z33,z4,z58,z5,z6]),(0,[z7,z178,z2,z165,z4,z5,z6]),(0,[z7,z3,z4,z5,z84,z69,z6]),(0,[z7,z321,z2,z3,z4,z5,z6]),(0,[z23,z7,z2,z3,z4,z5,z72]),(0,[z7,z2,z3,z322,z4,z5,z6])],[(0,[z180,z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z323,z5,z6]),(0,[z9,z7,z2,z3,z4,z138,z6]),(0,[z324,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z325,z6]),(0,[z7,z2,z3,z59,z5,z73,z6]),(0,[z7,z2,z3,z4,z139,z6,z203])],[(0,[z7,z2,z3,z4,z225,z5,z6]),(0,[z7,z2,z3,z60,z4,z5,z6]),(0,[z326,z7,z2,z3,z4,z5,z6]),(0,[z23,z7,z2,z3,z4,z193,z6]),(0,[z7,z2,z327,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z328,z6]),(0,[z79,z7,z2,z3,z5,z232,z6])],[(0,[z7,z2,z329,z3,z4,z5,z6]),(0,[z7,z2,z3,z330,z4,z5,z6]),(0,[z190,z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z331]),(0,[z177,z7,z2,z3,z60,z5,z6]),(0,[z7,z2,z3,z60,z5,z6,z15]),(1,[z7,z2,z3,z332,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z203])]],
   [[(0,[z7,z2,z333,z3,z4,z5,z6]),(0,[z1,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z334,z5,z6]),(0,[z7,z2,z3,z45,z5,z278,z6]),(0,[z7,z2,z3,z4,z5,z6,z335])],[(0,[z226,z7,z2,z3,z4,z5,z6]),(0,[z96,z7,z2,z336,z4,z5,z6]),(0,[z7,z2,z3,z337,z4,z5,z6]),(0,[z79,z85,z7,z2,z3,z5,z6]),(0,[z85,z7,z2,z3,z4,z5,z6])],[(0,[z52,z7,z2,z3,z4,z5,z338]),(0,[z7,z2,z3,z4,z339,z5,z6]),(0,[z7,z2,z3,z4,z5,z340,z6]),(0,[z182,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z33,z4,z5,z6]),(0,[z7,z2,z3,z341,z4,z5,z6]),(0,[z342,z7,z2,z3,z4,z5,z6]),(0,[z7,z343,z2,z3,z4,z5,z6]),(0,[z180,z7,z2,z3,z267,z5,z6]),(0,[z344,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z345,z5,z6]),(0,[z346,z224,z2,z3,z4,z5,z6]),(0,[z255,z7,z2,z209,z4,z5,z6]),(0,[z155,z7,z2,z3,z10,z5,z6]),(0,[z347,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z44,z3,z4,z5,z28]),(0,[z7,z2,z3,z4,z39,z6,z203]),(0,[z7,z2,z3,z348,z4,z5,z6]),(0,[z85,z7,z2,z3,z5,z6,z15])],[(0,[z349,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z350,z6]),(0,[z7,z2,z3,z4,z5,z71,z6]),(0,[z7,z2,z3,z4,z351,z5,z6]),(0,[z210,z7,z2,z3,z4,z5,z100]),(0,[z7,z2,z3,z4,z5,z352,z6]),(0,[z7,z2,z3,z353,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z354])],[(0,[z255,z7,z2,z3,z4,z70,z6])],[(0,[z7,z2,z355,z3,z4,z5,z6]),(0,[z356,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z357,z5,z6]),(0,[z7,z2,z3,z4,z358,z5,z6]),(0,[z7,z2,z359,z3,z4,z5,z6]),(0,[z360,z7,z2,z3,z4,z5,z6]),(0,[z79,z7,z2,z3,z4,z232,z6])]],
   [[(0,[z7,z361,z2,z3,z4,z5,z6]),(0,[z362,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z363,z4,z5,z6]),(0,[z364,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z365])],[(0,[z52,z7,z2,z366,z4,z5,z6]),(0,[z7,z367,z2,z3,z4,z5,z6]),(0,[z177,z7,z2,z3,z58,z5,z6]),(1,[z7,z2,z14,z4,z5,z6])],[(0,[z7,z2,z3,z368,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z369]),(0,[z7,z2,z3,z10,z5,z370,z6]),(0,[z7,z2,z371,z3,z4,z5,z6]),(0,[z372,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z4,z5,z6,z221]),(0,[z373,z7,z2,z3,z4,z5,z6])],[(1,[z7,z2,z51,z4,z5,z6]),(0,[z210,z7,z2,z165,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z374]),(0,[z7,z2,z3,z147,z4,z5,z6]),(0,[z23,z7,z375,z3,z4,z5,z6])],[(0,[z7,z376,z2,z3,z4,z5,z6]),(0,[z377,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z378,z5,z6]),(0,[z79,z7,z2,z3,z4,z59,z6]),(0,[z7,z2,z379,z3,z4,z5,z6])],[(0,[z380,z7,z2,z3,z4,z5,z6]),(0,[z381,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z138,z6,z203]),(0,[z23,z382,z2,z3,z4,z5,z6]),(0,[z23,z7,z383,z3,z4,z5,z6])],[(1,[z7,z2,z3,z4,z5,z6]),(0,[z384,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z69,z97,z6]),(0,[z7,z2,z3,z165,z45,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6,z385]),(0,[z386,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z387,z6])]],
   [[(0,[z7,z2,z3,z4,z388,z5,z6]),(0,[z7,z178,z2,z41,z4,z5,z6]),(0,[z7,z2,z3,z389,z4,z5,z6]),(0,[z210,z7,z2,z3,z4,z5,z109]),(0,[z7,z2,z3,z4,z390,z5,z6]),(0,[z7,z391,z2,z3,z4,z5,z6]),(1,[z320,z7,z2,z3,z5,z6])],[(0,[z7,z2,z3,z4,z5,z5,z6]),(0,[z7,z2,z3,z4,z392,z5,z6]),(0,[z7,z2,z41,z165,z4,z5,z6]),(0,[z7,z2,z393,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z394,z6]),(0,[z7,z395,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z45,z5,z6,z203]),(0,[z7,z197,z2,z3,z396,z5,z6]),(0,[z7,z2,z3,z4,z5,z397,z6])],[(0,[z7,z2,z3,z398,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z399,z6]),(0,[z7,z400,z2,z3,z4,z5,z6])],[(0,[z401,z7,z2,z3,z4,z5,z6]),(0,[z239,z7,z2,z3,z5,z69,z6]),(0,[z7,z2,z3,z4,z5,z6,z402]),(0,[z7,z2,z3,z4,z403,z5,z6]),(0,[z404,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z405,z4,z5,z6]),(0,[z7,z2,z3,z4,z406,z5,z6]),(0,[z7,z2,z3,z4,z39,z5,z6]),(0,[z7,z2,z3,z4,z5,z407,z6]),(0,[z320,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z408,z4,z5,z6])],[(0,[z409,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z410,z5,z6]),(0,[z178,z2,z3,z33,z4,z5,z6]),(1,[z7,z2,z3,z68,z5,z6]),(0,[z7,z2,z3,z411,z4,z5,z6]),(0,[z7,z2,z3,z4,z412,z5,z6]),(0,[z7,z2,z3,z413,z4,z5,z6]),(0,[z414,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z415,z3,z4,z5,z6])],[(0,[z416,z7,z2,z3,z4,z5,z6]),(0,[z210,z7,z2,z3,z161,z5,z6]),(0,[z7,z417,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z221]),(1,[z7,z2,z3,z5,z6,z208])]],
   [[(0,[z7,z2,z3,z51,z4,z5,z6]),(0,[z155,z7,z2,z3,z45,z5,z6]),(0,[z7,z2,z3,z60,z59,z5,z6])],[(0,[z52,z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z38]),(0,[z7,z2,z3,z4,z5,z6,z418]),(0,[z210,z7,z2,z3,z171,z5,z6]),(0,[z177,z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z62,z5,z6]),(0,[z7,z2,z44,z3,z4,z5,z6])],[(0,[z7,z178,z2,z4,z5,z138,z6]),(0,[z7,z2,z3,z4,z4,z5,z6]),(0,[z96,z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z419,z5,z6]),(0,[z7,z2,z3,z4,z5,z420,z6]),(0,[z7,z2,z3,z421,z4,z5,z6]),(0,[z7,z2,z422,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z423,z5,z6])],[(0,[z7,z2,z3,z3,z4,z5,z6]),(0,[z1,z7,z2,z3,z59,z5,z6]),(1,[z155,z7,z3,z45,z5,z6]),(0,[z7,z2,z3,z424,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z425,z6]),(0,[z7,z2,z3,z4,z5,z6,z426])],[(0,[z7,z2,z366,z3,z4,z5,z6]),(0,[z427,z7,z2,z3,z4,z5,z6]),(0,[z23,z7,z2,z3,z10,z5,z6]),(0,[z85,z7,z2,z3,z59,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z428])],[(0,[z346,z7,z2,z3,z4,z5,z6]),(0,[z429,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z271,z5,z6]),(0,[z79,z7,z2,z3,z150,z5,z6])],[(1,[z32,z2,z33,z4,z5,z6]),(0,[z430,z7,z2,z3,z4,z5,z6]),(0,[z7,z431,z2,z3,z4,z5,z6]),(0,[z7,z2,z432,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z38,z28]),(0,[z50,z7,z164,z2,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z433,z6])],[(0,[z2,z3,z4,z70,z5,z69,z6]),(0,[z37,z7,z2,z3,z4,z5,z38]),(0,[z7,z434,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z171,z4,z5,z6])]],
   [[(1,[z7,z2,z3,z306,z5,z6]),(0,[z435,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z436,z6]),(0,[z437,z7,z2,z3,z45,z5,z6]),(1,[z7,z2,z3,z4,z319,z6]),(0,[z7,z2,z3,z4,z5,z6,z202]),(0,[z7,z2,z3,z4,z5,z6,z438])],[(0,[z7,z2,z3,z439,z4,z5,z6]),(0,[z7,z2,z3,z440,z4,z5,z6]),(1,[z255,z2,z3,z4,z69,z6]),(0,[z7,z2,z3,z4,z5,z6,z441])],[(0,[z442,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z68,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z443]),(0,[z7,z2,z3,z4,z5,z6,z444]),(0,[z7,z2,z60,z4,z58,z5,z6]),(0,[z445,z7,z2,z3,z4,z5,z6])],[(0,[z346,z7,z224,z3,z4,z5,z6]),(0,[z7,z189,z2,z3,z45,z5,z6]),(0,[z7,z2,z446,z3,z4,z5,z6]),(1,[z447,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z319,z6]),(1,[z7,z2,z3,z4,z193,z6]),(0,[z448,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z103,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z208])],[(0,[z7,z449,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z450,z5,z6]),(0,[z7,z13,z2,z3,z45,z5,z6]),(0,[z7,z2,z3,z4,z5,z451,z6]),(0,[z7,z452,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z453,z4,z5,z6]),(1,[z7,z197,z3,z4,z11,z6])],[(0,[z7,z454,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z455,z6]),(0,[z7,z2,z3,z4,z70,z97,z6]),(0,[z7,z2,z3,z4,z5,z456,z6]),(0,[z102,z395,z2,z3,z4,z5,z6]),(0,[z290,z7,z2,z3,z10,z5,z6]),(0,[z96,z7,z197,z3,z4,z5,z6]),(0,[z457,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z10,z70,z5,z6]),(0,[z7,z102,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z10,z5,z72,z6])]],
   [[(0,[z7,z149,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z248,z4,z5,z6]),(0,[z7,z458,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z459,z4,z5,z6]),(0,[z460,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z461])],[(1,[z1,z2,z3,z250,z5,z6]),(1,[z7,z2,z336,z4,z5,z6]),(0,[z110,z7,z2,z3,z4,z5,z6])],[(0,[z7,z224,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z332,z4,z5,z6]),(0,[z7,z462,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z61,z5,z73]),(0,[z463,z7,z2,z3,z4,z5,z6])],[(1,[z7,z2,z3,z4,z5,z338]),(0,[z182,z224,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z464]),(0,[z7,z2,z3,z45,z5,z6,z24]),(0,[z9,z7,z2,z41,z4,z5,z6])],[(0,[z465,z7,z2,z3,z4,z5,z6]),(0,[z7,z164,z2,z3,z4,z5,z6]),(0,[z466,z7,z2,z3,z4,z5,z6]),(0,[z7,z189,z3,z165,z4,z5,z6]),(0,[z467,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z61,z4,z5,z6])],[(0,[z7,z224,z2,z3,z294,z5,z6]),(0,[z7,z2,z3,z4,z5,z468,z6]),(0,[z7,z13,z3,z165,z4,z5,z6]),(0,[z7,z2,z3,z45,z4,z5,z6]),(0,[z17,z7,z2,z3,z45,z5,z6]),(1,[z7,z2,z3,z317,z5,z6]),(0,[z7,z2,z3,z4,z5,z139,z6])],[(0,[z255,z115,z2,z3,z4,z5,z6]),(0,[z177,z7,z2,z3,z45,z5,z6]),(0,[z177,z7,z2,z469,z4,z5,z6]),(0,[z9,z7,z2,z3,z4,z39,z6]),(0,[z7,z2,z470,z3,z4,z5,z6])],[(0,[z7,z2,z3,z471,z4,z5,z6]),(0,[z7,z2,z3,z10,z11,z5,z6]),(0,[z7,z2,z3,z45,z5,z6,z15]),(0,[z7,z2,z3,z4,z5,z6,z55]),(0,[z7,z197,z2,z3,z4,z97,z6]),(0,[z7,z2,z3,z4,z5,z27,z6]),(0,[z7,z2,z3,z4,z472,z5,z6])]],
   [[(0,[z7,z2,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z473,z4,z5,z6]),(0,[z7,z2,z3,z150,z4,z232,z6])],[(0,[z7,z2,z3,z60,z10,z5,z6]),(0,[z23,z7,z2,z3,z45,z5,z6]),(0,[z474,z7,z2,z3,z4,z5,z6]),(0,[z23,z7,z2,z469,z4,z5,z6]),(0,[z7,z2,z3,z475,z4,z5,z6]),(1,[z7,z375,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z476,z5,z6])],[(1,[z7,z2,z366,z4,z5,z6]),(0,[z7,z2,z3,z45,z5,z232,z6]),(0,[z7,z13,z2,z3,z4,z5,z27])],[(0,[z7,z2,z3,z4,z5,z6,z77]),(0,[z224,z2,z3,z53,z4,z5,z6]),(1,[z382,z2,z3,z4,z5,z6]),(1,[z7,z383,z3,z4,z5,z6]),(0,[z23,z7,z2,z3,z459,z5,z6])],[(1,[z226,z7,z3,z4,z5,z6]),(1,[z7,z88,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z477,z5,z6])],[(0,[z478,z7,z2,z3,z4,z5,z6]),(0,[z255,z7,z2,z3,z4,z69,z6]),(0,[z85,z7,z2,z3,z10,z5,z6]),(0,[z7,z197,z2,z3,z4,z11,z6]),(0,[z7,z2,z3,z150,z4,z59,z6]),(0,[z110,z7,z2,z3,z4,z5,z139])],[(0,[z52,z7,z2,z3,z479,z5,z6]),(0,[z7,z2,z3,z33,z10,z5,z6]),(0,[z182,z115,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z336,z4,z5,z6])],[(0,[z7,z2,z3,z4,z173,z5,z6]),(0,[z177,z7,z178,z2,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z480,z6]),(0,[z347,z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z481,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z10,z57,z5,z6]),(0,[z7,z2,z3,z45,z5,z97,z6])],[(0,[z52,z7,z2,z3,z4,z482,z6]),(0,[z52,z7,z3,z53,z4,z5,z6]),(0,[z115,z2,z3,z53,z4,z5,z6]),(1,[z483,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z317,z5,z6]),(1,[z313,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z484,z5,z6])],[(0,[z1,z7,z2,z3,z250,z5,z6]),(0,[z7,z88,z2,z3,z45,z5,z6]),(0,[z7,z2,z3,z4,z485,z5,z6]),(0,[z7,z2,z41,z3,z4,z138,z6])],[(0,[z486,z7,z2,z3,z4,z5,z6]),(0,[z7,z487,z2,z3,z4,z5,z6]),(0,[z7,z2,z488,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z27,z139])],[(0,[z7,z489,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z396,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z28]),(0,[z79,z7,z2,z3,z4,z5,z6])],[(0,[z7,z490,z2,z3,z4,z5,z6]),(0,[z7,z2,z491,z3,z4,z5,z6]),(0,[z255,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z492,z6]),(0,[z493,z7,z2,z3,z4,z5,z6])],[(0,[z7,z494,z2,z3,z4,z5,z6]),(0,[z495,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z58,z5,z6]),(0,[z7,z2,z3,z4,z496,z5,z6])],[(0,[z7,z224,z2,z3,z45,z5,z6]),(1,[z7,z3,z45,z10,z5,z6]),(0,[z7,z2,z3,z4,z5,z497,z6]),(0,[z23,z452,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z103,z139,z6])]],
   [[(0,[z498,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z45,z5,z139,z6]),(0,[z499,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z500,z6]),(0,[z7,z2,z3,z4,z5,z501,z6])],[(0,[z7,z189,z2,z165,z4,z5,z6]),(0,[z7,z111,z2,z3,z45,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z502]),(0,[z7,z2,z469,z3,z4,z5,z6]),(0,[z503,z7,z2,z3,z4,z5,z6])],[(1,[z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z5,z504,z6]),(0,[z7,z13,z2,z167,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z505,z6])],[(1,[z182,z178,z2,z4,z5,z6]),(0,[z506,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z507,z6])],[(0,[z7,z2,z3,z508,z4,z5,z6]),(0,[z509,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z510])],[(0,[z2,z3,z53,z4,z5,z69,z6]),(1,[z7,z2,z3,z294,z5,z6]),(0,[z511,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z512]),(0,[z513,z7,z2,z3,z4,z5,z6]),(0,[z483,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z514,z5,z6]),(0,[z7,z2,z3,z515,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z516,z6]),(0,[z7,z2,z3,z4,z5,z517,z6]),(0,[z7,z2,z3,z5,z73,z6,z15])],[(0,[z7,z2,z3,z518,z4,z5,z6])]],
   [[(0,[z115,z346,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z45,z59,z5,z6]),(1,[z7,z2,z3,z267,z5,z6])],[(0,[z32,z7,z2,z3,z45,z5,z6]),(0,[z7,z2,z519,z3,z4,z5,z6]),(0,[z7,z197,z2,z3,z158,z5,z6]),(0,[z7,z2,z3,z4,z5,z520,z6])],[(0,[z7,z2,z3,z4,z5,z521,z6])],[(0,[z7,z2,z3,z33,z45,z5,z6]),(0,[z7,z2,z522,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z45,z5,z6]),(0,[z523,z7,z2,z3,z4,z5,z6]),(0,[z524,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z525,z6]),(0,[z7,z2,z3,z4,z5,z6,z526])],[(0,[z7,z2,z3,z4,z5,z69,z6]),(0,[z7,z2,z3,z45,z216,z5,z6]),(1,[z180,z7,z3,z4,z5,z28])],[(0,[z115,z2,z3,z4,z70,z5,z6]),(0,[z7,z2,z44,z3,z10,z5,z6]),(0,[z527,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z528]),(0,[z7,z529,z2,z3,z4,z5,z6])],[(0,[z7,z2,z41,z33,z4,z5,z6]),(0,[z7,z2,z3,z530,z4,z5,z6]),(0,[z7,z2,z3,z4,z10,z5,z6]),(0,[z7,z2,z3,z4,z5,z234,z6]),(0,[z7,z375,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z531,z4,z5,z6]),(0,[z23,z7,z2,z165,z4,z5,z6]),(0,[z7,z2,z3,z45,z5,z6,z28])]],
   [[(0,[z7,z2,z3,z61,z58,z5,z6]),(1,[z7,z2,z3,z62,z5,z6])],[(0,[z346,z7,z2,z3,z10,z5,z6]),(0,[z115,z7,z2,z3,z45,z5,z6]),(0,[z7,z2,z532,z3,z4,z5,z6]),(0,[z7,z2,z3,z45,z150,z5,z6]),(0,[z7,z2,z46,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z533])],[(0,[z32,z7,z178,z2,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z534,z6]),(0,[z7,z2,z3,z4,z5,z6,z6])],[(1,[z395,z2,z3,z4,z5,z6]),(0,[z535,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z306,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z536,z6]),(0,[z7,z2,z3,z4,z250,z5,z6]),(0,[z0,z7,z2,z3,z132,z5,z6]),(0,[z7,z2,z3,z537,z4,z5,z6]),(0,[z180,z7,z2,z3,z45,z5,z6]),(0,[z382,z7,z2,z3,z4,z5,z6])],[(0,[z52,z7,z3,z4,z11,z5,z6]),(0,[z7,z2,z33,z4,z5,z72,z6]),(0,[z182,z50,z2,z3,z4,z5,z6]),(0,[z538,z7,z2,z3,z4,z5,z6]),(0,[z539,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z383,z3,z4,z5,z6])],[(0,[z7,z2,z3,z186,z45,z5,z6]),(0,[z7,z2,z3,z4,z5,z540,z6]),(0,[z79,z7,z2,z3,z60,z5,z6]),(0,[z7,z211,z2,z3,z4,z5,z6])],[(0,[z541,z7,z2,z3,z4,z5,z6]),(0,[z542,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z543,z5,z6])]],
   [[(0,[z544,z7,z2,z3,z4,z5,z6]),(0,[z37,z7,z2,z3,z4,z5,z6]),(0,[z7,z189,z2,z3,z545,z5,z6])],[(0,[z52,z2,z3,z53,z4,z5,z6]),(0,[z546,z7,z2,z3,z4,z5,z6]),(0,[z346,z2,z3,z4,z5,z69,z6]),(0,[z547,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z459,z5,z6])],[(0,[z7,z2,z3,z45,z5,z71,z6]),(0,[z7,z2,z3,z548,z4,z5,z6]),(1,[z85,z7,z2,z3,z5,z15])],[(0,[z52,z7,z2,z549,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z550]),(1,[z50,z2,z3,z4,z5,z71]),(0,[z7,z2,z469,z3,z60,z5,z6]),(1,[z9,z7,z2,z4,z138,z6]),(0,[z7,z2,z3,z4,z5,z551,z6]),(0,[z7,z2,z3,z4,z5,z552,z6])],[(0,[z553,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z554,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z555,z5,z6]),(0,[z110,z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z556,z5,z6])],[(0,[z7,z2,z33,z4,z5,z138,z6]),(0,[z7,z557,z2,z3,z4,z5,z6]),(0,[z7,z197,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z271,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z202,z203])],[(1,[z7,z2,z3,z479,z5,z6]),(0,[z558,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z559,z4,z5,z6]),(0,[z7,z2,z3,z45,z5,z69,z6]),(0,[z7,z2,z3,z4,z5,z560,z6]),(0,[z7,z2,z3,z561,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z562])]],
   [[(0,[z7,z2,z3,z274,z4,z5,z6]),(0,[z563,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z564,z4,z5,z6]),(0,[z7,z2,z3,z565,z4,z5,z6]),(0,[z7,z566,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z61,z10,z5,z6]),(0,[z79,z7,z2,z3,z58,z5,z6]),(0,[z7,z2,z3,z567,z4,z5,z6]),(0,[z568,z7,z2,z3,z4,z5,z6]),(1,[z110,z7,z2,z3,z4,z203])],[(0,[z210,z7,z2,z3,z4,z5,z6]),(0,[z569,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z45,z10,z5,z6])],[(1,[z7,z2,z3,z4,z482,z6]),(0,[z96,z52,z7,z3,z4,z5,z6]),(0,[z180,z7,z2,z3,z4,z5,z27])],[(0,[z7,z570,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z543,z5,z6])],[(0,[z7,z571,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z572,z4,z5,z6]),(0,[z7,z2,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z10,z5,z6,z24]),(0,[z7,z2,z469,z4,z58,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z573]),(0,[z7,z2,z3,z4,z5,z574,z6]),(0,[z7,z575,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z482,z6]),(0,[z7,z2,z3,z4,z5,z6,z576]),(0,[z577,z7,z2,z3,z4,z5,z6]),(1,[z7,z13,z3,z10,z5,z6]),(1,[z7,z2,z3,z4,z5,z504]),(0,[z7,z2,z469,z3,z58,z5,z6]),(1,[z177,z7,z2,z60,z5,z6]),(1,[z452,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z150,z4,z5,z6])],[(0,[z346,z7,z2,z3,z45,z5,z6]),(1,[z7,z3,z10,z5,z6,z28]),(0,[z578,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z579])],[(0,[z2,z3,z132,z4,z250,z5,z6]),(0,[z7,z2,z3,z45,z250,z5,z6]),(0,[z2,z3,z4,z5,z71,z6,z38]),(0,[z580,z7,z2,z3,z4,z5,z6]),(0,[z581,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z61,z5,z73,z6]),(0,[z7,z2,z3,z4,z5,z582,z6])]],
   [[(0,[z52,z346,z2,z3,z4,z5,z6]),(0,[z7,z583,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z10,z5,z6,z15]),(0,[z584,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z585,z3,z4,z5,z6]),(0,[z7,z586,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z587,z4,z5,z6]),(0,[z7,z588,z2,z3,z4,z5,z6])],[(0,[z7,z2,z589,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z590]),(0,[z7,z2,z3,z4,z5,z591,z6]),(1,[z23,z7,z2,z4,z5,z24]),(0,[z592,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z479,z5,z6]),(0,[z7,z189,z2,z3,z248,z5,z6]),(0,[z483,z102,z2,z3,z4,z5,z6]),(0,[z7,z593,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z10,z5,z232,z6]),(0,[z7,z2,z3,z45,z39,z5,z6]),(0,[z594,z7,z2,z3,z4,z5,z6]),(0,[z23,z7,z2,z3,z4,z5,z24]),(0,[z7,z2,z3,z4,z5,z6,z595])],[(0,[z7,z2,z3,z4,z5,z27,z71]),(0,[z7,z102,z189,z2,z4,z5,z6]),(0,[z9,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z41,z3,z4,z39,z6]),(0,[z7,z596,z2,z3,z4,z5,z6])],[(0,[z597,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z598,z5,z6]),(0,[z599,z7,z2,z3,z4,z5,z6]),(0,[z210,z7,z3,z4,z5,z6,z28])],[(0,[z224,z2,z3,z33,z4,z5,z6]),(0,[z182,z32,z2,z3,z4,z5,z6]),(0,[z118,z7,z2,z3,z4,z5,z6]),(1,[z136,z7,z2,z4,z5,z6])],[(0,[z52,z7,z2,z3,z4,z90,z6]),(0,[z7,z2,z3,z4,z5,z600,z6]),(0,[z7,z2,z3,z4,z70,z11,z6]),(0,[z7,z2,z3,z45,z5,z6,z38]),(0,[z180,z7,z2,z3,z4,z5,z28]),(0,[z7,z2,z44,z3,z4,z5,z72])]],
   [[(0,[z7,z102,z2,z4,z5,z72,z6]),(0,[z79,z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z45,z419,z5,z6]),(0,[z126,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z127,z4,z5,z6]),(0,[z601,z7,z2,z3,z4,z5,z6]),(0,[z447,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z602]),(0,[z7,z2,z3,z61,z4,z5,z15])],[(0,[z52,z7,z2,z3,z45,z5,z6]),(0,[z346,z7,z3,z53,z4,z5,z6]),(0,[z255,z7,z2,z3,z10,z5,z6]),(0,[z50,z7,z2,z3,z4,z5,z38]),(0,[z7,z2,z3,z10,z5,z97,z6]),(0,[z7,z2,z3,z4,z5,z176,z6]),(0,[z7,z603,z2,z3,z4,z5,z6])],[(0,[z604,z7,z2,z3,z4,z5,z6]),(0,[z96,z7,z2,z3,z45,z5,z6]),(0,[z96,z7,z2,z3,z543,z5,z6]),(0,[z7,z2,z3,z4,z5,z605,z6]),(0,[z7,z2,z3,z606,z4,z5,z6]),(0,[z7,z607,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z103,z5,z139])],[(0,[z7,z2,z3,z10,z5,z138,z6]),(0,[z7,z2,z3,z245,z4,z5,z6]),(0,[z7,z2,z3,z608,z4,z5,z6])],[(0,[z7,z178,z2,z4,z58,z5,z6]),(0,[z7,z609,z2,z3,z4,z5,z6]),(0,[z7,z2,z610,z3,z4,z5,z6]),(0,[z7,z2,z3,z611,z4,z5,z6])],[(0,[z7,z2,z3,z612,z4,z5,z6]),(0,[z210,z7,z189,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z613,z5,z6]),(0,[z7,z2,z469,z3,z10,z5,z6]),(1,[z7,z2,z167,z4,z5,z6])],[(0,[z614,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z615,z6]),(0,[z1,z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z45,z5,z6,z441]),(0,[z7,z121,z2,z3,z4,z5,z6]),(0,[z616,z7,z2,z3,z4,z5,z6]),(0,[z617,z7,z2,z3,z4,z5,z6]),(0,[z618,z7,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z6,z619]),(0,[z620,z7,z2,z3,z4,z5,z6])],[(0,[z621,z7,z2,z3,z4,z5,z6]),(0,[z182,z7,z2,z3,z10,z5,z6]),(0,[z0,z2,z3,z132,z4,z5,z6]),(0,[z255,z2,z3,z4,z5,z69,z6]),(0,[z7,z2,z3,z4,z5,z622,z6]),(0,[z7,z2,z3,z45,z103,z5,z6])],[(1,[z7,z2,z3,z4,z5,z109]),(0,[z623,z7,z2,z3,z4,z5,z6]),(0,[z7,z624,z2,z3,z4,z5,z6]),(0,[z7,z625,z2,z3,z4,z5,z6]),(0,[z626,z7,z2,z3,z4,z5,z6])],[(0,[z92,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z627]),(0,[z7,z2,z3,z518,z10,z5,z6]),(0,[z7,z2,z3,z4,z5,z370,z6]),(0,[z7,z2,z3,z4,z5,z6,z628]),(0,[z629,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z469,z58,z5,z6]),(0,[z7,z2,z469,z4,z5,z72,z6]),(0,[z7,z2,z630,z3,z4,z5,z6])],[(0,[z7,z2,z3,z631,z4,z5,z6]),(0,[z7,z2,z209,z3,z4,z5,z6]),(0,[z632,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z60,z4,z5,z72,z6])],[(0,[z23,z7,z178,z2,z4,z5,z6])],[(0,[z7,z633,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z634,z6]),(0,[z7,z2,z3,z4,z5,z6,z635]),(0,[z290,z7,z2,z3,z45,z5,z6]),(0,[z7,z2,z3,z636,z4,z5,z6]),(0,[z7,z637,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z638,z6]),(0,[z7,z2,z3,z4,z5,z6,z639])],[(0,[z7,z2,z3,z4,z5,z338,z6]),(0,[z7,z102,z2,z3,z45,z5,z6]),(1,[z7,z2,z3,z396,z5,z6])]],
   [[(0,[z640,z7,z2,z3,z4,z5,z6]),(0,[z7,z641,z2,z3,z4,z5,z6]),(0,[z96,z7,z2,z3,z4,z5,z504]),(0,[z7,z2,z3,z4,z5,z6,z642]),(0,[z7,z2,z3,z150,z59,z5,z6])],[(0,[z182,z2,z3,z4,z5,z69,z6]),(0,[z7,z2,z3,z643,z4,z5,z6]),(0,[z7,z2,z3,z10,z59,z5,z6]),(0,[z7,z2,z644,z3,z4,z5,z6]),(0,[z9,z447,z2,z3,z4,z5,z6])],[(0,[z7,z2,z33,z165,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z645,z6]),(0,[z7,z13,z2,z3,z4,z5,z28]),(0,[z7,z2,z3,z4,z5,z646,z6]),(0,[z23,z7,z2,z3,z4,z5,z27]),(0,[z647,z7,z2,z3,z4,z5,z6])],[(0,[z52,z7,z2,z3,z4,z5,z77]),(0,[z7,z2,z3,z4,z648,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z649]),(0,[z7,z2,z3,z10,z298,z5,z6]),(0,[z7,z2,z3,z59,z5,z232,z6])],[(1,[z7,z2,z549,z4,z5,z6]),(0,[z7,z2,z3,z53,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z650,z6]),(0,[z651,z7,z2,z3,z4,z5,z6]),(0,[z210,z7,z13,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z652]),(0,[z7,z2,z3,z4,z5,z653,z6])],[(0,[z52,z182,z2,z3,z4,z5,z6]),(0,[z7,z2,z125,z3,z4,z5,z6]),(0,[z7,z2,z3,z45,z5,z27,z6])],[(0,[z255,z7,z2,z3,z45,z5,z6]),(0,[z7,z654,z2,z3,z4,z5,z6]),(0,[z7,z2,z655,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z656,z5,z6]),(0,[z7,z2,z3,z4,z5,z657,z6]),(0,[z7,z2,z3,z4,z5,z658,z6])],[(0,[z7,z2,z3,z132,z4,z5,z6]),(0,[z1,z2,z3,z4,z250,z5,z6]),(0,[z133,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z659]),(0,[z23,z7,z2,z44,z4,z5,z6])]],
   [[(0,[z660,z7,z2,z3,z4,z5,z6]),(0,[z7,z102,z178,z2,z4,z5,z6]),(0,[z7,z102,z3,z165,z4,z5,z6]),(0,[z7,z2,z3,z537,z10,z5,z6]),(0,[z85,z7,z2,z3,z4,z5,z15])],[(0,[z7,z661,z2,z3,z4,z5,z6]),(0,[z177,z7,z2,z33,z4,z5,z6]),(1,[z7,z189,z165,z4,z5,z6]),(0,[z662,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z60,z45,z5,z6])],[(0,[z7,z2,z3,z4,z663,z5,z6]),(0,[z7,z2,z469,z3,z45,z5,z6]),(0,[z7,z2,z3,z4,z5,z664,z6])],[(0,[z665,z7,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z132,z5,z6])],[(0,[z7,z2,z3,z666,z4,z5,z6]),(0,[z23,z7,z2,z33,z4,z5,z6]),(0,[z1,z7,z2,z3,z45,z5,z6]),(0,[z37,z7,z2,z3,z10,z5,z6]),(1,[z7,z2,z3,z545,z5,z6])],[(0,[z346,z7,z3,z4,z11,z5,z6]),(0,[z115,z7,z2,z3,z4,z70,z6]),(0,[z7,z2,z3,z4,z161,z5,z6]),(0,[z667,z7,z2,z3,z4,z5,z6]),(0,[z85,z7,z2,z3,z45,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z668])],[(0,[z7,z2,z3,z4,z5,z669,z6]),(0,[z182,z7,z2,z3,z45,z5,z6]),(1,[z37,z2,z3,z4,z5,z38]),(0,[z7,z2,z3,z10,z5,z6,z203]),(0,[z7,z2,z3,z341,z45,z5,z6])],[(0,[z7,z3,z45,z4,z10,z5,z6]),(0,[z23,z7,z2,z3,z4,z5,z28]),(1,[z7,z2,z41,z4,z39,z6]),(0,[z7,z2,z3,z4,z5,z670,z6])]],
   [[(0,[z671,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z672,z4,z5,z6]),(0,[z96,z121,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z58,z5,z6,z15]),(0,[z673,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z549,z4,z5,z6]),(0,[z182,z2,z3,z4,z5,z6,z38]),(0,[z7,z2,z3,z674,z4,z5,z6])],[(0,[z675,z7,z2,z3,z4,z5,z6]),(0,[z676,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z677]),(0,[z7,z678,z2,z3,z4,z5,z6]),(0,[z679,z7,z2,z3,z4,z5,z6]),(0,[z7,z197,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z680,z4,z5,z6]),(0,[z7,z2,z3,z681,z4,z5,z6])],[(0,[z7,z2,z3,z4,z682,z5,z6]),(0,[z7,z2,z3,z10,z5,z71,z6]),(0,[z7,z2,z3,z4,z5,z28,z203]),(0,[z110,z7,z2,z3,z4,z5,z203])],[(0,[z437,z7,z2,z3,z4,z5,z6]),(0,[z7,z178,z2,z3,z4,z5,z6]),(0,[z362,z7,z2,z3,z45,z5,z6]),(0,[z7,z2,z3,z45,z58,z5,z6]),(0,[z7,z2,z683,z3,z4,z5,z6])],[(0,[z684,z7,z2,z3,z4,z5,z6]),(0,[z1,z7,z2,z3,z132,z5,z6]),(0,[z685,z7,z2,z3,z4,z5,z6]),(0,[z37,z7,z2,z3,z4,z5,z71]),(0,[z210,z7,z2,z3,z10,z5,z6]),(0,[z183,z7,z2,z3,z4,z5,z6]),(0,[z686,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z687,z6]),(0,[z7,z2,z3,z4,z5,z688,z6]),(0,[z7,z2,z3,z4,z5,z6,z689]),(0,[z7,z2,z44,z4,z5,z72,z6])],[(0,[z7,z2,z3,z4,z690,z5,z6]),(0,[z182,z7,z178,z2,z4,z5,z6]),(0,[z7,z189,z2,z3,z4,z5,z6]),(0,[z7,z13,z3,z4,z5,z27,z6]),(0,[z9,z313,z2,z3,z4,z5,z6]),(0,[z7,z2,z691,z3,z4,z5,z6])]],
   [[(1,[z7,z2,z3,z4,z90,z6]),(0,[z7,z2,z3,z4,z70,z5,z6]),(0,[z7,z2,z3,z4,z11,z69,z6]),(0,[z7,z2,z3,z4,z545,z5,z6]),(0,[z155,z7,z3,z4,z5,z6,z28]),(0,[z96,z7,z3,z4,z5,z97,z6]),(0,[z7,z13,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z72,z6]),(0,[z7,z2,z3,z4,z5,z73,z6])],[(0,[z7,z2,z3,z692,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z693]),(0,[z7,z2,z3,z4,z5,z6,z694]),(0,[z7,z2,z3,z4,z5,z695,z6]),(0,[z7,z2,z3,z4,z5,z27,z203]),(0,[z696,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z697])],[(1,[z7,z2,z3,z45,z5,z6]),(0,[z7,z2,z3,z10,z5,z6,z374]),(0,[z7,z698,z2,z3,z4,z5,z6])],[(0,[z7,z699,z2,z3,z4,z5,z6]),(0,[z7,z2,z41,z3,z332,z5,z6]),(0,[z700,z7,z2,z3,z4,z5,z6])],[(0,[z50,z2,z3,z33,z4,z5,z6]),(0,[z7,z2,z44,z3,z4,z5,z24]),(0,[z701,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z61,z4,z5,z73])],[(0,[z702,z7,z2,z3,z4,z5,z6]),(0,[z7,z703,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z704,z5,z6])],[(0,[z50,z2,z3,z4,z5,z71,z6]),(0,[z210,z7,z102,z2,z4,z5,z6]),(1,[z7,z211,z3,z4,z5,z6])],[(0,[z96,z346,z7,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z705]),(0,[z7,z706,z2,z3,z4,z5,z6]),(0,[z136,z7,z2,z4,z5,z6,z203])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z7,z2,z366,z4,z90,z6]),(0,[z133,z2,z3,z173,z5,z6]),(0,[z9,z447,z2,z4,z138,z6]),(0,[z79,z7,z2,z3,z707,z6])],[(0,[z0,z2,z3,z5,z552,z6]),(0,[z708,z7,z2,z3,z5,z6]),(0,[z7,z189,z165,z10,z5,z6]),(0,[z7,z375,z3,z45,z5,z6]),(0,[z452,z2,z3,z4,z193,z6]),(0,[z7,z151,z3,z127,z5,z6])],[(0,[z7,z2,z366,z45,z5,z6]),(0,[z7,z2,z709,z4,z5,z6]),(0,[z7,z2,z3,z710,z5,z6]),(0,[z1,z2,z3,z711,z5,z6]),(0,[z7,z566,z3,z4,z5,z27]),(0,[z304,z7,z2,z4,z138,z6]),(0,[z146,z2,z3,z147,z5,z6]),(0,[z7,z2,z469,z58,z5,z6]),(0,[z7,z2,z3,z61,z5,z257]),(0,[z7,z2,z3,z712,z5,z6]),(0,[z7,z2,z4,z5,z713,z6])],[(0,[z7,z2,z3,z479,z5,z338]),(0,[z7,z2,z33,z104,z5,z6]),(0,[z714,z2,z3,z4,z5,z6]),(0,[z382,z2,z3,z45,z5,z6]),(0,[z7,z383,z3,z45,z5,z6]),(0,[z7,z2,z379,z4,z39,z6]),(0,[z7,z375,z3,z459,z5,z6]),(0,[z7,z2,z3,z150,z59,z6]),(0,[z715,z2,z3,z4,z5,z6])],[(0,[z226,z7,z3,z45,z5,z6]),(0,[z146,z2,z46,z4,z5,z6]),(0,[z7,z2,z46,z147,z5,z6]),(0,[z7,z2,z3,z5,z6,z716]),(0,[z23,z7,z2,z4,z5,z717])],[(0,[z79,z7,z2,z78,z5,z6]),(0,[z7,z2,z3,z718,z5,z6]),(0,[z382,z2,z3,z459,z5,z6]),(0,[z7,z383,z3,z459,z5,z6]),(0,[z7,z151,z3,z5,z6,z15])],[(0,[z7,z2,z3,z4,z482,z338]),(0,[z416,z7,z2,z4,z138,z6]),(0,[z7,z3,z45,z692,z5,z6]),(0,[z7,z2,z3,z719,z5,z6]),(0,[z7,z2,z3,z396,z5,z6]),(0,[z7,z720,z2,z10,z5,z6]),(0,[z721,z7,z2,z3,z5,z6]),(0,[z23,z7,z2,z4,z193,z24]),(0,[z7,z2,z3,z722,z5,z6])],[(0,[z7,z723,z3,z4,z5,z6]),(0,[z7,z2,z3,z5,z6,z724]),(0,[z180,z7,z3,z10,z5,z28]),(0,[z7,z2,z41,z10,z39,z6]),(0,[z146,z2,z3,z4,z5,z55]),(0,[z7,z2,z336,z4,z5,z504]),(0,[z7,z2,z3,z147,z5,z55]),(0,[z7,z2,z41,z332,z39,z6])]],
   [[(0,[z7,z2,z3,z161,z5,z6]),(0,[z7,z2,z3,z725,z5,z6]),(0,[z7,z12,z13,z10,z5,z6]),(0,[z7,z2,z3,z59,z707,z6])],[(0,[z346,z121,z3,z4,z5,z6]),(0,[z7,z164,z2,z4,z5,z6]),(0,[z7,z2,z3,z726,z5,z6]),(0,[z483,z2,z3,z45,z5,z6]),(0,[z313,z2,z3,z45,z5,z6])],[(0,[z7,z2,z3,z171,z5,z6]),(0,[z727,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z728,z5,z6])],[(0,[z7,z2,z3,z729,z5,z6]),(0,[z7,z2,z78,z59,z5,z6]),(0,[z1,z2,z78,z250,z5,z6]),(0,[z7,z730,z2,z4,z5,z6]),(0,[z7,z2,z3,z731,z5,z6]),(0,[z7,z2,z167,z271,z5,z6]),(0,[z7,z2,z3,z4,z5,z732])],[(0,[z382,z178,z2,z4,z5,z6]),(0,[z7,z2,z3,z733,z5,z6]),(0,[z7,z3,z45,z636,z5,z6])],[(0,[z7,z2,z3,z734,z4,z5]),(0,[z7,z3,z10,z5,z6,z418]),(0,[z7,z3,z161,z5,z6,z28]),(0,[z7,z119,z3,z10,z5,z6]),(0,[z180,z7,z3,z267,z5,z28])],[(0,[z735,z7,z2,z3,z5,z6]),(0,[z7,z2,z165,z4,z319,z6]),(0,[z96,z7,z3,z4,z736,z6])],[(0,[z7,z3,z45,z737,z5,z6]),(0,[z96,z7,z336,z4,z97,z6]),(0,[z96,z7,z3,z147,z97,z6]),(0,[z7,z13,z3,z4,z5,z27]),(0,[z452,z375,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z10,z90,z6]),(0,[z32,z738,z2,z4,z5,z6]),(0,[z7,z2,z739,z4,z5,z6]),(0,[z740,z2,z3,z4,z5,z6]),(0,[z177,z7,z2,z741,z5,z6]),(0,[z7,z742,z3,z4,z5,z6]),(0,[z7,z2,z3,z743,z5,z6]),(1,[z7,z2,z3,z4,z732])],[(0,[z7,z2,z3,z744,z5,z6])],[(0,[z7,z2,z745,z4,z5,z6]),(0,[z483,z178,z2,z4,z5,z6]),(0,[z0,z2,z3,z132,z5,z6]),(0,[z7,z2,z3,z737,z5,z6]),(0,[z7,z2,z746,z4,z5,z6])],[(0,[z7,z2,z3,z747,z5,z6]),(0,[z748,z7,z2,z3,z4,z5]),(0,[z182,z178,z2,z45,z5,z6]),(0,[z7,z2,z3,z545,z5,z6]),(0,[z210,z7,z102,z171,z5,z6])],[(0,[z7,z2,z366,z4,z5,z77]),(0,[z7,z749,z2,z4,z5,z6]),(0,[z226,z3,z33,z4,z5,z6]),(0,[z1,z603,z2,z3,z5,z6]),(0,[z7,z750,z189,z4,z5,z6]),(0,[z395,z2,z4,z5,z72,z6]),(0,[z362,z7,z2,z216,z5,z6])],[(0,[z255,z239,z2,z3,z69,z6]),(0,[z37,z2,z3,z4,z5,z38]),(0,[z7,z3,z10,z5,z6,z441]),(0,[z7,z2,z3,z751,z5,z6]),(0,[z7,z3,z10,z5,z6,z573]),(0,[z7,z2,z3,z5,z6,z752]),(0,[z7,z2,z3,z4,z5,z753]),(0,[z7,z2,z41,z62,z39,z6])],[(0,[z182,z2,z366,z4,z5,z6]),(0,[z7,z3,z4,z11,z482,z6]),(0,[z50,z2,z3,z10,z5,z71]),(0,[z7,z2,z3,z10,z754,z6]),(0,[z9,z7,z2,z10,z138,z6]),(0,[z118,z2,z3,z274,z5,z6])],[(0,[z7,z13,z3,z4,z5,z525]),(0,[z121,z2,z336,z4,z5,z6]),(0,[z121,z2,z3,z147,z5,z6]),(0,[z755,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z756,z4,z5,z6]),(0,[z7,z2,z3,z757,z5,z6]),(0,[z7,z2,z758,z4,z5,z6])],[(0,[z7,z2,z549,z479,z5,z6]),(0,[z7,z2,z3,z759,z5,z6]),(0,[z760,z2,z3,z4,z5,z6]),(0,[z7,z607,z3,z10,z5,z6]),(0,[z7,z462,z3,z45,z5,z6])],[(0,[z7,z2,z41,z4,z388,z6]),(0,[z761,z2,z3,z4,z5,z6]),(0,[z437,z2,z3,z245,z5,z6]),(0,[z23,z7,z2,z4,z5,z502])],[(0,[z7,z3,z762,z10,z5,z6]),(0,[z7,z2,z167,z317,z5,z6]),(0,[z7,z375,z3,z763,z5,z6])],[(0,[z7,z2,z549,z4,z482,z6]),(0,[z7,z2,z4,z5,z6,z764]),(0,[z7,z2,z3,z765,z5,z6]),(0,[z7,z174,z3,z10,z5,z6]),(0,[z180,z7,z3,z45,z5,z28]),(0,[z766,z2,z3,z4,z5,z6]),(0,[z7,z2,z469,z741,z5,z6])],[(0,[z7,z2,z3,z767,z5,z6]),(0,[z7,z2,z3,z768,z5,z6]),(0,[z133,z2,z3,z250,z5,z6]),(0,[z7,z197,z3,z396,z11,z6]),(1,[z7,z2,z4,z5,z717])],[(0,[z7,z2,z3,z4,z769,z6]),(0,[z1,z149,z2,z250,z5,z6]),(0,[z2,z3,z4,z5,z6,z770]),(0,[z771,z2,z3,z4,z5,z6]),(0,[z7,z772,z3,z4,z5,z6]),(0,[z7,z151,z3,z59,z5,z6])],[(0,[z7,z2,z3,z773,z5,z6]),(0,[z7,z641,z3,z10,z5,z6]),(0,[z7,z2,z774,z4,z5,z6]),(0,[z7,z375,z165,z4,z5,z6])]],
   [[(0,[z52,z3,z53,z10,z5,z6]),(0,[z7,z2,z3,z10,z5,z504]),(0,[z7,z2,z3,z4,z5,z775]),(0,[z7,z2,z776,z3,z5,z6])],[(0,[z7,z2,z3,z711,z5,z6]),(0,[z7,z2,z3,z4,z777,z6]),(0,[z778,z7,z3,z5,z84,z6]),(0,[z7,z3,z737,z4,z5,z6]),(0,[z110,z7,z2,z3,z45,z203]),(0,[z9,z7,z2,z4,z319,z6])],[(0,[z7,z557,z3,z10,z5,z6]),(0,[z779,z2,z3,z4,z5,z6]),(0,[z326,z7,z2,z3,z5,z15])],[(0,[z239,z7,z2,z3,z5,z6]),(0,[z7,z2,z4,z5,z6,z780]),(0,[z651,z7,z3,z4,z5,z28]),(0,[z395,z2,z3,z45,z5,z6])],[(0,[z448,z2,z33,z4,z5,z6]),(0,[z7,z2,z78,z10,z5,z6]),(0,[z255,z3,z4,z84,z69,z6]),(0,[z7,z375,z3,z4,z5,z109])],[(0,[z7,z2,z781,z4,z5,z6]),(0,[z2,z3,z33,z4,z5,z77]),(0,[z7,z2,z3,z782,z5,z6]),(0,[z7,z2,z783,z3,z5,z6]),(0,[z7,z211,z3,z4,z5,z6]),(0,[z155,z7,z3,z271,z5,z6])],[(0,[z7,z2,z3,z248,z5,z6]),(0,[z7,z2,z3,z4,z784,z6]),(0,[z785,z2,z3,z4,z5,z6]),(0,[z7,z2,z786,z45,z5,z6])],[(0,[z7,z2,z3,z787,z5,z6]),(0,[z7,z788,z3,z4,z5,z6]),(0,[z136,z715,z2,z4,z5,z6]),(0,[z7,z2,z3,z4,z139,z732])]],
   [[(0,[z7,z2,z549,z4,z5,z338]),(0,[z178,z738,z2,z4,z5,z6]),(0,[z7,z789,z3,z4,z5,z6]),(0,[z790,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z791,z5,z6])],[(0,[z7,z2,z3,z4,z5,z792]),(0,[z7,z178,z2,z62,z5,z6]),(0,[z7,z2,z793,z4,z5,z6]),(0,[z7,z12,z2,z4,z5,z6]),(0,[z7,z2,z3,z10,z5,z100]),(0,[z85,z7,z2,z3,z5,z441]),(0,[z7,z794,z3,z4,z5,z6])],[(0,[z146,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z147,z5,z6])],[(0,[z7,z12,z165,z4,z5,z6]),(0,[z7,z13,z3,z161,z5,z6]),(0,[z7,z2,z10,z5,z6,z795]),(0,[z9,z7,z2,z45,z138,z6]),(0,[z7,z2,z3,z4,z5,z717]),(0,[z7,z2,z5,z6,z208,z202])],[(0,[z796,z7,z2,z4,z5,z6]),(0,[z486,z7,z3,z45,z5,z6]),(0,[z7,z2,z797,z4,z5,z6]),(0,[z7,z2,z46,z4,z5,z6]),(0,[z798,z7,z2,z3,z5,z6]),(0,[z7,z2,z3,z799,z5,z6]),(0,[z7,z800,z3,z4,z5,z6])],[(0,[z7,z2,z3,z479,z90,z6]),(0,[z7,z2,z801,z4,z5,z6]),(0,[z7,z2,z802,z4,z5,z6]),(0,[z7,z220,z3,z10,z5,z6]),(0,[z7,z2,z4,z803,z138,z6])],[(0,[z382,z164,z2,z4,z5,z6]),(0,[z804,z7,z2,z45,z5,z6]),(0,[z7,z13,z3,z317,z5,z27]),(0,[z7,z2,z3,z805,z5,z6])],[(0,[z7,z806,z3,z4,z5,z6]),(0,[z7,z2,z117,z10,z5,z6]),(0,[z7,z2,z3,z4,z5,z55]),(1,[z7,z2,z3,z5,z807])]],
   [[(0,[z7,z2,z3,z808,z5,z6]),(0,[z121,z2,z3,z10,z5,z6]),(0,[z7,z2,z167,z10,z5,z6]),(0,[z7,z2,z3,z809,z5,z6]),(0,[z79,z7,z2,z3,z232,z6])],[(0,[z7,z2,z3,z4,z810,z6]),(0,[z811,z7,z3,z4,z5,z6])],[(0,[z7,z2,z3,z45,z482,z6]),(0,[z2,z3,z4,z5,z770,z38]),(0,[z96,z146,z3,z4,z97,z6]),(0,[z812,z7,z2,z3,z5,z6])],[(0,[z7,z2,z3,z4,z5,z77]),(0,[z7,z2,z3,z813,z5,z6]),(0,[z7,z814,z3,z4,z5,z6]),(0,[z7,z212,z3,z10,z5,z6]),(0,[z7,z111,z2,z341,z5,z6])],[(0,[z7,z2,z3,z815,z5,z6]),(0,[z7,z2,z3,z816,z5,z6]),(0,[z7,z211,z3,z271,z5,z6]),(0,[z7,z2,z3,z4,z817,z6])],[(0,[z7,z2,z3,z225,z5,z6]),(1,[z2,z3,z711,z5,z6]),(0,[z7,z2,z3,z4,z818,z6]),(0,[z7,z2,z3,z4,z5,z819]),(0,[z7,z2,z3,z10,z5,z109]),(0,[z7,z2,z820,z4,z5,z6]),(0,[z7,z2,z3,z45,z5,z504]),(0,[z452,z2,z3,z45,z5,z6]),(0,[z7,z2,z3,z543,z5,z504])],[(0,[z7,z2,z821,z4,z5,z6]),(0,[z7,z2,z822,z4,z5,z6]),(0,[z7,z2,z823,z4,z5,z6]),(0,[z7,z2,z3,z45,z193,z6]),(0,[z7,z18,z3,z45,z5,z6]),(0,[z7,z2,z3,z824,z5,z6])],[(0,[z7,z825,z2,z3,z5,z6]),(0,[z826,z2,z3,z45,z5,z6]),(0,[z96,z7,z3,z4,z97,z6]),(0,[z452,z2,z3,z459,z5,z6])]],
   [[(0,[z7,z2,z33,z62,z5,z6]),(0,[z7,z827,z2,z4,z5,z6]),(0,[z7,z2,z3,z828,z5,z6])],[(0,[z7,z2,z3,z829,z5,z6]),(0,[z7,z2,z3,z830,z5,z6]),(0,[z568,z7,z3,z45,z5,z6]),(0,[z831,z7,z2,z3,z4,z5]),(0,[z7,z2,z3,z4,z103,z139])],[(0,[z7,z2,z3,z832,z5,z6]),(0,[z210,z102,z395,z4,z5,z6]),(0,[z7,z3,z10,z5,z517,z6]),(0,[z23,z7,z2,z45,z5,z24]),(0,[z7,z197,z3,z4,z736,z6])],[(0,[z833,z2,z3,z45,z5,z6]),(0,[z17,z7,z2,z3,z278,z6])],[(0,[z7,z2,z3,z4,z90,z338]),(0,[z7,z2,z3,z834,z5,z6]),(0,[z313,z2,z41,z4,z5,z6]),(0,[z7,z2,z3,z835,z5,z6]),(0,[z23,z7,z2,z459,z5,z24])],[(0,[z52,z3,z53,z479,z5,z6]),(0,[z442,z2,z3,z4,z69,z6]),(0,[z7,z164,z2,z10,z5,z6]),(0,[z7,z2,z3,z158,z5,z6]),(0,[z836,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z837,z5,z6])],[(0,[z7,z3,z672,z45,z5,z6]),(0,[z838,z7,z2,z4,z5,z6]),(0,[z839,z2,z3,z4,z5,z6]),(0,[z136,z7,z2,z45,z5,z6]),(0,[z840,z2,z3,z4,z5,z6]),(0,[z7,z2,z4,z5,z72,z354])],[(0,[z7,z2,z470,z60,z5,z6]),(0,[z7,z2,z3,z841,z5,z6])]],
   [[(0,[z52,z3,z53,z4,z482,z6]),(0,[z7,z2,z3,z842,z5,z6])],[(0,[z52,z3,z53,z306,z5,z6]),(0,[z2,z3,z4,z843,z69,z6]),(0,[z79,z7,z2,z3,z278,z6]),(0,[z7,z2,z60,z104,z5,z6])],[(0,[z7,z588,z3,z10,z5,z6]),(0,[z7,z122,z3,z10,z5,z6]),(0,[z7,z683,z3,z45,z5,z6]),(0,[z7,z2,z844,z4,z5,z6])],[(0,[z7,z13,z3,z10,z5,z27]),(0,[z452,z2,z3,z4,z5,z27]),(0,[z23,z7,z2,z4,z5,z590]),(0,[z7,z2,z3,z5,z6,z845])],[(0,[z7,z2,z3,z4,z482,z77]),(0,[z7,z2,z116,z4,z5,z72]),(0,[z182,z738,z2,z4,z5,z6]),(0,[z7,z2,z739,z10,z5,z6]),(0,[z7,z3,z10,z5,z28,z203]),(1,[z7,z3,z4,z736,z6]),(0,[z23,z7,z2,z4,z5,z595]),(0,[z7,z846,z2,z4,z5,z6])],[(0,[z2,z366,z33,z4,z5,z6]),(0,[z7,z2,z3,z306,z5,z77]),(0,[z7,z2,z847,z4,z5,z6]),(0,[z498,z7,z3,z4,z5,z28]),(0,[z92,z2,z3,z518,z5,z6]),(0,[z146,z2,z336,z4,z5,z6]),(0,[z7,z2,z336,z147,z5,z6]),(0,[z7,z2,z3,z363,z59,z6]),(0,[z7,z2,z3,z848,z5,z6])],[(0,[z7,z2,z3,z4,z5,z849]),(0,[z182,z2,z3,z4,z482,z6]),(0,[z7,z2,z3,z850,z5,z6]),(0,[z7,z149,z2,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z851]),(0,[z115,z2,z3,z4,z843,z6]),(0,[z23,z395,z2,z4,z5,z6]),(0,[z7,z151,z3,z4,z5,z6]),(0,[z7,z2,z852,z4,z5,z6]),(0,[z313,z2,z4,z5,z138,z6])],[(0,[z7,z3,z45,z5,z84,z6]),(0,[z7,z2,z3,z5,z6,z853]),(0,[z7,z88,z3,z737,z5,z6]),(0,[z7,z2,z4,z5,z72,z187]),(0,[z7,z2,z44,z4,z5,z72])]],
   [[(0,[z7,z2,z3,z4,z5,z854]),(0,[z7,z2,z855,z4,z5,z6]),(0,[z7,z2,z3,z856,z5,z6])],[(0,[z7,z2,z3,z857,z5,z6]),(0,[z226,z7,z3,z4,z97,z6]),(0,[z37,z2,z3,z10,z5,z38])],[(0,[z7,z2,z3,z858,z5,z6]),(0,[z7,z2,z3,z45,z5,z109]),(0,[z7,z2,z336,z4,z5,z55])],[(0,[z7,z2,z859,z4,z5,z6]),(0,[z7,z2,z33,z4,z319,z6]),(0,[z7,z860,z3,z4,z5,z6]),(0,[z7,z570,z3,z45,z5,z6]),(0,[z7,z417,z3,z10,z5,z6])],[(0,[z52,z3,z53,z4,z5,z338]),(0,[z7,z2,z3,z4,z861,z6]),(0,[z0,z2,z3,z711,z5,z6]),(0,[z7,z2,z3,z862,z5,z6]),(0,[z7,z2,z3,z863,z5,z6]),(0,[z136,z7,z2,z4,z5,z27]),(0,[z7,z2,z864,z4,z5,z6]),(0,[z7,z2,z3,z4,z732,z203]),(0,[z7,z2,z3,z4,z6,z732])],[(0,[z7,z2,z14,z4,z5,z6])],[(0,[z7,z2,z3,z865,z5,z6]),(0,[z115,z2,z3,z4,z70,z6]),(0,[z7,z2,z3,z4,z319,z28]),(0,[z7,z2,z4,z5,z6,z221]),(0,[z7,z866,z3,z4,z5,z6])],[(0,[z7,z867,z3,z4,z5,z6]),(0,[z226,z7,z3,z4,z11,z6]),(0,[z7,z2,z3,z868,z5,z6]),(0,[z126,z7,z2,z3,z5,z441]),(0,[z7,z2,z45,z5,z6,z869])]],
   [[(0,[z7,z3,z68,z5,z84,z6]),(0,[z7,z13,z3,z10,z5,z28]),(0,[z452,z2,z3,z4,z5,z28]),(0,[z7,z870,z3,z4,z5,z6])],[(0,[z7,z2,z3,z871,z5,z6]),(0,[z7,z2,z3,z872,z5,z6]),(0,[z7,z2,z3,z873,z5,z6]),(0,[z7,z2,z874,z4,z5,z6]),(0,[z738,z2,z33,z4,z5,z6]),(0,[z255,z2,z117,z4,z69,z6]),(0,[z226,z255,z3,z4,z69,z6]),(0,[z23,z7,z2,z4,z5,z619]),(0,[z7,z3,z537,z10,z5,z28]),(0,[z85,z7,z2,z3,z5,z807])],[(0,[z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z549,z4,z90,z6]),(0,[z409,z2,z3,z4,z69,z6]),(0,[z115,z2,z3,z4,z682,z6]),(0,[z37,z2,z3,z4,z5,z770]),(0,[z7,z375,z3,z4,z5,z27]),(0,[z7,z2,z741,z58,z5,z6])],[(0,[z143,z178,z2,z4,z5,z6]),(0,[z226,z7,z802,z4,z5,z6]),(0,[z452,z2,z165,z4,z5,z6]),(0,[z875,z2,z3,z4,z5,z6]),(0,[z7,z13,z167,z10,z5,z6]),(0,[z2,z3,z10,z5,z876,z6])],[(0,[z7,z2,z549,z45,z5,z6]),(0,[z7,z3,z877,z4,z5,z6]),(0,[z599,z2,z33,z4,z5,z6]),(0,[z7,z2,z3,z878,z5,z6]),(0,[z7,z2,z3,z879,z5,z6]),(0,[z7,z197,z3,z158,z11,z6]),(0,[z7,z2,z4,z5,z6,z880]),(0,[z7,z2,z3,z4,z5,z881]),(0,[z320,z7,z2,z3,z5,z6])],[(0,[z7,z2,z3,z4,z843,z6]),(0,[z7,z2,z3,z882,z5,z6]),(0,[z7,z2,z3,z4,z5,z883]),(0,[z483,z210,z102,z4,z5,z6]),(0,[z7,z3,z737,z10,z5,z6]),(0,[z7,z2,z3,z5,z807,z15])],[(0,[z395,z2,z41,z4,z5,z6]),(0,[z7,z2,z3,z884,z5,z6]),(0,[z12,z885,z2,z4,z5,z6])],[(0,[z7,z2,z3,z886,z5,z6]),(0,[z7,z2,z887,z4,z5,z6]),(0,[z701,z7,z2,z60,z5,z6]),(0,[z7,z2,z4,z5,z6,z202])]],
   [[(0,[z7,z2,z3,z888,z5,z6])],[(0,[z7,z189,z165,z45,z5,z6]),(0,[z7,z44,z3,z10,z5,z28]),(0,[z7,z211,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z889,z6]),(0,[z23,z7,z375,z4,z5,z24])],[(0,[z7,z2,z3,z890,z5,z6]),(0,[z7,z3,z353,z10,z5,z6]),(0,[z891,z7,z2,z3,z5,z6]),(0,[z7,z2,z3,z892,z5,z6]),(0,[z7,z2,z14,z104,z5,z6])],[(0,[z7,z2,z209,z4,z5,z6]),(0,[z210,z7,z102,z4,z5,z6]),(0,[z7,z2,z3,z5,z6,z208])],[(0,[z7,z2,z3,z4,z893,z6]),(1,[z7,z3,z737,z5,z6]),(0,[z790,z2,z3,z10,z5,z6]),(0,[z347,z7,z2,z3,z5,z15]),(0,[z7,z2,z3,z894,z5,z6])],[(0,[z2,z3,z53,z4,z482,z6]),(0,[z7,z12,z2,z10,z5,z6]),(0,[z7,z749,z2,z45,z5,z6])],[(0,[z382,z2,z33,z4,z5,z6]),(0,[z7,z383,z33,z4,z5,z6]),(0,[z37,z2,z3,z45,z5,z38]),(0,[z146,z2,z3,z10,z5,z6])],[(0,[z7,z2,z3,z895,z5,z6]),(0,[z155,z7,z3,z45,z5,z6]),(0,[z177,z7,z2,z80,z5,z6]),(0,[z7,z2,z41,z45,z39,z6]),(0,[z7,z375,z3,z4,z5,z28]),(0,[z7,z2,z3,z104,z5,z6])]],
   [[(0,[z7,z2,z896,z4,z5,z6]),(0,[z7,z175,z3,z10,z5,z6]),(0,[z395,z2,z4,z5,z138,z6]),(0,[z7,z2,z46,z10,z5,z6]),(0,[z23,z7,z2,z4,z5,z659])],[(0,[z7,z13,z3,z271,z5,z27]),(0,[z7,z2,z3,z897,z5,z6])],[(0,[z7,z2,z3,z4,z5,z898]),(0,[z32,z2,z33,z4,z5,z6]),(0,[z7,z2,z691,z58,z5,z6]),(0,[z7,z2,z3,z899,z5,z6]),(0,[z7,z2,z4,z5,z6,z717])],[(0,[z7,z2,z3,z4,z5,z900]),(0,[z901,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z10,z5,z55])],[(0,[z7,z2,z3,z306,z5,z6]),(0,[z483,z2,z33,z4,z5,z6]),(0,[z7,z2,z3,z4,z319,z6])],[(0,[z7,z2,z3,z902,z5,z6]),(0,[z255,z2,z3,z4,z69,z6]),(0,[z7,z2,z3,z4,z5,z903]),(0,[z592,z7,z3,z45,z5,z6]),(0,[z904,z2,z3,z4,z5,z6]),(0,[z7,z2,z4,z5,z72,z717]),(0,[z79,z7,z151,z3,z5,z6])],[(0,[z7,z2,z549,z4,z5,z77]),(0,[z3,z877,z53,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z905]),(0,[z347,z7,z3,z4,z5,z28]),(0,[z7,z2,z4,z5,z717,z24])],[(0,[z7,z2,z3,z10,z5,z77]),(0,[z7,z2,z3,z236,z5,z6]),(0,[z7,z2,z14,z60,z5,z6])]],
   [[(0,[z7,z2,z3,z45,z90,z6]),(0,[z7,z2,z165,z4,z5,z109]),(0,[z7,z2,z906,z4,z5,z6])],[(0,[z182,z489,z2,z4,z5,z6]),(1,[z2,z3,z4,z843,z6]),(0,[z7,z2,z820,z10,z5,z6]),(0,[z7,z197,z3,z4,z11,z6]),(0,[z373,z7,z3,z4,z5,z28])],[(0,[z7,z2,z907,z4,z5,z6]),(0,[z7,z2,z45,z5,z6,z202]),(0,[z7,z3,z4,z11,z736,z6]),(0,[z7,z2,z3,z908,z5,z6])],[(0,[z96,z7,z3,z10,z97,z6]),(0,[z7,z596,z3,z10,z5,z6]),(0,[z909,z2,z3,z4,z5,z6]),(0,[z7,z2,z910,z4,z5,z6])],[(0,[z346,z2,z3,z4,z482,z6]),(0,[z7,z2,z3,z911,z5,z6]),(0,[z7,z2,z3,z4,z912,z6]),(0,[z676,z2,z3,z4,z5,z38]),(0,[z7,z913,z3,z4,z5,z6]),(0,[z7,z2,z914,z4,z5,z6]),(0,[z7,z2,z3,z915,z5,z6]),(0,[z7,z415,z3,z10,z5,z6])],[(0,[z7,z2,z3,z4,z5,z916]),(0,[z1,z2,z3,z250,z5,z6]),(0,[z7,z2,z336,z4,z5,z6]),(0,[z7,z2,z3,z10,z103,z139]),(0,[z7,z2,z3,z917,z5,z6]),(0,[z180,z7,z3,z4,z5,z918])],[(0,[z255,z2,z209,z4,z69,z6]),(0,[z7,z654,z3,z4,z11,z6]),(0,[z50,z2,z3,z45,z5,z71]),(0,[z7,z12,z13,z4,z5,z27]),(0,[z919,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z61,z5,z73])],[(0,[z7,z2,z3,z4,z5,z920]),(0,[z7,z921,z3,z4,z5,z6])]],
   [[(0,[z255,z2,z3,z4,z843,z6])],[(0,[z7,z922,z2,z4,z5,z6]),(0,[z923,z2,z3,z4,z5,z6]),(0,[z7,z2,z14,z58,z5,z6]),(0,[z9,z313,z2,z4,z138,z6]),(0,[z7,z2,z3,z104,z319,z6])],[(0,[z7,z2,z924,z4,z5,z6]),(0,[z22,z178,z2,z4,z5,z6]),(0,[z226,z7,z3,z862,z5,z6]),(0,[z7,z925,z2,z4,z5,z6]),(0,[z839,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z537,z5,z234]),(0,[z7,z926,z2,z4,z5,z6]),(0,[z7,z2,z3,z707,z232,z6]),(0,[z110,z136,z7,z2,z4,z203])],[(0,[z7,z2,z3,z4,z927,z6]),(0,[z700,z7,z3,z4,z5,z28]),(0,[z7,z928,z3,z4,z5,z6])],[(0,[z7,z2,z3,z929,z5,z6]),(0,[z7,z432,z3,z10,z5,z6]),(1,[z7,z750,z4,z5,z6]),(0,[z7,z2,z3,z161,z5,z109]),(0,[z930,z2,z3,z4,z5,z6]),(0,[z136,z7,z2,z4,z39,z6]),(0,[z7,z2,z3,z104,z193,z6])],[(0,[z7,z2,z3,z4,z5,z931]),(0,[z7,z3,z10,z5,z163,z6]),(0,[z7,z2,z46,z45,z5,z6]),(0,[z7,z2,z46,z543,z5,z6]),(0,[z7,z2,z3,z932,z5,z6])],[(0,[z7,z2,z366,z4,z5,z6]),(0,[z52,z3,z53,z4,z90,z6]),(0,[z7,z2,z933,z4,z5,z6]),(0,[z226,z121,z3,z4,z5,z6]),(0,[z702,z2,z3,z4,z70,z6]),(0,[z7,z2,z3,z171,z5,z109]),(0,[z934,z7,z2,z3,z5,z6])],[(0,[z7,z2,z935,z4,z5,z6]),(0,[z382,z2,z3,z4,z5,z6]),(0,[z7,z3,z439,z10,z5,z6]),(0,[z7,z2,z936,z4,z5,z6])]],
   [[(0,[z226,z7,z3,z4,z5,z6]),(0,[z52,z3,z53,z45,z5,z6]),(0,[z7,z2,z3,z543,z5,z55]),(0,[z7,z937,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z103,z214])],[(0,[z938,z2,z3,z4,z5,z6]),(0,[z939,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z90,z77]),(0,[z226,z182,z3,z4,z5,z6]),(0,[z7,z149,z2,z10,z5,z6]),(0,[z7,z2,z3,z4,z5,z940]),(0,[z7,z151,z3,z10,z5,z6]),(0,[z7,z2,z3,z941,z5,z6])],[(0,[z7,z750,z2,z4,z5,z6]),(0,[z7,z2,z44,z10,z5,z72]),(0,[z7,z111,z2,z60,z5,z6]),(0,[z7,z12,z2,z271,z5,z6]),(0,[z136,z939,z2,z4,z5,z6])],[(0,[z7,z2,z3,z45,z5,z77]),(0,[z7,z2,z78,z45,z5,z6]),(0,[z7,z102,z750,z4,z5,z6])],[(0,[z483,z2,z3,z4,z5,z6]),(0,[z313,z2,z3,z4,z5,z6]),(0,[z7,z2,z942,z4,z5,z6]),(0,[z7,z750,z165,z4,z5,z6]),(0,[z594,z7,z2,z3,z4,z203]),(0,[z136,z320,z7,z2,z5,z6])],[(0,[z226,z346,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z109,z28]),(0,[z7,z2,z3,z943,z5,z6])],[(0,[z239,z7,z3,z5,z84,z6])]],
   [[(0,[z346,z3,z4,z11,z69,z6]),(0,[z7,z2,z3,z944,z5,z6]),(0,[z7,z2,z3,z945,z5,z6]),(0,[z7,z3,z10,z5,z84,z6]),(0,[z7,z2,z3,z4,z5,z946]),(0,[z96,z7,z3,z45,z97,z6]),(0,[z96,z7,z3,z543,z97,z6])],[(0,[z346,z3,z4,z5,z695,z6]),(0,[z7,z2,z3,z947,z5,z6]),(0,[z7,z2,z3,z948,z5,z6]),(0,[z7,z949,z3,z4,z5,z6]),(0,[z7,z2,z3,z45,z5,z100]),(0,[z7,z2,z14,z10,z5,z6]),(0,[z950,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z951,z5,z6]),(0,[z7,z2,z3,z59,z455,z6]),(0,[z115,z2,z3,z10,z70,z6]),(1,[z7,z2,z741,z5,z6]),(0,[z7,z375,z3,z104,z5,z6])],[(0,[z952,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z6,z953]),(0,[z7,z2,z46,z4,z5,z504])],[(0,[z7,z2,z3,z479,z5,z77]),(0,[z7,z2,z3,z954,z5,z6]),(0,[z7,z2,z955,z4,z5,z6]),(0,[z7,z2,z3,z956,z5,z6]),(0,[z7,z957,z3,z4,z5,z6]),(0,[z7,z2,z3,z958,z5,z6]),(0,[z382,z2,z3,z104,z5,z6]),(0,[z7,z383,z3,z104,z5,z6])],[(0,[z7,z2,z3,z4,z959,z6]),(0,[z7,z2,z3,z960,z5,z6]),(0,[z7,z3,z882,z5,z84,z6]),(0,[z7,z3,z10,z5,z139,z28]),(0,[z961,z12,z2,z4,z5,z6]),(0,[z136,z7,z2,z4,z138,z6])],[(0,[z7,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z5,z962]),(0,[z584,z2,z33,z4,z5,z6]),(0,[z7,z624,z3,z10,z5,z6]),(0,[z7,z2,z3,z963,z5,z6]),(0,[z7,z2,z3,z332,z5,z6]),(0,[z7,z2,z964,z4,z5,z6])],[(0,[z182,z178,z2,z4,z5,z6]),(0,[z7,z965,z3,z4,z5,z6]),(0,[z2,z175,z3,z4,z69,z6]),(0,[z7,z2,z117,z45,z5,z6]),(0,[z201,z2,z3,z4,z5,z38]),(0,[z7,z2,z966,z4,z5,z6]),(0,[z85,z7,z2,z14,z5,z15])]],
   [[(0,[z7,z2,z366,z306,z5,z6]),(0,[z7,z2,z3,z967,z5,z6]),(0,[z121,z2,z3,z45,z5,z6]),(0,[z7,z2,z167,z45,z5,z6]),(0,[z121,z2,z3,z543,z5,z6]),(0,[z7,z968,z3,z4,z5,z6]),(0,[z7,z2,z3,z969,z5,z6])],[(0,[z7,z2,z3,z970,z5,z6]),(0,[z971,z2,z3,z4,z5,z6]),(0,[z972,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z973,z5,z6]),(0,[z7,z2,z3,z974,z5,z6])],[(0,[z7,z2,z3,z975,z5,z6]),(0,[z976,z7,z2,z3,z4,z5]),(0,[z7,z2,z41,z4,z613,z6]),(0,[z7,z13,z3,z236,z5,z6]),(0,[z7,z2,z3,z977,z5,z6]),(0,[z620,z7,z2,z3,z4,z203]),(0,[z7,z2,z3,z978,z5,z6])],[(0,[z979,z7,z3,z4,z5,z6]),(0,[z79,z7,z2,z3,z480,z6]),(0,[z2,z117,z4,z5,z69,z6]),(0,[z7,z980,z3,z4,z5,z6]),(0,[z7,z2,z3,z981,z5,z6]),(0,[z7,z575,z3,z10,z5,z6]),(0,[z7,z12,z2,z317,z5,z6])],[(0,[z2,z3,z711,z4,z5,z6]),(0,[z7,z2,z3,z267,z5,z6]),(0,[z7,z2,z3,z4,z656,z139]),(0,[z7,z2,z4,z39,z6,z533]),(0,[z23,z382,z2,z4,z5,z24]),(0,[z7,z2,z3,z4,z5,z807])],[(0,[z571,z2,z33,z4,z5,z6]),(0,[z7,z2,z3,z4,z982,z6]),(0,[z2,z3,z4,z5,z71,z770]),(0,[z7,z983,z2,z4,z5,z6])],[(0,[z50,z2,z3,z4,z5,z152]),(0,[z7,z189,z165,z545,z5,z6]),(0,[z984,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z985,z6]),(0,[z347,z7,z2,z3,z5,z374]),(0,[z7,z2,z3,z186,z419,z6]),(0,[z96,z7,z3,z4,z97,z504]),(0,[z23,z452,z2,z4,z5,z24])],[(0,[z7,z149,z2,z45,z5,z6]),(0,[z7,z2,z209,z10,z5,z6]),(0,[z210,z7,z102,z10,z5,z6]),(0,[z7,z151,z3,z45,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z986,z6]),(0,[z7,z2,z3,z4,z5,z987]),(0,[z416,z2,z3,z4,z69,z6]),(1,[z7,z2,z3,z707,z6])],[(0,[z7,z2,z3,z4,z988,z6]),(0,[z7,z989,z3,z4,z5,z6]),(0,[z7,z2,z3,z990,z5,z6]),(0,[z7,z2,z991,z3,z5,z6]),(0,[z992,z2,z3,z4,z5,z6])],[(0,[z7,z2,z51,z4,z5,z6]),(0,[z226,z7,z914,z4,z5,z6]),(0,[z7,z993,z2,z4,z5,z6]),(0,[z7,z2,z994,z4,z5,z6]),(0,[z995,z7,z2,z3,z5,z6])],[(0,[z7,z2,z366,z4,z5,z338]),(0,[z7,z491,z3,z10,z5,z6]),(0,[z7,z583,z3,z10,z5,z6]),(0,[z155,z7,z3,z737,z5,z6])],[(0,[z7,z2,z3,z4,z996,z6]),(0,[z7,z997,z3,z4,z5,z6]),(0,[z7,z3,z998,z4,z5,z6]),(0,[z7,z2,z3,z62,z5,z6])],[(0,[z7,z2,z999,z4,z5,z6]),(0,[z226,z7,z3,z4,z5,z1000]),(0,[z7,z164,z2,z45,z5,z6])],[(0,[z32,z2,z33,z10,z5,z6]),(0,[z7,z2,z4,z5,z6,z1001]),(0,[z121,z2,z3,z4,z5,z504]),(0,[z7,z2,z3,z1002,z5,z6]),(1,[z7,z2,z4,z803,z6]),(0,[z79,z7,z2,z3,z505,z6])],[(0,[z395,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z1003,z5,z6]),(0,[z115,z2,z3,z45,z70,z6]),(0,[z901,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z5,z6,z1004]),(0,[z7,z2,z1005,z4,z5,z6]),(0,[z7,z2,z3,z59,z6,z639])]],
   [[(0,[z2,z3,z33,z4,z482,z6]),(0,[z164,z2,z33,z4,z5,z6]),(0,[z2,z3,z132,z711,z5,z6]),(0,[z7,z2,z125,z298,z5,z6])],[(0,[z2,z3,z4,z5,z843,z6]),(0,[z7,z2,z3,z4,z5,z770]),(0,[z50,z164,z2,z4,z5,z71]),(0,[z7,z13,z3,z762,z5,z6]),(0,[z7,z212,z3,z4,z5,z27]),(0,[z7,z1006,z2,z4,z5,z6])],[(0,[z7,z2,z3,z4,z1007,z6]),(0,[z52,z3,z877,z4,z5,z6]),(0,[z7,z2,z786,z4,z5,z6]),(0,[z7,z2,z3,z1008,z5,z6]),(0,[z347,z7,z3,z10,z5,z28])],[(0,[z7,z2,z3,z1009,z5,z6]),(0,[z183,z7,z2,z3,z370,z6]),(0,[z7,z13,z3,z45,z5,z27]),(0,[z7,z2,z1010,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1011]),(0,[z7,z566,z3,z10,z5,z6]),(0,[z7,z2,z3,z157,z57,z6]),(0,[z7,z2,z4,z5,z6,z795]),(0,[z7,z3,z280,z45,z5,z6]),(0,[z136,z7,z2,z4,z5,z28])],[(0,[z52,z291,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z1012,z6]),(0,[z7,z2,z3,z68,z5,z6]),(0,[z7,z2,z3,z4,z1013,z6]),(0,[z7,z197,z3,z10,z11,z6])],[(0,[z7,z2,z3,z4,z1014,z6]),(0,[z85,z7,z151,z3,z5,z15]),(0,[z85,z7,z2,z3,z5,z15])],[(0,[z7,z2,z1015,z4,z5,z6]),(0,[z7,z3,z10,z5,z71,z28]),(0,[z1016,z2,z3,z4,z5,z6]),(0,[z9,z7,z2,z4,z138,z6])]],
   [[(0,[z7,z2,z265,z58,z5,z6]),(0,[z7,z2,z3,z4,z5,z1017]),(0,[z1018,z2,z3,z4,z5,z6])],[(0,[z483,z2,z366,z4,z5,z6]),(0,[z7,z522,z3,z10,z5,z6]),(0,[z7,z189,z165,z248,z5,z6]),(0,[z7,z102,z2,z4,z319,z6]),(0,[z7,z2,z336,z10,z5,z6]),(0,[z23,z7,z3,z10,z5,z28]),(0,[z2,z3,z4,z5,z6,z1019]),(0,[z7,z2,z4,z39,z319,z6])],[(0,[z7,z3,z10,z5,z6,z289])],[(0,[z7,z2,z3,z479,z5,z6]),(0,[z7,z2,z1020,z4,z5,z6]),(0,[z7,z2,z3,z5,z1021,z6]),(0,[z34,z7,z102,z4,z5,z6]),(0,[z7,z2,z1022,z4,z5,z6]),(0,[z7,z2,z3,z1023,z5,z6]),(0,[z7,z2,z3,z1024,z5,z6]),(0,[z452,z102,z2,z4,z5,z6])],[(0,[z7,z738,z2,z4,z5,z6]),(0,[z23,z7,z2,z4,z5,z188]),(0,[z7,z2,z209,z45,z5,z6]),(0,[z210,z7,z102,z45,z5,z6]),(0,[z7,z2,z3,z271,z5,z6]),(0,[z7,z2,z45,z5,z6,z221]),(0,[z9,z7,z2,z4,z803,z6])],[(0,[z180,z7,z3,z236,z5,z28])],[(0,[z7,z2,z3,z4,z482,z6]),(0,[z7,z2,z3,z1025,z5,z6]),(0,[z7,z2,z3,z4,z5,z1026]),(0,[z7,z2,z3,z1027,z5,z6]),(0,[z7,z2,z3,z1028,z5,z6]),(0,[z7,z2,z41,z4,z803,z6]),(0,[z85,z7,z2,z3,z5,z246])],[(0,[z633,z2,z33,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1029]),(0,[z7,z2,z1030,z4,z5,z6]),(0,[z7,z2,z3,z1031,z5,z6])]],
   [[(0,[z7,z2,z3,z1032,z5,z6]),(0,[z7,z3,z10,z5,z6,z310]),(0,[z7,z2,z469,z104,z5,z6]),(0,[z7,z2,z3,z1033,z5,z6]),(0,[z7,z2,z3,z1034,z5,z6])],[(0,[z7,z3,z4,z11,z311,z6]),(0,[z452,z2,z3,z4,z5,z6]),(0,[z182,z164,z2,z4,z5,z6]),(0,[z34,z7,z3,z10,z5,z6]),(0,[z50,z2,z3,z4,z5,z770]),(0,[z7,z13,z3,z10,z5,z6]),(0,[z320,z7,z2,z5,z6,z202])],[(0,[z7,z2,z366,z10,z5,z6]),(0,[z7,z2,z3,z4,z1035,z6]),(0,[z346,z224,z3,z45,z5,z6]),(0,[z447,z2,z3,z4,z5,z6]),(0,[z249,z2,z3,z4,z5,z71]),(0,[z23,z7,z2,z4,z5,z206]),(0,[z885,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z193,z6])],[(0,[z7,z2,z3,z1036,z5,z6]),(0,[z7,z2,z3,z161,z5,z100]),(0,[z826,z2,z3,z4,z5,z6]),(0,[z382,z2,z3,z10,z5,z6]),(0,[z7,z383,z3,z963,z5,z6]),(0,[z7,z2,z4,z5,z6,z1037])],[(0,[z226,z7,z3,z10,z5,z6]),(0,[z7,z2,z1038,z4,z5,z6]),(0,[z7,z2,z3,z1039,z5,z6])],[(0,[z738,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z770]),(0,[z7,z2,z3,z171,z5,z100]),(0,[z7,z2,z1040,z4,z5,z6]),(0,[z1041,z2,z3,z4,z5,z6])],[(0,[z535,z2,z33,z4,z5,z6]),(0,[z7,z2,z1042,z4,z5,z6]),(0,[z7,z2,z572,z4,z5,z72]),(0,[z961,z2,z3,z4,z5,z6]),(0,[z23,z7,z2,z4,z5,z24])],[(0,[z833,z2,z3,z4,z5,z6]),(0,[z7,z3,z10,z5,z6,z134]),(0,[z7,z151,z3,z61,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z1043]),(0,[z7,z2,z3,z4,z1044,z6]),(0,[z255,z2,z3,z68,z69,z6]),(0,[z210,z7,z12,z4,z5,z6]),(0,[z1045,z7,z2,z3,z10,z6]),(0,[z7,z383,z3,z981,z5,z6]),(0,[z85,z7,z211,z3,z5,z15])],[(0,[z483,z2,z3,z10,z5,z6]),(0,[z313,z2,z3,z10,z5,z6]),(0,[z7,z211,z3,z45,z5,z6])],[(0,[z7,z2,z3,z4,z5,z338]),(0,[z7,z2,z3,z4,z5,z1000]),(0,[z136,z7,z2,z4,z5,z6])],[],[(0,[z7,z3,z271,z10,z5,z6]),(0,[z7,z2,z3,z317,z5,z6])],[(0,[z7,z2,z3,z5,z1046,z6]),(0,[z1047,z2,z3,z4,z5,z6]),(0,[z7,z12,z2,z45,z5,z6]),(0,[z7,z2,z60,z741,z5,z6])],[(0,[z7,z2,z1048,z4,z5,z6]),(0,[z7,z2,z3,z1049,z5,z6]),(0,[z7,z2,z3,z1050,z5,z6]),(0,[z1051,z2,z3,z4,z5,z6]),(0,[z7,z625,z3,z10,z5,z6]),(0,[z146,z2,z3,z45,z5,z6]),(0,[z146,z2,z3,z543,z5,z6]),(0,[z7,z2,z336,z543,z5,z6]),(0,[z7,z13,z3,z4,z5,z918]),(0,[z452,z2,z3,z104,z5,z6])],[(0,[z2,z3,z877,z4,z5,z6]),(0,[z7,z2,z1052,z4,z5,z6]),(0,[z7,z2,z3,z10,z6,z953]),(0,[z7,z2,z3,z5,z6,z1053]),(0,[z7,z2,z3,z5,z6,z1054])]],
   [[(0,[z7,z2,z3,z306,z482,z6]),(1,[z738,z2,z4,z5,z6]),(0,[z7,z2,z1055,z4,z5,z6]),(0,[z7,z375,z3,z4,z5,z6])],[(0,[z307,z2,z33,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1056]),(0,[z7,z624,z165,z4,z5,z6]),(0,[z7,z2,z3,z762,z5,z6]),(0,[z7,z2,z3,z61,z5,z176]),(0,[z7,z13,z167,z4,z5,z27])],[(0,[z96,z7,z3,z4,z482,z6]),(0,[z563,z2,z33,z4,z5,z6]),(0,[z404,z2,z3,z4,z69,z6]),(0,[z7,z383,z3,z4,z5,z6]),(0,[z7,z2,z469,z216,z5,z6]),(0,[z23,z7,z383,z4,z5,z24])],[(0,[z7,z1057,z3,z4,z5,z6]),(0,[z182,z178,z2,z10,z5,z6]),(0,[z210,z7,z102,z4,z5,z100]),(0,[z7,z88,z3,z10,z5,z6]),(0,[z7,z3,z10,z5,z6,z369]),(0,[z7,z2,z3,z45,z5,z55]),(0,[z7,z2,z1058,z4,z5,z6]),(0,[z452,z2,z3,z4,z319,z6]),(0,[z23,z7,z2,z104,z5,z24]),(0,[z136,z7,z2,z5,z6,z208])],[(0,[z7,z2,z3,z1059,z5,z6]),(0,[z7,z2,z3,z4,z5,z1060]),(0,[z7,z2,z1061,z4,z5,z6]),(0,[z7,z2,z1062,z4,z5,z6]),(0,[z7,z637,z3,z10,z5,z6]),(0,[z7,z2,z3,z1063,z5,z6])],[(0,[z7,z2,z1064,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1065]),(0,[z7,z2,z3,z4,z5,z109]),(0,[z7,z1066,z3,z4,z5,z6])],[(0,[z1045,z7,z2,z3,z4,z6]),(0,[z7,z2,z3,z1067,z5,z6])]],
   [[(0,[z2,z33,z4,z5,z634,z6]),(0,[z226,z7,z3,z1008,z5,z6]),(0,[z7,z2,z3,z1068,z5,z6]),(0,[z23,z7,z2,z4,z319,z24])],[(0,[z7,z2,z3,z1069,z5,z6])],[(0,[z7,z1070,z3,z4,z5,z6]),(0,[z210,z7,z750,z4,z5,z6]),(0,[z7,z2,z3,z10,z985,z6]),(0,[z7,z1071,z3,z4,z5,z6])],[(0,[z226,z7,z3,z68,z5,z6]),(0,[z7,z318,z165,z4,z5,z6]),(0,[z7,z12,z2,z4,z5,z27]),(0,[z7,z1072,z2,z4,z5,z6])],[(0,[z7,z2,z3,z306,z5,z338]),(0,[z115,z2,z3,z4,z316,z6]),(0,[z7,z361,z3,z10,z5,z6]),(0,[z1073,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z876,z6]),(0,[z146,z2,z3,z4,z5,z504]),(0,[z7,z2,z3,z147,z5,z504]),(0,[z136,z7,z2,z4,z319,z6]),(0,[z1074,z7,z2,z4,z5,z6]),(0,[z7,z2,z3,z5,z6,z807]),(0,[z7,z2,z3,z5,z6,z1075])],[(0,[z7,z2,z1076,z4,z5,z6]),(0,[z778,z7,z2,z3,z5,z6]),(0,[z7,z2,z3,z45,z103,z139]),(0,[z7,z3,z236,z5,z6,z28]),(0,[z7,z2,z3,z4,z1077,z6]),(0,[z7,z2,z3,z1078,z5,z6])],[(0,[z2,z3,z711,z250,z5,z6]),(0,[z7,z2,z1079,z4,z5,z6]),(0,[z7,z2,z51,z10,z5,z6]),(0,[z7,z3,z45,z10,z5,z6]),(0,[z7,z3,z127,z10,z5,z6]),(0,[z7,z2,z46,z4,z5,z55])],[(0,[z7,z2,z366,z479,z5,z6]),(0,[z210,z7,z102,z4,z5,z109]),(0,[z7,z2,z3,z5,z73,z807])]],
   [[(0,[z7,z2,z549,z4,z5,z6]),(0,[z7,z661,z165,z4,z5,z6]),(0,[z7,z2,z3,z127,z5,z176])],[(0,[z1080,z7,z2,z3,z10,z6]),(0,[z7,z2,z3,z4,z5,z1081]),(0,[z7,z2,z3,z5,z6,z1082])],[(0,[z7,z2,z366,z4,z482,z6]),(0,[z7,z2,z3,z1083,z5,z6]),(0,[z191,z7,z102,z4,z5,z6]),(0,[z7,z3,z4,z736,z97,z6]),(0,[z2,z3,z4,z5,z6,z1084]),(0,[z1085,z2,z3,z4,z5,z6]),(0,[z7,z375,z3,z4,z319,z6]),(0,[z7,z2,z44,z4,z5,z717])],[(0,[z7,z2,z3,z1086,z5,z6]),(0,[z7,z2,z3,z1087,z5,z6]),(0,[z7,z2,z3,z1088,z5,z6]),(0,[z395,z2,z3,z10,z5,z6])],[(0,[z7,z2,z3,z294,z5,z6]),(0,[z226,z7,z3,z4,z482,z6]),(0,[z52,z121,z3,z4,z5,z6]),(0,[z7,z2,z1089,z4,z5,z6]),(0,[z226,z239,z7,z3,z5,z6]),(0,[z382,z2,z3,z4,z319,z6]),(0,[z7,z383,z3,z4,z319,z6])],[(0,[z52,z3,z53,z4,z5,z77]),(0,[z1090,z7,z3,z4,z5,z6]),(0,[z7,z189,z165,z4,z5,z6]),(0,[z121,z2,z3,z4,z97,z6]),(0,[z1091,z7,z2,z4,z5,z6]),(0,[z7,z375,z3,z4,z193,z6])],[(0,[z210,z7,z102,z161,z5,z6]),(0,[z96,z7,z46,z4,z97,z6]),(0,[z7,z2,z3,z1092,z5,z6]),(0,[z452,z383,z3,z4,z5,z6]),(0,[z7,z2,z3,z150,z707,z6])],[(0,[z7,z3,z10,z5,z38,z28]),(0,[z1093,z2,z3,z4,z5,z6]),(0,[z7,z3,z45,z348,z5,z6]),(0,[z7,z3,z4,z5,z918,z28]),(0,[z7,z2,z3,z4,z5,z1094]),(0,[z382,z2,z3,z4,z193,z6]),(0,[z7,z383,z3,z4,z193,z6])]],
   [[(0,[z7,z2,z3,z1095,z5,z6]),(0,[z7,z2,z3,z537,z5,z73]),(0,[z7,z12,z2,z4,z5,z28])],[(0,[z7,z2,z3,z4,z5,z1096]),(0,[z7,z2,z3,z1097,z5,z6]),(0,[z7,z2,z1098,z4,z5,z6]),(0,[z96,z7,z3,z4,z97,z55]),(0,[z7,z2,z3,z4,z5,z1099])],[(0,[z7,z2,z3,z4,z1100,z6]),(0,[z7,z1101,z2,z4,z5,z6]),(0,[z7,z2,z3,z1102,z5,z6]),(0,[z7,z720,z2,z4,z5,z6])],[(0,[z182,z2,z3,z4,z5,z77]),(0,[z7,z750,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1103]),(0,[z7,z2,z44,z45,z5,z72]),(0,[z121,z2,z3,z4,z11,z6]),(0,[z180,z7,z3,z4,z5,z28]),(0,[z7,z2,z3,z741,z5,z6]),(0,[z7,z2,z41,z4,z39,z6]),(0,[z7,z1104,z2,z4,z5,z6])],[(0,[z7,z1105,z2,z4,z5,z6]),(0,[z23,z7,z165,z4,z5,z28]),(0,[z7,z2,z3,z1106,z5,z6]),(0,[z1107,z2,z3,z4,z5,z6]),(0,[z7,z12,z375,z4,z5,z6]),(0,[z110,z320,z7,z2,z3,z203])],[(0,[z7,z2,z1108,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1109]),(0,[z1110,z7,z2,z3,z5,z6]),(0,[z7,z2,z3,z1111,z5,z6]),(0,[z7,z2,z3,z1112,z5,z6]),(0,[z7,z3,z4,z5,z27,z918]),(0,[z1113,z2,z3,z4,z5,z6]),(0,[z7,z2,z1114,z4,z5,z6])],[(0,[z7,z2,z3,z4,z1115,z6]),(0,[z727,z2,z3,z4,z5,z6]),(0,[z121,z2,z46,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z918]),(0,[z1116,z7,z2,z4,z5,z6])],[(0,[z7,z2,z1117,z4,z5,z6])]],
   [[(0,[z1080,z7,z2,z3,z4,z6]),(0,[z1118,z7,z3,z4,z5,z6]),(0,[z110,z7,z2,z3,z10,z203]),(0,[z79,z7,z2,z3,z653,z6])],[(0,[z226,z3,z53,z4,z5,z6]),(0,[z7,z2,z1119,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1120]),(0,[z1121,z2,z3,z4,z5,z6]),(0,[z7,z2,z14,z45,z5,z6]),(0,[z121,z2,z3,z4,z5,z55]),(0,[z110,z7,z2,z3,z208,z203])],[(0,[z7,z2,z3,z4,z1122,z6]),(0,[z7,z2,z3,z4,z5,z1123]),(0,[z7,z2,z549,z306,z5,z6]),(0,[z7,z2,z3,z10,z482,z6]),(0,[z7,z3,z4,z5,z1124,z6]),(0,[z7,z2,z3,z150,z419,z6]),(0,[z7,z2,z3,z1125,z5,z6])],[(0,[z7,z2,z51,z45,z5,z6]),(0,[z7,z2,z3,z10,z319,z6]),(0,[z7,z2,z3,z4,z5,z1126]),(0,[z7,z3,z4,z5,z736,z6])],[(0,[z7,z2,z3,z4,z90,z6]),(0,[z255,z2,z3,z10,z69,z6]),(0,[z7,z2,z3,z1127,z5,z6]),(0,[z1128,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z1129,z5,z6])],[(0,[z7,z1130,z3,z4,z5,z6]),(0,[z2,z3,z4,z70,z843,z6]),(0,[z1131,z2,z3,z4,z5,z6]),(0,[z452,z2,z3,z10,z5,z6]),(0,[z7,z2,z10,z5,z6,z221]),(1,[z7,z3,z4,z5,z918]),(0,[z7,z2,z60,z5,z6,z642]),(0,[z7,z2,z4,z5,z803,z6]),(0,[z382,z375,z3,z4,z5,z6]),(0,[z7,z2,z3,z1132,z5,z6]),(0,[z2,z3,z4,z5,z1133,z6])],[(0,[z7,z2,z3,z45,z5,z6]),(0,[z7,z2,z1134,z4,z5,z6]),(0,[z7,z3,z4,z5,z1135,z6]),(0,[z447,z2,z3,z10,z5,z6]),(0,[z7,z2,z3,z10,z193,z6]),(0,[z7,z2,z3,z543,z5,z6]),(0,[z7,z1136,z2,z4,z5,z6]),(0,[z1137,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z1138,z5,z6]),(0,[z118,z2,z3,z132,z5,z6]),(0,[z226,z7,z3,z4,z5,z1056]),(0,[z7,z2,z3,z1139,z5,z6]),(0,[z50,z2,z51,z4,z5,z71]),(0,[z382,z383,z3,z4,z5,z6])]],
   [[(0,[z7,z3,z4,z5,z6,z1140]),(0,[z7,z2,z3,z1141,z5,z6]),(0,[z7,z2,z3,z459,z5,z6])],[(0,[z7,z2,z3,z1142,z5,z6]),(0,[z7,z13,z3,z4,z5,z109]),(0,[z7,z2,z4,z39,z803,z6])],[(0,[z50,z2,z3,z4,z5,z71]),(0,[z7,z2,z3,z1143,z5,z6]),(0,[z7,z2,z3,z1144,z5,z6]),(0,[z7,z2,z3,z4,z754,z6]),(0,[z23,z7,z2,z10,z5,z24]),(0,[z7,z2,z125,z58,z5,z6])],[(0,[z7,z1145,z3,z4,z5,z6]),(0,[z7,z2,z3,z1146,z5,z6])],[(0,[z7,z3,z4,z5,z6,z1147]),(0,[z7,z375,z3,z943,z5,z6]),(0,[z7,z2,z3,z5,z707,z6])],[(0,[z7,z2,z3,z4,z5,z1148]),(0,[z7,z1149,z3,z4,z5,z6]),(0,[z7,z2,z3,z1150,z10,z6]),(0,[z804,z7,z2,z4,z5,z6]),(0,[z1151,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z10,z5,z338]),(0,[z7,z2,z3,z4,z5,z1152]),(0,[z136,z7,z2,z10,z5,z6]),(0,[z7,z2,z10,z5,z6,z202]),(0,[z7,z2,z3,z4,z1153,z6]),(0,[z7,z2,z3,z4,z103,z732])],[(0,[z52,z549,z53,z4,z5,z6]),(0,[z7,z2,z3,z1154,z5,z6]),(0,[z1,z2,z3,z245,z5,z6]),(0,[z190,z7,z2,z80,z5,z6]),(0,[z7,z2,z3,z4,z803,z6]),(0,[z110,z7,z2,z3,z4,z203])]],
   [[(0,[z85,z7,z2,z5,z221,z15])],[(0,[z7,z2,z3,z1155,z5,z6])],[(0,[z7,z2,z44,z4,z5,z526])],[(0,[z7,z2,z1156,z4,z5,z6]),(0,[z7,z2,z3,z4,z1157,z6]),(0,[z7,z1158,z3,z4,z5,z6]),(0,[z1159,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z1160,z5,z6]),(0,[z7,z2,z741,z4,z5,z6])],[(0,[z52,z3,z53,z4,z5,z6]),(0,[z115,z2,z117,z4,z5,z6]),(0,[z1161,z7,z2,z3,z5,z6]),(0,[z7,z2,z3,z1162,z5,z6]),(0,[z7,z375,z3,z10,z5,z6]),(0,[z7,z2,z3,z4,z5,z504]),(0,[z177,z7,z2,z60,z5,z6]),(0,[z7,z1163,z3,z4,z5,z6]),(0,[z1164,z2,z3,z4,z5,z6])],[(0,[z52,z366,z53,z4,z5,z6]),(0,[z7,z2,z3,z1165,z5,z6]),(0,[z7,z3,z10,z5,z6,z28]),(0,[z2,z3,z10,z5,z6,z1019]),(0,[z7,z2,z3,z4,z707,z6])],[(0,[z7,z2,z3,z306,z90,z6]),(0,[z32,z2,z33,z45,z5,z6]),(0,[z7,z2,z3,z1166,z5,z6]),(0,[z7,z383,z3,z10,z5,z6]),(0,[z7,z2,z3,z157,z59,z6]),(0,[z7,z2,z3,z1167,z5,z6]),(0,[z629,z7,z3,z45,z5,z6]),(0,[z1168,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z5,z73,z602])],[(0,[z7,z2,z3,z1169,z5,z6])]],
   [[(0,[z7,z2,z78,z4,z5,z6]),(0,[z7,z2,z3,z45,z319,z6]),(0,[z1170,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z1171,z5,z6])],[(0,[z7,z3,z4,z5,z84,z6]),(0,[z255,z2,z3,z45,z69,z6])],[(0,[z7,z259,z165,z4,z5,z6]),(0,[z96,z121,z3,z4,z97,z6]),(0,[z7,z2,z3,z459,z319,z6])],[(0,[z7,z178,z383,z4,z5,z6]),(0,[z447,z2,z3,z45,z5,z6]),(0,[z7,z2,z3,z1172,z5,z6]),(0,[z110,z7,z2,z3,z4,z732])],[(0,[z7,z2,z3,z1150,z4,z6]),(0,[z7,z178,z2,z104,z5,z6]),(0,[z7,z2,z3,z1173,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1174]),(0,[z7,z2,z3,z1175,z5,z6]),(0,[z0,z2,z3,z518,z5,z6]),(0,[z7,z2,z3,z4,z5,z100]),(0,[z7,z197,z3,z45,z11,z6]),(0,[z7,z3,z45,z63,z5,z6]),(0,[z7,z2,z3,z459,z193,z6]),(0,[z7,z2,z3,z61,z5,z807])],[(0,[z7,z2,z3,z1176,z5,z6]),(0,[z7,z2,z3,z4,z5,z1177]),(0,[z110,z7,z2,z4,z202,z203])],[(0,[z7,z2,z3,z479,z482,z6]),(0,[z7,z102,z375,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z1178]),(0,[z7,z2,z1179,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z1180,z5,z6]),(0,[z7,z3,z4,z5,z6,z918]),(0,[z7,z2,z3,z763,z5,z6]),(0,[z7,z1181,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z1182,z6]),(0,[z7,z178,z2,z4,z319,z6]),(0,[z7,z1183,z2,z4,z5,z6]),(0,[z7,z2,z336,z45,z5,z6]),(0,[z7,z2,z4,z5,z6,z869])],[(0,[z177,z7,z2,z292,z5,z6]),(0,[z7,z2,z3,z1184,z5,z6]),(0,[z7,z2,z3,z4,z736,z6]),(0,[z1185,z2,z3,z4,z5,z6]),(0,[z313,z2,z4,z5,z72,z6]),(0,[z7,z2,z4,z5,z6,z1186])],[(0,[z7,z2,z3,z45,z5,z338]),(0,[z7,z2,z117,z4,z5,z6]),(0,[z7,z2,z3,z1187,z5,z6]),(0,[z7,z102,z2,z4,z5,z109]),(0,[z7,z2,z3,z1188,z5,z6])],[(0,[z7,z2,z549,z10,z5,z6]),(0,[z121,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z1189,z5,z6]),(0,[z7,z2,z167,z4,z5,z6]),(0,[z7,z300,z3,z10,z5,z6]),(0,[z183,z7,z2,z3,z232,z6]),(0,[z7,z1190,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z1191,z6]),(0,[z23,z313,z2,z4,z5,z6])],[(0,[z7,z1192,z2,z4,z5,z6]),(0,[z7,z2,z3,z4,z319,z27]),(0,[z7,z2,z3,z1193,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1194]),(0,[z7,z2,z3,z1195,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 525) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 525).take 525) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1050).take 187) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1237)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [525, 525, 187] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 106).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 106).take 107).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 213).take 43).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [106, 107, 43] = true :=
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

end PEqualNP.Outside.L_meta_37865

theorem PEqualNP.Outside.L_meta_37865 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4274846336) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4274846336) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37865.solve
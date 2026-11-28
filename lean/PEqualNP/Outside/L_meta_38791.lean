import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38791

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4272603136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x800002b0aa2155e2#64 ++ 0xa00000ac2a885578#64 ++ 0x6008e7f1fa23ffe3#64 ++ 0xd80239fc7e88fff8#64 : BitVec 256),
   (0x04334996642ccc6c#64 ++ 0xc10cd265990b331b#64 ++ 0xfc77599e643cccff#64 ++ 0xbf1dd667990f333f#64 : BitVec 256),
   (0x0985961b86c0f0b7#64 ++ 0x02616586e1b03c2d#64 ++ 0xef879e1f87c0f0ff#64 ++ 0x7be1e787e1f03c3f#64 : BitVec 256),
   (0x12d81fe0037700d8#64 ++ 0x04b607f800ddc036#64 ++ 0xf7f81fe007ff00fe#64 ++ 0xfdfe07f801ffc03f#64 : BitVec 256),
   (0x036fe000059aaa00#64 ++ 0x00dbf8000166aa80#64 ++ 0xffffe00007ffff01#64 ++ 0xfffff80001ffffc0#64 : BitVec 256),
   (0x03fefd4d50000000#64 ++ 0x00ffbf5354000000#64 ++ 0xdbfffffff8000003#64 ++ 0xf6fffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [6, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 7]⟩, ⟨.and, [11, 3]⟩, ⟨.and, [13, 10]⟩, ⟨.or, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00901d4d50000000 0x0024075354000000 0x00001ffff8000002 0x000007fffe000000

def z1 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xffffe00007ffff01 0xfffff80001ffffc0

def z2 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc77599e643cccff 0xbf1dd667990f333f

def z3 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef879e1f87c0f0ff 0x7be1e787e1f03c3f

def z4 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f81fe007ff00fe 0xfdfe07f801ffc03f

def z5 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x6008e7f1fa23ffe3 0xd80239fc7e88fff8

def z6 : W := mkw 0x83fefffdfa2155e2 0xa0ffbfff7e885578 0xfbfffffffa23ffe3 0xfefffffffe88fff8

def z7 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0x9ff7000005dc0000 0x27fdc00001770000

def z8 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0xdbfffffff8000003 0xf6fffffffe000000

def z9 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x000007f1f80000e2 0x000001fc7e000038

def z10 : W := mkw 0x00234000059aaa00 0x0008d0000166aa80 0xfc77400007ffff01 0xbf1dd00001ffffc0

def z11 : W := mkw 0x1bcc966983d33093 0x06f3259a60f4cc24 0x0388866183c33000 0x40e2219860f0cc00

def z12 : W := mkw 0x03ccb44911922200 0x00f32d1244648880 0x0388a6619bc33300 0x40e2299866f0ccc0

def z13 : W := mkw 0x0000000000000000 0x0000000000000000 0x6008e0000223ff01 0xd80238000088ffc0

def z14 : W := mkw 0x10901fe0026500d8 0x042407f800994036 0x00001fe0000000fe 0x000007f80000003f

def z15 : W := mkw 0x036fe0000480a000 0x00dbf80001202800 0xffffe00007c0f001 0xfffff80001f03c00

def z16 : W := mkw 0x01b6dd0d40000000 0x006db74350000000 0xdbf7df9fe0000003 0xf6fdf7e7f8000000

def z17 : W := mkw 0x04334986442c884c 0x410cd261910b2213 0xfc77198e043c00fe 0xbf1dc663810f003f

def z18 : W := mkw 0x80000010a8005522 0xa00000042a001548 0x0000e011f800ff01 0x000038047e003fc0

def z19 : W := mkw 0x13feffed526500d8 0x04ffbffb54994036 0xdbfffffff80000ff 0xf6fffffffe00003f

def z20 : W := mkw 0x03fffd4d559aaa00 0x00ffff535566aa80 0xdffffffffddc0003 0xf7ffffffff770000

def z21 : W := mkw 0x100002a0037700d8 0x040000a800ddc036 0x2400000007ff00fc 0x0900000001ffc03f

def z22 : W := mkw 0x13feffed537700d8 0x04ffbffb54ddc036 0xffffffffffff00ff 0xffffffffffffc03f

def z23 : W := mkw 0x0000009020204460 0x8000002408081118 0x600041906020cce3 0x9800106418083338

def z24 : W := mkw 0x077fe906459eaa0c 0x41dffa419167aa83 0xfffff80e07ffff1d 0xfffffe0381ffffc7

def z25 : W := mkw 0x04334906440c880c 0x410cd24191032203 0x9c77180e041c001c 0x271dc60381070007

def z26 : W := mkw 0x800002208a011182 0x2000008822804460 0x0008a6619a033300 0x400229986680ccc0

def z27 : W := mkw 0x03feff4d52400090 0x00ffbfd354900024 0xffffffffffc000ff 0xfffffffffff0003f

def z28 : W := mkw 0x018594090480a000 0x0061650241202800 0xef879e1f87c0f003 0x7be1e787e1f03c00

def z29 : W := mkw 0x026a6000011a0a00 0x009a980000468280 0x10786000003f0f00 0x841e1800000fc3c0

def z30 : W := mkw 0x0880161b824050b7 0x02200586e090142d 0x00001e1f800000fe 0x00000787e000003f

def z31 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0x9bf71ffff8000002 0x26fdc7fffe000000

def z32 : W := mkw 0x03ccb44910000000 0x00f32d1244000000 0xcb8fbe7f98000003 0x72e3ef9fe6000000

def z33 : W := mkw 0x80000090a8205562 0xa00000242a081558 0x6000e191f820ffe3 0x980038647e083ff8

def z34 : W := mkw 0x8985963b8ec1f1b7 0x2261658ee3b07c6d 0xef8fbe7f9fc3f3ff 0x7be3ef9fe7f0fcff

def z35 : W := mkw 0x041009966024446c 0xc10402659809111b 0x0000199e600000fe 0x000006679800003f

def z36 : W := mkw 0x84334bb6ee2dddee 0xe10cd2edbb8b777b 0xfc7ffffffe3fffff 0xff1fffffff8fffff

def z37 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xffffe7f1ffffff03 0xfffff9fc7fffffc0

def z38 : W := mkw 0x042340166408cc24 0xc108d00599023309 0x0807401e6000cc01 0x0201d00798003300

def z39 : W := mkw 0x0905801b8480f027 0x02416006e1203c09 0x0807801f8000f001 0x0201e007e0003c00

def z40 : W := mkw 0x836fe010ad9aff22 0xa0dbf8042b66bfc8 0xffffe011ffffff01 0xfffff8047fffffc0

def z41 : W := mkw 0x0000000000000000 0x0000000000000000 0x0008600000230f00 0x800218000008c3c0

def z42 : W := mkw 0x0184940900000000 0x0061250240000000 0xcb879e1f80000003 0x72e1e787e0000000

def z43 : W := mkw 0x0bffff5fd6c0f0b7 0x02ffffd7f5b03c2d 0xffffffffffc0f0ff 0xfffffffffff03c3f

def z44 : W := mkw 0x02d81d4000000000 0x00b6075000000000 0xd3f81fe000000002 0xf4fe07f800000000

def z45 : W := mkw 0x0000020082001082 0x0000008020800420 0x0000860182003000 0x4000218060800c00

def z46 : W := mkw 0x000102128600d0a6 0x00004084a1803429 0xec079e1f8600f0ff 0x7b01e787e1803c3f

def z47 : W := mkw 0x0927e01b8488fa27 0x0249f806e1223e89 0x0807e01f8000ff01 0x0201f807e0003fc0

def z48 : W := mkw 0x0beff61b87dafab7 0x02fbfd86e1f6bead 0xfffffe1f87ffffff 0xffffff87e1ffffff

def z49 : W := mkw 0x00334980042c8848 0x000cd260010b2212 0xfc775980043cccff 0xbf1dd660010f333f

def z50 : W := mkw 0x00901d4d50000000 0x0024075354000000 0x4008fffff8000003 0xd0023ffffe000000

def z51 : W := mkw 0x0000020002400090 0x0000008000900024 0x2400000007c000fc 0x0900000001f0003f

def z52 : W := mkw 0x080100128480f027 0x02004004a1203c09 0x000000000000f000 0x0000000000003c00

def z53 : W := mkw 0x00b25d4d50000000 0x002c975354000000 0xd8775ffff8000003 0xb61dd7fffe000000

def z54 : W := mkw 0x167b49f6653fcc6c 0xc59ed27d994ff31b 0xfc7f59fe643fccff 0xbf1fd67f990ff33f

def z55 : W := mkw 0x0023400004088800 0x0008d00001022200 0xfc774000043ccc01 0xbf1dd000010f3300

def z56 : W := mkw 0x077fe99665beee6c 0xc1dffa65996fbb9b 0xfffff99e67ffffff 0xfffffe6799ffffff

def z57 : W := mkw 0x13ffffe007ffaad8 0x04fffff801ffeab6 0xffffffe007ffffff 0xfffffff801ffffff

def z58 : W := mkw 0x92d81ff0ab7755fa 0xa4b607fc2addd57e 0xf7f8fff1ffffffff 0xfdfe3ffc7fffffff

def z59 : W := mkw 0x027a694450000000 0x009e9a5114000000 0x107861e078000000 0x841e18781e000000

def z60 : W := mkw 0x0801021286c0f0b7 0x02004084a1b03c2d 0x2400000007c0f0fc 0x0900000001f03c3f

def z61 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0x9bf7180e00000000 0x26fdc60380000000

def z62 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x200000000223ffe0 0x080000000088fff8

def z63 : W := mkw 0x000100120400c024 0x0000400481003009 0xec07181e0400c0ff 0x3b01c6078100303f

def z64 : W := mkw 0x0080160002400090 0x0020058000900024 0xe7801e0007c000fe 0x79e0078001f0003f

def z65 : W := mkw 0x0248000001120000 0x0092000000448000 0xf7f8000007ff0000 0xfdfe000001ffc000

def z66 : W := mkw 0x077fe99665beee6c 0xc1dffa65996fbb9b 0xfff7599e65fcccff 0xbffdd667997f333f

def z67 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000419060000003 0x9000106418000000

def z68 : W := mkw 0x125809e001370048 0x04960278004dc012 0xf47819e0043f00fe 0xbd1e0678010fc03f

def z69 : W := mkw 0x0136e90d50000000 0x004dba4354000000 0xd877f99ff8000003 0xb61dfe67fe000000

def z70 : W := mkw 0x0801021287dafab7 0x02004084a1f6bead 0x2400000007fffffc 0x0900000001ffffff

def z71 : W := mkw 0x0080160002400090 0x0020058000900024 0x00001e00000000fe 0x000007800000003f

def z72 : W := mkw 0x836fe2b0afbbffe2 0xa0dbf8ac2beefff8 0xffffe7f1ffffffe3 0xfffff9fc7ffffff8

def z73 : W := mkw 0x12580be0037700d8 0x049602f800ddc036 0x347801e007ff00fc 0x8d1e007801ffc03f

def z74 : W := mkw 0x898596bbaee1f5f7 0xa26165aeebb87d7d 0xef8fffffffe3ffff 0xfbe3fffffff8ffff

def z75 : W := mkw 0x12580be0033700c8 0x049602f800cdc032 0x707807e0023f00e2 0xdc1e01f8008fc038

def z76 : W := mkw 0x0126e00d50000000 0x0049b80354000000 0x480fe7fff8000003 0xd203f9fffe000000

def z77 : W := mkw 0x04b35ddf742ccc6c 0xc12cd777dd0b331b 0xfc775ffffc3cccff 0xbf1dd7ffff0f333f

def z78 : W := mkw 0x03dcbd4d50000000 0x00f72f5354000000 0x0388bffff8000002 0x40e22ffffe000000

def z79 : W := mkw 0x12c8166003530090 0x04b2059800d4c024 0x0388066003c30000 0x40e2019800f0c000

def z80 : W := mkw 0x03fffd4d559aaa00 0x00ffff535566aa80 0xffffffffffffff03 0xffffffffffffffc0

def z81 : W := mkw 0x03fffd4d559aaa00 0x00ffff535566aa80 0x9ff7180e05dc0000 0x27fdc60381770000

def z82 : W := mkw 0x124802a0037700d8 0x049200a800ddc036 0xf7f8000007ff00fc 0xfdfe000001ffc03f

def z83 : W := mkw 0x824802b0ab3355e2 0xa09200ac2accd578 0xf7f8e7f1ffffffe3 0xfdfe39fc7ffffff8

def z84 : W := mkw 0x12d81d4001560018 0x04b6075000558006 0x97f0180005dc001c 0x25fc060001770007

def z85 : W := mkw 0x0985940b04c0a015 0x02616502c1302805 0x8f87180e05c0001c 0x23e1c60381700007

def z86 : W := mkw 0x034da0000592a200 0x00d368000164a880 0xef8fa00007c3f301 0x7be3e80001f0fcc0

def z87 : W := mkw 0x92c816608b531192 0x24b2059822d4c464 0x0388a6619bc33300 0x40e2299866f0ccc0

def z88 : W := mkw 0x16fb5dd6657ecc7c 0xc5bed775995fb31f 0xfff7599e65fcccff 0xbffdd667997f333f

def z89 : W := mkw 0x1bfffffb87fffaff 0x06fffffee1fffebf 0xffffffff87ffffff 0xffffffffe1ffffff

def z90 : W := mkw 0x02490000059aaa00 0x009240000166aa80 0xf7f8000007ffff00 0xfdfe000001ffffc0

def z91 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0xdbff1fee00000002 0xf6ffc7fb80000000

def z92 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x200007f1fa23ffe2 0x080001fc7e88fff8

def z93 : W := mkw 0x167a49e4613f0c48 0xc59e9279184fc312 0x107841e0603f0c00 0x841e1078180fc300

def z94 : W := mkw 0x16fb5ff6677fccfc 0xc5bed7fd99dff33f 0xffff5ffe67ffccff 0xffffd7ff99fff33f

def z95 : W := mkw 0x000002a0022100c0 0x000000a800884030 0x600807e0022300e2 0xd80201f80088c038

def z96 : W := mkw 0x0184940900000000 0x0061250240000000 0x0380860180000000 0x40e0218060000000

def z97 : W := mkw 0x0000000000000000 0x0000000000000000 0x4008e7f1f8000003 0xd00239fc7e000000

def z98 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xaf87180e07c0f0fc 0x2be1c60381f03c3f

def z99 : W := mkw 0x026b4000051a8800 0x009ad0000146a200 0xffff400007ffcc01 0xffffd00001fff300

def z100 : W := mkw 0x04010092242ccc6c 0xc1004024890b331b 0x24000000043cccfc 0x09000000010f333f

def z101 : W := mkw 0x07fffddf742ccc6c 0xc1ffff77dd0b331b 0xfffffffffc3cccff 0xffffffffff0f333f

def z102 : W := mkw 0x108016a0037700d8 0x042005a800ddc036 0xe7801e0007ff00fe 0x79e0078001ffc03f

def z103 : W := mkw 0x898596bbaee1f5f7 0xa26165aeebb87d7d 0xef879e1f87e3ffff 0x7be1e787e1f8ffff

def z104 : W := mkw 0x92d81fe02b7705d8 0xa4b607f80addc176 0xf7f87fe07fff0ffe 0xfdfe1ff81fffc3ff

def z105 : W := mkw 0x0984961b824050b7 0x02612586e090142d 0xcb879e1f800000ff 0x72e1e787e000003f

def z106 : W := mkw 0x0000009020204460 0x8000002408081118 0x00000190600000e2 0x0000006418000038

def z107 : W := mkw 0x13ffffe007ffaad8 0x04fffff801ffeab6 0xffff1fe007ff00fe 0xffffc7f801ffc03f

def z108 : W := mkw 0x80000010a8005522 0xa00000042a001548 0x4008e7f1f800ff03 0xd00239fc7e003fc0

def z109 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0x0b8fe00003c3ff01 0x42e3f80000f0ffc0

def z110 : W := mkw 0x036fe2a007bbaac0 0x00dbf8a801eeeab0 0xffffe7e007ffffe3 0xfffff9f801fffff8

def z111 : W := mkw 0x04324984602c0c48 0xc10c9261180b0312 0x10704180603c0c00 0x841c1060180f0300

def z112 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0x97f01fe005dc00fe 0x25fc07f80177003f

def z113 : W := mkw 0x0527e0166488ee24 0xc149f80599223b89 0x0807e01e6000ff01 0x0201f80798003fc0

def z114 : W := mkw 0x03ccb44910000000 0x00f32d1244000000 0x0388a66198000000 0x40e2299866000000

def z115 : W := mkw 0x12d91ff20777c0fc 0x04b647fc81ddf03f 0xffff1ffe07ffc0ff 0xffffc7ff81fff03f

def z116 : W := mkw 0x10901fe0037700d8 0x042407f800ddc036 0x24001fe007ff00fe 0x090007f801ffc03f

def z117 : W := mkw 0x834ca2208b933382 0x20d3288822e4cce0 0x0388a6619bc33300 0x40e2299866f0ccc0

def z118 : W := mkw 0x92d81ff0ab7755fa 0xa4b607fc2addd57e 0xf7f81fe007fffffe 0xfdfe07f801ffffff

def z119 : W := mkw 0x1bdd9ffb87f7f0ff 0x06f767fee1fdfc3f 0xffff9fff87fff0ff 0xffffe7ffe1fffc3f

def z120 : W := mkw 0x0104800000000000 0x0041200000000000 0xcb87800000000001 0x72e1e00000000000

def z121 : W := mkw 0x010580000480a000 0x0041600001202800 0xef87800007c0f001 0x7be1e00001f03c00

def z122 : W := mkw 0x03eef40900000000 0x00fbbd0240000000 0xdbfffe1f80000003 0xf6ffff87e0000000

def z123 : W := mkw 0x02d81d4d50000000 0x00b6075354000000 0xd3f81ffff8000002 0xf4fe07fffe000000

def z124 : W := mkw 0x0126e00d50000000 0x0049b80354000000 0x0807e01ff8000001 0x0201f807fe000000

def z125 : W := mkw 0x0bccb60983d23293 0x02f32d8260f48ca4 0x0388a60183c33300 0x40e2298060f0ccc0

def z126 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef8fffffffc0f0ff 0xfbe3fffffff03c3f

def z127 : W := mkw 0x00000210820050a2 0x0000008420801428 0x600086118200f0e3 0x5800218460803c38

def z128 : W := mkw 0x800000a028210540 0xa00000280a084150 0x000861e078230f00 0x800218781e08c3c0

def z129 : W := mkw 0x0248000001120000 0x0092000000448000 0xf7f8e00007ffff01 0xfdfe380001ffffc0

def z130 : W := mkw 0x12c8166003530090 0x04b2059800d4c024 0xf7f8066007ff0000 0xfdfe019801ffc000

def z131 : W := mkw 0x8126e2bdfa2155e2 0xa049b8af7e885578 0x680fe7fffa23ffe3 0xda03f9fffe88fff8

def z132 : W := mkw 0x010580120480e024 0x0041600481203809 0xef87981e07c0f0ff 0x7be1e60781f03c3f

def z133 : W := mkw 0x800000a028210540 0xa00000280a084150 0x000001e078000000 0x000000781e000000

def z134 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0xfbfffffffa23ff03 0xfefffffffe88ffc0

def z135 : W := mkw 0x13fefd4d51560018 0x04ffbf5354558006 0xdffffffffddc001f 0xf7ffffffff770007

def z136 : W := mkw 0x0db7df1fc6ccf8bf 0x436df7c7f1b33e2f 0xfff79e1f87dcf0ff 0x7ffde787e1f73c3f

def z137 : W := mkw 0x0984961982c070b3 0x0261258660b01c2c 0x6380861183c0f0e3 0x58e0218460f03c38

def z138 : W := mkw 0x12d81ff0837750fa 0x04b607fc20ddd43e 0xf7f89ff187fff0ff 0xfdfe27fc61fffc3f

def z139 : W := mkw 0x026a600000000000 0x009a980000000000 0x1078600000000000 0x841e180000000000

def z140 : W := mkw 0x02fa7d4450000000 0x00be9f5114000000 0xd3f87fe078000002 0xf4fe1ff81e000000

def z141 : W := mkw 0x800102b0afbbffe2 0xa00040ac2beefff8 0x2400000007ffffe0 0x0900000001fffff8

def z142 : W := mkw 0x8000002008010100 0x2000000802004040 0x0008206018030300 0x000208180600c0c0

def z143 : W := mkw 0x0080140900000000 0x0020050240000000 0x00001e1f80000002 0x00000787e0000000

def z144 : W := mkw 0x0032490440000000 0x000c924110000000 0xd877599e60000003 0xb61dd66798000000

def z145 : W := mkw 0x0984960982c03093 0x0261258260b00c24 0x0380860183c03000 0x40e0218060f00c00

def z146 : W := mkw 0x067b6996653ece6c 0xc19eda65994fb39b 0xfc7f799e643fcfff 0xbf1fde67990ff3ff

def z147 : W := mkw 0x800102b2ae21d5e6 0xa00040acab887579 0xec0ffffffe23ffff 0xfb03ffffff88ffff

def z148 : W := mkw 0x04334986642c8c4c 0xc10cd261990b2313 0x9c77598e643c0c1c 0xa71dd663990f0307

def z149 : W := mkw 0x077fe996642ccc6c 0xc1dffa65990b331b 0xfffff99e643cccff 0xfffffe67990f333f

def z150 : W := mkw 0x0022400440000000 0x0008900110000000 0x0807401e60000001 0x0201d00798000000

def z151 : W := mkw 0x0184940900000000 0x0061250240000000 0xcb8ffffff8000003 0xf2e3fffffe000000

def z152 : W := mkw 0x140102b2277fccfc 0xc50040ac89dff33f 0x2400000007ffccfc 0x0900000001fff33f

def z153 : W := mkw 0x0423400644088804 0x4108d00191022201 0x0807000e00000000 0x0201c00380000000

def z154 : W := mkw 0x810582b0aea1f5e2 0xa04160ac2ba87d78 0xef8fe7f1ffe3ffe3 0xfbe3f9fc7ff8fff8

def z155 : W := mkw 0x0127e0000488aa00 0x0049f80001222a80 0x0807e0000000ff01 0x0201f80000003fc0

def z156 : W := mkw 0x03fffd5f5400c024 0x00ffff57d5003009 0xfffffffffc00c0ff 0xffffffffff00303f

def z157 : W := mkw 0x880102b2aee1f5f7 0xa20040acabb87d7d 0x2400000007e3fffc 0x0900000001f8ffff

def z158 : W := mkw 0x00010000059aaa00 0x000040000166aa80 0x2400000007ffff00 0x0900000001ffffc0

def z159 : W := mkw 0x036ee000011a0a00 0x00dbb80000468280 0xdbffe000003f0f01 0xf6fff800000fc3c0

def z160 : W := mkw 0x034ca00001922200 0x00d3280000648880 0x0388a00003c33300 0x40e2280000f0ccc0

def z161 : W := mkw 0x80000010a8005522 0xa00000042a001548 0x6008e011fa23ff01 0xd80238047e88ffc0

def z162 : W := mkw 0x0000000000000000 0x0000000000000000 0xc807181e00000003 0x3201c60780000000

def z163 : W := mkw 0x0000001000004020 0x0000000400001008 0x600000100000c0e3 0x1800000400003038

def z164 : W := mkw 0x04234096642ccc6c 0xc108d025990b331b 0x2c07401e643cccfd 0x0b01d007990f333f

def z165 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x4008e7f1f80000e3 0xd00239fc7e000038

def z166 : W := mkw 0x17fffff667ffeefc 0xc5fffffd99fffbbf 0xfffffffe67ffffff 0xffffffff99ffffff

def z167 : W := mkw 0x800000b028214560 0xa000002c0a085158 0x600861f07823cfe3 0x9802187c1e08f3f8

def z168 : W := mkw 0x0080140000400010 0x0020050000100004 0x8780180005c0001c 0x21e0060001700007

def z169 : W := mkw 0x00901d4d50000000 0x0024075354000000 0x0000180e00000000 0x0000060380000000

def z170 : W := mkw 0x02d81f4002400090 0x00b607d000900024 0xf7f81fe007c000fe 0xfdfe07f801f0003f

def z171 : W := mkw 0x125809e001370048 0x04960278004dc012 0x107801e0003f0000 0x841e0078000fc000

def z172 : W := mkw 0x036fe00d559aaa00 0x00dbf8035566aa80 0xffffe01fffffff01 0xfffff807ffffffc0

def z173 : W := mkw 0x04334b96e62cdcee 0xc10cd2e5b98b373b 0xfc77df9fe63cfcff 0xff1df7e7f98f3f3f

def z174 : W := mkw 0x0248200001120200 0x0092080000448080 0x0008200000030300 0x000208000000c0c0

def z175 : W := mkw 0x0d959f9fe6e4f4ff 0xc36567e7f9b93d3f 0xef879f9fe7c0f0ff 0x7be1e7e7f9f03c3f

def z176 : W := mkw 0x09959f9b86e4f0ff 0x026567e6e1b93c3f 0xfff79f9f87fcf0ff 0xfffde7e7e1ff3c3f

def z177 : W := mkw 0x92c816f0ab7355f2 0xa4b205bc2adcd57c 0x6388e7f1fbe3ffe3 0xd8e239fc7ef8fff8

def z178 : W := mkw 0x04334916440cc82c 0x410cd2459103320b 0xfc77181e041cc0ff 0x3f1dc6078107303f

def z179 : W := mkw 0x0905821b8680f0a7 0x02416086e1a03c29 0x6807861f8200f0e3 0x5a01e187e0803c38

def z180 : W := mkw 0x02c8160003520090 0x00b2058000d48024 0xf7f81e0007ff00fe 0xfdfe078001ffc03f

def z181 : W := mkw 0x0b6fe01b859afa27 0x02dbf806e166be89 0xffffe01f87ffff01 0xfffff807e1ffffc0

def z182 : W := mkw 0x1bdd9f5b87d6f0bf 0x06f767d6e1f5bc2f 0xfff79e1f87dcf0ff 0x7ffde787e1f73c3f

def z183 : W := mkw 0x010580000480a000 0x0041600001202800 0xef8fe00007e3ff01 0xfbe3f80001f8ffc0

def z184 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x600086118223ffe3 0x580021846088fff8

def z185 : W := mkw 0x0da7d61fe6c8fcb7 0xc369f587f9b23f2d 0xef87de1fe7c0fcff 0x7be1f787f9f03f3f

def z186 : W := mkw 0x888016bbaa6155f7 0xa22005aeea98557d 0x6008fffffa23ffff 0xd8023ffffe88ffff

def z187 : W := mkw 0x003349164400c024 0x000cd24591003009 0xfc77599e6400c0ff 0xbf1dd6679900303f

def z188 : W := mkw 0x1bcd967b87d3f0b7 0x06f3659ee1f4fc2d 0xef8f9e7f87c3f0ff 0x7be3e79fe1f0fc3f

def z189 : W := mkw 0x000100000480a000 0x0000400001202800 0x2400000007c0f000 0x0900000001f03c00

def z190 : W := mkw 0x03fffd4d54088800 0x00ffff5355022200 0xfffffffffc3ccc03 0xffffffffff0f3300

def z191 : W := mkw 0x09a7f61fd6c0f0b7 0x0269fd87f5b03c2d 0xef87fe1fffc0f0ff 0x7be1ff87fff03c3f

def z192 : W := mkw 0x0000000001922200 0x0000000000648880 0x0000000003c33300 0x0000000000f0ccc0

def z193 : W := mkw 0x0185960006c0a090 0x0061658001b02824 0xef879e0007c0f0ff 0x7be1e78001f03c3f

def z194 : W := mkw 0x0010090000000000 0x0004024000000000 0xd070198000000002 0xb41c066000000000

def z195 : W := mkw 0x0db7df9fe6ecfcff 0xc36df7e7f9bb3f3f 0xfff7df9fe7fcfcff 0xfffdf7e7f9ff3f3f

def z196 : W := mkw 0x12d81dc001760058 0x04b60770005d8016 0xf7f0198005fc00fe 0xbdfc0660017f003f

def z197 : W := mkw 0x03feffed522100c0 0x00ffbffb54884030 0xfbfffffffa2300e3 0xfefffffffe88c038

def z198 : W := mkw 0x000002a0022100c0 0x000000a800884030 0x6008e7f1fa2300e3 0xd80239fc7e88c038

def z199 : W := mkw 0x036ee00000000000 0x00dbb80000000000 0xdbffe7f1f8000003 0xf6fff9fc7e000000

def z200 : W := mkw 0x0000001200004024 0x0000000480001009 0x0000181e000000fe 0x000006078000003f

def z201 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef8ffe1f87e3ffff 0xfbe3ff87e1f8ffff

def z202 : W := mkw 0x00901f80026400d8 0x002407e000990036 0xf7f01f8007fc00fe 0xfdfc07e001ff003f

def z203 : W := mkw 0x00000290a22054e2 0x800000a428881538 0x6000c791e220fce3 0xd80031e478883f38

def z204 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0xdbf7599e60000003 0xb6fdd66798000000

def z205 : W := mkw 0x12d81f4003560098 0x04b607d000d58026 0xf7f01e0007dc00fe 0x7dfc078001f7003f

def z206 : W := mkw 0x0010098000240048 0x0004026000090012 0x00001980000000fe 0x000006600000003f

def z207 : W := mkw 0x0000000000000000 0x0000000000000000 0x0008a66198000000 0x4002299866000000

def z208 : W := mkw 0x0080160002400090 0x0020058000900024 0x0380060003c00000 0x40e0018000f00000

def z209 : W := mkw 0x008116120640c0b4 0x002045848190302d 0xef871e1e07c0c0ff 0x7be1c78781f0303f

def z210 : W := mkw 0x8985961baec0f5b7 0xa2616586ebb03d6d 0xef87fe1fffc0ffff 0x7be1ff87fff03fff

def z211 : W := mkw 0x0880161b824050b7 0x02200586e090142d 0xe7801e1f87c000fe 0x79e00787e1f0003f

def z212 : W := mkw 0x03ccb44910000000 0x00f32d1244000000 0x4388e7f1f8000003 0xd0e239fc7e000000

def z213 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0x2780860187c0f0fc 0x49e0218061f03c3f

def z214 : W := mkw 0x04110992242ccc6c 0xc1044264890b331b 0xf4701980043cccfe 0xbd1c0660010f333f

def z215 : W := mkw 0x0c901f9fe26454ff 0xc32407e7f899153f 0x00001f9fe00000fe 0x000007e7f800003f

def z216 : W := mkw 0x800000b0a8215562 0xa000002c2a085558 0x0008e1f1f823ff01 0x8002387c7e08ffc0

def z217 : W := mkw 0x1bdc9fe983f730db 0x06f727fa60fdcc36 0xf7f89fe187ff30fe 0xfdfe27f861ffcc3f

def z218 : W := mkw 0x0904800980803003 0x0241200260200c00 0x0000800180003000 0x0000200060000c00

def z219 : W := mkw 0x00100ba0022500c8 0x000402e800894032 0xf4781fe0063f00fe 0xfd1e07f8018fc03f

def z220 : W := mkw 0x03fffd4d5480a000 0x00ffff5355202800 0xffffffffffc0f003 0xfffffffffff03c00

def z221 : W := mkw 0x827a6bf4fa2155e2 0xa09e9afd3e885578 0x7078e7f1fa23ffe3 0xdc1e39fc7e88fff8

def z222 : W := mkw 0x12d81ff0237744f8 0x84b607fc08ddd13e 0xf7f85ff067ffccff 0xfdfe17fc19fff33f

def z223 : W := mkw 0x0985941b04c0e035 0x02616506c130380d 0xef87181e05c0c0ff 0x3be1c6078170303f

def z224 : W := mkw 0x000100120400c024 0x0000400481003009 0x240000000400c0fc 0x090000000100303f

def z225 : W := mkw 0x0001000204008004 0x0000400081002001 0x8c07180e0400001c 0x2301c60381000007

def z226 : W := mkw 0x0000000000000000 0x0000000000000000 0x6008e7f1fa23ff03 0xd80239fc7e88ffc0

def z227 : W := mkw 0x01949d4d50000000 0x0065275354000000 0xcb879ffff8000003 0x72e1e7fffe000000

def z228 : W := mkw 0x03eff409059aaa00 0x00fbfd024166aa80 0xfffffe1f87ffff03 0xffffff87e1ffffc0

def z229 : W := mkw 0x0104800900000000 0x0041200240000000 0x0807801f80000001 0x0201e007e0000000

def z230 : W := mkw 0x0258098001360048 0x00960260004d8012 0xf7f8198007ff00fe 0xfdfe066001ffc03f

def z231 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0x0b87861f83c0f001 0x42e1e187e0f03c00

def z232 : W := mkw 0x12d81fed537700d8 0x04b607fb54ddc036 0xf7f81fffffff00fe 0xfdfe07ffffffc03f

def z233 : W := mkw 0x0000000000000000 0x0000000000000000 0xf4700000043c0000 0xbd1c0000010f0000

def z234 : W := mkw 0x002340120408c824 0x0008d00481023209 0xfc77581e043cccff 0xbf1dd607810f333f

def z235 : W := mkw 0x0985940b04c0a015 0x02616502c1302805 0xef87980e07c0f01d 0x7be1e60381f03c07

def z236 : W := mkw 0x0000001020004420 0x8000000408001108 0x000040106000cc01 0x0000100418003300

def z237 : W := mkw 0x92d81fe08b7711da 0x24b607f822ddc476 0xf7f8bfe19fff33fe 0xfdfe2ff867ffccff

def z238 : W := mkw 0x042340166408cc24 0xc108d00599023309 0xec07581e6400ccff 0x3b01d6079900333f

def z239 : W := mkw 0x04334916640ccc2c 0xc10cd2459903330b 0x9c77581e641ccc1d 0x271dd60799073307

def z240 : W := mkw 0x0126e00000000000 0x0049b80000000000 0x0807e00000000001 0x0201f80000000000

def z241 : W := mkw 0x02fa7d4d50000000 0x00be9f5354000000 0x10787ffff8000002 0x841e1ffffe000000

def z242 : W := mkw 0x04334906440c880c 0x410cd24191032203 0xfc77580e043ccc1d 0xbf1dd603810f3307

def z243 : W := mkw 0x0022400000080800 0x0008900000020200 0x10704000003c0c00 0x841c1000000f0300

def z244 : W := mkw 0x0880160982401093 0x0220058260900424 0x0000060180000000 0x0000018060000000

def z245 : W := mkw 0x03fefd4d51120000 0x00ffbf5354448000 0xffffffffffff0003 0xffffffffffffc000

def z246 : W := mkw 0x0800020082c03093 0x0200008020b00c24 0x0000000003c03000 0x0000000000f00c00

def z247 : W := mkw 0x0000008000240048 0x0000002000090012 0x24000000043c00fc 0x09000000010f003f

def z248 : W := mkw 0x13feff6d53530090 0x04ffbfdb54d4c024 0xdbfffffffbc30003 0xf6fffffffef0c000

def z249 : W := mkw 0x067a69c4702c0c48 0xc19e9a711c0b0312 0x107861e0783c0c00 0x841e18781e0f0300

def z250 : W := mkw 0x127a69e451370048 0x049e9a79144dc012 0x107861e0783f0000 0x841e18781e0fc000

def z251 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0x9bffbe6f98000000 0x66ffef9be6000000

def z252 : W := mkw 0x840102b2ae2dddee 0xe10040acab8b777b 0x6408e7f1fe3fffff 0xd90239fc7f8fffff

def z253 : W := mkw 0x13ccb66913530090 0x04f32d9a44d4c024 0x0388a6619bc30000 0x40e2299866f0c000

def z254 : W := mkw 0x80000010a8005522 0xa00000042a001548 0x000000000000ff00 0x0000000000003fc0

def z255 : W := mkw 0x13dcbfe9137700d8 0x04f72ffa44ddc036 0xf7f8bfe19fff00fe 0xfdfe2ff867ffc03f

def z256 : W := mkw 0x027a694450000000 0x009e9a5114000000 0xd87f79fe78000003 0xb61fde7f9e000000

def z257 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f8fff1ffff00ff 0xfdfe3ffc7fffc03f

def z258 : W := mkw 0x040000922024446c 0xc10000248809111b 0x00000000000000fc 0x000000000000003f

def z259 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f8ffe007ffffff 0xfdfe3ff801ffffff

def z260 : W := mkw 0x16d91ff2277fccfc 0xc5b647fc89dff33f 0xf7f81fe007ffccfe 0xfdfe07f801fff33f

def z261 : W := mkw 0x07fffd5f7408cc24 0xc1ffff57dd023309 0xdbfffffff800cc03 0xf6fffffffe003300

def z262 : W := mkw 0x8905801bac80f527 0xa2416006eb203d49 0x0807e01ff800ff01 0x0201f807fe003fc0

def z263 : W := mkw 0x80901ffdfa2155e2 0xa02407ff7e885578 0x6008fffffa23ffe3 0xd8023ffffe88fff8

def z264 : W := mkw 0x10901fe0026500d8 0x042407f800994036 0xf4701fe0043c00fe 0xbd1c07f8010f003f

def z265 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xfff7800007dcf001 0x7ffde00001f73c00

def z266 : W := mkw 0x0bfeff5fd24050b7 0x02ffbfd7f490142d 0xdbfffffff80000ff 0xf6fffffffe00003f

def z267 : W := mkw 0x0000008000200040 0x0000002000080010 0x60000180002000e2 0x9800006000080038

def z268 : W := mkw 0x13fefd4d51560018 0x04ffbf5354558006 0x9ff7180e05dc001c 0x27fdc60381770007

def z269 : W := mkw 0x02c8144000000000 0x00b2051000000000 0x0388066000000000 0x40e2019800000000

def z270 : W := mkw 0x00000000011a0a00 0x0000000000468280 0x00000000003f0f00 0x00000000000fc3c0

def z271 : W := mkw 0x0000009020204460 0x8000002408081118 0x6008e1906223ffe3 0xd80238641888fff8

def z272 : W := mkw 0x067b4996653ecc6c 0xc19ed265994fb31b 0xffff599e67ffccff 0xffffd66799fff33f

def z273 : W := mkw 0x07fffddf742ccc6c 0xc1ffff77dd0b331b 0xfff7599e643cccff 0xbffdd667990f333f

def z274 : W := mkw 0x80100bb0aa2555ea 0xa00402ec2a89557a 0xf478fff1fe3fffff 0xfd1e3ffc7f8fffff

def z275 : W := mkw 0x13eff66007dbaa90 0x04fbfd9801f6eaa4 0xffffe66007ffff01 0xfffff99801ffffc0

def z276 : W := mkw 0x16fb5fe6477f88dc 0x45bed7f991dfe237 0xffff1fee07ff00fe 0xffffc7fb81ffc03f

def z277 : W := mkw 0x034ca00000000000 0x00d3280000000000 0x0388a00000000000 0x40e2280000000000

def z278 : W := mkw 0x800000a028210540 0xa00000280a084150 0x6008e1e07a23ff01 0xd80238781e88ffc0

def z279 : W := mkw 0x03ccb44910000000 0x00f32d1244000000 0x0380000000000000 0x00e0000000000000

def z280 : W := mkw 0x000002a0022100c0 0x000000a800884030 0x20000000022300e0 0x080000000088c038

def z281 : W := mkw 0x1000000001560018 0x0400000000558006 0x0400000005dc001c 0x0100000001770007

def z282 : W := mkw 0x000002b0222144e0 0x800000ac08885138 0x600847f06223cce3 0xd80211fc1888f338

def z283 : W := mkw 0x036fe09025baee60 0x80dbf824096ebb98 0xffffe19067ffffe3 0xfffff86419fffff8

def z284 : W := mkw 0x0d37c99fe4acfc6f 0xc34df267f92b3f1b 0xfc77d99fe43cfcff 0xbf1df667f90f3f3f

def z285 : W := mkw 0x0000001080005022 0x0000000420001408 0x000080118000f001 0x0000200460003c00

def z286 : W := mkw 0x036ee00000000000 0x00dbb80000000000 0x9bf7000000000000 0x26fdc00000000000

def z287 : W := mkw 0x0bfffd4f54c0a015 0x02ffff53d5302805 0x9ff7180e05c0001c 0x27fdc60381700007

def z288 : W := mkw 0x03dcbd4910000000 0x00f72f5244000000 0xd3f8bfe198000002 0xf4fe2ff866000000

def z289 : W := mkw 0x0127e0000488aa00 0x0049f80001222a80 0xfc77e000043cff01 0xbf1df800010f3fc0

def z290 : W := mkw 0x125809e001370048 0x04960278004dc012 0xf7f801e007ff0000 0xfdfe007801ffc000

def z291 : W := mkw 0x03fefd4000000000 0x00ffbf5000000000 0xdbffffe000000003 0xf6fffff800000000

def z292 : W := mkw 0x10901fed526500d8 0x042407fb54994036 0x00001ffff80000fe 0x000007fffe00003f

def z293 : W := mkw 0x0010098000240048 0x0004026000090012 0xf4701980043c00fe 0xbd1c0660010f003f

def z294 : W := mkw 0x037ee94450000000 0x00dfba5114000000 0xdbffe1e078000001 0xf6fff8781e000000

def z295 : W := mkw 0x84334996ec2cdd6e 0xe10cd265bb0b375b 0xfc77f99ffc3cffff 0xbf1dfe67ff0f3fff

def z296 : W := mkw 0x043249966024446c 0xc10c92659809111b 0xd877599e600000ff 0xb61dd6679800003f

def z297 : W := mkw 0x14334bb6677fccfc 0xc50cd2ed99dff33f 0xfc77599e67ffccff 0xbf1dd66799fff33f

def z298 : W := mkw 0x12d81d4001560018 0x04b6075000558006 0xd7f81fe005dc001e 0xf5fe07f801770007

def z299 : W := mkw 0x0beff61b86c0f0b7 0x02fbfd86e1b03c2d 0xfffffe1f87c0f0ff 0xffffff87e1f03c3f

def z300 : W := mkw 0x04000080202c0c48 0xc1000020080b0312 0x00000000003c0c00 0x00000000000f0300

def z301 : W := mkw 0x01849619820050a2 0x0061258660801428 0xeb879e1f8200f0e3 0x7ae1e787e0803c38

def z302 : W := mkw 0x836fe2b0afbbffe2 0xa0dbf8ac2beefff8 0xffffe00007ffffe1 0xfffff80001fffff8

def z303 : W := mkw 0x0000000000000000 0x0000000000000000 0x600080000200f001 0x5800200000803c00

def z304 : W := mkw 0x0fffffdff6ecfcff 0xc3fffff7fdbb3f3f 0xfffffffffffcfcff 0xffffffffffff3f3f

def z305 : W := mkw 0x0248204010000000 0x0092081004000000 0x0008206018000000 0x0002081806000000

def z306 : W := mkw 0x0104800000802000 0x0041200000200800 0x0380800003c03000 0x40e0200000f00c00

def z307 : W := mkw 0x0985960986c0b093 0x0261658261b02c24 0xef87860187c0f001 0x7be1e18061f03c00

def z308 : W := mkw 0x12fa7fe4537700d8 0x04be9ff914ddc036 0xf7f87fe07fff00fe 0xfdfe1ff81fffc03f

def z309 : W := mkw 0x0422400460080c00 0xc108900118020300 0x0000400060000c00 0x0000100018000300

def z310 : W := mkw 0x9bdd9ffbaff7f5ff 0xa6f767feebfdfd7f 0xffffffffffffffff 0xffffffffffffffff

def z311 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x00000000000000e0 0x0000000000000038

def z312 : W := mkw 0x0bfffd4f54c0a015 0x02ffff53d5302805 0xdffffffffdc0001f 0xf7ffffffff700007

def z313 : W := mkw 0x8000000028000500 0xa00000000a000140 0x0000600078000f00 0x000018001e0003c0

def z314 : W := mkw 0x03fffd4d559aaa00 0x00ffff535566aa80 0xfffff80e07ffff01 0xfffffe0381ffffc0

def z315 : W := mkw 0x07fffd4f540c880c 0x41ffff53d5032203 0xdffffffffc1c001f 0xf7ffffffff070007

def z316 : W := mkw 0x840102b2ae2dddee 0xe10040acab8b777b 0x24000000063ffffc 0x09000000018fffff

def z317 : W := mkw 0x036ee00000000000 0x00dbb80000000000 0xdbffe00000000001 0xf6fff80000000000

def z318 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x600087f1fa00f0e3 0x580021fc7e803c38

def z319 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000861180000003 0x5000218460000000

def z320 : W := mkw 0x03dc9d4900000000 0x00f7275240000000 0xdbff9fff80000003 0xf6ffe7ffe0000000

def z321 : W := mkw 0x84334bb6ee2dddee 0xe10cd2edbb8b777b 0xfc775ffffc3cccff 0xbf1dd7ffff0f333f

def z322 : W := mkw 0x0985960b06c0a095 0x02616582c1b02825 0xef871e0e07c000fe 0x7be1c78381f0003f

def z323 : W := mkw 0x0000000000000000 0x0000000000000000 0x000007f1f8000002 0x000001fc7e000000

def z324 : W := mkw 0x10901fe0026500d8 0x042407f800994036 0xe7801fe007c000fe 0x79e007f801f0003f

def z325 : W := mkw 0x08901f5fd24050b7 0x022407d7f490142d 0x00001ffff80000fe 0x000007fffe00003f

def z326 : W := mkw 0x80901ffdfa2155e2 0xa02407ff7e885578 0x00001ffff80000e2 0x000007fffe000038

def z327 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000e011f8000001 0x000038047e000000

def z328 : W := mkw 0x04324994602c4c68 0xc10c9265180b131a 0x70704190603ccce3 0x9c1c1064180f3338

def z329 : W := mkw 0x036ee00001120000 0x00dbb80000448000 0xffffe00007ff0001 0xfffff80001ffc000

def z330 : W := mkw 0x0d27c01fe488fc27 0xc349f007f9223f09 0x0807c01fe000fc01 0x0201f007f8003f00

def z331 : W := mkw 0x8db7dfbfeeedfdff 0xe36df7effbbb7f7f 0xffffffffffffffff 0xffffffffffffffff

def z332 : W := mkw 0x84100bb6ea2555ee 0xe10402edba89557b 0x6008fffffa23ffff 0xd8023ffffe88ffff

def z333 : W := mkw 0x036fe00004088800 0x00dbf80001022200 0xffffe000043ccc01 0xfffff800010f3300

def z334 : W := mkw 0x10100ba0037700d8 0x040402e800ddc036 0xf470198007ff00fe 0xbd1c066001ffc03f

def z335 : W := mkw 0x00000210820050a2 0x0000008420801428 0x6008e7f1fa00f0e3 0xd80239fc7e803c38

def z336 : W := mkw 0x04324984602c0c48 0xc10c9261180b0312 0xd877599e603c0c03 0xb61dd667980f0300

def z337 : W := mkw 0x000002b0822150e2 0x000000ac20885438 0x600887f18223f0e3 0xd80221fc6088fc38

def z338 : W := mkw 0x0410098460240448 0xc104026118090112 0x0000018060000000 0x0000006018000000

def z339 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0x08079e1f8000f0ff 0x0201e787e0003c3f

def z340 : W := mkw 0x127a69e0013f0a48 0x049e9a78004fc292 0x107861e0003f0f00 0x841e1878000fc3c0

def z341 : W := mkw 0x0000009020204460 0x8000002408081118 0x6008e7f1f820cce3 0xd80239fc7e083338

def z342 : W := mkw 0x843349b66c2dcd6c 0xe10cd26d9b0b735b 0xfc7f79fe7c3fcfff 0xbf1fde7f9f0ff3ff

def z343 : W := mkw 0x0400001660004424 0xc100000598001109 0x0000001e60000000 0x0000000798000000

def z344 : W := mkw 0x02d81dc000240048 0x00b6077000090012 0xf7f81fe0043c00fe 0xfdfe07f8010f003f

def z345 : W := mkw 0x0905821286c0f0b7 0x02416084a1b03c2d 0xef87800007c0f0fd 0x7be1e00001f03c3f

def z346 : W := mkw 0x87fffffffe2dddee 0xe1ffffffff8b777b 0xfffffffffe3fffff 0xffffffffff8fffff

def z347 : W := mkw 0x067a6984613e0e48 0xc19e9a61184f8392 0x10786180603f0f00 0x841e1860180fc3c0

def z348 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0x0807599e6000ccff 0x0201d6679800333f

def z349 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xbc77180e043cccfc 0x2f1dc603810f333f

def z350 : W := mkw 0x0db7dd9f64ecec7d 0xc36df767d93b3b1f 0xfff7599e65fcccff 0xbffdd667997f333f

def z351 : W := mkw 0x026a6000011a0a00 0x009a980000468280 0x10700000001c0000 0x041c000000070000

def z352 : W := mkw 0x0032490440000000 0x000c924110000000 0xd87ffffff8000003 0xf61ffffffe000000

def z353 : W := mkw 0x001109920424c06c 0x000442648109301b 0xfc77199e043cc0ff 0xbf1dc667810f303f

def z354 : W := mkw 0x0184960902400090 0x0061258240900024 0xef879e1f87c000ff 0x7be1e787e1f0003f

def z355 : W := mkw 0x0010090000040008 0x0004024000010002 0x94701800041c001c 0x251c060001070007

def z356 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0x9c77199e641c00fe 0x271dc6679907003f

def z357 : W := mkw 0x0905821b86c0f0b7 0x02416086e1b03c2d 0x2c07801f87c0f0fd 0x0b01e007e1f03c3f

def z358 : W := mkw 0x036fe210879afaa2 0x00dbf88421e6bea8 0xffffe61187ffffe3 0xfffff98461fffff8

def z359 : W := mkw 0x000100922420c464 0x8000402489083119 0xec07599e6420ccff 0xbb01d6679908333f

def z360 : W := mkw 0x90901ff0aa6555fa 0xa42407fc2a99557e 0x00001ff1f80000fe 0x000007fc7e00003f

def z361 : W := mkw 0x0127c0000488a800 0x0049f00001222a00 0xfff7c00007fcfc01 0xfffdf00001ff3f00

def z362 : W := mkw 0x041009966024446c 0xc10402659809111b 0x6000599e6020ccff 0x980016679808333f

def z363 : W := mkw 0x0527e01f7408cc24 0xc149f807dd023309 0x0807e01ff800cc01 0x0201f807fe003300

def z364 : W := mkw 0x03eef44d50000000 0x00fbbd1354000000 0x0b8fe67ff8000001 0x42e3f99ffe000000

def z365 : W := mkw 0x0beff40b05daaa15 0x02fbfd02c176aa85 0x9ff7180e05dc001c 0x27fdc60381770007

def z366 : W := mkw 0x0880140b00400015 0x02200502c0100005 0x0000180e0000001c 0x0000060380000007

def z367 : W := mkw 0x90901ff0aa6555fa 0xa42407fc2a99557e 0x6008fff1fa23ffff 0xd8023ffc7e88ffff

def z368 : W := mkw 0x900002b0ab7755fa 0xa40000ac2addd57e 0x2400000007fffffc 0x0900000001ffffff

def z369 : W := mkw 0x0032490440000000 0x000c924110000000 0x1070418060000000 0x841c106018000000

def z370 : W := mkw 0x800102b0afbbffe2 0xa00040ac2beefff8 0x6408e7f1ffffffe3 0xd90239fc7ffffff8

def z371 : W := mkw 0x09b7df1fc6c0f0b7 0x026df7c7f1b03c2d 0xfff7df9fe7c0f0ff 0xfffdf7e7f9f03c3f

def z372 : W := mkw 0x07fffddf75beee6c 0xc1ffff77dd6fbb9b 0xffffffffffffffff 0xffffffffffffffff

def z373 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xfff7400005fccc01 0xbffdd000017f3300

def z374 : W := mkw 0x898596bbaee1f5f7 0xa26165aeebb87d7d 0xef879fffffc0f0ff 0x7be1e7fffff03c3f

def z375 : W := mkw 0x13dc9fe9037700d8 0x04f727fa40ddc036 0xffff9fff87ff00ff 0xffffe7ffe1ffc03f

def z376 : W := mkw 0x02d81fe0022100c0 0x00b607f800884030 0xf3f81fe0022300e2 0xfcfe07f80088c038

def z377 : W := mkw 0x834ca2b0abb377e2 0xa0d328ac2aecddf8 0x6388e7f1fbe3ffe3 0xd8e239fc7ef8fff8

def z378 : W := mkw 0x0bcdb65b96c0f0b7 0x02f36d96e5b03c2d 0xef8fbe7f9fc0f0ff 0x7be3ef9fe7f03c3f

def z379 : W := mkw 0x1248006001130000 0x049200180044c000 0x0008006000030000 0x000200180000c000

def z380 : W := mkw 0x1bdd9feb07f7a0dd 0x06f767fac1fde837 0xffff1fee07ff00fe 0xffffc7fb81ffc03f

def z381 : W := mkw 0x04234092242ccc6c 0xc108d024890b331b 0xfc774000043cccfd 0xbf1dd000010f333f

def z382 : W := mkw 0x04010092242ccc6c 0xc1004024890b331b 0x64004190643cccff 0x99001064190f333f

def z383 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x200861e07a23ffe0 0x880218781e88fff8

def z384 : W := mkw 0x13feffe0037700d8 0x04ffbff800ddc036 0xffffffe007ff00ff 0xfffffff801ffc03f

def z385 : W := mkw 0x03fefd4d511a0a00 0x00ffbf5354468280 0xdbfffffff83f0f03 0xf6fffffffe0fc3c0

def z386 : W := mkw 0x01058000059aaa00 0x004160000166aa80 0xef87800007ffff01 0x7be1e00001ffffc0

def z387 : W := mkw 0x0032498440240048 0x000c926110090012 0xfc77599e643c00ff 0xbf1dd667990f003f

def z388 : W := mkw 0x09a7f61b86c8fab7 0x0269fd86e1b23ead 0xef87fe1f87c0ffff 0x7be1ff87e1f03fff

def z389 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0xdbfff80e00000001 0xf6fffe0380000000

def z390 : W := mkw 0x84100bb6ea2555ee 0xe10402edba89557b 0x00001ffff80000fe 0x000007fffe00003f

def z391 : W := mkw 0x13dd9fe007f7a0d8 0x04f767f801fde836 0xffff9fe007fff0ff 0xffffe7f801fffc3f

def z392 : W := mkw 0x13ccb66003d32290 0x04f32d9800f4c8a4 0x0388a66003c33300 0x40e2299800f0ccc0

def z393 : W := mkw 0x0127e0000488aa00 0x0049f80001222a80 0x0807000000000000 0x0201c00000000000

def z394 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x600807f1fa2300e2 0xd80201fc7e88c038

def z395 : W := mkw 0x19959ffb86e5f0ff 0x066567fee1b97c3f 0xef879fff87c0f0ff 0x7be1e7ffe1f03c3f

def z396 : W := mkw 0x10901d4000440018 0x0424075000110006 0x000018000000001c 0x0000060000000007

def z397 : W := mkw 0x0000000000000000 0x0000000000000000 0x600040000020cc01 0x9800100000083300

def z398 : W := mkw 0x04901ddf7024446c 0xc1240777dc09111b 0x00001ffff80000fe 0x000007fffe00003f

def z399 : W := mkw 0x925809e029370548 0xa49602780a4dc152 0x107861e0783f0f00 0x841e18781e0fc3c0

def z400 : W := mkw 0x0537e99664acee6c 0xc14dfa65992b3b9b 0xfc77f99e643cffff 0xbf1dfe67990f3fff

def z401 : W := mkw 0x026b6000059aaa00 0x009ad8000166aa80 0x3478600007ffff00 0x8d1e180001ffffc0

def z402 : W := mkw 0x037fe944559aaa00 0x00dffa511566aa80 0xffffe1e07fffff01 0xfffff8781fffffc0

def z403 : W := mkw 0x0801000204c0a015 0x0200400081302805 0x0400000005c0001c 0x0100000001700007

def z404 : W := mkw 0x13fffd4005deaa18 0x04ffff500177aa86 0x9ff7180005dc001c 0x27fdc60001770007

def z405 : W := mkw 0x07fefdcd702c0c48 0xc1ffbf735c0b0312 0xdbfffffff83c0c03 0xf6fffffffe0f0300

def z406 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xb7f0180007ff00fc 0x2dfc060001ffc03f

def z407 : W := mkw 0x84334bb6ee2dddee 0xe10cd2edbb8b777b 0xfc77599e663fffff 0xbf1dd667998fffff

def z408 : W := mkw 0x0985941b8480f027 0x02616506e1203c09 0xcb879e1f8000f003 0x72e1e787e0003c00

def z409 : W := mkw 0x0000000000000000 0x0000000000000000 0xe4001800040000fe 0x390006000100003f

def z410 : W := mkw 0x0cb35f9fe66cdcff 0xc32cd7e7f99b373f 0xfc775f9fe43cccff 0xbf1dd7e7f90f333f

def z411 : W := mkw 0x836ee2b0aa2155e2 0xa0dbb8ac2a885578 0xfbffe7f1fa23ffe3 0xfefff9fc7e88fff8

def z412 : W := mkw 0x04010092242ccc6c 0xc1004024890b331b 0xec07181e043cccff 0x3b01c607810f333f

def z413 : W := mkw 0x0bffff5fd6c0f0b7 0x02ffffd7f5b03c2d 0xfff79e1f87c0f0ff 0x7ffde787e1f03c3f

def z414 : W := mkw 0x02fa5d4440000000 0x00be975110000000 0xdbff5ffe60000003 0xf6ffd7ff98000000

def z415 : W := mkw 0x02d81d4000000000 0x00b6075000000000 0xd3f8fff1f8000003 0xf4fe3ffc7e000000

def z416 : W := mkw 0x03fefd4d51922200 0x00ffbf5354648880 0xdbfffffffbc33303 0xf6fffffffef0ccc0

def z417 : W := mkw 0x0104a00000802200 0x0041280000200880 0x0000a00000003300 0x0000280000000cc0

def z418 : W := mkw 0x12fa5fe4437700d8 0x04be97f910ddc036 0xffff5ffe67ff00ff 0xffffd7ff99ffc03f

def z419 : W := mkw 0x888016bbaa6155f7 0xa22005aeea98557d 0x00001ffff80000fe 0x000007fffe00003f

def z420 : W := mkw 0x00000210820050a2 0x0000008420801428 0x200000000200f0e0 0x0800000000803c38

def z421 : W := mkw 0x0801021286c0f0b7 0x02004084a1b03c2d 0x6400861187c0f0ff 0x5900218461f03c3f

def z422 : W := mkw 0x0985961b87dafab7 0x02616586e1f6bead 0xef879e1f87ffffff 0x7be1e787e1ffffff

def z423 : W := mkw 0x000002a0022100c0 0x000000a800884030 0x000007e0000000e2 0x000001f800000038

def z424 : W := mkw 0x0000009020204460 0x8000002408081118 0x200000000020cce0 0x0800000000083338

def z425 : W := mkw 0x0bfeff4dd2c03093 0x02ffbfd374b00c24 0xdbfffffffbc03003 0xf6fffffffef00c00

def z426 : W := mkw 0x843249a4682d0d48 0xe10c92691a0b4352 0x107861e0783f0f00 0x841e18781e0fc3c0

def z427 : W := mkw 0x0881161286c0f0b7 0x02204584a1b03c2d 0xe7801e0007c0f0fe 0x79e0078001f03c3f

def z428 : W := mkw 0x1bffffffd7f7f0ff 0x06fffffff5fdfc3f 0xfffffffffffff0ff 0xfffffffffffffc3f

def z429 : W := mkw 0x076fe016659aee24 0xc1dbf8059966bb89 0xffffe01e67ffff01 0xfffff80799ffffc0

def z430 : W := mkw 0x03eff60007daaa90 0x00fbfd8001f6aaa4 0xfffffe0007ffffff 0xffffff8001ffffff

def z431 : W := mkw 0x0032490440000000 0x000c924110000000 0x9877180e00000000 0x261dc60380000000

def z432 : W := mkw 0x800002a08a2111c2 0x200000a822884470 0x6008a7e19a2333e2 0xd80229f86688ccf8

def z433 : W := mkw 0x0881161b86c0f0b7 0x02204586e1b03c2d 0x24001e1f87c0f0fe 0x09000787e1f03c3f

def z434 : W := mkw 0x800002208a011182 0x2000008822804460 0x0000066198000000 0x0000019866000000

def z435 : W := mkw 0x00000210820050a2 0x0000008420801428 0x00000611800000e2 0x0000018460000038

def z436 : W := mkw 0x0258094000000000 0x0096025000000000 0x107801e000000000 0x841e007800000000

def z437 : W := mkw 0x09959f5fd6c0f0b7 0x026567d7f5b03c2d 0xef879fffffc0f0ff 0x7be1e7fffff03c3f

def z438 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z439 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xdfffe00005dc0001 0xf7fff80001770000

def z440 : W := mkw 0x041109966424c46c 0xc10442659909311b 0xec07199e6400c0ff 0x3b01c6679900303f

def z441 : W := mkw 0x0184940900000000 0x0061250240000000 0x8b87180e00000000 0x22e1c60380000000

def z442 : W := mkw 0x84234016ec08dd26 0xe108d005bb023749 0x0807e01ff800ff01 0x0201f807fe003fc0

def z443 : W := mkw 0x890582bbaea1f5e7 0xa24160aeeba87d79 0x680fe7fffa23ffe3 0xda03f9fffe88fff8

def z444 : W := mkw 0x13ffffed57ffaad8 0x04fffffb55ffeab6 0xffffffffffffffff 0xffffffffffffffff

def z445 : W := mkw 0x042340166408cc24 0xc108d00599023309 0xfc77401e643ccc01 0xbf1dd007990f3300

def z446 : W := mkw 0x098596bb86e1f0f7 0x026165aee1b87c3d 0xef8f9fff87e3f0ff 0xfbe3e7ffe1f8fc3f

def z447 : W := mkw 0x0000000001120000 0x0000000000448000 0x2400000007ff0000 0x0900000001ffc000

def z448 : W := mkw 0x100002a0037700d8 0x040000a800ddc036 0x640807e007ff00fe 0xd90201f801ffc03f

def z449 : W := mkw 0x842342b6ee29dde6 0xe108d0adbb8a7779 0x680fe7fffa23ffe3 0xda03f9fffe88fff8

def z450 : W := mkw 0x0000020002000080 0x0000008000800020 0x60000600020000e2 0x5800018000800038

def z451 : W := mkw 0x0001000004088800 0x0000400001022200 0x24000000043ccc00 0x09000000010f3300

def z452 : W := mkw 0x00901d4000000000 0x0024075000000000 0x00001fe000000002 0x000007f800000000

def z453 : W := mkw 0x036ee00000000000 0x00dbb80000000000 0xfbffe0000223ff01 0xfefff8000088ffc0

def z454 : W := mkw 0x036fe012059aea24 0x00dbf8048166ba89 0xfffff81e07ffffff 0xfffffe0781ffffff

def z455 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x600047f1f820cce3 0x980011fc7e083338

def z456 : W := mkw 0x08000212824050b7 0x02000084a090142d 0x00000000000000fc 0x000000000000003f

def z457 : W := mkw 0x010580000480a000 0x0041600001202800 0x080780000000f001 0x0201e00000003c00

def z458 : W := mkw 0x818496b9aa2155e2 0xa06125ae6a885578 0xeb8ffffffa23ffe3 0xfae3fffffe88fff8

def z459 : W := mkw 0x03feff5dd20050a2 0x00ffbfd774801428 0xfbfffffffa00f0e3 0xfefffffffe803c38

def z460 : W := mkw 0x100102a007ffaad8 0x040040a801ffeab6 0x2400000007fffffc 0x0900000001ffffff

def z461 : W := mkw 0x0fffff9fe7fefeff 0xc3ffffe7f9ffbfbf 0xffffff9fe7ffffff 0xffffffe7f9ffffff

def z462 : W := mkw 0x0010099020244468 0x800402640809111a 0xf4705990643cccff 0xbd1c1664190f333f

def z463 : W := mkw 0x0000000000000000 0x0000000000000000 0x4008e00000000001 0xd002380000000000

def z464 : W := mkw 0x03fefddd70204460 0x80ffbf775c081118 0xfbfffffff820cce3 0xfefffffffe083338

def z465 : W := mkw 0x0022400000000000 0x0008900000000000 0xd877400000000001 0xb61dd00000000000

def z466 : W := mkw 0x0022600000080a00 0x0008980000020280 0x0000600000000f00 0x00001800000003c0

def z467 : W := mkw 0x000100120400c024 0x0000400481003009 0x0807001e0000c001 0x0201c00780003000

def z468 : W := mkw 0x80324bb4ea2155e2 0xa00c92ed3a885578 0xf87ffffffa23ffe3 0xfe1ffffffe88fff8

def z469 : W := mkw 0x0000000000000000 0x0000000000000000 0x000861e078000000 0x800218781e000000

def z470 : W := mkw 0x000000a000210040 0x0000002800084010 0x000801e000230000 0x800200780008c000

def z471 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xffff000007ff0000 0xffffc00001ffc000

def z472 : W := mkw 0x83fefffdfa2155e2 0xa0ffbfff7e885578 0xdbfffffff80000e3 0xf6fffffffe000038

def z473 : W := mkw 0x12c8144001520010 0x04b2051000548004 0x0380000001c00000 0x00e0000000700000

def z474 : W := mkw 0x0beff61b87dafab7 0x02fbfd86e1f6bead 0xfff79e1f87dcf0ff 0x7ffde787e1f73c3f

def z475 : W := mkw 0x0984961b82c070b7 0x02612586e0b01c2d 0x03809e1f83c030fe 0x40e02787e0f00c3f

def z476 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x0008a7f1fa0333e2 0x400229fc7e80ccf8

def z477 : W := mkw 0x0bccb64992c03093 0x02f32d9264b00c24 0x0388a6619bc03000 0x40e2299866f00c00

def z478 : W := mkw 0x96fb5ff6ef7fddfe 0xe5bed7fdbbdff77f 0xffffffffffffffff 0xffffffffffffffff

def z479 : W := mkw 0x034ca00001922200 0x00d3280000648880 0x6388e00003e3ff01 0xd8e2380000f8ffc0

def z480 : W := mkw 0x1bdd9d4b05d6a01d 0x06f76752c175a807 0x9ff7180e05dc001c 0x27fdc60381770007

def z481 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0x10781fe0003f00fe 0x841e07f8000fc03f

def z482 : W := mkw 0x034ca00001922200 0x00d3280000648880 0x0380000001c00000 0x00e0000000700000

def z483 : W := mkw 0x01b6fd4d50000000 0x006dbf5354000000 0x0807fffff8000003 0x0201fffffe000000

def z484 : W := mkw 0x800000a028210540 0xa00000280a084150 0x0000000000230f00 0x000000000008c3c0

def z485 : W := mkw 0x80000210aa0055a2 0xa00000842a801568 0x6000e611fa00ffe3 0x580039847e803ff8

def z486 : W := mkw 0x8127e010ac88ff22 0xa049f8042b223fc8 0x0807e011f800ff01 0x0201f8047e003fc0

def z487 : W := mkw 0x83feff6dda011182 0x20ffbfdb76804460 0xdbfffffffa033303 0xf6fffffffe80ccc0

def z488 : W := mkw 0x02d81d4000000000 0x00b6075000000000 0x93f0180000000000 0x24fc060000000000

def z489 : W := mkw 0x034ca00001922200 0x00d3280000648880 0xf7f8a00007ff3300 0xfdfe280001ffccc0

def z490 : W := mkw 0x076fe09225beee6c 0xc1dbf824896fbb9b 0xffffe00007fffffd 0xfffff80001ffffff

def z491 : W := mkw 0x800002308a0151a2 0x2000008c22805468 0x6008a6719a03f3e3 0x5802299c6680fcf8

def z492 : W := mkw 0x024802a0033300c0 0x009200a800ccc030 0xf7f807e007ff00e2 0xfdfe01f801ffc038

def z493 : W := mkw 0x0127e000059aaa00 0x0049f8000166aa80 0x2c07e00007ffff01 0x0b01f80001ffffc0

def z494 : W := mkw 0x80000010a8005522 0xa00000042a001548 0x00000011f8000000 0x000000047e000000

def z495 : W := mkw 0x1fffdfffe7fffcff 0xc7fff7fff9ffff3f 0xffffdfffe7fffcff 0xfffff7fff9ffff3f

def z496 : W := mkw 0x877febb6efbfffee 0xe1dffaedbbeffffb 0xffffffffffffffff 0xffffffffffffffff

def z497 : W := mkw 0x0bcd961b87d2f0b7 0x02f36586e1f4bc2d 0xffff9e1f87fff0ff 0xffffe787e1fffc3f

def z498 : W := mkw 0x0000000000000000 0x0000000000000000 0x6008000002230000 0xd80200000088c000

def z499 : W := mkw 0x026a6000011a0a00 0x009a980000468280 0x7078e000023fff01 0xdc1e3800008fffc0

def z500 : W := mkw 0x036ee000019a2a00 0x00dbb80000668a80 0x13f8e00003ff3f00 0xc4fe380000ffcfc0

def z501 : W := mkw 0x06fb5dd6642ccc6c 0xc1bed775990b331b 0xffff5ffe643cccff 0xffffd7ff990f333f

def z502 : W := mkw 0x136fe2a007ffaad8 0x04dbf8a801ffeab6 0xffffe00007fffffd 0xfffff80001ffffff

def z503 : W := mkw 0x0010094450000000 0x0004025114000000 0x000001e078000000 0x000000781e000000

def z504 : W := mkw 0x04324996602c4c6c 0xc10c9265980b131b 0x1070599e603c0cfe 0x841c1667980f033f

def z505 : W := mkw 0x077fe906459eaa0c 0x41dffa419167aa83 0x9ff7180e05dc001c 0x27fdc60381770007

def z506 : W := mkw 0x0000000000000000 0x0000000000000000 0xe780000007c00000 0x79e0000001f00000

def z507 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0x8f871e1f85c000fe 0x23e1c787e170003f

def z508 : W := mkw 0x0000008020200440 0x8000002008080110 0x0000418060200c00 0x8000106018080300

def z509 : W := mkw 0x0beff60987daba93 0x02fbfd8261f6aea4 0xffffe60187ffff01 0xfffff98061ffffc0

def z510 : W := mkw 0x0905801b8480f027 0x02416006e1203c09 0xec07981f8400f0ff 0x3b01e607e1003c3f

def z511 : W := mkw 0x180102b287f7f0ff 0x060040aca1fdfc3f 0x2400000007fff0fc 0x0900000001fffc3f

def z512 : W := mkw 0x800002208a011182 0x2000008822804460 0x4008e7f1fa033303 0xd00239fc7e80ccc0

def z513 : W := mkw 0x800000a028210540 0xa00000280a084150 0x4008e7f1f8230f03 0xd00239fc7e08c3c0

def z514 : W := mkw 0x0433499665beee6c 0xc10cd265996fbb9b 0xfc77599e67ffffff 0xbf1dd66799ffffff

def z515 : W := mkw 0x03fffd4d5488aa00 0x00ffff5355222a80 0xdbfffffff800ff03 0xf6fffffffe003fc0

def z516 : W := mkw 0x03fefdcd50240048 0x00ffbf7354090012 0xfffffffffc3c00ff 0xffffffffff0f003f

def z517 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0x9bf7f81ff8000001 0x26fdfe07fe000000

def z518 : W := mkw 0x0023400004088800 0x0008d00001022200 0x9c770000041c0000 0x271dc00001070000

def z519 : W := mkw 0x0537c99664acec6c 0xc14df265992b3b1b 0xfff7d99e67fcfcff 0xfffdf66799ff3f3f

def z520 : W := mkw 0x05b7dd9f642ccc6c 0xc16df767d90b331b 0xfff7df9fe43cccff 0xfffdf7e7f90f333f

def z521 : W := mkw 0x93fffff0affffffa 0xa4fffffc2bfffffe 0xfffffff1ffffffff 0xfffffffc7fffffff

def z522 : W := mkw 0x010582108680f0a2 0x0041608421a03c28 0xef87861187c0f0e3 0x7be1e18461f03c38

def z523 : W := mkw 0x02d81d4001120000 0x00b6075000448000 0xf7f81fe007ff0002 0xfdfe07f801ffc000

def z524 : W := mkw 0x8beff6bbaffbfff7 0xa2fbfdaeebfefffd 0xffffffffffffffff 0xffffffffffffffff

def z525 : W := mkw 0x0010090440000000 0x0004024110000000 0x0000199e60000002 0x0000066798000000

def z526 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x2008a6619a23ffe0 0x480229986688fff8

def z527 : W := mkw 0x037ee90440000000 0x00dfba4110000000 0xdbfff99e60000003 0xf6fffe6798000000

def z528 : W := mkw 0x0800001b80005027 0x02000006e0001409 0x0000001f80000000 0x00000007e0000000

def z529 : W := mkw 0x034da000059aaa00 0x00d368000166aa80 0x2788a00007ffff00 0x49e2280001ffffc0

def z530 : W := mkw 0x12c816e0037700d8 0x04b205b800ddc036 0x2788066007ff00fc 0x49e2019801ffc03f

def z531 : W := mkw 0x034d80000592a000 0x00d360000164a800 0xffff800007fff001 0xffffe00001fffc00

def z532 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0x03881fe003c300fe 0x40e207f800f0c03f

def z533 : W := mkw 0x03eef44910000000 0x00fbbd1244000000 0xdbffe66198000001 0xf6fff99866000000

def z534 : W := mkw 0x0927e01fd480f027 0x0249f807f5203c09 0x0807e01ff800f001 0x0201f807fe003c00

def z535 : W := mkw 0x0bdd9f5b86c0f0b7 0x02f767d6e1b03c2d 0xffff9fff87c0f0ff 0xffffe7ffe1f03c3f

def z536 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xbff7000007ffff00 0x2ffdc00001ffffc0

def z537 : W := mkw 0x13fefded51370048 0x04ffbf7b544dc012 0xdbfffffff83f0003 0xf6fffffffe0fc000

def z538 : W := mkw 0x13dcbfe003f722d8 0x04f72ff800fdc8b6 0xf7f8bfe007ff33fe 0xfdfe2ff801ffccff

def z539 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x0000e7f1f800ffe3 0x000039fc7e003ff8

def z540 : W := mkw 0x14b35ff6666dccfc 0xc52cd7fd999b733f 0xfc775ffe643cccff 0xbf1dd7ff990f333f

def z541 : W := mkw 0x82d81ff0aa2155e2 0xa0b607fc2a885578 0xf3f8fff1fa23ffe3 0xfcfe3ffc7e88fff8

def z542 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0x1877419e603ccc01 0x861dd067980f3300

def z543 : W := mkw 0x042340966428cc64 0xc108d025990a3319 0x6807419e6020cce3 0x9a01d06798083338

def z544 : W := mkw 0x0880161b824050b7 0x02200586e090142d 0x60009e1f8200f0ff 0x58002787e0803c3f

def z545 : W := mkw 0x880102b2aee1f5f7 0xa20040acabb87d7d 0x6408e7f1ffe3ffff 0xd90239fc7ff8ffff

def z546 : W := mkw 0x13fffd4005deaa18 0x04ffff500177aa86 0xfffff80007ffff1d 0xfffffe0001ffffc7

def z547 : W := mkw 0x1080166002410090 0x0420059800904024 0x0000066000000000 0x0000019800000000

def z548 : W := mkw 0x0032499460204460 0x800c926518081118 0xf877599e6020cce3 0xbe1dd66798083338

def z549 : W := mkw 0x027a6944511a0a00 0x009e9a5114468280 0x107861e0783f0f00 0x841e18781e0fc3c0

def z550 : W := mkw 0x0881161b8640d0b7 0x02204586e190342d 0xec071e1f8400c0ff 0x3b01c787e100303f

def z551 : W := mkw 0x0801021286c0f0b7 0x02004084a1b03c2d 0xec07181e07c0f0ff 0x3b01c60781f03c3f

def z552 : W := mkw 0x037ee94d50000000 0x00dfba5354000000 0x187fe1fff8000001 0x861ff87ffe000000

def z553 : W := mkw 0x067b69d6742ccc6c 0xc19eda759d0b331b 0xfc7f79fe7c3cccff 0xbf1fde7f9f0f333f

def z554 : W := mkw 0x0984960982c03093 0x0261258260b00c24 0xe7809e0187c030fe 0x79e0278061f00c3f

def z555 : W := mkw 0x026a6000011a0a00 0x009a980000468280 0xf7f8600007ff0f00 0xfdfe180001ffc3c0

def z556 : W := mkw 0x10901fe0026500d8 0x042407f800994036 0x60081fe0022300fe 0xd80207f80088c03f

def z557 : W := mkw 0x16fa5fe4637f0cd8 0xc5be97f918dfc336 0xf7f85fe067ff0cfe 0xfdfe17f819ffc33f

def z558 : W := mkw 0x037fe98005beaa48 0x00dffa60016faa92 0xfffff98007ffffff 0xfffffe6001ffffff

def z559 : W := mkw 0x92580bf0ab3755ea 0xa49602fc2acdd57a 0x7078e7f1fa3fffe3 0xdc1e39fc7e8ffff8

def z560 : W := mkw 0x0127e0000488aa00 0x0049f80001222a80 0x680fe0000223ff01 0xda03f8000088ffc0

def z561 : W := mkw 0x83fefd5df8005522 0xa0ffbf577e001548 0xdbfffffff800ff03 0xf6fffffffe003fc0

def z562 : W := mkw 0x00010000059aaa00 0x000040000166aa80 0x0400000005dc0000 0x0100000001770000

def z563 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc7ff99e663fffff 0xff1ffe67998fffff

def z564 : W := mkw 0x036ee00001922200 0x00dbb80000648880 0xdbffe00003c33301 0xf6fff80000f0ccc0

def z565 : W := mkw 0x04b35f96666cccfc 0xc12cd7e5999b333f 0xfff75f9e67fcccff 0xfffdd7e799ff333f

def z566 : W := mkw 0x808016b0aa6155f2 0xa02005ac2a98557c 0xe788fff1ffe3ffff 0xf9e23ffc7ff8ffff

def z567 : W := mkw 0x036fe0000488aa00 0x00dbf80001222a80 0xdbffe0000000ff01 0xf6fff80000003fc0

def z568 : W := mkw 0x800002a0aa2115c2 0xa00000a82a884570 0x0008e7e1fa233f00 0xc00239f87e88cfc0

def z569 : W := mkw 0x077fe98465beae48 0xc1dffa61196fab92 0xffffe18067ffff01 0xfffff86019ffffc0

def z570 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0x13f8e7e1f8000000 0xc4fe39f87e000000

def z571 : W := mkw 0x16fb5d46455e881c 0x45bed7519157a207 0x9ff7180e05dc001c 0x27fdc60381770007

def z572 : W := mkw 0x0537e99f742ccc6c 0xc14dfa67dd0b331b 0xfc77f99ffc3cccff 0xbf1dfe67ff0f333f

def z573 : W := mkw 0x0984960982c03093 0x0261258260b00c24 0xcb879e1f83c03003 0x72e1e787e0f00c00

def z574 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0x9bff79ee78000000 0xa6ffde7b9e000000

def z575 : W := mkw 0x0000000000000000 0x0000000000000000 0x200000000223ff00 0x080000000088ffc0

def z576 : W := mkw 0x802342b0ae29dde2 0xa008d0ac2b8a7778 0xfc7fe7f1fe3fffe3 0xff1ff9fc7f8ffff8

def z577 : W := mkw 0x900002b0ab7755fa 0xa40000ac2addd57e 0x6408e7f1ffffffff 0xd90239fc7fffffff

def z578 : W := mkw 0x0127e0000488aa00 0x0049f80001222a80 0xef87e00007c0ff01 0x7be1f80001f03fc0

def z579 : W := mkw 0x800002208a011182 0x2000008822804460 0x6008e6619a23ff01 0xd80239986688ffc0

def z580 : W := mkw 0x836fe0a02dbbaf40 0xa0dbf8280b6eebd0 0xffffe1e07fffff01 0xfffff8781fffffc0

def z581 : W := mkw 0x0985941b84c0f037 0x02616506e1303c0d 0x8f87981f85c0f01d 0x23e1e607e1703c07

def z582 : W := mkw 0x0127e00d5488aa00 0x0049f80355222a80 0x0807e01ff800ff01 0x0201f807fe003fc0

def z583 : W := mkw 0x0401009225beee6c 0xc1004024896fbb9b 0x2400000007fffffc 0x0900000001ffffff

def z584 : W := mkw 0x036ee00d50000000 0x00dbb80354000000 0xdbffe01ff8000001 0xf6fff807fe000000

def z585 : W := mkw 0x03fffd40059aaa00 0x00ffff500166aa80 0xffffffe007ffff03 0xfffffff801ffffc0

def z586 : W := mkw 0x84324bb4ea2d5dea 0xe10c92ed3a8b577a 0x7078e7f1fa3fffe3 0xdc1e39fc7e8ffff8

def z587 : W := mkw 0x0033490444088800 0x000cd24111022200 0xfc77599e643ccc03 0xbf1dd667990f3300

def z588 : W := mkw 0x000002a0022100c0 0x000000a800884030 0x6008e7e00223ffe3 0xd80239f80088fff8

def z589 : W := mkw 0x0bfffd5fd480f027 0x02ffff57f5203c09 0xdbfffffff800f003 0xf6fffffffe003c00

def z590 : W := mkw 0x027a694450000000 0x009e9a5114000000 0x5078e7f1f8000003 0xd41e39fc7e000000

def z591 : W := mkw 0x040100122408cc24 0xc100400489023309 0x000000000000cc00 0x0000000000003300

def z592 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x2000e011fa23ffe1 0x080038047e88fff8

def z593 : W := mkw 0x18901ffb826550ff 0x062407fee099543f 0x00001fff800000fe 0x000007ffe000003f

def z594 : W := mkw 0x04324984602c0c48 0xc10c9261180b0312 0xf4705980643c0cfe 0xbd1c1660190f033f

def z595 : W := mkw 0x1258094001160008 0x0496025000458002 0x10700000001c0000 0x041c000000070000

def z596 : W := mkw 0x0905801b8480f027 0x02416006e1203c09 0xef87801f87c0f001 0x7be1e007e1f03c00

def z597 : W := mkw 0x00000210820050a2 0x0000008420801428 0x6008e6118223ffe3 0xd80239846088fff8

def z598 : W := mkw 0x04324904400c0808 0x410c924110030202 0x10700000001c0000 0x041c000000070000

def z599 : W := mkw 0x0185941b0400c024 0x00616506c1003009 0xef879e1f8400c0ff 0x7be1e787e100303f

def z600 : W := mkw 0x01a6f40d50000000 0x0069bd0354000000 0xcb87fe1ff8000003 0x72e1ff87fe000000

def z601 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc7ffffffc3cccff 0xff1fffffff0f333f

def z602 : W := mkw 0x898496298ac13193 0x2261258a62b04c64 0x0388a6619bc33300 0x40e2299866f0ccc0

def z603 : W := mkw 0x1ad81ffb837750ff 0x06b607fee0ddd43f 0xf7f81fff87ff00fe 0xfdfe07ffe1ffc03f

def z604 : W := mkw 0x0984940900c02011 0x0261250240300804 0x0380000001c00000 0x00e0000000700000

def z605 : W := mkw 0x0248000001120000 0x0092000000448000 0x10780000003f0000 0x841e0000000fc000

def z606 : W := mkw 0x1000022003530090 0x0400008800d4c024 0x0000000003c30000 0x0000000000f0c000

def z607 : W := mkw 0x826a62b0ab3b5fe2 0xa09a98ac2aced7f8 0x7078e7f1fa3fffe3 0xdc1e39fc7e8ffff8

def z608 : W := mkw 0x83fffffdffbbffe2 0xa0ffffff7feefff8 0xffffffffffffffe3 0xfffffffffffffff8

def z609 : W := mkw 0x0080144910000000 0x0020051244000000 0x0000066198000000 0x0000019866000000

def z610 : W := mkw 0x04334984642c8c48 0xc10cd261190b2312 0xfc774180643ccc01 0xbf1dd060190f3300

def z611 : W := mkw 0x0b6fe21287dafab7 0x02dbf884a1f6bead 0xffffe00007fffffd 0xfffff80001ffffff

def z612 : W := mkw 0x83ccb6699a011182 0x20f32d9a66804460 0x0388a6619a033300 0x40e229986680ccc0

def z613 : W := mkw 0x8126e01df8005522 0xa049b8077e001548 0x0807e01ff800ff01 0x0201f807fe003fc0

def z614 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0x9fffa00007df3300 0x67ffe80001f7ccc0

def z615 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x000867f1f8230fe2 0x800219fc7e08c3f8

def z616 : W := mkw 0x041009966024446c 0xc10402659809111b 0xf470199e643c00fe 0xbd1c0667990f003f

def z617 : W := mkw 0x0104a00910000000 0x0041280244000000 0x0000a00198000000 0x0000280066000000

def z618 : W := mkw 0x0126e00d50000000 0x0049b80354000000 0x0807000e00000000 0x0201c00380000000

def z619 : W := mkw 0x043349166408cc24 0xc10cd24599023309 0xd877599e6000cc03 0xb61dd66798003300

def z620 : W := mkw 0x041009064004000c 0x4104024190010003 0x0000180e0000001c 0x0000060380000007

def z621 : W := mkw 0x826a60a0293b0f40 0xa09a98280a4ec3d0 0x107861e0783f0f00 0x841e18781e0fc3c0

def z622 : W := mkw 0x12d81f6003530090 0x04b607d800d4c024 0xd3f81fe003c30002 0xf4fe07f800f0c000

def z623 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x6008e0000223ffe1 0xd80238000088fff8

def z624 : W := mkw 0x0248000001120000 0x0092000000448000 0x97f0000005dc0000 0x25fc000001770000

def z625 : W := mkw 0x8bfffffffee1f5f7 0xa2ffffffffb87d7d 0xffffffffffe3ffff 0xfffffffffff8ffff

def z626 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0x34704180643cccfc 0x8d1c1060190f333f

def z627 : W := mkw 0x1ad91ff287f7f0ff 0x06b647fca1fdfc3f 0xf7f81fe007fff0fe 0xfdfe07f801fffc3f

def z628 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x600807e00223ffe2 0xd80201f80088fff8

def z629 : W := mkw 0x80000230aa0155a2 0xa000008c2a805568 0x0008e671fa03ff01 0x4002399c7e80ffc0

def z630 : W := mkw 0x12d81d4001560018 0x04b6075000558006 0xf7f8180007ff001c 0xfdfe060001ffc007

def z631 : W := mkw 0x0000000000000000 0x0000000000000000 0x400807e000000002 0xd00201f800000000

def z632 : W := mkw 0x037fe904459aaa00 0x00dffa411166aa80 0xfffff99e67ffff03 0xfffffe6799ffffc0

def z633 : W := mkw 0x12c816e0037300d0 0x04b205b800dcc034 0x638807e003e300e2 0xd8e201f800f8c038

def z634 : W := mkw 0x12fa7fe0037f0ad8 0x04be9ff800dfc2b6 0xf7f87fe007ff0ffe 0xfdfe1ff801ffc3ff

def z635 : W := mkw 0x03eff449159aaa00 0x00fbfd124566aa80 0xffffe6619fffff01 0xfffff99867ffffc0

def z636 : W := mkw 0x0905800b0480a005 0x02416002c1202801 0x0807000e00000000 0x0201c00380000000

def z637 : W := mkw 0x0000000000000000 0x0000000000000000 0x0008a00002033300 0x400228000080ccc0

def z638 : W := mkw 0x04010002040c880c 0x4100400081032203 0x04000000041c001c 0x0100000001070007

def z639 : W := mkw 0x0c334b96e6ecfcff 0xc30cd2e5b9bb3f3f 0xfc77599e67fcfcff 0xbf1dd66799ff3f3f

def z640 : W := mkw 0x0985960b86c0b097 0x02616582e1b02c25 0x8f879e0f87c0301c 0x63e1e783e1f00c07

def z641 : W := mkw 0x002340902428cc60 0x8008d024090a3318 0xfc774190643ccce3 0xbf1dd064190f3338

def z642 : W := mkw 0x0000022002010080 0x0000008800804020 0x0008066002030000 0x400201980080c000

def z643 : W := mkw 0x13feffed537700d8 0x04ffbffb54ddc036 0xffff1fee07ff00fe 0xffffc7fb81ffc03f

def z644 : W := mkw 0x12c8166003530090 0x04b2059800d4c024 0xe7881e6007c300fe 0x79e2079801f0c03f

def z645 : W := mkw 0x12d91fe007ffaad8 0x04b647f801ffeab6 0xf7f81fe007fffffe 0xfdfe07f801ffffff

def z646 : W := mkw 0x92d81ff0ab7755fa 0xa4b607fc2addd57e 0xf7f81ff1ffff00fe 0xfdfe07fc7fffc03f

def z647 : W := mkw 0x93fefffdfb7755fa 0xa4ffbfff7eddd57e 0xffffffffffffffff 0xffffffffffffffff

def z648 : W := mkw 0x14901ff6626544fc 0xc52407fd9899513f 0x00001ffe600000fe 0x000007ff9800003f

def z649 : W := mkw 0x0d85969ba6ecfcff 0xc36165a6e9bb3f3f 0xef879e1f87fcfcff 0x7be1e787e1ff3f3f

def z650 : W := mkw 0x800002208a011182 0x2000008822804460 0x0000000002033300 0x000000000080ccc0

def z651 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0x187fe000003fff01 0x861ff800000fffc0

def z652 : W := mkw 0x04110996642ccc6c 0xc1044265990b331b 0x2400199e643cccfe 0x09000667990f333f

def z653 : W := mkw 0x12fb5fe0077f88d8 0x04bed7f801dfe236 0xffff5fe007ffccff 0xffffd7f801fff33f

def z654 : W := mkw 0x100000a001370048 0x04000028004dc012 0x00000000003f0000 0x00000000000fc000

def z655 : W := mkw 0x09a7d61b86c8f8b7 0x0269f586e1b23e2d 0xfff7de1f87fcfcff 0xfffdf787e1ff3f3f

def z656 : W := mkw 0x8127e2b0aea9ffe2 0xa049f8ac2baa7ff8 0x680fe7f1fa23ffe3 0xda03f9fc7e88fff8

def z657 : W := mkw 0x100002a0026500d8 0x040000a800994036 0x00000000000000fc 0x000000000000003f

def z658 : W := mkw 0x0001000004008000 0x0000400001002000 0xec0700000400c001 0x3b01c00001003000

def z659 : W := mkw 0x16d81ff6637744fc 0xc5b607fd98ddd13f 0xf7f81ffe67ff00fe 0xfdfe07ff99ffc03f

def z660 : W := mkw 0x027a694450000000 0x009e9a5114000000 0x1070000000000000 0x041c000000000000

def z661 : W := mkw 0x010580000480a000 0x0041600001202800 0x8f87000005c00000 0x23e1c00001700000

def z662 : W := mkw 0x0db7dd0f44cca81d 0x436df743d1332a07 0x9ff7180e05dc001c 0x27fdc60381770007

def z663 : W := mkw 0x83fefded78210540 0xa0ffbf7b5e084150 0xdbfffffff8230f03 0xf6fffffffe08c3c0

def z664 : W := mkw 0x04334906440c880c 0x410cd24191032203 0xdc77599e641c001f 0xb71dd66799070007

def z665 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0x9ff7e00005dcff01 0x27fdf80001773fc0

def z666 : W := mkw 0x12d81de001370048 0x04b60778004dc012 0xd3f81fe0003f0002 0xf4fe07f8000fc000

def z667 : W := mkw 0x898496b9aae175f3 0xa26125ae6ab85d7c 0x6388e7f1fbe3ffe3 0xd8e239fc7ef8fff8

def z668 : W := mkw 0x12d81de001770058 0x04b60778005dc016 0x97f819e005ff001c 0xa5fe0678017fc007

def z669 : W := mkw 0x0248000000000000 0x0092000000000000 0xd3f8000000000000 0xf4fe000000000000

def z670 : W := mkw 0x000100000488aa00 0x0000400001222a80 0x000000000000ff00 0x0000000000003fc0

def z671 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0x13f807e003ff0000 0xc4fe01f800ffc000

def z672 : W := mkw 0x00801610824050b2 0x002005842090142c 0xe7809e1187c0f0ff 0x79e0278461f03c3f

def z673 : W := mkw 0x12d81fe0026500d8 0x04b607f800994036 0xd3f81fe0000000fe 0xf4fe07f80000003f

def z674 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x600041906223ffe3 0x980010641888fff8

def z675 : W := mkw 0x198596bb87f7f0ff 0x066165aee1fdfc3f 0xef879e1f87fff0ff 0x7be1e787e1fffc3f

def z676 : W := mkw 0x800002a02a2105c0 0xa00000a80a884170 0x600867e07a230fe2 0xd80219f81e88c3f8

def z677 : W := mkw 0x0023400004088800 0x0008d00001022200 0x080740000000cc01 0x0201d00000003300

def z678 : W := mkw 0x83ccb6f9ba2155e2 0xa0f32dbe6e885578 0x6388e7f1fa23ffe3 0xd8e239fc7e88fff8

def z679 : W := mkw 0x137fe9e005bfaa48 0x04dffa78016fea92 0xffffe1e007ffff01 0xfffff87801ffffc0

def z680 : W := mkw 0x12d81f6003570098 0x04b607d800d5c026 0x97f81e6007df001c 0x65fe079801f7c007

def z681 : W := mkw 0x0023400004088800 0x0008d00001022200 0xfc7fe000063fff01 0xff1ff800018fffc0

def z682 : W := mkw 0x04334bb6662dccec 0xc10cd2ed998b733b 0xfc7f5ffe663fccff 0xff1fd7ff998ff33f

def z683 : W := mkw 0x0beff40b05daaa15 0x02fbfd02c176aa85 0xfffff80e07ffff1d 0xfffffe0381ffffc7

def z684 : W := mkw 0x0000000d50000000 0x0000000354000000 0x0000001ff8000000 0x00000007fe000000

def z685 : W := mkw 0x0010098000240048 0x0004026000090012 0x10700180003c0000 0x841c0060000f0000

def z686 : W := mkw 0x008016a0026100d0 0x002005a800984034 0xe7881fe007e300fe 0xf9e207f801f8c03f

def z687 : W := mkw 0x101009e000250048 0x0404027800094012 0x000001e000000000 0x0000007800000000

def z688 : W := mkw 0x0080140000000000 0x0020050000000000 0xc3801e0000000002 0x70e0078000000000

def z689 : W := mkw 0x0bcdb61b87d2f2b7 0x02f36d86e1f4bcad 0xef8fbe1f87c3f3ff 0x7be3ef87e1f0fcff

def z690 : W := mkw 0x026b6000051a8a00 0x009ad8000146a280 0xfc7f6000043fcf01 0xbf1fd800010ff3c0

def z691 : W := mkw 0x0985969ba6e0f4f7 0x826165a6e9b83d3d 0xef87df9fe7e0fcff 0xfbe1f7e7f9f83f3f

def z692 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000e0000000ff01 0x0000380000003fc0

def z693 : W := mkw 0x07fffd4f540c880c 0x41ffff53d5032203 0x9ff7180e041c001c 0x27fdc60381070007

def z694 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0x9fff600005ff0f00 0xa7ffd800017fc3c0

def z695 : W := mkw 0x0c010292a6ecfcff 0xc30040a4a9bb3f3f 0x2400000007fcfcfc 0x0900000001ff3f3f

def z696 : W := mkw 0x8000000088001102 0x2000000022000440 0x0000a00198003300 0x0000280066000cc0

def z697 : W := mkw 0x17ffffff777fccfc 0xc5ffffffdddff33f 0xffffffffffffccff 0xfffffffffffff33f

def z698 : W := mkw 0x0022600450000000 0x0008980114000000 0x0000600078000000 0x000018001e000000

def z699 : W := mkw 0x0985940b04c0a015 0x02616502c1302805 0xcf879e1f85c0001f 0x73e1e787e1700007

def z700 : W := mkw 0x827a69e478210540 0xa09e9a791e084150 0x107861e078230f00 0x841e18781e08c3c0

def z701 : W := mkw 0x836fe2208f9bbb82 0x20dbf88823e6eee0 0xffffe6619fffff01 0xfffff99867ffffc0

def z702 : W := mkw 0x0bffff5fd7dafab7 0x02ffffd7f5f6bead 0xffffffffffffffff 0xffffffffffffffff

def z703 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0xdbf79e1f80000003 0x76fde787e0000000

def z704 : W := mkw 0x0248000001120000 0x0092000000448000 0x0388000003c30000 0x40e2000000f0c000

def z705 : W := mkw 0x07fefddf7024446c 0xc1ffbf77dc09111b 0xdbfffffff80000ff 0xf6fffffffe00003f

def z706 : W := mkw 0x00010000059aaa00 0x000040000166aa80 0x6408e00007ffff01 0xd902380001ffffc0

def z707 : W := mkw 0x04334986442c884c 0x410cd261910b2213 0x9c77198e041c00fe 0x271dc6638107003f

def z708 : W := mkw 0x127a69e451370048 0x049e9a79144dc012 0x107801e0003f0000 0x841e0078000fc000

def z709 : W := mkw 0x1126e2ad537700d8 0x0449b8ab54ddc036 0x2c07e01fffff00fd 0x0b01f807ffffc03f

def z710 : W := mkw 0x01949d4d50000000 0x0065275354000000 0x8b871ffff8000002 0x22e1c7fffe000000

def z711 : W := mkw 0x00911d4d559aaa00 0x002447535566aa80 0x24001fffffffff02 0x090007ffffffffc0

def z712 : W := mkw 0x898594ab2ce1a555 0xa261652acb386955 0x8f8f79ee7de30f1c 0xa3e3de7b9f78c3c7

def z713 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xbc77199e643cccfe 0x2f1dc667990f333f

def z714 : W := mkw 0x92d81fe02b7705d8 0xa4b607f80addc176 0xf7f81fe07fff00fe 0xfdfe07f81fffc03f

def z715 : W := mkw 0x880102b2aea1f5e7 0xa20040acaba87d79 0x200000000223ffe0 0x080000000088fff8

def z716 : W := mkw 0x12d81f4003560098 0x04b607d000d58026 0xf7f81e0007ff00fe 0xfdfe078001ffc03f

def z717 : W := mkw 0x0032490440000000 0x000c924110000000 0xd8775ffff8000003 0xb61dd7fffe000000

def z718 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef8f9fff87c0f0ff 0xfbe3e7ffe1f03c3f

def z719 : W := mkw 0x0aea761b835a5ab7 0x02ba9d86e0d696ad 0x10787e1f803f0ffe 0x841e1f87e00fc3ff

def z720 : W := mkw 0x042340166408cc24 0xc108d00599023309 0xfc77581e643cccff 0xbf1dd607990f333f

def z721 : W := mkw 0x12d81f4003560098 0x04b607d000d58026 0x97f01e0005dc00fe 0x25fc07800177003f

def z722 : W := mkw 0x11b7ffe006edaad8 0x046dfff801bb6ab6 0x0807ffe00000ffff 0x0201fff800003fff

def z723 : W := mkw 0x0185961b0640c0b4 0x00616586c190302d 0xef879e1f87c0c0ff 0x7be1e787e1f0303f

def z724 : W := mkw 0x026b6000059aaa00 0x009ad8000166aa80 0xf7f8600007ffff00 0xfdfe180001ffffc0

def z725 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xffffe1e07fffff01 0xfffff8781fffffc0

def z726 : W := mkw 0x16eb5676675bccb4 0xc5bad59d99d6f32d 0x0b8f467e63c3cc01 0x42e3d19f98f0f300

def z727 : W := mkw 0x0185941b0480e024 0x00616506c1203809 0xef879e1f87c0f0ff 0x7be1e787e1f03c3f

def z728 : W := mkw 0x12d83fe0037702d8 0x04b60ff800ddc0b6 0xf7f83fe007ff03fe 0xfdfe0ff801ffc0ff

def z729 : W := mkw 0x0927e0128488fa27 0x0249f804a1223e89 0x0807e0000000ff01 0x0201f80000003fc0

def z730 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef871e1f87c000fe 0x7be1c787e1f0003f

def z731 : W := mkw 0x07cdb4db342ccc6c 0xc1f36d36cd0b331b 0x2788a6619c3cccfc 0x49e22998670f333f

def z732 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef87fe1fffc0f0ff 0x7be1ff87fff03c3f

def z733 : W := mkw 0x0985963b86c1f0b7 0x0261658ee1b07c2d 0xef8f9e7f87c3f0ff 0x7be3e79fe1f0fc3f

def z734 : W := mkw 0x1b5d89fb85b7f06f 0x06d7627ee16dfc1b 0x187f81ff803ff001 0x861fe07fe00ffc00

def z735 : W := mkw 0x124802a0037700d8 0x049200a800ddc036 0xb7f0000007ff00fc 0x2dfc000001ffc03f

def z736 : W := mkw 0x0984960982c03093 0x0261258260b00c24 0xef879e1f87c030ff 0x7be1e787e1f00c3f

def z737 : W := mkw 0x034ca00001922200 0x00d3280000648880 0xf7f8e00007ffff01 0xfdfe380001ffffc0

def z738 : W := mkw 0x02fa5d4440000000 0x00be975110000000 0xdbfffffff8000003 0xf6fffffffe000000

def z739 : W := mkw 0x10901fe0026500d8 0x042407f800994036 0xf7f01fe007fc00fe 0xfdfc07f801ff003f

def z740 : W := mkw 0x0185960906c0a090 0x0061658241b02824 0xef879e1f87c0f0ff 0x7be1e787e1f03c3f

def z741 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc77d99e663cfcff 0xff1df667998f3f3f

def z742 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc7ffffffe3fffff 0xff1fffffff8fffff

def z743 : W := mkw 0x0bcc960983d23093 0x02f3258260f48c24 0x0388860183c33000 0x40e2218060f0cc00

def z744 : W := mkw 0x83fefffdfa2155e2 0xa0ffbfff7e885578 0xbbf7180e0223ffe0 0x2efdc6038088fff8

def z745 : W := mkw 0x0985960b86c0b097 0x02616582e1b02c25 0xef879e0f87c030fe 0x7be1e783e1f00c3f

def z746 : W := mkw 0x01b6fd4d50000000 0x006dbf5354000000 0x08071ffff8000002 0x0201c7fffe000000

def z747 : W := mkw 0x0022400440000000 0x0008900110000000 0x480fe7fff8000003 0xd203f9fffe000000

def z748 : W := mkw 0x980102b2aff7f5ff 0xa60040acabfdfd7f 0x2400000007fffffc 0x0900000001ffffff

def z749 : W := mkw 0x13ccb66913d32290 0x04f32d9a44f4c8a4 0x0388a6619bc33300 0x40e2299866f0ccc0

def z750 : W := mkw 0x03fefd4d50080800 0x00ffbf5354020200 0xdbfffffff83c0c03 0xf6fffffffe0f0300

def z751 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0xdbf75ffff8000003 0xb6fdd7fffe000000

def z752 : W := mkw 0x80000230aa0155a2 0xa000008c2a805568 0x4008e7f1fa03ff03 0xd00239fc7e80ffc0

def z753 : W := mkw 0x03dc9d4900000000 0x00f7275240000000 0xdbfffffff8000003 0xf6fffffffe000000

def z754 : W := mkw 0x9bcc96698bd33193 0x26f3259a62f4cc64 0x0388a6619bc33300 0x40e2299866f0ccc0

def z755 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f01fe005fc00fe 0xbdfc07f8017f003f

def z756 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc77df9fe43cccff 0xff1df7e7f90f333f

def z757 : W := mkw 0x13fefd4d51520010 0x04ffbf5354548004 0xdbfffffff9c00003 0xf6fffffffe700000

def z758 : W := mkw 0x867a69a4693f0f48 0xe19e9a691a4fc3d2 0x107861e0783f0f00 0x841e18781e0fc3c0

def z759 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0x187ffffff8000003 0x861ffffffe000000

def z760 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xaf879e0f87c0f0fc 0x6be1e783e1f03c3f

def z761 : W := mkw 0x167a69e4713f0c48 0xc59e9a791c4fc312 0x107861e0783f0c00 0x841e18781e0fc300

def z762 : W := mkw 0x037ee94d50000000 0x00dfba5354000000 0x587fe7fff8000003 0xd61ff9fffe000000

def z763 : W := mkw 0x00334992042cc86c 0x000cd264810b321b 0xfc77599e043cccff 0xbf1dd667810f333f

def z764 : W := mkw 0x8985963b8ec1f1b7 0x2261658ee3b07c6d 0xef8fffffffc3f3ff 0xfbe3fffffff0fcff

def z765 : W := mkw 0x12d81fe0837710da 0x04b607f820ddc436 0xf7f89fe187ff30fe 0xfdfe27f861ffcc3f

def z766 : W := mkw 0x92d81d50a956553a 0xa4b607542a55954e 0x97f0f811fddcff1d 0x25fc3e047f773fc7

def z767 : W := mkw 0x125809e001370048 0x04960278004dc012 0xf7f819e007ff00fe 0xfdfe067801ffc03f

def z768 : W := mkw 0x8985961baec0f5b7 0xa2616586ebb03d6d 0xef8fffffffc0ffff 0xfbe3fffffff03fff

def z769 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0x97f81fe005ff00fe 0xa5fe07f8017fc03f

def z770 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x2008e7e1fa23ffe0 0xc80239f87e88fff8

def z771 : W := mkw 0x003349964424c06c 0x000cd2659109301b 0xfc77599e643cc0ff 0xbf1dd667990f303f

def z772 : W := mkw 0x92d81fe02b7705d8 0xa4b607f80addc176 0xf7f8fff1ffff0fff 0xfdfe3ffc7fffc3ff

def z773 : W := mkw 0x001109120404c02c 0x000442448101300b 0xfc77181e041cc0ff 0x3f1dc6078107303f

def z774 : W := mkw 0x0881161286c0f0b7 0x02204584a1b03c2d 0xef871e1e07c0f0ff 0x7be1c78781f03c3f

def z775 : W := mkw 0x008114120440c034 0x002045048110300d 0xef87181e05c0c0ff 0x3be1c6078170303f

def z776 : W := mkw 0x12d81fe4437700d8 0x04b607f910ddc036 0xf7f81ffe67ff00fe 0xfdfe07ff99ffc03f

def z777 : W := mkw 0x03fefd4d50802000 0x00ffbf5354200800 0xdbfffffffbc03003 0xf6fffffffef00c00

def z778 : W := mkw 0x0927e01b8488fa27 0x0249f806e1223e89 0x0807801f8000f001 0x0201e007e0003c00

def z779 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0xfffffffffc0000ff 0xffffffffff00003f

def z780 : W := mkw 0x0985940b04c0a015 0x02616502c1302805 0xef87180e05c000fe 0x3be1c6038170003f

def z781 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0x1877599e603cccff 0x861dd667980f333f

def z782 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xffff1ffe07ff00ff 0xffffc7ff81ffc03f

def z783 : W := mkw 0x127a49e441370048 0x049e9279104dc012 0x107841e0603f0000 0x841e1078180fc000

def z784 : W := mkw 0x0927c01b8488f827 0x0249f006e1223e09 0x0807c01f8000fc01 0x0201f007e0003f00

def z785 : W := mkw 0x03fefd4d51120200 0x00ffbf5354448080 0xdbfffffff8030303 0xf6fffffffe00c0c0

def z786 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0x1bffe7fff8000001 0xc6fff9fffe000000

def z787 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xdc77599e641c00ff 0xb71dd6679907003f

def z788 : W := mkw 0x03eef40900000000 0x00fbbd0240000000 0xdbfffffff8000003 0xf6fffffffe000000

def z789 : W := mkw 0x0127e0120488ea24 0x0049f80481223a89 0x0807e01e0000ff01 0x0201f80780003fc0

def z790 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0x9c77180e041c00fc 0x271dc6038107003f

def z791 : W := mkw 0x00901fa0026500d8 0x002407e800994036 0xf7f81fe007ff00fe 0xfdfe07f801ffc03f

def z792 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xbff7e00007ffff01 0x2ffdf80001ffffc0

def z793 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef87980e07c0f0fd 0x7be1e60381f03c3f

def z794 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0xdbfffffff800ff03 0xf6fffffffe003fc0

def z795 : W := mkw 0x0985965b96c0f0b7 0x02616596e5b03c2d 0xef879e7f9fc0f0ff 0x7be1e79fe7f03c3f

def z796 : W := mkw 0x0985941b04c0e035 0x02616506c130380d 0xaf87180e05c0c0fc 0x2be1c6038170303f

def z797 : W := mkw 0x8927e01bac88ff27 0xa249f806eb223fc9 0x0807e01ff800ff01 0x0201f807fe003fc0

def z798 : W := mkw 0x041109966424c46c 0xc10442659909311b 0xfc77199e643cc0ff 0xbf1dc667990f303f

def z799 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef8f9e1f87e3f0ff 0xfbe3e787e1f8fc3f

def z800 : W := mkw 0x067a6984613e0e48 0xc19e9a61184f8392 0x10704180603c0c00 0x841c1060180f0300

def z801 : W := mkw 0x02d81fc0026400d8 0x00b607f000990036 0xf7f81fe007fc00fe 0xfdfe07f801ff003f

def z802 : W := mkw 0x12d81f6003570098 0x04b607d800d5c026 0xf7f81e6007df00fe 0x7dfe079801f7c03f

def z803 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0x8f87180e05c000fc 0x23e1c6038170003f

def z804 : W := mkw 0x02d81f80037600d8 0x00b607e000dd8036 0xf7f81f8007ff00fe 0xfdfe07e001ffc03f

def z805 : W := mkw 0x12d81fc0037600d8 0x04b607f000dd8036 0xf7f01f8007fc00fe 0xfdfc07e001ff003f

def z806 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f8fff1ffffffff 0xfdfe3ffc7fffffff

def z807 : W := mkw 0x12d81fe9037700d8 0x04b607fa40ddc036 0xf7f81fff87ff00fe 0xfdfe07ffe1ffc03f

def z808 : W := mkw 0x836fe2b0afbbffe2 0xa0dbf8ac2beefff8 0x9ff707f1fddc00e2 0x27fdc1fc7f770038

def z809 : W := mkw 0x13ccb66913530090 0x04f32d9a44d4c024 0x0388066003c30000 0x40e2019800f0c000

def z810 : W := mkw 0x12c816e0037700d8 0x04b205b800ddc036 0xf7f8066007ff00fc 0xfdfe019801ffc03f

def z811 : W := mkw 0x0881161b8640d0b7 0x02204586e190342d 0xef871e1f87c0c0ff 0x7be1c787e1f0303f

def z812 : W := mkw 0x010580120480e024 0x0041600481203809 0xef87181e05c0c0ff 0x3be1c6078170303f

def z813 : W := mkw 0x04334996442cc86c 0x410cd265910b321b 0xfc77199e043cc0ff 0xbf1dc667810f303f

def z814 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xfffff81e07ffff03 0xfffffe0781ffffc0

def z815 : W := mkw 0x03eef44d50000000 0x00fbbd1354000000 0x4b8fe7fff8000003 0xd2e3f9fffe000000

def z816 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xfff79e1f87fcf0ff 0xfffde787e1ff3c3f

def z817 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xfff7800007ffff01 0x7ffde00001ffffc0

def z818 : W := mkw 0x13fefd4d50440018 0x04ffbf5354110006 0xdbfffffff800001f 0xf6fffffffe000007

def z819 : W := mkw 0x02490000059aaa00 0x009240000166aa80 0xb7f0000007ffff00 0x2dfc000001ffffc0

def z820 : W := mkw 0x0527c0166488ec24 0xc149f00599223b09 0x0807c01e6000fc01 0x0201f00798003f00

def z821 : W := mkw 0x92d81fe0ab7715da 0xa4b607f82addc576 0xf7f8ffe1ffff3ffe 0xfdfe3ff87fffcfff

def z822 : W := mkw 0x0985961b86c8fab7 0x02616586e1b23ead 0xef879e1f87c0ffff 0x7be1e787e1f03fff

def z823 : W := mkw 0x00901f0002440098 0x002407c000910026 0xf7f01e0007dc00fe 0x7dfc078001f7003f

def z824 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f8bfe007ff33fe 0xfdfe2ff801ffccff

def z825 : W := mkw 0x0a7b6b56d6c0f0b7 0x029edad5b5b03c2d 0x347861e07fc0f0fc 0x8d1e18781ff03c3f

def z826 : W := mkw 0x067a69c4713e0e48 0xc19e9a711c4f8392 0x107861e0783f0f00 0x841e18781e0fc3c0

def z827 : W := mkw 0x01b6fd4d50000000 0x006dbf5354000000 0x480ffffff8000003 0xd203fffffe000000

def z828 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc77f99ffc3cccff 0xbf1dfe67ff0f333f

def z829 : W := mkw 0x12d81fe0237704d8 0x84b607f808ddc136 0xf7f85fe067ff0cfe 0xfdfe17f819ffc33f

def z830 : W := mkw 0x07fefd4d500c0808 0x41ffbf5354030202 0xdbfffffff81c0003 0xf6fffffffe070000

def z831 : W := mkw 0x0bfefd4d50c02011 0x02ffbf5354300804 0xdbfffffff9c00003 0xf6fffffffe700000

def z832 : W := mkw 0x03fefd4d511a0a00 0x00ffbf5354468280 0xffffffffffff0f03 0xffffffffffffc3c0

def z833 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0x9c77599e643c0cfe 0xa71dd667990f033f

def z834 : W := mkw 0x10901fa0037700d8 0x042407e800ddc036 0xf7f01f8007ff00fe 0xfdfc07e001ffc03f

def z835 : W := mkw 0x03fefd4d51120000 0x00ffbf5354448000 0xdbfffffffbc30003 0xf6fffffffef0c000

def z836 : W := mkw 0x04334996e42cdc6e 0xc10cd265b90b371b 0xfc77d99fe43cfcff 0xbf1df667f90f3f3f

def z837 : W := mkw 0x8d27c01fec88fd27 0xe349f007fb223f49 0x0807e01ff800ff01 0x0201f807fe003fc0

def z838 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc775ffffc3cccff 0xbf1dd7ffff0f333f

def z839 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f89fe007fff0ff 0xfdfe27f801fffc3f

def z840 : W := mkw 0x04336996642cce6c 0xc10cda65990b339b 0xfc77799e643ccfff 0xbf1dde67990f33ff

def z841 : W := mkw 0x04324984602c0c48 0xc10c9261180b0312 0xfc77599e643c0cff 0xbf1dd667990f033f

def z842 : W := mkw 0x12d81f4003560098 0x04b607d000d58026 0xb7f0180007dc00fc 0x2dfc060001f7003f

def z843 : W := mkw 0x0d27c01f6488ec25 0xc349f007d9223b09 0x0807401e6000cc01 0x0201d00798003300

def z844 : W := mkw 0x04334986442c884c 0x410cd261910b2213 0xfc77598e043cccff 0xbf1dd663810f333f

def z845 : W := mkw 0x0126e00d50000000 0x0049b80354000000 0x0807e7fff8000003 0x0201f9fffe000000

def z846 : W := mkw 0x1bccb66993d33093 0x06f32d9a64f4cc24 0x0388a6619bc33000 0x40e2299866f0cc00

def z847 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef879e1f87e3ffff 0x7be1e787e1f8ffff

def z848 : W := mkw 0x043349d6742ccc6c 0xc10cd2759d0b331b 0xfc7759fe7c3cccff 0xbf1dd67f9f0f333f

def z849 : W := mkw 0x01b6dd4d50000000 0x006db75354000000 0xdbf7dffff8000003 0xf6fdf7fffe000000

def z850 : W := mkw 0x01b6fd4d50000000 0x006dbf5354000000 0xd877fffff8000003 0xb61dfffffe000000

def z851 : W := mkw 0x000100120400c024 0x0000400481003009 0xef87181e07c0c0ff 0x7be1c60781f0303f

def z852 : W := mkw 0x036fe00d559aaa00 0x00dbf8035566aa80 0xffffe7ffffffff03 0xfffff9ffffffffc0

def z853 : W := mkw 0x92d81fe00b7701d8 0x24b607f802ddc076 0xf7f83fe01fff03fe 0xfdfe0ff807ffc0ff

def z854 : W := mkw 0x008116128640d0b6 0x00204584a190342d 0xef879e1f87c0f0ff 0x7be1e787e1f03c3f

def z855 : W := mkw 0x03fefd4d50802200 0x00ffbf5354200880 0xdbfffffff8003303 0xf6fffffffe000cc0

def z856 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xffffe7e007ffff03 0xfffff9f801ffffc0

def z857 : W := mkw 0x075ca99661b6666c 0xc1d72a65986d999b 0x0388b99e63c333fe 0x40e22e6798f0ccff

def z858 : W := mkw 0x04334916440cc82c 0x410cd2459103320b 0xbc77180e041cc0fc 0x2f1dc6038107303f

def z859 : W := mkw 0x076fe006459aaa04 0x41dbf8019166aa81 0xffffe00e07ffff01 0xfffff80381ffffc0

def z860 : W := mkw 0x167a49c4613e0c48 0xc59e9271184f8312 0x10704180603c0c00 0x841c1060180f0300

def z861 : W := mkw 0x843349b66c2dcd6c 0xe10cd26d9b0b735b 0xfc77599e643fcfff 0xbf1dd667990ff3ff

def z862 : W := mkw 0x90901ff0aa6555fa 0xa42407fc2a99557e 0x00001fe0000000fe 0x000007f80000003f

def z863 : W := mkw 0x0db6df8de2ec3cdb 0xc36db7e378bb0f36 0x13f0c781e3fc3c00 0xc4fc31e078ff0f00

def z864 : W := mkw 0x043349b6642dcc6c 0xc10cd26d990b731b 0xfc7f59fe643fccff 0xbf1fd67f990ff33f

def z865 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f01fe007dc00fe 0x7dfc07f801f7003f

def z866 : W := mkw 0x0080160002400090 0x0020058000900024 0xef871e1e07c000ff 0x7be1c78781f0003f

def z867 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f81fe007fffffe 0xfdfe07f801ffffff

def z868 : W := mkw 0x02fa7d4d50000000 0x00be9f5354000000 0xd87f7ffff8000003 0xb61fdffffe000000

def z869 : W := mkw 0x02fa5d4d50000000 0x00be975354000000 0xdbff5ffff8000003 0xf6ffd7fffe000000

def z870 : W := mkw 0x92d81fe08b7711da 0x24b607f822ddc476 0xf7f8fff1ffff33ff 0xfdfe3ffc7fffccff

def z871 : W := mkw 0x167a49e4413f0848 0x459e9279104fc212 0x107801e0003f0000 0x841e0078000fc000

def z872 : W := mkw 0x8985961baec0f5b7 0xa2616586ebb03d6d 0xef8ffe1fffe3ffff 0xfbe3ff87fff8ffff

def z873 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef8fbe1f87c3f3ff 0x7be3ef87e1f0fcff

def z874 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc7f5ffe643cccff 0xff1fd7ff990f333f

def z875 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0x97f81fe007df00fe 0x65fe07f801f7c03f

def z876 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0x9c77599e641cccff 0x271dd6679907333f

def z877 : W := mkw 0x0527e01f7488ee24 0xc149f807dd223b89 0x0807e01ff800ff01 0x0201f807fe003fc0

def z878 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xffffe6619fffff01 0xfffff99867ffffc0

def z879 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xb7f819e007ff00fc 0xadfe067801ffc03f

def z880 : W := mkw 0x8c0102b2aeedfdff 0xe30040acabbb7f7f 0x2400000007fffffc 0x0900000001ffffff

def z881 : W := mkw 0x13fefd4d51160008 0x04ffbf5354458002 0xdbfffffff81c0003 0xf6fffffffe070000

def z882 : W := mkw 0x98901ffbaa6555ff 0xa62407feea99557f 0x00001ffff80000fe 0x000007fffe00003f

def z883 : W := mkw 0x0000000000000000 0x0000000000000000 0xc80ffffff8000003 0xf203fffffe000000

def z884 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc77181e043cccff 0x3f1dc607810f333f

def z885 : W := mkw 0x0000009020204460 0x8000002408081118 0x6008e7f1fa23ffe3 0xd80239fc7e88fff8

def z886 : W := mkw 0x04336996742ccc6c 0xc10cda659d0b331b 0xfc77799e7c3cccff 0xbf1dde679f0f333f

def z887 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x0008e7f1fa03ffe3 0x400239fc7e80fff8

def z888 : W := mkw 0x143349f6642dcc6c 0xc50cd27d990b731b 0xfc7759fe643cccff 0xbf1dd67f990f333f

def z889 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0x8f879e1f85c0f0ff 0x23e1e787e1703c3f

def z890 : W := mkw 0x0127c0000488a800 0x0049f00001222a00 0xffffe00007ffff01 0xfffff80001ffffc0

def z891 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc77580e043cccfd 0xbf1dd603810f333f

def z892 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef879fffffc0f0ff 0x7be1e7fffff03c3f

def z893 : W := mkw 0x8bccb6298bd33393 0x22f32d8a62f4cce4 0x0388a6619bc33300 0x40e2299866f0ccc0

def z894 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xbfff600007ffff00 0xafffd80001ffffc0

def z895 : W := mkw 0x0527e0166488ee24 0xc149f80599223b89 0x0807401e6000cc01 0x0201d00798003300

def z896 : W := mkw 0x04334906440c880c 0x410cd24191032203 0xfc77180e041c00fe 0x3f1dc6038107003f

def z897 : W := mkw 0x800002208a011182 0x2000008822804460 0x6008e7f1fa23ff03 0xd80239fc7e88ffc0

def z898 : W := mkw 0x0185961206c0e0b4 0x0061658481b0382d 0xef879e1e07c0f0ff 0x7be1e78781f03c3f

def z899 : W := mkw 0x01949d4d50000000 0x0065275354000000 0x08079ffff8000003 0x0201e7fffe000000

def z900 : W := mkw 0x843349966c2ccd6c 0xe10cd2659b0b335b 0xfc77799e7c3ccfff 0xbf1dde679f0f33ff

def z901 : W := mkw 0x02580ba0033700c8 0x009602e800cdc032 0xf7f81fe007ff00fe 0xfdfe07f801ffc03f

def z902 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f85fe007ffccff 0xfdfe17f801fff33f

def z903 : W := mkw 0x036fe002059aaa04 0x00dbf8008166aa81 0xfffff80e07ffff1d 0xfffffe0381ffffc7

def z904 : W := mkw 0x00000210820050a2 0x0000008420801428 0x6008e7f1fa23ffe3 0xd80239fc7e88fff8

def z905 : W := mkw 0x92d81fe08b7711da 0x24b607f822ddc476 0xf7f8ffe19fffffff 0xfdfe3ff867ffffff

def z906 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xb7f81e6007ff00fc 0x6dfe079801ffc03f

def z907 : W := mkw 0x0927e01fd488fa27 0x0249f807f5223e89 0x0807e01ff800ff01 0x0201f807fe003fc0

def z908 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc7f799e643fcfff 0xbf1fde67990ff3ff

def z909 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xffffe19067ffff03 0xfffff86419ffffc0

def z910 : W := mkw 0x036fe00d559aaa00 0x00dbf8035566aa80 0xffffe00e07ffff01 0xfffff80381ffffc0

def z911 : W := mkw 0x843349b66c2dcd6c 0xe10cd26d9b0b735b 0xfc7ff9fe7e3fffff 0xff1ffe7f9f8fffff

def z912 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f85ff067ff00ff 0xfdfe17fc19ffc03f

def z913 : W := mkw 0x167a69e4613f0e48 0xc59e9a79184fc392 0x107861e0603f0f00 0x841e1878180fc3c0

def z914 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0xffffffffffc00003 0xfffffffffff00000

def z915 : W := mkw 0x8985961baec0f5b7 0xa2616586ebb03d6d 0xef879e1fffc0f0ff 0x7be1e787fff03c3f

def z916 : W := mkw 0x034d8000059aaa00 0x00d360000166aa80 0xffff800007ffff01 0xffffe00001ffffc0

def z917 : W := mkw 0x84334996ec2cdd6e 0xe10cd265bb0b375b 0xfc7ffffffc3cffff 0xff1fffffff0f3fff

def z918 : W := mkw 0x12d81f4003560098 0x04b607d000d58026 0xf7f81fe007dc00fe 0xfdfe07f801f7003f

def z919 : W := mkw 0x0985961ba6c0f4b7 0x82616586e9b03d2d 0xef87de1fe7c0fcff 0x7be1f787f9f03f3f

def z920 : W := mkw 0x0985960b06c0a095 0x02616582c1b02825 0xaf87180e07c000fc 0x2be1c60381f0003f

def z921 : W := mkw 0x0081160206408094 0x0020458081902025 0xef871e0e07c000fe 0x7be1c78381f0003f

def z922 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfff7599e67fcccff 0xfffdd66799ff333f

def z923 : W := mkw 0x90901ffdfa6555fa 0xa42407ff7e99557e 0x00001ffff80000fe 0x000007fffe00003f

def z924 : W := mkw 0x0104800900000000 0x0041200240000000 0x480fe7fff8000003 0xd203f9fffe000000

def z925 : W := mkw 0x12d81d4001560018 0x04b6075000558006 0xf7f0180005dc00fe 0x3dfc06000177003f

def z926 : W := mkw 0x1bcc964983d23093 0x06f3259260f48c24 0x0380860183c03000 0x40e0218060f00c00

def z927 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc7f79fe7c3cccff 0xbf1fde7f9f0f333f

def z928 : W := mkw 0x03fefd4d51120000 0x00ffbf5354448000 0xdffffffffddc0003 0xf7ffffffff770000

def z929 : W := mkw 0x80000010a8005522 0xa00000042a001548 0x6008e7f1fa23ff03 0xd80239fc7e88ffc0

def z930 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0x0b8ffffff8000003 0x42e3fffffe000000

def z931 : W := mkw 0x02d81dc001360048 0x00b60770004d8012 0xf7f81fe007ff00fe 0xfdfe07f801ffc03f

def z932 : W := mkw 0x84334996ec2cdd6e 0xe10cd265bb0b375b 0xfc7ff99ffe3fffff 0xff1ffe67ff8fffff

def z933 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xffffe011ffffff01 0xfffff8047fffffc0

def z934 : W := mkw 0x0080160002400090 0x0020058000900024 0xf7f01e0007fc00fe 0xfdfc078001ff003f

def z935 : W := mkw 0x0433499664acec6c 0xc10cd265992b3b1b 0xfc77599e67fcfcff 0xbf1dd66799ff3f3f

def z936 : W := mkw 0x04334986442c884c 0x410cd261910b2213 0xfc77599e643c00ff 0xbf1dd667990f003f

def z937 : W := mkw 0x036ee000019a2a00 0x00dbb80000668a80 0x73f8e00003ffff01 0xdcfe380000ffffc0

def z938 : W := mkw 0x04334986442c884c 0x410cd261910b2213 0xbc77180e043c00fc 0x2f1dc603810f003f

def z939 : W := mkw 0x00b25d4d50000000 0x002c975354000000 0xd87ffffff8000003 0xf61ffffffe000000

def z940 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xaf87981f87c0f0fd 0x2be1e607e1f03c3f

def z941 : W := mkw 0x002340120408c824 0x0008d00481023209 0xfc77181e041cc0ff 0x3f1dc6078107303f

def z942 : W := mkw 0x000002a0022100c0 0x000000a800884030 0x6008e7f1fa23ffe3 0xd80239fc7e88fff8

def z943 : W := mkw 0x0985b61b86c0f2b7 0x02616d86e1b03cad 0xef87be1f87c0f3ff 0x7be1ef87e1f03cff

def z944 : W := mkw 0x12d81fe4537700d8 0x04b607f914ddc036 0xf7f81fe07fff00fe 0xfdfe07f81fffc03f

def z945 : W := mkw 0x840102b2ae2dddee 0xe10040acab8b777b 0x24000000043cccfc 0x09000000010f333f

def z946 : W := mkw 0x04234092242ccc6c 0xc108d024890b331b 0xfc77581e043cccff 0xbf1dd607810f333f

def z947 : W := mkw 0x1985967b86c1f0b7 0x0661659ee1b07c2d 0xef879e7f87c0f0ff 0x7be1e79fe1f03c3f

def z948 : W := mkw 0x0bccb60983d23293 0x02f32d8260f48ca4 0x0380860183c03000 0x40e0218060f00c00

def z949 : W := mkw 0x034da000059aaa00 0x00d368000166aa80 0xf7f8a00007ffff00 0xfdfe280001ffffc0

def z950 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef87fe1f87c0ffff 0x7be1ff87e1f03fff

def z951 : W := mkw 0x800102b2ae21d5e6 0xa00040acab887579 0x240000000623fffc 0x090000000188ffff

def z952 : W := mkw 0x0985941b04c0e035 0x02616506c130380d 0xef879e1f85c0c0ff 0x7be1e787e170303f

def z953 : W := mkw 0x00901d8000640058 0x0024076000190016 0xf7f0198005fc00fe 0xbdfc0660017f003f

def z954 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xcf879e1f85c000ff 0x73e1e787e170003f

def z955 : W := mkw 0x12d81de001770058 0x04b60778005dc016 0xf7f819e005ff00fe 0xbdfe0678017fc03f

def z956 : W := mkw 0x92d81fe08b7711da 0x24b607f822ddc476 0xf7f81fe19fff00fe 0xfdfe07f867ffc03f

def z957 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0xdbfffffff8230f03 0xf6fffffffe08c3c0

def z958 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc7f599e663fccff 0xff1fd667998ff33f

def z959 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef871e0e07c0f0fe 0x7be1c78381f03c3f

def z960 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0xfbfffffffa230003 0xfefffffffe88c000

def z961 : W := mkw 0x04334916440cc82c 0x410cd2459103320b 0xfc77599e641cc0ff 0xbf1dd6679907303f

def z962 : W := mkw 0x0985961b86c8f8b7 0x02616586e1b23e2d 0xef879e1f87fcfcff 0x7be1e787e1ff3f3f

def z963 : W := mkw 0x0985961b06c0e0b5 0x02616586c1b0382d 0xef871e1e07c0c0ff 0x7be1c78781f0303f

def z964 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc7ff99e643cccff 0xff1ffe67990f333f

def z965 : W := mkw 0x12d81fe9137700d8 0x04b607fa44ddc036 0xf7f81fe19fff00fe 0xfdfe07f867ffc03f

def z966 : W := mkw 0x0032499460244468 0x800c92651809111a 0xfc77599e643cccff 0xbf1dd667990f333f

def z967 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0xe408fff1fe23ffff 0xf9023ffc7f88ffff

def z968 : W := mkw 0x0985960b06c0a095 0x02616582c1b02825 0xef879e0e07c0f0ff 0x7be1e78381f03c3f

def z969 : W := mkw 0x8985963b8ec1f1b7 0x2261658ee3b07c6d 0xef879e1f87c3f3ff 0x7be1e787e1f0fcff

def z970 : W := mkw 0x800002b0aa2555ea 0xa00000ac2a89557a 0x6408e7f1fe3fffff 0xd90239fc7f8fffff

def z971 : W := mkw 0x00901d4d50000000 0x0024075354000000 0xc8071ffff8000003 0x3201c7fffe000000

def z972 : W := mkw 0x84334b26ce0d998e 0x610cd2c9b3836663 0x9c7fbe6f9e1f331c 0x671fef9be787ccc7

def z973 : W := mkw 0x880002b2aa6155f7 0xa20000acaa98557d 0x6008e7f1fa23ffff 0xd80239fc7e88ffff

def z974 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f89ff187ff00ff 0xfdfe27fc61ffc03f

def z975 : W := mkw 0x07fffd4f559eaa0c 0x41ffff53d567aa83 0x9ff7180e05dc001c 0x27fdc60381770007

def z976 : W := mkw 0x0bccb64993d23293 0x02f32d9264f48ca4 0x0388a6619bc33300 0x40e2299866f0ccc0

def z977 : W := mkw 0x026b4000051a8800 0x009ad0000146a200 0xffffe00007ffff01 0xfffff80001ffffc0

def z978 : W := mkw 0x03fefd4d51120000 0x00ffbf5354448000 0xdbfffffff83f0003 0xf6fffffffe0fc000

def z979 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f8bfe19fff00fe 0xfdfe2ff867ffc03f

def z980 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f8ffe007ff00ff 0xfdfe3ff801ffc03f

def z981 : W := mkw 0x1bccb66983d33293 0x06f32d9a60f4cca4 0x0388a66183c33300 0x40e2299860f0ccc0

def z982 : W := mkw 0x0985960b06c0a095 0x02616582c1b02825 0x8f871e0e05c000fe 0x23e1c7838170003f

def z983 : W := mkw 0x840002b2aa2555ee 0xe10000acaa89557b 0x6008e7f1fa23ffff 0xd80239fc7e88ffff

def z984 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0x0b879e1f83c0f0ff 0x42e1e787e0f03c3f

def z985 : W := mkw 0x01b6fd4d50000000 0x006dbf5354000000 0xcb87fffff8000003 0x72e1fffffe000000

def z986 : W := mkw 0x1bcc966903d32091 0x06f3259a40f4c824 0x0388066003c30000 0x40e2019800f0c000

def z987 : W := mkw 0x010582128680f0a6 0x00416084a1a03c29 0xef879e1f87c0f0ff 0x7be1e787e1f03c3f

def z988 : W := mkw 0x12d81fed537700d8 0x04b607fb54ddc036 0xf7f8ffffffff00ff 0xfdfe3fffffffc03f

def z989 : W := mkw 0x01849619824050b2 0x006125866090142c 0xef879e1f87c0f0ff 0x7be1e787e1f03c3f

def z990 : W := mkw 0x0bfffd4f55daaa15 0x02ffff53d576aa85 0x9ff7180e05dc001c 0x27fdc60381770007

def z991 : W := mkw 0x800000a028210540 0xa00000280a084150 0x6008e7f1fa23ff03 0xd80239fc7e88ffc0

def z992 : W := mkw 0x12580ba0037700d8 0x049602e800ddc036 0xf7f8198007ff00fe 0xfdfe066001ffc03f

def z993 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc77198e043cccfe 0xbf1dc663810f333f

def z994 : W := mkw 0x12d81dc001760058 0x04b60770005d8016 0xf7f8198007ff00fe 0xfdfe066001ffc03f

def z995 : W := mkw 0x036ee00001120000 0x00dbb80000448000 0xffffe00007ffff01 0xfffff80001ffffc0

def z996 : W := mkw 0x12d81dc001760058 0x04b60770005d8016 0x97f0198005dc00fe 0x25fc06600177003f

def z997 : W := mkw 0x880102b2aee1f5f7 0xa20040acabb87d7d 0x2400000007c0f0fc 0x0900000001f03c3f

def z998 : W := mkw 0x8985963baec1f5b7 0xa261658eebb07d6d 0xef8ffe7fffc3ffff 0x7be3ff9ffff0ffff

def z999 : W := mkw 0x001109922424c46c 0x800442648909311b 0xfc77599e643cccff 0xbf1dd667990f333f

def z1000 : W := mkw 0x02c816a0037300d0 0x00b205a800dcc034 0xf7f81fe007ff00fe 0xfdfe07f801ffc03f

def z1001 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef87de1f87e0fcff 0xfbe1f787e1f83f3f

def z1002 : W := mkw 0x843349b66c2dcd6c 0xe10cd26d9b0b735b 0xfc7759fe7c3cccff 0xbf1dd67f9f0f333f

def z1003 : W := mkw 0x03fefd4d50080a00 0x00ffbf5354020280 0xdbfffffff8000f03 0xf6fffffffe0003c0

def z1004 : W := mkw 0x000100120400c024 0x0000400481003009 0xfc77181e043cc0ff 0xbf1dc607810f303f

def z1005 : W := mkw 0x026a6000011a0a00 0x009a980000468280 0xf7f8e00007ffff01 0xfdfe380001ffffc0

def z1006 : W := mkw 0x8527e016ec88ff26 0xe149f805bb223fc9 0x0807e01ff800ff01 0x0201f807fe003fc0

def z1007 : W := mkw 0x12580be0037700d8 0x049602f800ddc036 0xf7f801e007ff00fc 0xfdfe007801ffc03f

def z1008 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f87fe007ff0ffe 0xfdfe1ff801ffc3ff

def z1009 : W := mkw 0x036ee00d50000000 0x00dbb80354000000 0xdbffe7fff8000003 0xf6fff9fffe000000

def z1010 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0x8f879e1f87c030fe 0x63e1e787e1f00c3f

def z1011 : W := mkw 0x0d85961ba6c8fcb7 0xc3616586e9b23f2d 0xef879e1f87c0fcff 0x7be1e787e1f03f3f

def z1012 : W := mkw 0x0985b61b96c0f0b7 0x02616d86e5b03c2d 0xef87be1f9fc0f0ff 0x7be1ef87e7f03c3f

def z1013 : W := mkw 0x0984961b824050b7 0x02612586e090142d 0xef879e1f87c000ff 0x7be1e787e1f0003f

def z1014 : W := mkw 0x03fefd4d51922200 0x00ffbf5354648880 0xdbfffffff9c00003 0xf6fffffffe700000

def z1015 : W := mkw 0x03fefd4d511a0a00 0x00ffbf5354468280 0xdbfffffff81c0003 0xf6fffffffe070000

def z1016 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xb7f01fe007ff00fe 0x2dfc07f801ffc03f

def z1017 : W := mkw 0x0248000001120000 0x0092000000448000 0xf7f8000007ffff00 0xfdfe000001ffffc0

def z1018 : W := mkw 0x84334996ec2cdd6e 0xe10cd265bb0b375b 0xfc77599ffc3cccff 0xbf1dd667ff0f333f

def z1019 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef8fffffffe3ffff 0xfbe3fffffff8ffff

def z1020 : W := mkw 0x0010098000240048 0x0004026000090012 0xf7f0198007fc00fe 0xfdfc066001ff003f

def z1021 : W := mkw 0x8985961b8ec0f1b7 0x22616586e3b03c6d 0xef87be1f9fc0f3ff 0x7be1ef87e7f03cff

def z1022 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef8ffe1f87c0f0ff 0xfbe3ff87e1f03c3f

def z1023 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f81ff1ffff00fe 0xfdfe07fc7fffc03f

def z1024 : W := mkw 0x00b25d4d50000000 0x002c975354000000 0x98771ffff8000002 0x261dc7fffe000000

def z1025 : W := mkw 0x03ccb44910000000 0x00f32d1244000000 0xcb8ffffff8000003 0xf2e3fffffe000000

def z1026 : W := mkw 0x92d81fe02b7705d8 0xa4b607f80addc176 0xf7f81fe007ff0ffe 0xfdfe07f801ffc3ff

def z1027 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0x9bffbffff8000002 0x66ffeffffe000000

def z1028 : W := mkw 0x0985941b04c0e035 0x02616506c130380d 0xef87981e07c0f0ff 0x7be1e60781f03c3f

def z1029 : W := mkw 0x02c8160003520090 0x00b2058000d48024 0xf7f01e0007dc00fe 0x7dfc078001f7003f

def z1030 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f87fe07fff00fe 0xfdfe1ff81fffc03f

def z1031 : W := mkw 0x800002b0aa6155f2 0xa00000ac2a98557c 0x6408e7f1ffe3ffff 0xd90239fc7ff8ffff

def z1032 : W := mkw 0x0032498440240048 0x000c926110090012 0xfc77198e043c00fe 0xbf1dc663810f003f

def z1033 : W := mkw 0x03fefd4d51922200 0x00ffbf5354648880 0xfbfffffffbe3ff03 0xfefffffffef8ffc0

def z1034 : W := mkw 0x03fefd4d511a0a00 0x00ffbf5354468280 0xfbfffffffa3fff03 0xfefffffffe8fffc0

def z1035 : W := mkw 0x0985941b04c0e035 0x02616506c130380d 0x8f87181e05c000fe 0x23e1c6078170003f

def z1036 : W := mkw 0x12d81dc001760058 0x04b60770005d8016 0xb7f0180005fc00fc 0x2dfc0600017f003f

def z1037 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xffff000007ffff00 0xffffc00001ffffc0

def z1038 : W := mkw 0x067a4984613e0c48 0xc19e9261184f8312 0x10784180603f0c00 0x841e1060180fc300

def z1039 : W := mkw 0x04334916640ccc2c 0xc10cd2459903330b 0xfc77581e641cccff 0x3f1dd6079907333f

def z1040 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xfff7400007ffff01 0xbffdd00001ffffc0

def z1041 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xffffe61187ffff03 0xfffff98461ffffc0

def z1042 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x0008e7f1f823ffe3 0x800239fc7e08fff8

def z1043 : W := mkw 0x04334916440cc82c 0x410cd2459103320b 0x9c77181e041c00fe 0x271dc6078107003f

def z1044 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0x97f0180005dc00fc 0x25fc06000177003f

def z1045 : W := mkw 0x0c334996e4acfc6f 0xc30cd265b92b3f1b 0xfc77599e643cfcff 0xbf1dd667990f3f3f

def z1046 : W := mkw 0x8c901fbfea6555ff 0xe32407effa99557f 0x00001ffff80000fe 0x000007fffe00003f

def z1047 : W := mkw 0x034d80000592a000 0x00d360000164a800 0xffffe00007ffff01 0xfffff80001ffffc0

def z1048 : W := mkw 0x12d81fed537700d8 0x04b607fb54ddc036 0xf7f81fee07ff00fe 0xfdfe07fb81ffc03f

def z1049 : W := mkw 0x0248000001120000 0x0092000000448000 0xf7f8180007ff00fe 0xfdfe060001ffc03f

def z1050 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xd7f81fe005dc00fe 0xf5fe07f80177003f

def z1051 : W := mkw 0x002340922428cc64 0x8008d024890a3319 0xfc77599e643cccff 0xbf1dd667990f333f

def z1052 : W := mkw 0x12c8166003530090 0x04b2059800d4c024 0xf7f81e6007ff00fe 0xfdfe079801ffc03f

def z1053 : W := mkw 0x00334984442c8848 0x000cd261110b2212 0xfc77599e643cccff 0xbf1dd667990f333f

def z1054 : W := mkw 0x0248008001360048 0x00920020004d8012 0xf7f8000007ff00fc 0xfdfe000001ffc03f

def z1055 : W := mkw 0x940102b2af7fddfe 0xe50040acabdff77f 0x2400000007fffffc 0x0900000001ffffff

def z1056 : W := mkw 0x001109820424804c 0x0004426081092013 0xfc77198e043c00fe 0xbf1dc663810f003f

def z1057 : W := mkw 0x036fe009059aaa00 0x00dbf8024166aa80 0xffffe01f87ffff01 0xfffff807e1ffffc0

def z1058 : W := mkw 0x02490000059aaa00 0x009240000166aa80 0xf7f8e00007ffff01 0xfdfe380001ffffc0

def z1059 : W := mkw 0x0136e90d50000000 0x004dba4354000000 0xd87ffffff8000003 0xf61ffffffe000000

def z1060 : W := mkw 0x03fefd4d51120000 0x00ffbf5354448000 0xffffffffffffff03 0xffffffffffffffc0

def z1061 : W := mkw 0x927a69e479370548 0xa49e9a791e4dc152 0x107861e0783f0f00 0x841e18781e0fc3c0

def z1062 : W := mkw 0x84334996ec2cdd6e 0xe10cd265bb0b375b 0xfc77599e643cffff 0xbf1dd667990f3fff

def z1063 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0xfffffffffc3c0003 0xffffffffff0f0000

def z1064 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef871e1f85c0c0ff 0x3be1c787e170303f

def z1065 : W := mkw 0x0184960902400090 0x0061258240900024 0xef871e0e07c000fe 0x7be1c78381f0003f

def z1066 : W := mkw 0x8985963b8ec1f1b7 0x2261658ee3b07c6d 0xef8ffe7f9fe3ffff 0xfbe3ff9fe7f8ffff

def z1067 : W := mkw 0x01a6f40d50000000 0x0069bd0354000000 0xcb8ffffff8000003 0xf2e3fffffe000000

def z1068 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0xdbff1ffff8000002 0xf6ffc7fffe000000

def z1069 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0x37f807e007ff00fc 0xcdfe01f801ffc03f

def z1070 : W := mkw 0x967a49e4693f0d48 0xe59e92791a4fc352 0x107861e0783f0f00 0x841e18781e0fc3c0

def z1071 : W := mkw 0x13cc966903530090 0x04f3259a40d4c024 0x0388866183c30000 0x40e2219860f0c000

def z1072 : W := mkw 0x0258098001360048 0x00960260004d8012 0xf7f0198005fc00fe 0xbdfc0660017f003f

def z1073 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xbc77598e643cccfc 0xaf1dd663990f333f

def z1074 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0x0008e7f1fa23ff01 0xc00239fc7e88ffc0

def z1075 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f0198007ff00fe 0xbdfc066001ffc03f

def z1076 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xbc77581e643cccfd 0x2f1dd607990f333f

def z1077 : W := mkw 0x1ad81fe9837710db 0x06b607fa60ddc436 0xf7f81fe187ff00fe 0xfdfe07f861ffc03f

def z1078 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f8180007ff00fc 0xfdfe060001ffc03f

def z1079 : W := mkw 0x0985960b06c0a095 0x02616582c1b02825 0xef879e1f87c000ff 0x7be1e787e1f0003f

def z1080 : W := mkw 0x800000b0a8215562 0xa000002c2a085558 0x4008e7f1f823ff03 0xd00239fc7e08ffc0

def z1081 : W := mkw 0x94901ff6ea6555fe 0xe52407fdba99557f 0x00001ffff80000fe 0x000007fffe00003f

def z1082 : W := mkw 0x0433499664acee6c 0xc10cd265992b3b9b 0xfc77599e643cffff 0xbf1dd667990f3fff

def z1083 : W := mkw 0x036fe040159aaa00 0x00dbf8100566aa80 0xffffe0601fffff01 0xfffff81807ffffc0

def z1084 : W := mkw 0x01949d4d50000000 0x0065275354000000 0xcb8ffffff8000003 0xf2e3fffffe000000

def z1085 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0x1bffe00003ffff01 0xc6fff80000ffffc0

def z1086 : W := mkw 0x01b6dd0d40000000 0x006db74350000000 0xdbfffffff8000003 0xf6fffffffe000000

def z1087 : W := mkw 0x900002b0aa6555fa 0xa40000ac2a99557e 0x6008e7f1fa23ffff 0xd80239fc7e88ffff

def z1088 : W := mkw 0x04324996602c4c6c 0xc10c9265980b131b 0xd877599e603c0cff 0xb61dd667980f033f

def z1089 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc77199e643c00fe 0xbf1dc667990f003f

def z1090 : W := mkw 0x043249966024446c 0xc10c92659809111b 0xfc77599e643c00ff 0xbf1dd667990f003f

def z1091 : W := mkw 0x8985961baec0f5b7 0xa2616586ebb03d6d 0xef879e1f87c0ffff 0x7be1e787e1f03fff

def z1092 : W := mkw 0x03dc9d4d50000000 0x00f7275354000000 0xdbff9ffff8000003 0xf6ffe7fffe000000

def z1093 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0xfbfffffff820cc03 0xfefffffffe083300

def z1094 : W := mkw 0x800002b2aa2155e6 0xa00000acaa885579 0x6008fffffa23ffff 0xd8023ffffe88ffff

def z1095 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0xdbfffffffa033303 0xf6fffffffe80ccc0

def z1096 : W := mkw 0x04110992242ccc6c 0xc1044264890b331b 0xfc77199e043cccff 0xbf1dc667810f333f

def z1097 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0x37f8e00007ffff00 0xcdfe380001ffffc0

def z1098 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0xe80ffffffa23ffe3 0xfa03fffffe88fff8

def z1099 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef87df9fe7c0f0ff 0xfbe1f7e7f9f03c3f

def z1100 : W := mkw 0x0d27c01fc488f827 0x4349f007f1223e09 0x0807801f8000f001 0x0201e007e0003c00

def z1101 : W := mkw 0x127a69e4513f0a48 0x049e9a79144fc292 0x107861e0783f0f00 0x841e18781e0fc3c0

def z1102 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0x9bff7ffff8000002 0xa6ffdffffe000000

def z1103 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xfffff80007ffffff 0xfffffe0001ffffff

def z1104 : W := mkw 0x880102b2affbfff7 0xa20040acabfefffd 0x2400000007fffffc 0x0900000001ffffff

def z1105 : W := mkw 0x0010098000240048 0x0004026000090012 0xfc77199e043c00ff 0xbf1dc667810f003f

def z1106 : W := mkw 0x13fffd4d55deaa18 0x04ffff535577aa86 0x9ff7180e05dc001c 0x27fdc60381770007

def z1107 : W := mkw 0x036fe000059aaa00 0x00dbf8000166aa80 0xbfffa00007ffff00 0x6fffe80001ffffc0

def z1108 : W := mkw 0x036fe004559aaa00 0x00dbf8011566aa80 0xffffe0007fffff01 0xfffff8001fffffc0

def z1109 : W := mkw 0x843349b6ec2ddd6e 0xe10cd26dbb0b775b 0xfc7ff9fffc3fffff 0xbf1ffe7fff0fffff

def z1110 : W := mkw 0x12c816a0037700d8 0x04b205a800ddc036 0xf7f81e0007ff00fe 0xfdfe078001ffc03f

def z1111 : W := mkw 0x03fefd4d51922200 0x00ffbf5354648880 0xffffffffffff3303 0xffffffffffffccc0

def z1112 : W := mkw 0x840102b2afbfffee 0xe10040acabeffffb 0x2400000007fffffc 0x0900000001ffffff

def z1113 : W := mkw 0x92d81fe08b7711da 0x24b607f822ddc476 0xf7f81fe007ff33fe 0xfdfe07f801ffccff

def z1114 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xaf871e1f87c0f0fe 0x2be1c787e1f03c3f

def z1115 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0xe788e7f1ffe3ffe3 0xf9e239fc7ff8fff8

def z1116 : W := mkw 0x036fe009159aaa00 0x00dbf8024566aa80 0xffffe0019fffff01 0xfffff80067ffffc0

def z1117 : W := mkw 0x12d81fe0037700d8 0x04b607f800ddc036 0xf7f01e0007ff00fe 0x7dfc078001ffc03f

def z1118 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0xfbfffffffa00f003 0xfefffffffe803c00

def z1119 : W := mkw 0x8985963b8ec1f1b7 0x2261658ee3b07c6d 0xef879e7f9fc0f0ff 0x7be1e79fe7f03c3f

def z1120 : W := mkw 0x12d81dc001760058 0x04b60770005d8016 0xf7f81fe005fc00fe 0xfdfe07f8017f003f

def z1121 : W := mkw 0x003349164408c824 0x000cd24591023209 0xfc77599e643cccff 0xbf1dd667990f333f

def z1122 : W := mkw 0x037ee90440000000 0x00dfba4110000000 0xdbfffffff8000003 0xf6fffffffe000000

def z1123 : W := mkw 0x92d81fe02b7705d8 0xa4b607f80addc176 0xf7f8ffe07fffffff 0xfdfe3ff81fffffff

def z1124 : W := mkw 0x16d81fe4637704d8 0xc5b607f918ddc136 0xf7f81fe067ff00fe 0xfdfe07f819ffc03f

def z1125 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0xdbf79ffff8000003 0x76fde7fffe000000

def z1126 : W := mkw 0x0127c000059aaa00 0x0049f0000166aa80 0xfff7c00007ffff01 0xfffdf00001ffffc0

def z1127 : W := mkw 0x04334986642c8c4c 0xc10cd261990b2313 0xfc77598e643c0cfe 0xbf1dd663990f033f

def z1128 : W := mkw 0x02d81f4003520090 0x00b607d000d48024 0xf7f81fe007ff00fe 0xfdfe07f801ffc03f

def z1129 : W := mkw 0x0d27e01ff488fc27 0xc349f807fd223f09 0x0807e01ff800fc01 0x0201f807fe003f00

def z1130 : W := mkw 0x0985941b84c0f037 0x02616506e1303c0d 0xef87981f85c0f0ff 0x3be1e607e1703c3f

def z1131 : W := mkw 0x0184940900000000 0x0061250240000000 0xcb879ffff8000003 0x72e1e7fffe000000

def z1132 : W := mkw 0x03fefd4d50040008 0x00ffbf5354010002 0xdffffffffc1c001f 0xf7ffffffff070007

def z1133 : W := mkw 0x00b25d4d50000000 0x002c975354000000 0x08075ffff8000003 0x0201d7fffe000000

def z1134 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc77599e663fffff 0xbf1dd667998fffff

def z1135 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc77199e641cc0ff 0x3f1dc6679907303f

def z1136 : W := mkw 0x0248020003520090 0x0092008000d48024 0xf7f8000007ff00fc 0xfdfe000001ffc03f

def z1137 : W := mkw 0x03fefd4d519a2a00 0x00ffbf5354668a80 0xdbfffffffbff3f03 0xf6fffffffeffcfc0

def z1138 : W := mkw 0x0984961b82c070b7 0x02612586e0b01c2d 0xcb879e1f83c030ff 0x72e1e787e0f00c3f

def z1139 : W := mkw 0x03dcbd4d50000000 0x00f72f5354000000 0xcb8fbffff8000003 0x72e3effffe000000

def z1140 : W := mkw 0x04334996642ccc6c 0xc10cd265990b331b 0xfc77f99e643cffff 0xbf1dfe67990f3fff

def z1141 : W := mkw 0x03fefd4d50400010 0x00ffbf5354100004 0xdffffffffdc0001f 0xf7ffffffff700007

def z1142 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef87181e07c0f0ff 0x3be1c60781f03c3f

def z1143 : W := mkw 0x13fefd4d51560018 0x04ffbf5354558006 0xffffffffffff001f 0xffffffffffffc007

def z1144 : W := mkw 0x0985961b86c0f0b7 0x02616586e1b03c2d 0xef8fbe7f9fc0f0ff 0x7be3ef9fe7f03c3f

def z1145 : W := mkw 0x0527e0122488ee24 0xc149f80489223b89 0x0807e0000000ff01 0x0201f80000003fc0

def z1146 : W := mkw 0x026b4000059aaa00 0x009ad0000166aa80 0xffff400007ffff01 0xffffd00001ffffc0

def z1147 : W := mkw 0x0905821286c0f0b7 0x02416084a1b03c2d 0xef87981e07c0f0ff 0x7be1e60781f03c3f

def z1148 : W := mkw 0x12d83fe0137700d8 0x04b60ff804ddc036 0xf7f83fe01fff00fe 0xfdfe0ff807ffc03f

def z1149 : W := mkw 0x840102b2ae29dde6 0xe10040acab8a7779 0x200000000223ffe0 0x080000000088fff8

def z1150 : W := mkw 0x124802a0037700d8 0x049200a800ddc036 0xf7f807e007ff00fe 0xfdfe01f801ffc03f

def z1151 : W := mkw 0x04334916440cc82c 0x410cd2459103320b 0xfc77581e043cccff 0xbf1dd607810f333f

def z1152 : W := mkw 0x843349b66c2dcd6c 0xe10cd26d9b0b735b 0xfc7ffffffc3fcfff 0xff1fffffff0ff3ff

def z1153 : W := mkw 0x0b6fe00b059aaa05 0x02dbf802c166aa81 0xffffe00e07ffff01 0xfffff80381ffffc0

def z1154 : W := mkw 0x0d27e01fe488fe27 0xc349f807f9223f89 0x0807e01fe000ff01 0x0201f807f8003fc0

def z1155 : W := mkw 0x800002a0aa2115c2 0xa00000a82a884570 0x6008e7e1fa23ff01 0xd80239f87e88ffc0

def z1156 : W := mkw 0x03fefd4d50000000 0x00ffbf5354000000 0x9bf7fffff8000003 0x26fdfffffe000000

def z1157 : W := mkw 0x027a694450000000 0x009e9a5114000000 0xd87ffffff8000003 0xf61ffffffe000000

def z1158 : W := mkw 0x800002b0aa2155e2 0xa00000ac2a885578 0xf478e7f1fe3fffe3 0xfd1e39fc7f8ffff8

def z1159 : W := mkw 0x0905801b8480f027 0x02416006e1203c09 0xef87981f87c0f0ff 0x7be1e607e1f03c3f

def z1160 : W := mkw 0x93ccb6699b531192 0x24f32d9a66d4c464 0x0388a6619bc33300 0x40e2299866f0ccc0

def z1161 : W := mkw 0x036fe004459aaa00 0x00dbf8011166aa80 0xffffe01e67ffff01 0xfffff80799ffffc0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z7,z8,z2,z3,z4,z9]),(0,[z10,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z11,z5])],[(0,[z1,z12,z8,z2,z3,z4,z5]),(0,[z13,z8,z2,z3,z14,z4,z5]),(0,[z15,z1,z8,z2,z3,z4,z5]),(0,[z16,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z17,z3,z4,z18,z5])],[(0,[z1,z8,z2,z3,z4,z19,z5]),(0,[z1,z8,z20,z2,z3,z4,z5]),(0,[z1,z2,z3,z21,z4,z22,z5]),(0,[z23,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z24,z3,z4,z5]),(0,[z1,z8,z25,z2,z3,z4,z26]),(0,[z1,z8,z27,z2,z3,z4,z5])],[(0,[z28,z1,z8,z2,z3,z4,z5]),(0,[z29,z8,z2,z30,z3,z4,z5]),(0,[z1,z31,z8,z2,z3,z4,z5]),(0,[z1,z32,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z33,z5]),(1,[z1,z8,z2,z4,z5,z34])],[(0,[z1,z8,z35,z3,z4,z5,z36]),(1,[z37,z8,z2,z3,z4,z5]),(0,[z1,z8,z38,z2,z39,z3,z5]),(0,[z1,z8,z2,z3,z4,z5,z40])],[(0,[z41,z1,z8,z2,z3,z4,z5]),(1,[z42,z1,z2,z43,z4,z5]),(1,[z44,z1,z2,z3,z22,z5]),(0,[z1,z8,z2,z4,z26,z5,z34])],[(0,[z45,z1,z8,z2,z3,z4,z5]),(0,[z46,z1,z8,z2,z3,z4,z5])],[(0,[z1,z8,z2,z47,z3,z48,z5]),(0,[z49,z1,z8,z2,z3,z4,z5]),(0,[z50,z1,z8,z2,z3,z4,z5]),(0,[z51,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z52,z3,z4,z5])]],
   [[(0,[z53,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z54,z5])],[(0,[z55,z1,z8,z56,z3,z4,z5]),(0,[z1,z8,z2,z3,z57,z5,z58]),(1,[z1,z31,z2,z3,z4,z5]),(1,[z59,z1,z2,z60,z4,z5]),(0,[z1,z61,z2,z3,z4,z62,z5]),(0,[z63,z1,z8,z3,z4,z5,z36])],[(0,[z64,z65,z1,z8,z2,z3,z5]),(0,[z1,z8,z2,z66,z3,z4,z5]),(0,[z67,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z68,z4,z5]),(0,[z69,z1,z8,z2,z3,z4,z5])],[(0,[z1,z8,z2,z70,z3,z4,z5]),(0,[z71,z1,z8,z2,z3,z4,z5]),(0,[z7,z1,z8,z2,z3,z4,z72]),(0,[z1,z8,z2,z3,z73,z4,z5]),(0,[z64,z1,z8,z2,z4,z5,z74]),(0,[z1,z8,z2,z3,z75,z4,z5]),(1,[z76,z1,z2,z3,z4,z5])],[(0,[z1,z8,z2,z77,z3,z4,z5]),(0,[z1,z78,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z21,z4,z5]),(0,[z1,z8,z38,z2,z3,z79,z5])],[(0,[z7,z8,z80,z2,z3,z4,z5]),(0,[z1,z8,z81,z80,z2,z3,z4]),(1,[z1,z8,z2,z3,z82,z5]),(0,[z1,z8,z2,z3,z4,z5,z83]),(0,[z1,z8,z2,z3,z84,z57,z5]),(0,[z1,z8,z2,z60,z85,z4,z5]),(0,[z86,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z87]),(0,[z1,z8,z2,z3,z4,z88,z5])],[(0,[z1,z8,z2,z3,z4,z89,z5]),(0,[z1,z61,z8,z2,z3,z4,z6])],[(0,[z13,z7,z8,z2,z3,z4,z5]),(0,[z8,z2,z3,z4,z9,z5,z72]),(0,[z90,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z38,z3,z79,z4,z5]),(0,[z1,z91,z8,z2,z3,z4,z5])]],
   [[(0,[z1,z8,z2,z3,z4,z92,z5]),(0,[z1,z8,z2,z4,z93,z94,z5]),(0,[z1,z8,z2,z3,z4,z5,z34]),(0,[z95,z1,z8,z2,z3,z84,z5])],[(0,[z1,z8,z2,z3,z4,z4,z5]),(0,[z96,z1,z8,z2,z3,z4,z5]),(0,[z97,z1,z8,z2,z98,z4,z5]),(0,[z99,z1,z8,z2,z3,z4,z5])],[(0,[z1,z100,z2,z101,z3,z4,z5]),(0,[z1,z8,z2,z3,z102,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z103]),(1,[z1,z8,z2,z3,z5,z104])],[(0,[z1,z8,z2,z105,z3,z4,z5]),(0,[z106,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z107,z5]),(0,[z1,z8,z2,z3,z4,z108,z5]),(0,[z109,z1,z8,z2,z3,z4,z5]),(0,[z1,z110,z8,z2,z3,z4,z5]),(0,[z95,z1,z8,z2,z3,z5,z58])],[(0,[z29,z1,z8,z111,z2,z4,z5]),(0,[z13,z1,z8,z2,z3,z112,z5])],[(0,[z1,z80,z100,z2,z3,z4,z5]),(0,[z55,z1,z8,z35,z3,z4,z5]),(0,[z1,z8,z2,z113,z56,z3,z5]),(1,[z1,z114,z100,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z115,z5])],[(0,[z1,z8,z2,z3,z116,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z117]),(0,[z1,z8,z2,z3,z4,z5,z118]),(0,[z64,z1,z8,z2,z3,z119,z5])],[(0,[z120,z1,z8,z2,z3,z4,z5]),(0,[z63,z121,z1,z8,z2,z4,z5]),(0,[z1,z122,z8,z2,z3,z4,z5]),(0,[z123,z1,z8,z2,z3,z4,z5]),(0,[z124,z1,z8,z2,z3,z22,z5])]],
   [[(0,[z8,z2,z3,z14,z4,z57,z5]),(0,[z1,z8,z25,z3,z4,z26,z5])],[(1,[z1,z8,z81,z2,z3,z4]),(1,[z1,z8,z3,z125,z4,z5]),(0,[z97,z1,z8,z2,z126,z4,z5]),(0,[z127,z1,z8,z2,z3,z4,z128]),(0,[z129,z1,z8,z2,z3,z4,z5])],[(0,[z1,z8,z2,z3,z130,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z131])],[(0,[z132,z1,z8,z2,z56,z4,z5]),(0,[z1,z8,z2,z3,z4,z133,z5]),(0,[z13,z1,z134,z2,z3,z4,z5]),(0,[z97,z1,z8,z2,z3,z4,z62]),(0,[z1,z8,z2,z3,z4,z5,z6]),(0,[z63,z1,z8,z111,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z135,z5])],[(0,[z121,z8,z2,z3,z48,z4,z5]),(0,[z1,z37,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z136,z4,z5]),(0,[z1,z8,z2,z137,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z138,z5])],[(0,[z139,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z56,z3,z4,z5]),(0,[z1,z8,z2,z60,z4,z5,z74]),(0,[z140,z1,z8,z2,z3,z4,z5])],[(0,[z1,z8,z134,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z141]),(0,[z1,z8,z2,z3,z4,z142,z5]),(1,[z1,z8,z38,z3,z79,z5])],[(0,[z143,z1,z8,z2,z3,z4,z5]),(1,[z144,z1,z101,z3,z4,z5]),(1,[z1,z8,z111,z145,z4,z5]),(0,[z1,z8,z25,z2,z3,z4,z5]),(0,[z1,z8,z2,z4,z128,z5,z74])]],
   [[(0,[z1,z8,z2,z146,z3,z4,z5]),(0,[z1,z8,z2,z3,z14,z84,z5]),(0,[z1,z8,z2,z3,z4,z5,z147]),(0,[z1,z8,z148,z2,z3,z4,z5])],[(0,[z1,z8,z2,z149,z3,z4,z5]),(0,[z150,z1,z8,z2,z3,z4,z5]),(0,[z97,z144,z1,z2,z3,z4,z5]),(0,[z97,z1,z61,z2,z3,z4,z5]),(1,[z151,z1,z2,z3,z4,z5])],[(0,[z1,z8,z2,z85,z48,z4,z5]),(0,[z97,z7,z1,z8,z2,z3,z4]),(0,[z1,z8,z2,z3,z4,z152,z5]),(0,[z1,z8,z153,z2,z3,z4,z5])],[(0,[z1,z8,z2,z3,z4,z5,z154]),(0,[z1,z8,z2,z3,z125,z4,z5]),(0,[z155,z1,z8,z38,z2,z3,z5]),(0,[z1,z8,z100,z3,z4,z5,z36]),(0,[z1,z8,z156,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z157])],[(0,[z158,z8,z2,z3,z14,z4,z5]),(0,[z159,z1,z8,z2,z3,z4,z5])],[(0,[z8,z80,z2,z3,z14,z4,z5]),(0,[z1,z61,z80,z2,z3,z4,z5]),(0,[z160,z1,z8,z35,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z161,z5]),(0,[z162,z1,z8,z2,z3,z4,z5]),(0,[z163,z1,z8,z2,z3,z4,z5])],[(0,[z1,z8,z164,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z18,z5])],[(0,[z1,z8,z2,z3,z4,z165,z5]),(0,[z1,z8,z2,z3,z4,z166,z5]),(0,[z121,z1,z8,z2,z48,z4,z5]),(0,[z1,z8,z2,z3,z4,z167,z5]),(0,[z168,z1,z8,z2,z3,z4,z5])]],
   [[(0,[z169,z1,z8,z2,z3,z4,z5]),(0,[z13,z1,z8,z2,z3,z4,z9]),(0,[z97,z13,z1,z8,z2,z3,z4]),(0,[z1,z8,z2,z85,z43,z4,z5]),(0,[z170,z1,z8,z2,z3,z4,z5]),(0,[z59,z1,z8,z2,z171,z4,z5]),(0,[z124,z172,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z173,z3,z4,z5]),(0,[z127,z1,z8,z2,z85,z4,z5]),(0,[z1,z8,z2,z85,z4,z128,z5])],[(0,[z174,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z48,z4,z5]),(1,[z172,z8,z2,z3,z4,z5])],[(0,[z1,z8,z2,z3,z175,z4,z5]),(0,[z1,z8,z2,z3,z176,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z177]),(1,[z1,z8,z178,z3,z4,z5]),(0,[z1,z8,z2,z179,z3,z4,z5])],[(0,[z1,z80,z2,z3,z4,z22,z5]),(0,[z180,z1,z8,z2,z3,z4,z5]),(1,[z1,z8,z2,z47,z3,z5]),(0,[z64,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z181,z4,z5]),(0,[z1,z8,z2,z3,z4,z182,z5])],[(0,[z183,z1,z8,z2,z3,z4,z5])],[(0,[z1,z8,z2,z113,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z184,z5]),(0,[z1,z8,z2,z3,z185,z4,z5])],[(0,[z1,z8,z2,z3,z4,z5,z186]),(0,[z187,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z188,z5])],[(0,[z1,z8,z2,z3,z43,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z36])]],
   [[(0,[z189,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z190,z2,z3,z4,z5]),(0,[z55,z1,z8,z145,z3,z4,z5]),(0,[z1,z8,z2,z3,z191,z4,z5])],[(0,[z192,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z35,z25,z3,z4,z5]),(0,[z64,z59,z1,z8,z2,z4,z5])],[(0,[z158,z7,z8,z2,z3,z4,z5]),(0,[z53,z160,z1,z2,z3,z4,z5]),(0,[z193,z1,z8,z2,z3,z4,z5]),(0,[z194,z1,z8,z2,z3,z4,z5]),(0,[z63,z1,z8,z2,z195,z4,z5]),(0,[z1,z8,z2,z3,z196,z4,z5]),(0,[z1,z8,z197,z2,z3,z4,z5])],[(0,[z198,z1,z8,z2,z3,z4,z5])],[(0,[z199,z1,z8,z2,z3,z4,z5])],[(0,[z200,z1,z8,z2,z3,z4,z5]),(1,[z1,z8,z2,z201,z4,z5]),(0,[z63,z1,z8,z3,z195,z4,z5]),(0,[z202,z1,z8,z2,z3,z195,z5]),(0,[z203,z1,z8,z2,z3,z4,z5]),(1,[z1,z8,z25,z3,z4,z26])],[(0,[z63,z1,z8,z25,z3,z4,z5]),(0,[z1,z204,z8,z2,z3,z4,z5])],[(0,[z1,z8,z2,z39,z3,z4,z5]),(0,[z1,z8,z2,z3,z205,z4,z5])]],
   [[(0,[z206,z1,z8,z2,z3,z4,z5]),(0,[z144,z1,z8,z100,z3,z4,z5]),(0,[z1,z8,z101,z3,z4,z5,z36]),(0,[z207,z1,z8,z2,z3,z4,z5]),(0,[z208,z1,z8,z2,z3,z4,z5]),(0,[z209,z1,z8,z2,z3,z4,z5]),(0,[z127,z1,z8,z2,z4,z5,z74]),(1,[z1,z8,z2,z4,z5,z210])],[(0,[z65,z8,z80,z2,z3,z4,z5]),(0,[z1,z8,z2,z211,z3,z4,z5]),(0,[z1,z212,z8,z2,z3,z4,z5]),(0,[z127,z1,z8,z2,z3,z4,z74])],[(1,[z155,z8,z2,z3,z14,z5]),(0,[z1,z8,z2,z213,z3,z4,z5]),(0,[z1,z8,z214,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z215,z4,z5]),(0,[z1,z8,z2,z3,z4,z216,z5])],[(0,[z1,z8,z2,z3,z4,z217,z5]),(0,[z1,z8,z2,z218,z3,z4,z5]),(0,[z219,z1,z8,z2,z3,z4,z5])],[(0,[z1,z8,z220,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z221])],[(0,[z144,z1,z80,z2,z3,z4,z5]),(0,[z8,z35,z2,z56,z3,z4,z5]),(0,[z1,z8,z2,z60,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z222,z5]),(0,[z1,z8,z2,z223,z4,z26,z5]),(1,[z1,z8,z2,z85,z4,z128])],[(1,[z1,z8,z2,z113,z3,z5]),(0,[z224,z1,z8,z2,z3,z4,z5]),(0,[z225,z1,z8,z2,z3,z4,z5])],[(0,[z226,z1,z8,z80,z2,z3,z4]),(0,[z227,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z72]),(0,[z7,z8,z2,z3,z4,z9,z5]),(0,[z1,z228,z8,z2,z3,z4,z5]),(0,[z229,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z119,z5])]],
   [[(0,[z230,z1,z8,z2,z56,z3,z5]),(0,[z1,z8,z2,z231,z3,z4,z5])],[(0,[z0,z8,z80,z2,z3,z4,z5]),(0,[z0,z1,z8,z2,z3,z232,z5]),(0,[z233,z1,z8,z2,z3,z4,z5]),(1,[z234,z1,z8,z3,z4,z5]),(0,[z1,z172,z8,z2,z3,z4,z5]),(0,[z209,z1,z8,z2,z4,z94,z5])],[(0,[z1,z8,z2,z3,z201,z4,z5]),(0,[z1,z8,z2,z235,z3,z4,z5]),(0,[z236,z1,z8,z2,z3,z4,z5])],[(0,[z1,z80,z2,z3,z4,z5,z6]),(1,[z202,z1,z8,z2,z3,z5]),(0,[z1,z8,z2,z3,z4,z5,z237])],[(0,[z1,z8,z2,z145,z3,z4,z5]),(0,[z1,z8,z238,z2,z3,z4,z5]),(0,[z1,z8,z239,z2,z3,z4,z5])],[(0,[z240,z1,z8,z2,z3,z4,z5]),(0,[z241,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z210])],[(0,[z1,z8,z242,z2,z3,z4,z5]),(0,[z97,z1,z100,z2,z3,z4,z5]),(0,[z1,z100,z2,z3,z4,z62,z5]),(0,[z1,z8,z2,z171,z4,z119,z5])],[(0,[z243,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z244,z3,z4,z5]),(0,[z234,z1,z8,z2,z3,z4,z5]),(1,[z1,z245,z2,z3,z4,z5]),(0,[z1,z8,z2,z246,z3,z4,z5]),(0,[z247,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z38,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z248,z5]),(0,[z1,z8,z2,z223,z3,z4,z5])]],
   [[(0,[z1,z8,z35,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z112,z4,z5]),(0,[z1,z8,z2,z249,z3,z4,z5]),(0,[z1,z8,z2,z250,z4,z22,z5]),(0,[z1,z251,z8,z2,z3,z4,z5])],[(0,[z1,z8,z2,z3,z4,z5,z252]),(1,[z1,z8,z3,z4,z253,z5]),(0,[z1,z8,z2,z3,z4,z254,z5])],[(0,[z1,z8,z2,z3,z82,z4,z5]),(0,[z8,z2,z3,z14,z4,z9,z5])],[(1,[z227,z1,z2,z3,z4,z5]),(0,[z65,z1,z245,z2,z3,z4,z5]),(0,[z13,z8,z2,z3,z4,z5,z72]),(0,[z1,z8,z2,z3,z4,z255,z5]),(0,[z256,z1,z8,z2,z3,z4,z5])],[(0,[z97,z1,z8,z2,z3,z257,z5])],[(0,[z1,z8,z80,z2,z3,z4,z5]),(0,[z1,z8,z258,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z57,z5]),(0,[z13,z1,z8,z2,z3,z259,z5]),(0,[z1,z8,z2,z3,z4,z260,z5]),(0,[z1,z8,z2,z261,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z262])],[(0,[z1,z8,z2,z3,z4,z5,z263]),(0,[z1,z8,z2,z3,z264,z4,z5]),(0,[z1,z8,z2,z47,z3,z4,z5]),(1,[z1,z8,z2,z98,z4,z5])],[(0,[z265,z1,z8,z2,z3,z4,z5])]],
   [[(0,[z29,z1,z8,z2,z48,z4,z5]),(0,[z1,z8,z2,z3,z266,z4,z5]),(0,[z155,z65,z8,z2,z3,z4,z5]),(0,[z1,z8,z100,z25,z3,z4,z5]),(0,[z267,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z85,z3,z4,z74])],[(0,[z59,z1,z8,z2,z60,z4,z5]),(0,[z1,z8,z2,z3,z4,z268,z5])],[(1,[z180,z1,z8,z2,z3,z5]),(0,[z269,z1,z8,z2,z3,z4,z5]),(0,[z97,z42,z1,z2,z3,z4,z5]),(1,[z1,z8,z2,z250,z4,z5])],[(0,[z270,z1,z8,z2,z3,z4,z5]),(0,[z271,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z272,z3,z4,z5]),(0,[z155,z1,z8,z2,z3,z22,z5]),(0,[z1,z8,z2,z3,z4,z253,z5]),(0,[z1,z8,z2,z273,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z274]),(0,[z1,z8,z2,z3,z4,z275,z5]),(0,[z1,z8,z2,z3,z4,z276,z5])],[(0,[z277,z1,z8,z2,z3,z4,z5]),(0,[z63,z55,z1,z8,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z278,z5]),(0,[z1,z279,z8,z2,z3,z4,z5]),(0,[z280,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z281,z4,z5]),(0,[z282,z1,z8,z2,z3,z4,z5]),(0,[z1,z283,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z284,z4,z5]),(0,[z285,z1,z8,z2,z3,z4,z5])],[(0,[z286,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z287,z4,z5]),(0,[z124,z44,z1,z2,z3,z4,z5]),(0,[z1,z8,z3,z79,z4,z94,z5]),(0,[z1,z288,z8,z2,z3,z4,z5]),(0,[z289,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z205,z128,z5])],[(0,[z1,z8,z2,z3,z290,z4,z5]),(0,[z1,z291,z8,z2,z3,z4,z5]),(1,[z1,z8,z2,z126,z4,z5])],[(0,[z1,z8,z2,z3,z4,z232,z5]),(0,[z13,z1,z8,z2,z3,z4,z72]),(0,[z1,z8,z2,z3,z292,z4,z5]),(0,[z1,z61,z8,z2,z3,z4,z62]),(0,[z293,z1,z8,z2,z3,z94,z5]),(0,[z293,z1,z8,z2,z3,z84,z5])]],
   [[(0,[z230,z1,z8,z2,z3,z4,z5]),(0,[z1,z294,z8,z2,z3,z4,z5]),(0,[z63,z1,z8,z3,z79,z4,z5]),(0,[z127,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z3,z4,z18,z5,z295])],[(0,[z1,z8,z296,z2,z3,z4,z5]),(0,[z13,z1,z8,z2,z201,z4,z5]),(0,[z1,z8,z2,z3,z4,z297,z5]),(0,[z1,z8,z2,z3,z298,z4,z5])],[(0,[z1,z8,z2,z3,z299,z4,z5]),(0,[z1,z8,z300,z2,z3,z4,z5]),(0,[z301,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z302]),(0,[z293,z1,z8,z2,z3,z5,z58])],[(0,[z303,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z304,z4,z5]),(0,[z305,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z195,z4,z5]),(1,[z1,z8,z17,z3,z4,z5])],[(0,[z0,z1,z8,z2,z3,z82,z5]),(0,[z160,z1,z8,z56,z3,z4,z5]),(0,[z132,z1,z8,z2,z3,z4,z5]),(0,[z306,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z307,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z308,z5]),(0,[z97,z1,z2,z3,z4,z22,z5]),(0,[z1,z8,z309,z2,z3,z4,z5]),(0,[z1,z8,z111,z145,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z310])],[(0,[z1,z8,z2,z3,z4,z311,z5]),(0,[z1,z8,z2,z3,z312,z4,z5]),(0,[z95,z1,z8,z2,z3,z4,z18])],[(0,[z7,z1,z61,z8,z2,z3,z4]),(0,[z1,z8,z2,z3,z4,z313,z5])],[(0,[z65,z1,z8,z2,z3,z22,z5]),(0,[z1,z8,z2,z3,z250,z4,z5]),(0,[z1,z8,z314,z2,z3,z4,z5]),(0,[z64,z1,z8,z111,z2,z4,z5]),(0,[z1,z8,z2,z315,z3,z4,z5])]],
   [[(0,[z44,z1,z8,z2,z3,z22,z5]),(0,[z1,z2,z3,z4,z62,z5,z6]),(0,[z63,z1,z8,z2,z85,z4,z5]),(0,[z1,z2,z3,z4,z5,z316,z36])],[(0,[z317,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z318,z5]),(0,[z155,z1,z8,z2,z39,z3,z5]),(0,[z319,z1,z8,z2,z3,z4,z5]),(0,[z1,z320,z8,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z157,z74])],[(0,[z1,z8,z2,z3,z4,z5,z321]),(0,[z293,z1,z8,z3,z4,z5,z36]),(0,[z1,z8,z2,z322,z3,z4,z5])],[(0,[z323,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z324,z4,z5]),(0,[z42,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z325,z3,z4,z5]),(0,[z59,z1,z2,z60,z3,z4,z5]),(0,[z1,z8,z2,z3,z126,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z326]),(1,[z63,z1,z8,z195,z4,z5])],[(0,[z327,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z328,z2,z3,z4,z5])],[(0,[z0,z1,z2,z60,z3,z4,z5]),(0,[z1,z8,z56,z3,z4,z5,z36]),(0,[z329,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z330,z195,z5]),(0,[z1,z8,z2,z3,z4,z5,z331]),(0,[z1,z8,z2,z39,z3,z119,z5])],[(0,[z1,z8,z2,z3,z4,z5,z332]),(0,[z1,z8,z2,z3,z14,z5,z58]),(0,[z333,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z334,z4,z5]),(0,[z1,z114,z8,z100,z3,z4,z5]),(0,[z335,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z336,z2,z3,z4,z5]),(0,[z337,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z39,z171,z4,z5])],[(0,[z1,z8,z338,z2,z3,z4,z5]),(0,[z1,z8,z2,z339,z3,z4,z5]),(0,[z1,z8,z2,z3,z340,z4,z5]),(0,[z341,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z3,z4,z128,z5,z342])]],
   [[(0,[z1,z8,z343,z2,z3,z4,z5]),(0,[z344,z1,z8,z2,z3,z4,z5])],[(0,[z1,z8,z2,z345,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z346]),(0,[z1,z8,z2,z43,z4,z5,z74])],[(0,[z0,z1,z61,z2,z3,z4,z5]),(0,[z1,z8,z2,z347,z56,z4,z5]),(0,[z1,z8,z348,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z22,z62,z5]),(1,[z1,z8,z349,z3,z4,z5]),(0,[z1,z8,z2,z3,z350,z4,z5])],[(0,[z351,z1,z8,z2,z3,z4,z5]),(0,[z65,z8,z2,z3,z4,z9,z5]),(0,[z1,z8,z111,z2,z4,z5,z74]),(0,[z352,z1,z8,z2,z3,z4,z5]),(1,[z353,z1,z8,z3,z4,z5])],[(1,[z354,z1,z8,z2,z4,z5]),(0,[z355,z1,z8,z2,z3,z4,z5]),(0,[z95,z1,z8,z2,z3,z4,z58])],[(0,[z158,z1,z80,z2,z3,z4,z5]),(0,[z65,z1,z8,z2,z39,z3,z5]),(1,[z1,z8,z356,z3,z4,z5]),(0,[z1,z8,z2,z357,z3,z4,z5]),(0,[z1,z358,z8,z2,z3,z4,z5]),(0,[z359,z1,z8,z2,z3,z4,z5]),(1,[z8,z2,z3,z4,z5,z360])],[(0,[z158,z8,z2,z3,z4,z5,z72]),(0,[z1,z8,z245,z2,z3,z4,z5]),(0,[z361,z1,z8,z2,z3,z4,z5])],[(0,[z8,z80,z2,z3,z4,z5,z72]),(0,[z1,z8,z362,z2,z3,z4,z5]),(0,[z1,z8,z2,z363,z3,z4,z5]),(0,[z59,z1,z8,z2,z43,z4,z5]),(0,[z97,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z98,z3,z4,z5]),(0,[z1,z364,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z18,z5,z58])]],
   [[(0,[z1,z8,z2,z3,z365,z4,z5]),(0,[z1,z8,z2,z366,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z367]),(0,[z13,z1,z31,z2,z3,z4,z5]),(0,[z97,z1,z8,z349,z3,z4,z5]),(0,[z63,z1,z8,z2,z4,z5,z74]),(0,[z1,z8,z111,z2,z195,z4,z5]),(1,[z293,z1,z8,z3,z94,z5]),(0,[z1,z8,z2,z3,z4,z5,z368])],[(0,[z1,z8,z81,z2,z3,z4,z5]),(1,[z158,z0,z2,z3,z4,z5]),(0,[z369,z1,z8,z2,z3,z4,z5]),(0,[z151,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z178,z3,z4,z128,z5])],[(0,[z1,z8,z2,z3,z4,z5,z370]),(0,[z65,z1,z8,z38,z2,z3,z5]),(0,[z1,z8,z2,z3,z371,z4,z5]),(0,[z1,z8,z2,z3,z4,z128,z5])],[(0,[z1,z8,z2,z372,z3,z4,z5]),(0,[z373,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z85,z3,z4,z128])],[(0,[z1,z8,z2,z3,z4,z5,z374]),(0,[z1,z8,z2,z3,z128,z5,z104])],[(0,[z1,z8,z2,z3,z4,z375,z5]),(0,[z376,z1,z8,z2,z3,z4,z5])],[(1,[z55,z8,z56,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z377]),(0,[z1,z8,z2,z3,z378,z4,z5])],[(0,[z1,z8,z2,z101,z3,z4,z5]),(0,[z124,z90,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z379,z4,z5]),(0,[z293,z1,z8,z145,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z380,z5]),(0,[z1,z8,z2,z3,z4,z5,z104])]],
   [[(0,[z1,z8,z381,z2,z3,z4,z5]),(1,[z13,z8,z2,z3,z4,z72]),(0,[z1,z8,z382,z2,z3,z4,z5]),(0,[z63,z1,z8,z2,z145,z4,z5])],[(0,[z160,z8,z35,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z383,z5]),(0,[z23,z1,z8,z2,z3,z4,z36])],[(0,[z1,z8,z2,z3,z4,z384,z5]),(1,[z53,z1,z2,z3,z4,z5]),(1,[z1,z385,z2,z3,z4,z5]),(0,[z386,z1,z8,z2,z3,z4,z5]),(0,[z387,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z21,z84,z5]),(1,[z1,z8,z3,z4,z5,z342])],[(0,[z1,z8,z3,z125,z48,z4,z5]),(0,[z1,z8,z2,z3,z388,z4,z5]),(0,[z1,z389,z8,z2,z3,z4,z5]),(0,[z23,z1,z8,z3,z4,z5,z36]),(0,[z1,z8,z2,z3,z4,z5,z390]),(1,[z1,z8,z3,z4,z5,z295])],[(0,[z65,z8,z2,z3,z4,z57,z5]),(0,[z63,z1,z8,z2,z171,z4,z5])],[(0,[z1,z8,z2,z3,z21,z5,z58])],[(0,[z1,z8,z2,z3,z4,z391,z5]),(0,[z1,z8,z2,z3,z4,z392,z5]),(0,[z393,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z394,z5]),(0,[z1,z8,z2,z3,z4,z395,z5]),(0,[z1,z8,z2,z3,z396,z4,z5]),(0,[z42,z1,z2,z3,z4,z62,z5]),(0,[z1,z8,z2,z3,z79,z4,z5])],[(0,[z397,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z9,z5]),(0,[z1,z8,z2,z398,z3,z4,z5]),(0,[z353,z1,z8,z3,z4,z119,z5]),(0,[z1,z8,z2,z3,z4,z5,z399])]],
   [[(0,[z55,z160,z8,z2,z3,z4,z5]),(1,[z29,z8,z2,z30,z4,z5]),(0,[z1,z8,z2,z400,z3,z4,z5]),(0,[z401,z1,z8,z2,z3,z4,z5]),(0,[z1,z402,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z403,z3,z4,z5]),(1,[z387,z1,z8,z3,z4,z5]),(0,[z1,z8,z2,z3,z84,z22,z5]),(0,[z124,z1,z8,z2,z3,z21,z5])],[(0,[z1,z8,z2,z3,z4,z404,z5]),(1,[z97,z1,z2,z3,z4,z6]),(0,[z1,z8,z2,z405,z3,z4,z5])],[(0,[z97,z1,z8,z2,z3,z406,z5]),(0,[z1,z8,z2,z3,z4,z5,z407]),(0,[z1,z8,z2,z3,z4,z5,z58])],[(0,[z160,z1,z8,z145,z3,z4,z5]),(0,[z1,z8,z2,z408,z3,z4,z5]),(0,[z409,z1,z8,z2,z3,z4,z5])],[(0,[z121,z1,z8,z2,z30,z4,z5]),(0,[z1,z8,z2,z3,z410,z4,z5]),(0,[z1,z8,z2,z30,z4,z5,z74]),(0,[z7,z1,z8,z2,z3,z4,z5]),(0,[z387,z1,z8,z3,z4,z22,z5]),(0,[z1,z8,z3,z4,z11,z119,z5]),(0,[z1,z8,z2,z3,z4,z5,z342])],[(0,[z1,z8,z2,z3,z4,z5,z411]),(1,[z230,z1,z8,z2,z3,z5]),(0,[z1,z8,z412,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z413,z4,z5]),(0,[z414,z1,z8,z2,z3,z4,z5]),(1,[z127,z1,z8,z2,z4,z74]),(0,[z1,z8,z2,z3,z4,z5,z360]),(0,[z415,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z295])],[(0,[z1,z8,z25,z56,z3,z4,z5]),(1,[z1,z416,z2,z3,z4,z5]),(0,[z417,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z418,z5]),(0,[z1,z8,z2,z3,z4,z5,z419])],[(0,[z420,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z421,z3,z4,z5])]],
   [[(0,[z158,z317,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z422,z4,z5]),(0,[z423,z1,z8,z2,z3,z4,z5]),(0,[z424,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z425,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z426])],[(0,[z1,z8,z2,z427,z3,z4,z5]),(1,[z1,z8,z2,z3,z257,z5]),(0,[z1,z8,z2,z3,z406,z4,z5])],[(0,[z1,z8,z2,z3,z4,z428,z5]),(0,[z1,z8,z2,z429,z3,z4,z5]),(0,[z64,z1,z8,z2,z3,z171,z5])],[(0,[z144,z1,z8,z3,z79,z4,z5]),(1,[z1,z2,z3,z4,z5,z316]),(0,[z1,z430,z8,z2,z3,z4,z5])],[(0,[z431,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z432,z5]),(0,[z1,z8,z2,z3,z84,z4,z18])],[(0,[z1,z8,z2,z433,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z434,z5]),(0,[z435,z1,z8,z2,z3,z4,z5]),(0,[z436,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z196,z26,z5])],[(0,[z1,z8,z2,z3,z437,z4,z5]),(0,[z1,z8,z2,z3,z4,z259,z5])],[(0,[z1,z8,z356,z2,z3,z4,z5]),(0,[z293,z1,z8,z25,z3,z4,z5])]],
   [[(0,[z438,z1,z8,z2,z3,z4,z5]),(0,[z439,z1,z8,z2,z3,z4,z5]),(0,[z63,z1,z8,z2,z3,z4,z5])],[(0,[z13,z1,z8,z356,z3,z4,z5]),(0,[z202,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z17,z2,z3,z4,z5])],[(0,[z227,z29,z1,z2,z3,z4,z5]),(0,[z1,z8,z440,z2,z3,z4,z5]),(0,[z441,z1,z8,z2,z3,z4,z5]),(0,[z42,z1,z8,z2,z171,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z442]),(0,[z1,z8,z2,z3,z4,z5,z443])],[(0,[z1,z8,z2,z3,z4,z444,z5]),(0,[z1,z8,z445,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z446,z4,z5])],[(0,[z447,z1,z8,z2,z3,z4,z5]),(1,[z65,z8,z2,z3,z57,z5]),(0,[z1,z8,z2,z3,z448,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z449]),(0,[z450,z1,z8,z2,z3,z4,z5])],[(0,[z451,z1,z8,z2,z3,z4,z5]),(0,[z452,z1,z8,z2,z3,z4,z5]),(0,[z453,z1,z8,z2,z3,z4,z5]),(0,[z1,z454,z8,z2,z3,z4,z5])],[(0,[z1,z8,z2,z3,z4,z455,z5]),(0,[z293,z1,z8,z38,z3,z4,z5]),(0,[z1,z8,z25,z2,z3,z4,z36]),(0,[z1,z8,z2,z39,z3,z171,z5])],[(0,[z1,z8,z2,z456,z3,z4,z5]),(0,[z457,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z458]),(0,[z354,z1,z8,z2,z3,z4,z5]),(0,[z63,z64,z1,z8,z2,z4,z5]),(0,[z1,z8,z459,z2,z3,z4,z5])]],
   [[(1,[z1,z8,z2,z3,z205,z5])],[(1,[z121,z8,z2,z48,z4,z5]),(0,[z1,z8,z2,z3,z460,z4,z5]),(0,[z1,z2,z60,z3,z4,z62,z5]),(0,[z64,z1,z8,z2,z3,z84,z5]),(0,[z1,z8,z2,z3,z4,z5,z74])],[(0,[z1,z8,z2,z3,z461,z4,z5])],[(0,[z0,z42,z1,z2,z3,z4,z5]),(1,[z1,z8,z2,z3,z5,z237]),(0,[z462,z1,z8,z2,z3,z4,z5])],[(0,[z463,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z464,z2,z3,z4,z5]),(0,[z64,z1,z8,z2,z3,z5,z58])],[(0,[z465,z1,z8,z2,z3,z4,z5]),(0,[z466,z1,z8,z2,z3,z4,z5]),(0,[z155,z1,z8,z2,z3,z14,z5]),(0,[z467,z1,z8,z2,z3,z4,z5])],[(0,[z1,z8,z2,z3,z4,z5,z468]),(0,[z469,z1,z8,z2,z3,z4,z5]),(0,[z354,z1,z8,z2,z4,z22,z5]),(1,[z1,z8,z2,z3,z330,z5]),(0,[z1,z8,z111,z2,z85,z4,z5]),(1,[z64,z1,z8,z2,z119,z5]),(0,[z1,z8,z2,z85,z171,z4,z5]),(0,[z470,z1,z8,z2,z3,z4,z5]),(0,[z471,z1,z8,z2,z3,z4,z5])],[(0,[z158,z65,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z472]),(0,[z1,z8,z3,z4,z253,z22,z5]),(0,[z1,z8,z2,z3,z473,z4,z5]),(1,[z1,z8,z2,z39,z171,z5])]],
   [[(0,[z1,z8,z2,z3,z474,z4,z5]),(0,[z1,z8,z2,z171,z4,z5,z74])],[(0,[z1,z8,z2,z475,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z476,z5]),(0,[z1,z8,z385,z2,z3,z4,z5]),(0,[z63,z29,z1,z8,z2,z4,z5]),(0,[z1,z8,z2,z3,z477,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z478]),(0,[z479,z1,z8,z2,z3,z4,z5])],[(0,[z55,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z480,z5]),(0,[z95,z1,z8,z2,z3,z4,z5])],[(0,[z226,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z481,z4,z5])],[(0,[z482,z1,z8,z2,z3,z4,z5]),(0,[z155,z1,z8,z2,z3,z4,z5]),(1,[z483,z1,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z484,z5]),(0,[z1,z8,z145,z3,z4,z5,z36]),(0,[z1,z8,z2,z3,z4,z485,z5])],[(0,[z1,z8,z2,z3,z4,z5,z486]),(0,[z1,z8,z2,z3,z4,z5,z487]),(0,[z1,z8,z2,z39,z3,z84,z5])],[(0,[z488,z1,z8,z2,z3,z4,z5]),(0,[z293,z1,z8,z2,z39,z3,z5]),(0,[z489,z1,z8,z2,z3,z4,z5])],[(0,[z1,z8,z2,z490,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z491,z5])]],
   [[(0,[z1,z80,z2,z60,z3,z4,z5]),(0,[z483,z65,z1,z2,z3,z4,z5]),(0,[z492,z1,z8,z2,z3,z4,z5]),(0,[z493,z1,z8,z2,z3,z4,z5]),(0,[z23,z1,z8,z25,z3,z4,z5]),(0,[z1,z8,z2,z39,z3,z5,z58])],[(0,[z65,z1,z8,z2,z3,z14,z5]),(0,[z1,z8,z2,z3,z4,z494,z5]),(0,[z1,z8,z2,z3,z4,z495,z5])],[(0,[z1,z8,z2,z3,z4,z5,z496]),(0,[z1,z8,z2,z3,z497,z4,z5]),(0,[z498,z1,z8,z2,z3,z4,z5]),(0,[z13,z1,z61,z8,z2,z3,z4]),(0,[z1,z8,z100,z2,z3,z4,z5]),(0,[z144,z1,z2,z101,z3,z4,z5]),(0,[z64,z1,z8,z38,z2,z3,z5]),(0,[z8,z2,z3,z4,z5,z360,z58])],[(0,[z1,z8,z2,z347,z3,z4,z5]),(0,[z42,z59,z1,z2,z3,z4,z5]),(0,[z124,z1,z8,z2,z3,z4,z5]),(0,[z499,z1,z8,z2,z3,z4,z5])],[(1,[z1,z8,z2,z3,z4,z5]),(0,[z500,z1,z8,z2,z3,z4,z5])],[(0,[z1,z8,z416,z2,z3,z4,z5]),(0,[z29,z1,z8,z2,z30,z4,z5]),(1,[z1,z8,z2,z3,z112,z5]),(0,[z97,z124,z1,z2,z3,z4,z5]),(0,[z1,z8,z25,z145,z3,z4,z5])],[(0,[z158,z0,z8,z2,z3,z4,z5]),(0,[z29,z1,z385,z2,z3,z4,z5]),(0,[z1,z8,z2,z501,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z502,z5]),(0,[z293,z1,z8,z2,z3,z79,z5])],[(0,[z503,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z504,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z26,z5]),(0,[z1,z8,z2,z3,z26,z5,z237])]],
   [[(0,[z1,z8,z2,z505,z3,z4,z5]),(0,[z506,z1,z8,z2,z3,z4,z5]),(0,[z65,z1,z8,z2,z3,z4,z5]),(0,[z483,z1,z8,z2,z3,z4,z5]),(1,[z1,z8,z2,z507,z4,z5]),(0,[z293,z144,z1,z8,z3,z4,z5]),(0,[z508,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z509,z4,z5]),(0,[z1,z8,z2,z510,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z511,z5])],[(0,[z293,z155,z1,z8,z2,z3,z5]),(0,[z1,z8,z2,z3,z4,z512,z5]),(0,[z1,z8,z2,z3,z4,z513,z5]),(0,[z64,z1,z8,z2,z4,z119,z5])],[(0,[z1,z8,z2,z514,z3,z4,z5]),(0,[z1,z8,z515,z2,z3,z4,z5]),(0,[z1,z114,z8,z101,z3,z4,z5]),(0,[z1,z8,z516,z2,z3,z4,z5]),(0,[z293,z1,z8,z3,z4,z94,z5]),(0,[z1,z8,z2,z3,z4,z5,z316]),(0,[z1,z8,z2,z85,z3,z4,z5]),(0,[z1,z517,z8,z2,z3,z4,z5])],[(0,[z518,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z519,z3,z4,z5]),(0,[z1,z8,z2,z520,z3,z4,z5])],[(0,[z1,z8,z2,z3,z4,z5,z521]),(0,[z522,z1,z8,z2,z3,z4,z5]),(0,[z76,z1,z2,z3,z84,z4,z5])],[(0,[z523,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z524]),(0,[z1,z8,z38,z2,z3,z94,z5]),(0,[z1,z8,z38,z2,z3,z84,z5]),(0,[z1,z8,z178,z2,z3,z4,z5])],[(0,[z525,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z526,z5]),(0,[z1,z8,z111,z2,z145,z4,z5]),(0,[z76,z1,z8,z2,z3,z4,z5])],[(0,[z1,z527,z8,z2,z3,z4,z5]),(0,[z121,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z528,z3,z4,z5]),(0,[z1,z8,z2,z30,z85,z4,z5]),(0,[z529,z1,z8,z2,z3,z4,z5]),(0,[z144,z1,z114,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z530,z4,z5]),(0,[z97,z1,z2,z3,z4,z5,z6]),(0,[z531,z1,z8,z2,z3,z4,z5])]],
   [[(0,[z1,z8,z2,z3,z532,z4,z5]),(0,[z1,z533,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z5]),(0,[z1,z8,z2,z534,z3,z4,z5]),(0,[z1,z8,z2,z3,z535,z4,z5]),(0,[z536,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z38,z2,z3,z5,z58]),(1,[z352,z1,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z537,z5])],[(0,[z1,z8,z2,z3,z4,z538,z5]),(0,[z1,z8,z2,z3,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z539,z5]),(0,[z1,z8,z2,z3,z4,z540,z5]),(0,[z1,z114,z8,z3,z79,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z541]),(0,[z1,z8,z542,z2,z3,z4,z5]),(0,[z1,z8,z543,z2,z3,z4,z5])],[(0,[z234,z1,z8,z3,z48,z4,z5]),(0,[z1,z8,z2,z544,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z545]),(0,[z1,z8,z111,z2,z171,z4,z5]),(0,[z1,z8,z2,z3,z4,z546,z5])],[(1,[z317,z80,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z547,z4,z5]),(0,[z1,z8,z2,z48,z4,z5,z74]),(0,[z42,z1,z8,z2,z60,z4,z5]),(1,[z90,z8,z2,z3,z4,z5]),(0,[z548,z1,z8,z2,z3,z4,z5]),(1,[z1,z8,z2,z223,z4,z5]),(0,[z1,z8,z2,z4,z18,z5,z210])],[(0,[z549,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z550,z3,z4,z5]),(0,[z155,z1,z8,z2,z3,z21,z5]),(0,[z1,z8,z2,z551,z3,z4,z5]),(0,[z1,z552,z8,z2,z3,z4,z5])],[(1,[z226,z1,z8,z2,z3,z4]),(0,[z1,z8,z2,z553,z3,z4,z5]),(0,[z1,z8,z2,z554,z3,z4,z5]),(0,[z555,z1,z8,z2,z3,z4,z5])],[(0,[z121,z29,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z556,z4,z5]),(0,[z1,z8,z2,z3,z4,z557,z5]),(0,[z1,z558,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z559]),(0,[z560,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z561])],[(0,[z562,z1,z8,z2,z3,z4,z5]),(1,[z1,z8,z2,z347,z4,z5]),(0,[z13,z65,z8,z2,z3,z4,z5]),(1,[z1,z8,z563,z3,z4,z5]),(0,[z564,z1,z8,z2,z3,z4,z5]),(0,[z42,z1,z2,z3,z43,z4,z5]),(1,[z124,z1,z2,z3,z21,z5]),(1,[z1,z8,z2,z3,z406,z5]),(0,[z1,z8,z2,z565,z3,z4,z5]),(0,[z64,z1,z8,z2,z39,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z566])]],
   [[(0,[z1,z8,z2,z3,z4,z22,z5]),(0,[z567,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z568,z5]),(0,[z1,z8,z2,z569,z3,z4,z5])],[(1,[z132,z1,z8,z2,z4,z5]),(0,[z1,z570,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z330,z4,z5]),(0,[z1,z8,z2,z3,z4,z571,z5])],[(0,[z1,z8,z2,z572,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z94,z5]),(0,[z1,z8,z3,z79,z4,z5,z36])],[(0,[z144,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z573,z3,z4,z5]),(0,[z1,z574,z8,z2,z3,z4,z5])],[(0,[z1,z1,z8,z2,z3,z4,z5]),(0,[z575,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z576]),(0,[z1,z8,z2,z3,z4,z5,z577]),(0,[z1,z8,z3,z4,z26,z5,z36]),(0,[z578,z1,z8,z2,z3,z4,z5])],[],[(0,[z1,z8,z2,z3,z4,z579,z5]),(0,[z124,z1,z2,z3,z4,z62,z5]),(0,[z1,z8,z2,z3,z4,z5,z580]),(0,[z1,z8,z2,z581,z3,z4,z5])],[(0,[z582,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z583,z2,z3,z4,z5]),(0,[z584,z1,z8,z2,z3,z4,z5]),(0,[z144,z1,z8,z101,z3,z4,z5]),(0,[z1,z8,z585,z2,z3,z4,z5]),(0,[z97,z37,z8,z2,z3,z4,z5]),(1,[z1,z61,z2,z3,z4,z62]),(0,[z1,z8,z2,z3,z4,z5,z586]),(0,[z352,z1,z2,z3,z4,z5,z36])]],
   [[(0,[z587,z1,z8,z2,z3,z4,z5]),(0,[z8,z2,z30,z3,z48,z4,z5]),(0,[z65,z1,z8,z2,z3,z21,z5]),(0,[z293,z65,z1,z8,z2,z3,z5]),(0,[z588,z1,z8,z2,z3,z4,z5]),(0,[z1,z114,z100,z2,z3,z4,z5])],[(0,[z1,z8,z2,z563,z3,z4,z5]),(0,[z44,z1,z8,z2,z3,z21,z5]),(0,[z1,z8,z2,z3,z589,z4,z5])],[(0,[z144,z0,z1,z2,z3,z4,z5]),(0,[z590,z1,z8,z2,z3,z4,z5])],[(0,[z1,z8,z591,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z592,z5]),(1,[z23,z1,z8,z3,z4,z36]),(0,[z1,z8,z2,z3,z4,z593,z5]),(0,[z1,z8,z594,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z595,z4,z5])],[(0,[z1,z8,z2,z596,z3,z4,z5]),(0,[z64,z42,z1,z8,z2,z4,z5])],[(0,[z597,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z598,z2,z3,z4,z5]),(1,[z1,z8,z2,z4,z93,z5])],[(0,[z599,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z111,z2,z3,z4,z5])],[(0,[z160,z1,z416,z2,z3,z4,z5]),(0,[z63,z160,z1,z8,z3,z4,z5]),(0,[z600,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z322,z4,z18,z5])]],
   [[(0,[z13,z1,z8,z2,z3,z4,z5]),(1,[z1,z8,z601,z3,z4,z5]),(0,[z1,z8,z145,z3,z195,z4,z5])],[(0,[z1,z8,z2,z3,z4,z5,z602]),(0,[z1,z8,z2,z3,z84,z4,z5])],[(0,[z0,z1,z100,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z603,z5]),(0,[z97,z1,z8,z2,z3,z4,z6]),(0,[z1,z8,z2,z604,z3,z4,z5])],[(0,[z1,z8,z8,z2,z3,z4,z5]),(0,[z605,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z606,z4,z5])],[(0,[z1,z8,z2,z3,z4,z5,z607]),(0,[z13,z1,z8,z2,z507,z4,z5])],[(0,[z1,z8,z2,z3,z4,z5,z608]),(0,[z609,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z610,z2,z3,z4,z5]),(0,[z155,z8,z2,z3,z14,z4,z5]),(0,[z1,z8,z2,z3,z611,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z612]),(0,[z1,z8,z2,z3,z4,z5,z613]),(0,[z614,z1,z8,z2,z3,z4,z5]),(1,[z1,z8,z2,z3,z84,z18])],[(0,[z1,z8,z2,z3,z4,z615,z5]),(0,[z97,z1,z8,z601,z3,z4,z5]),(0,[z293,z64,z1,z8,z2,z3,z5])],[(0,[z1,z8,z616,z2,z3,z4,z5]),(0,[z617,z1,z8,z2,z3,z4,z5]),(0,[z618,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z619,z2,z3,z4,z5]),(0,[z129,z8,z2,z3,z4,z5,z58])]],
   [[(0,[z1,z8,z620,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z621]),(0,[z1,z8,z2,z3,z622,z4,z5])],[(0,[z1,z8,z2,z3,z4,z623,z5]),(0,[z624,z1,z8,z2,z3,z4,z5]),(0,[z42,z1,z8,z2,z43,z4,z5]),(0,[z97,z1,z2,z60,z3,z4,z5]),(1,[z209,z1,z8,z2,z4,z5])],[(0,[z1,z2,z60,z3,z43,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z625]),(0,[z1,z8,z2,z601,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z93,z5])],[(0,[z317,z1,z80,z2,z3,z4,z5]),(0,[z1,z8,z626,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z627,z5]),(0,[z1,z8,z2,z3,z4,z628,z5]),(0,[z1,z8,z2,z3,z4,z629,z5])],[(0,[z0,z317,z1,z2,z3,z4,z5]),(0,[z7,z1,z8,z2,z3,z4,z9]),(1,[z536,z8,z2,z3,z4,z5])],[(0,[z42,z1,z80,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z630,z4,z5])],[(0,[z144,z1,z2,z3,z4,z62,z5]),(0,[z631,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z22,z5,z58]),(0,[z1,z8,z2,z3,z84,z4,z58])],[(0,[z1,z632,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z633,z4,z5])]],
   [[(0,[z29,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z634,z5]),(0,[z155,z1,z8,z2,z3,z57,z5]),(0,[z1,z8,z25,z101,z3,z4,z5]),(0,[z1,z635,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z636,z3,z4,z5])],[(0,[z637,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z638,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z639,z4,z5]),(0,[z44,z1,z2,z3,z4,z22,z5]),(0,[z1,z8,z2,z640,z3,z4,z5])],[(0,[z124,z1,z80,z2,z3,z4,z5]),(0,[z641,z1,z8,z2,z3,z4,z5]),(0,[z97,z536,z8,z2,z3,z4,z5]),(0,[z642,z1,z8,z2,z3,z4,z5]),(1,[z1,z8,z2,z322,z4,z5])],[(0,[z13,z1,z8,z563,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z643,z5]),(0,[z1,z8,z2,z3,z644,z4,z5])],[(0,[z1,z8,z2,z3,z4,z645,z5]),(0,[z180,z1,z8,z2,z3,z48,z5]),(0,[z1,z8,z2,z3,z4,z5,z646]),(0,[z1,z8,z2,z3,z4,z5,z647]),(0,[z124,z1,z2,z3,z21,z4,z5]),(0,[z1,z8,z2,z3,z4,z648,z5])],[(0,[z1,z8,z2,z3,z649,z4,z5]),(0,[z23,z1,z8,z2,z3,z4,z26]),(1,[z129,z8,z2,z3,z4,z5])],[(0,[z1,z8,z2,z507,z3,z4,z5]),(1,[z1,z8,z2,z3,z259,z5]),(0,[z63,z293,z1,z8,z3,z4,z5]),(0,[z1,z8,z2,z3,z84,z18,z5])],[(0,[z1,z8,z2,z30,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z650,z5]),(0,[z1,z8,z25,z3,z79,z4,z5]),(0,[z651,z1,z8,z2,z3,z4,z5])]],
   [[(0,[z1,z8,z652,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z22,z5]),(0,[z1,z8,z2,z3,z4,z653,z5]),(0,[z1,z8,z349,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z171,z4,z5])],[(0,[z1,z8,z2,z3,z654,z4,z5]),(0,[z293,z1,z8,z2,z3,z4,z5])],[(0,[z317,z8,z80,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z655,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z656])],[(0,[z1,z8,z2,z3,z657,z4,z5]),(0,[z658,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z659,z5]),(0,[z121,z1,z8,z111,z2,z4,z5]),(0,[z660,z1,z8,z2,z3,z4,z5])],[(0,[z661,z1,z8,z2,z3,z4,z5]),(0,[z65,z1,z8,z2,z3,z57,z5]),(0,[z1,z8,z2,z3,z662,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z663])],[(0,[z1,z8,z664,z2,z3,z4,z5]),(0,[z665,z1,z8,z2,z3,z4,z5])],[(0,[z1,z8,z2,z3,z666,z4,z5]),(0,[z1,z61,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z257,z5]),(0,[z1,z8,z2,z3,z4,z62,z5]),(0,[z1,z8,z2,z3,z4,z5,z667]),(0,[z1,z8,z2,z3,z668,z4,z5])],[(0,[z669,z1,z8,z2,z3,z4,z5]),(0,[z670,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z671,z4,z5]),(0,[z672,z1,z8,z2,z3,z4,z5])]],
   [[(0,[z1,z8,z2,z3,z673,z4,z5]),(0,[z1,z8,z2,z3,z4,z674,z5]),(0,[z1,z8,z2,z3,z4,z675,z5]),(0,[z1,z8,z2,z3,z4,z676,z5])],[(0,[z677,z1,z8,z2,z3,z4,z5]),(0,[z1,z114,z8,z2,z3,z4,z5])],[(1,[z1,z8,z2,z3,z232,z5]),(0,[z1,z8,z2,z3,z4,z5,z678]),(0,[z293,z1,z114,z8,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z679,z5])],[(0,[z158,z1,z8,z2,z3,z4,z5]),(0,[z64,z155,z1,z8,z2,z3,z5]),(0,[z1,z8,z145,z3,z79,z4,z5]),(0,[z1,z8,z2,z3,z680,z4,z5]),(0,[z681,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z682,z3,z4,z5]),(1,[z95,z1,z8,z2,z3,z58])],[(0,[z44,z1,z8,z2,z3,z4,z5]),(0,[z151,z1,z2,z3,z4,z5,z74]),(1,[z1,z2,z3,z4,z135,z5])],[(0,[z160,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z14,z4,z5]),(0,[z1,z8,z2,z3,z683,z4,z5]),(0,[z1,z2,z3,z84,z4,z135,z5])],[(0,[z684,z1,z8,z2,z3,z4,z5]),(0,[z0,z124,z1,z2,z3,z4,z5]),(0,[z685,z1,z8,z2,z3,z4,z5]),(0,[z353,z1,z8,z2,z3,z4,z5]),(1,[z1,z8,z3,z4,z11,z5]),(0,[z686,z1,z8,z2,z3,z4,z5])],[(0,[z1,z8,z2,z3,z687,z4,z5]),(1,[z1,z134,z2,z3,z4,z5]),(0,[z688,z1,z8,z2,z3,z4,z5]),(1,[z1,z8,z2,z3,z196,z5])]],
   [[(0,[z1,z8,z2,z3,z689,z4,z5]),(0,[z690,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z691,z4,z5])],[(0,[z692,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z693,z3,z4,z5]),(0,[z59,z1,z8,z2,z3,z4,z5]),(0,[z694,z1,z8,z2,z3,z4,z5])],[(0,[z158,z0,z1,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z695,z4,z5]),(0,[z1,z8,z2,z3,z4,z696,z5])],[(0,[z0,z1,z8,z2,z3,z4,z5]),(0,[z55,z8,z2,z56,z3,z4,z5]),(0,[z64,z1,z8,z2,z85,z4,z5])],[(0,[z1,z8,z2,z3,z4,z697,z5]),(0,[z698,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z699,z3,z4,z5]),(1,[z1,z2,z3,z4,z5,z157])],[(1,[z160,z8,z35,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z5,z700]),(0,[z1,z8,z2,z3,z4,z5,z701])],[(0,[z1,z8,z2,z3,z702,z4,z5]),(0,[z1,z703,z8,z2,z3,z4,z5])],[(0,[z704,z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z705,z3,z4,z5]),(0,[z706,z1,z8,z2,z3,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z401,z2,z3,z4,z5]),(0,[z1,z8,z707,z3,z4,z5]),(0,[z1,z8,z2,z708,z4,z5]),(0,[z209,z1,z8,z2,z4,z5])],[(0,[z226,z1,z100,z2,z3,z4]),(0,[z44,z1,z2,z3,z709,z5]),(0,[z354,z1,z8,z2,z84,z5]),(0,[z710,z1,z2,z3,z4,z5])],[(0,[z711,z1,z2,z3,z4,z5]),(0,[z76,z1,z2,z3,z406,z5]),(0,[z293,z1,z8,z565,z3,z5]),(0,[z1,z8,z2,z85,z4,z712])],[(0,[z536,z8,z2,z3,z4,z5]),(0,[z1,z8,z713,z3,z4,z5]),(0,[z1,z8,z2,z3,z5,z714]),(0,[z8,z2,z3,z4,z9,z367]),(0,[z1,z8,z25,z3,z4,z512]),(0,[z352,z1,z601,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z715])],[(0,[z1,z8,z2,z3,z716,z5]),(0,[z717,z1,z2,z3,z4,z5]),(0,[z1,z8,z2,z718,z4,z5]),(0,[z354,z1,z8,z2,z5,z58])],[(0,[z8,z2,z3,z719,z4,z5]),(0,[z234,z1,z8,z4,z5,z74]),(0,[z1,z8,z720,z3,z4,z5]),(0,[z1,z8,z2,z3,z721,z5]),(0,[z8,z2,z3,z722,z4,z5]),(0,[z129,z8,z2,z3,z57,z5]),(0,[z723,z1,z8,z2,z4,z5]),(0,[z97,z536,z2,z3,z4,z6])],[(0,[z724,z8,z2,z3,z4,z5]),(0,[z725,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z726,z5])],[(0,[z354,z1,z80,z2,z4,z5]),(0,[z727,z1,z8,z2,z4,z5]),(0,[z1,z8,z2,z3,z728,z5]),(0,[z1,z8,z2,z729,z3,z5]),(0,[z76,z1,z2,z3,z21,z5])]],
   [[(0,[z1,z2,z3,z298,z22,z5])],[(0,[z1,z8,z2,z730,z4,z5]),(0,[z1,z8,z731,z3,z4,z5]),(0,[z1,z8,z2,z732,z4,z5]),(0,[z1,z8,z2,z733,z4,z5]),(0,[z1,z8,z2,z171,z734,z5])],[(0,[z1,z8,z2,z3,z735,z5]),(0,[z1,z8,z2,z736,z4,z5]),(0,[z1,z8,z2,z171,z308,z5]),(0,[z354,z1,z2,z4,z62,z5]),(0,[z387,z1,z8,z250,z4,z5]),(0,[z1,z8,z601,z3,z406,z5]),(0,[z737,z8,z2,z3,z4,z5])],[(0,[z738,z1,z2,z3,z4,z5])],[(0,[z1,z8,z2,z113,z347,z5]),(0,[z1,z8,z2,z3,z739,z5]),(0,[z353,z1,z8,z39,z3,z5])],[(0,[z172,z8,z2,z3,z4,z5]),(0,[z740,z1,z8,z2,z4,z5]),(0,[z1,z8,z741,z3,z4,z5]),(0,[z1,z8,z2,z3,z259,z5]),(0,[z1,z8,z2,z3,z84,z216])],[(0,[z1,z8,z742,z3,z4,z5]),(0,[z1,z8,z3,z743,z4,z5]),(0,[z1,z61,z2,z3,z4,z744]),(0,[z1,z8,z178,z3,z4,z5]),(0,[z1,z8,z2,z745,z4,z5]),(0,[z746,z129,z2,z3,z4,z5]),(0,[z1,z8,z17,z4,z5,z210])],[(0,[z55,z132,z1,z8,z4,z5]),(0,[z1,z8,z2,z47,z3,z5]),(0,[z747,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z748])]],
   [[(0,[z1,z8,z2,z719,z4,z5])],[(0,[z1,z8,z3,z4,z749,z5]),(0,[z1,z750,z2,z3,z4,z5]),(0,[z1,z751,z2,z3,z4,z5]),(0,[z1,z8,z2,z507,z259,z5]),(0,[z387,z44,z1,z3,z22,z5]),(0,[z97,z1,z2,z3,z4,z744]),(0,[z1,z8,z85,z4,z128,z342])],[(0,[z286,z80,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z752])],[(0,[z1,z753,z2,z3,z4,z5]),(0,[z1,z8,z3,z4,z5,z754])],[(0,[z1,z8,z2,z3,z755,z5]),(0,[z1,z8,z756,z3,z4,z5]),(0,[z1,z2,z3,z4,z757,z5])],[(0,[z132,z1,z8,z2,z113,z5]),(0,[z1,z61,z20,z2,z3,z4])],[(0,[z1,z12,z100,z3,z4,z5]),(0,[z1,z8,z2,z4,z5,z758]),(0,[z1,z759,z2,z3,z4,z5]),(0,[z155,z8,z2,z429,z3,z5]),(0,[z1,z8,z2,z760,z4,z5]),(0,[z1,z8,z2,z4,z761,z5]),(0,[z536,z8,z2,z3,z406,z5]),(0,[z63,z1,z8,z176,z4,z5]),(0,[z1,z762,z2,z3,z4,z5])],[(0,[z226,z42,z1,z2,z3,z4]),(0,[z234,z180,z1,z8,z3,z5]),(0,[z763,z1,z8,z3,z4,z5]),(0,[z29,z8,z2,z719,z4,z5]),(0,[z1,z8,z2,z4,z5,z764]),(0,[z1,z8,z2,z126,z257,z5]),(0,[z1,z8,z2,z3,z765,z5]),(1,[z1,z8,z2,z3,z766])]],
   [[(0,[z1,z8,z2,z3,z767,z5]),(0,[z387,z1,z8,z3,z5,z58]),(0,[z1,z8,z2,z4,z5,z768]),(0,[z76,z1,z2,z3,z84,z18])],[(0,[z90,z80,z2,z3,z4,z5]),(0,[z63,z1,z8,z655,z4,z5]),(0,[z55,z132,z8,z56,z4,z5]),(0,[z1,z8,z2,z3,z769,z5]),(0,[z1,z8,z2,z201,z4,z5]),(0,[z1,z8,z2,z3,z4,z770]),(0,[z771,z1,z8,z3,z4,z5])],[(0,[z1,z61,z2,z3,z4,z623]),(0,[z7,z134,z2,z3,z4,z5]),(0,[z1,z8,z2,z201,z112,z5]),(0,[z59,z1,z2,z4,z537,z5]),(0,[z1,z8,z2,z3,z5,z772]),(0,[z95,z1,z8,z2,z3,z58]),(0,[z773,z1,z8,z3,z4,z5])],[(0,[z1,z8,z2,z774,z4,z5]),(0,[z1,z2,z3,z4,z135,z5]),(0,[z63,z1,z8,z662,z4,z5]),(0,[z775,z1,z8,z2,z4,z5])],[(0,[z584,z80,z2,z3,z4,z5]),(0,[z121,z8,z2,z47,z48,z5]),(0,[z65,z8,z2,z3,z502,z5]),(0,[z1,z8,z2,z39,z388,z5]),(0,[z209,z1,z8,z79,z4,z5]),(0,[z1,z8,z2,z4,z5,z210])],[(0,[z1,z8,z2,z3,z776,z5]),(0,[z1,z777,z2,z3,z4,z5]),(0,[z13,z8,z356,z3,z4,z72]),(0,[z1,z8,z2,z778,z3,z5]),(0,[z42,z1,z2,z126,z4,z5]),(0,[z1,z779,z2,z3,z4,z5]),(0,[z1,z8,z3,z4,z11,z5]),(0,[z1,z8,z2,z780,z4,z5])],[(0,[z1,z8,z2,z3,z196,z5]),(0,[z95,z8,z2,z3,z360,z58])],[(0,[z1,z8,z781,z3,z4,z5]),(0,[z1,z8,z2,z3,z782,z5]),(0,[z1,z8,z2,z783,z4,z5])]],
   [[(0,[z1,z8,z2,z784,z3,z5]),(0,[z1,z785,z2,z3,z4,z5]),(0,[z1,z8,z563,z3,z259,z5]),(0,[z1,z786,z2,z3,z4,z5])],[(0,[z1,z8,z787,z3,z4,z5]),(0,[z1,z788,z2,z3,z4,z5]),(0,[z789,z1,z8,z2,z3,z5])],[(0,[z1,z8,z790,z3,z4,z5]),(0,[z1,z8,z2,z113,z3,z5]),(0,[z791,z1,z8,z2,z3,z5])],[(0,[z1,z2,z3,z4,z5,z157]),(0,[z792,z8,z2,z3,z4,z5]),(0,[z64,z129,z8,z2,z3,z5])],[(0,[z1,z8,z2,z793,z4,z5]),(0,[z1,z794,z2,z3,z4,z5]),(0,[z97,z1,z2,z3,z4,z458])],[(0,[z1,z8,z2,z795,z4,z5]),(0,[z706,z0,z2,z3,z4,z5]),(0,[z234,z1,z8,z3,z4,z5]),(0,[z63,z1,z8,z519,z4,z5]),(0,[z1,z8,z2,z796,z4,z5]),(0,[z1,z2,z3,z709,z4,z5])],[],[(0,[z132,z1,z8,z25,z4,z5]),(0,[z1,z8,z2,z3,z5,z797]),(0,[z1,z8,z798,z3,z4,z5]),(0,[z1,z8,z2,z799,z4,z5]),(0,[z65,z8,z2,z3,z460,z5]),(0,[z7,z8,z2,z3,z4,z9]),(0,[z1,z8,z2,z800,z4,z5]),(0,[z801,z1,z8,z2,z3,z5]),(0,[z536,z8,z601,z3,z4,z5]),(0,[z202,z1,z8,z2,z3,z5]),(0,[z1,z8,z2,z3,z802,z5])]],
   [[(0,[z1,z8,z2,z803,z4,z5]),(0,[z804,z1,z8,z2,z3,z5]),(0,[z1,z8,z2,z3,z805,z5]),(0,[z1,z8,z25,z223,z4,z26]),(0,[z64,z1,z8,z2,z480,z5])],[(0,[z1,z8,z2,z3,z806,z5]),(0,[z1,z8,z2,z3,z807,z5]),(0,[z124,z172,z2,z3,z21,z5]),(0,[z1,z8,z2,z171,z557,z5])],[(0,[z1,z8,z2,z85,z4,z278]),(0,[z13,z8,z2,z3,z4,z83]),(0,[z8,z2,z3,z4,z9,z808]),(0,[z1,z8,z3,z4,z809,z5]),(0,[z1,z8,z3,z196,z5,z36]),(0,[z1,z8,z2,z3,z18,z766])],[(0,[z1,z245,z2,z3,z4,z5])],[(0,[z1,z8,z2,z3,z810,z5]),(0,[z483,z1,z2,z3,z82,z5]),(0,[z1,z8,z2,z811,z4,z5]),(0,[z1,z8,z563,z201,z4,z5]),(0,[z812,z1,z8,z2,z4,z5]),(0,[z44,z1,z2,z3,z22,z5]),(0,[z202,z1,z8,z111,z2,z5])],[(0,[z1,z8,z3,z4,z253,z5]),(0,[z209,z1,z8,z38,z2,z5]),(0,[z1,z8,z2,z223,z196,z5]),(0,[z1,z8,z813,z3,z4,z5])],[],[(0,[z227,z1,z2,z3,z4,z5]),(0,[z124,z1,z2,z3,z82,z5]),(0,[z814,z8,z2,z3,z4,z5]),(1,[z1,z2,z3,z709,z5]),(0,[z63,z202,z1,z8,z195,z5]),(0,[z1,z815,z2,z3,z4,z5]),(1,[z353,z64,z1,z8,z5])]],
   [[(0,[z1,z31,z2,z3,z4,z5]),(0,[z711,z80,z2,z3,z4,z5]),(0,[z144,z37,z2,z3,z4,z5]),(0,[z59,z1,z2,z60,z4,z5]),(0,[z37,z2,z3,z4,z5,z6]),(0,[z1,z8,z3,z726,z94,z5])],[(0,[z1,z8,z2,z816,z4,z5]),(0,[z1,z31,z2,z3,z112,z5]),(0,[z7,z37,z8,z2,z3,z4]),(0,[z817,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z4,z5,z712])],[(0,[z1,z2,z3,z4,z818,z5]),(0,[z1,z8,z2,z3,z4,z712]),(0,[z819,z8,z2,z3,z4,z5])],[(0,[z1,z8,z2,z820,z3,z5]),(0,[z8,z2,z30,z719,z4,z5]),(0,[z1,z61,z134,z2,z3,z4]),(0,[z1,z100,z3,z4,z5,z407]),(0,[z1,z8,z349,z98,z4,z5]),(0,[z1,z8,z2,z3,z5,z821])],[(0,[z523,z1,z2,z3,z22,z5]),(0,[z1,z31,z2,z507,z4,z5]),(1,[z1,z2,z3,z4,z744]),(0,[z1,z8,z2,z322,z84,z5])],[(0,[z1,z8,z2,z822,z4,z5]),(0,[z823,z1,z8,z2,z3,z5])],[(0,[z63,z174,z1,z8,z4,z5]),(0,[z1,z8,z2,z3,z824,z5]),(0,[z180,z1,z8,z2,z3,z5]),(0,[z97,z1,z134,z2,z3,z4]),(1,[z1,z2,z825,z4,z5]),(0,[z1,z8,z2,z250,z4,z5])],[(0,[z1,z8,z25,z3,z4,z579]),(0,[z483,z1,z2,z3,z22,z5]),(0,[z13,z37,z8,z2,z3,z4]),(0,[z1,z8,z2,z322,z5,z58])]],
   [[(0,[z1,z8,z2,z826,z4,z5]),(0,[z234,z1,z8,z85,z4,z5]),(0,[z827,z1,z2,z3,z4,z5]),(0,[z1,z8,z828,z3,z4,z5]),(0,[z1,z8,z2,z3,z829,z5]),(0,[z1,z2,z830,z3,z4,z5]),(0,[z1,z2,z3,z831,z4,z5])],[(0,[z1,z8,z38,z3,z5,z87]),(0,[z1,z832,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z676,z58])],[(0,[z1,z8,z833,z3,z4,z5]),(0,[z183,z8,z2,z48,z4,z5]),(0,[z65,z430,z8,z2,z3,z5]),(0,[z1,z8,z2,z3,z834,z5]),(0,[z1,z8,z2,z126,z4,z5])],[(0,[z226,z1,z61,z2,z3,z4]),(0,[z1,z8,z349,z126,z4,z5])],[(0,[z1,z835,z2,z3,z4,z5]),(0,[z1,z114,z100,z3,z4,z5]),(0,[z1,z2,z3,z4,z62,z252]),(0,[z1,z8,z836,z3,z4,z5])],[(0,[z271,z1,z8,z3,z4,z36]),(0,[z1,z8,z2,z3,z5,z837]),(0,[z23,z1,z3,z4,z316,z36]),(0,[z1,z8,z178,z3,z205,z5])],[(0,[z1,z8,z838,z3,z4,z5]),(0,[z1,z8,z2,z3,z839,z5]),(0,[z1,z8,z840,z3,z4,z5]),(0,[z8,z2,z3,z14,z259,z5]),(0,[z1,z8,z841,z3,z4,z5]),(0,[z1,z8,z2,z3,z842,z5]),(0,[z1,z8,z2,z3,z843,z5])],[(0,[z1,z8,z844,z3,z4,z5]),(0,[z134,z2,z3,z4,z5,z72]),(0,[z845,z1,z2,z3,z4,z5]),(0,[z1,z8,z3,z4,z846,z5])]],
   [[(0,[z1,z8,z2,z847,z4,z5]),(0,[z1,z8,z848,z3,z4,z5]),(0,[z849,z1,z2,z3,z4,z5]),(0,[z850,z1,z2,z3,z4,z5]),(0,[z590,z1,z2,z60,z4,z5]),(1,[z293,z209,z1,z8,z5])],[(0,[z851,z1,z8,z2,z4,z5]),(0,[z8,z2,z3,z722,z57,z5]),(0,[z42,z1,z2,z825,z4,z5]),(0,[z354,z1,z8,z4,z253,z5]),(0,[z76,z852,z2,z3,z4,z5])],[(0,[z1,z8,z2,z3,z5,z853])],[(0,[z1,z31,z563,z3,z4,z5]),(0,[z854,z1,z8,z2,z4,z5])],[(0,[z1,z855,z2,z3,z4,z5]),(0,[z1,z2,z3,z825,z4,z5]),(0,[z856,z8,z2,z3,z4,z5])],[(0,[z8,z2,z719,z48,z4,z5]),(0,[z1,z8,z2,z98,z406,z5]),(0,[z1,z8,z38,z3,z79,z5])],[(0,[z226,z124,z1,z2,z3,z4]),(0,[z226,z1,z8,z2,z3,z806]),(0,[z1,z8,z111,z146,z4,z5]),(0,[z129,z8,z2,z3,z259,z5]),(0,[z144,z1,z101,z3,z4,z5]),(0,[z1,z8,z111,z145,z4,z5])],[]],
   [[(0,[z42,z1,z2,z437,z4,z5]),(0,[z160,z8,z857,z3,z4,z5]),(0,[z151,z1,z2,z3,z4,z5]),(0,[z1,z8,z858,z3,z4,z5]),(0,[z293,z209,z1,z8,z2,z5]),(0,[z8,z2,z859,z3,z4,z5]),(0,[z129,z8,z38,z2,z3,z5])],[(0,[z1,z8,z2,z4,z860,z5])],[(0,[z121,z8,z2,z719,z4,z5]),(0,[z1,z8,z3,z4,z5,z861]),(0,[z97,z1,z2,z98,z4,z6]),(0,[z8,z2,z3,z4,z5,z862]),(1,[z1,z8,z863,z4,z5]),(0,[z1,z8,z864,z3,z4,z5]),(0,[z1,z8,z2,z84,z18,z210])],[(0,[z1,z8,z2,z3,z865,z5]),(0,[z866,z1,z8,z2,z4,z5]),(0,[z63,z1,z8,z136,z4,z5]),(0,[z1,z8,z322,z4,z5,z295])],[(0,[z1,z8,z2,z3,z867,z5]),(0,[z868,z1,z2,z3,z4,z5]),(0,[z869,z1,z2,z3,z4,z5]),(0,[z341,z1,z8,z3,z4,z36]),(0,[z1,z8,z2,z3,z5,z870]),(0,[z1,z8,z2,z4,z871,z5])],[(0,[z1,z8,z2,z126,z406,z5])],[(0,[z1,z8,z2,z4,z5,z872]),(0,[z90,z8,z2,z3,z22,z5])],[(0,[z1,z8,z2,z873,z4,z5]),(0,[z1,z8,z874,z3,z4,z5]),(0,[z37,z8,z601,z3,z4,z5]),(0,[z353,z1,z8,z3,z4,z5]),(0,[z1,z8,z2,z734,z119,z5])]],
   [[(0,[z226,z1,z8,z2,z803,z4]),(0,[z1,z8,z2,z3,z875,z5]),(0,[z483,z65,z2,z3,z57,z5]),(0,[z1,z8,z2,z85,z205,z128])],[(0,[z1,z8,z356,z3,z4,z5]),(0,[z1,z8,z876,z3,z4,z5]),(1,[z8,z2,z3,z722,z5]),(0,[z8,z2,z3,z4,z5,z360]),(0,[z63,z1,z8,z330,z195,z5])],[(0,[z1,z8,z2,z877,z3,z5]),(0,[z65,z8,z2,z3,z645,z5]),(0,[z878,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z879,z5]),(0,[z37,z2,z60,z3,z4,z5]),(0,[z124,z1,z2,z3,z709,z5]),(0,[z97,z1,z2,z126,z4,z6]),(0,[z1,z8,z2,z98,z257,z5])],[(0,[z230,z1,z8,z2,z347,z5]),(0,[z1,z2,z3,z4,z5,z880]),(0,[z1,z2,z3,z4,z881,z5])],[(0,[z352,z1,z100,z3,z4,z5]),(0,[z64,z1,z8,z309,z2,z5]),(0,[z8,z2,z3,z4,z5,z882])],[(0,[z158,z0,z2,z3,z4,z5]),(0,[z1,z8,z356,z507,z4,z5])],[(0,[z65,z245,z2,z3,z57,z5]),(0,[z883,z1,z2,z3,z4,z5])],[(0,[z479,z8,z35,z3,z4,z5]),(0,[z1,z8,z884,z3,z4,z5]),(0,[z1,z8,z2,z3,z709,z5])]],
   [[(0,[z885,z1,z8,z2,z3,z4]),(0,[z1,z134,z2,z3,z259,z5]),(0,[z1,z114,z3,z4,z248,z5]),(0,[z1,z8,z2,z3,z4,z766])],[(0,[z1,z8,z886,z3,z4,z5]),(0,[z387,z354,z1,z8,z4,z5])],[],[(0,[z1,z8,z2,z3,z4,z887]),(0,[z293,z1,z8,z3,z418,z5])],[(0,[z8,z2,z857,z3,z4,z5]),(0,[z13,z8,z2,z3,z4,z72]),(0,[z293,z1,z8,z3,z726,z5]),(0,[z1,z8,z25,z3,z4,z26]),(0,[z1,z8,z2,z4,z485,z74])],[(0,[z13,z8,z2,z3,z112,z72]),(0,[z1,z8,z2,z863,z4,z5])],[(0,[z53,z1,z2,z3,z4,z5]),(0,[z1,z8,z3,z4,z888,z5]),(0,[z1,z8,z2,z889,z4,z5]),(0,[z1,z8,z2,z825,z4,z5]),(0,[z293,z129,z8,z2,z3,z5])],[(0,[z890,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z4,z491,z74]),(0,[z1,z8,z25,z3,z26,z237])]],
   [[(0,[z13,z8,z2,z507,z4,z72]),(0,[z1,z8,z3,z863,z4,z5])],[(0,[z1,z8,z891,z3,z4,z5]),(0,[z1,z8,z2,z892,z4,z5]),(0,[z155,z8,z2,z3,z14,z5]),(0,[z42,z37,z2,z3,z4,z5]),(0,[z1,z8,z3,z4,z726,z5])],[(0,[z1,z8,z3,z4,z5,z893]),(0,[z894,z8,z2,z3,z4,z5])],[(0,[z132,z230,z1,z8,z2,z5]),(0,[z8,z2,z3,z4,z5,z808]),(0,[z1,z8,z2,z895,z3,z5]),(0,[z63,z1,z8,z379,z4,z5]),(0,[z1,z8,z2,z3,z84,z629]),(0,[z1,z8,z896,z3,z4,z5])],[(0,[z1,z8,z2,z3,z4,z897]),(0,[z898,z1,z8,z2,z4,z5]),(0,[z588,z1,z8,z2,z3,z58]),(0,[z155,z8,z2,z3,z292,z5]),(0,[z1,z134,z2,z201,z4,z5]),(0,[z899,z1,z2,z3,z4,z5]),(0,[z1,z8,z2,z85,z4,z128])],[(0,[z65,z80,z2,z3,z22,z5]),(0,[z1,z8,z3,z4,z5,z900])],[(0,[z901,z1,z8,z2,z3,z5]),(0,[z97,z1,z349,z3,z4,z6])],[(0,[z226,z8,z2,z3,z14,z4]),(0,[z1,z8,z2,z3,z902,z5]),(0,[z42,z1,z27,z2,z4,z5]),(0,[z903,z8,z2,z3,z4,z5])]],
   [[(0,[z904,z1,z8,z2,z3,z4]),(0,[z160,z8,z3,z509,z4,z5]),(0,[z1,z8,z2,z3,z5,z905]),(0,[z1,z8,z2,z3,z906,z5]),(0,[z127,z1,z2,z4,z157,z74])],[(0,[z1,z8,z2,z907,z3,z5]),(0,[z230,z1,z8,z2,z3,z5]),(0,[z597,z1,z8,z2,z4,z74]),(0,[z1,z8,z908,z3,z4,z5]),(0,[z909,z8,z2,z3,z4,z5]),(0,[z910,z8,z2,z3,z4,z5])],[(0,[z226,z1,z134,z2,z3,z4]),(0,[z1,z8,z857,z3,z4,z5]),(0,[z1,z8,z3,z4,z5,z911]),(0,[z1,z31,z2,z3,z259,z5]),(0,[z1,z8,z2,z3,z912,z5]),(0,[z1,z8,z38,z3,z284,z5])],[(0,[z1,z8,z2,z4,z913,z5]),(0,[z1,z914,z2,z3,z4,z5]),(0,[z293,z1,z8,z3,z276,z5])],[(0,[z1,z8,z2,z4,z5,z915]),(0,[z916,z8,z2,z3,z4,z5]),(0,[z63,z293,z64,z1,z8,z5])],[(0,[z1,z8,z2,z3,z257,z5]),(0,[z1,z8,z3,z4,z5,z917]),(0,[z127,z1,z8,z2,z4,z712])],[(0,[z97,z1,z2,z3,z4,z468]),(0,[z1,z8,z2,z3,z918,z5]),(0,[z1,z8,z349,z3,z257,z5]),(0,[z293,z209,z1,z8,z3,z5]),(0,[z1,z8,z2,z919,z4,z5])],[(0,[z13,z8,z563,z3,z4,z72]),(0,[z1,z8,z2,z3,z4,z808]),(0,[z1,z8,z2,z920,z4,z5]),(0,[z921,z1,z8,z2,z4,z5]),(0,[z1,z8,z2,z85,z4,z216])]],
   [[(0,[z158,z483,z2,z3,z4,z5]),(0,[z1,z8,z2,z4,z712,z74])],[(0,[z1,z8,z922,z3,z4,z5]),(0,[z8,z2,z3,z4,z5,z923]),(0,[z924,z1,z2,z3,z4,z5])],[(0,[z1,z8,z2,z3,z925,z5]),(0,[z1,z8,z3,z4,z926,z5])],[(0,[z1,z8,z927,z3,z4,z5])],[(0,[z1,z928,z2,z3,z4,z5]),(0,[z1,z731,z101,z3,z4,z5]),(0,[z1,z8,z2,z85,z4,z513]),(0,[z1,z8,z178,z3,z5,z104])],[(0,[z121,z8,z125,z48,z4,z5]),(0,[z29,z385,z2,z30,z4,z5]),(0,[z1,z8,z2,z98,z4,z5]),(0,[z1,z8,z2,z4,z734,z5])],[(0,[z1,z8,z2,z3,z4,z929]),(0,[z1,z930,z2,z3,z4,z5]),(0,[z1,z8,z111,z4,z5,z602]),(0,[z293,z1,z8,z3,z5,z478])],[(0,[z931,z1,z8,z2,z3,z5]),(0,[z234,z121,z8,z48,z4,z5]),(0,[z1,z8,z3,z4,z5,z932]),(0,[z933,z8,z2,z3,z4,z5]),(0,[z151,z1,z2,z171,z4,z5])]],
   [[(0,[z934,z1,z8,z2,z3,z5]),(0,[z55,z454,z8,z3,z4,z5]),(0,[z129,z8,z2,z3,z22,z5])],[(0,[z1,z8,z935,z3,z4,z5]),(0,[z1,z8,z936,z3,z4,z5]),(0,[z937,z8,z2,z3,z4,z5])],[(0,[z8,z80,z2,z3,z82,z5]),(0,[z1,z8,z938,z3,z4,z5])],[(0,[z226,z1,z8,z742,z3,z4]),(0,[z293,z1,z8,z272,z3,z5])],[(0,[z939,z1,z2,z3,z4,z5]),(0,[z1,z8,z2,z940,z4,z5]),(0,[z1,z8,z2,z5,z34,z237])],[(0,[z121,z8,z2,z48,z4,z5]),(0,[z941,z1,z8,z3,z4,z5]),(0,[z95,z129,z8,z2,z3,z58])],[(0,[z155,z354,z1,z8,z2,z5]),(0,[z353,z1,z8,z171,z4,z5])],[(0,[z942,z1,z8,z2,z3,z4]),(0,[z1,z8,z2,z943,z4,z5])]],
   [[(0,[z1,z8,z2,z3,z944,z5]),(0,[z1,z2,z3,z4,z5,z945]),(0,[z1,z8,z2,z85,z128,z104]),(0,[z76,z819,z2,z3,z4,z5])],[(0,[z1,z8,z946,z3,z4,z5]),(0,[z1,z8,z2,z4,z947,z5]),(0,[z64,z1,z8,z2,z497,z5]),(0,[z1,z8,z3,z948,z4,z5]),(0,[z949,z8,z2,z3,z4,z5]),(0,[z144,z1,z516,z3,z4,z5]),(0,[z335,z1,z8,z2,z4,z74])],[(0,[z1,z8,z2,z950,z4,z5]),(0,[z1,z2,z3,z4,z5,z951]),(0,[z1,z8,z2,z3,z330,z5]),(0,[z1,z8,z3,z79,z217,z5]),(0,[z1,z8,z17,z3,z4,z5])],[(0,[z155,z8,z2,z3,z181,z5]),(0,[z1,z8,z2,z952,z4,z5]),(0,[z1,z2,z825,z43,z4,z5]),(0,[z1,z8,z2,z39,z171,z5]),(0,[z1,z8,z2,z3,z766,z58])],[(0,[z1,z2,z3,z4,z5,z744]),(0,[z1,z8,z25,z4,z26,z34]),(0,[z1,z8,z3,z205,z5,z342])],[(0,[z97,z1,z2,z3,z257,z6]),(0,[z953,z1,z8,z2,z3,z5])],[(0,[z1,z8,z2,z954,z4,z5]),(0,[z1,z8,z2,z3,z955,z5]),(0,[z129,z8,z2,z39,z3,z5])],[(0,[z1,z8,z2,z3,z5,z956]),(0,[z65,z134,z2,z3,z4,z5])]],
   [[(0,[z226,z1,z2,z3,z4,z22]),(0,[z293,z209,z1,z8,z4,z5]),(0,[z1,z8,z25,z223,z4,z5])],[(0,[z1,z957,z2,z3,z4,z5]),(0,[z1,z8,z958,z3,z4,z5]),(0,[z1,z8,z2,z959,z4,z5])],[(0,[z1,z960,z2,z3,z4,z5]),(0,[z1,z8,z961,z3,z4,z5]),(0,[z37,z8,z2,z98,z4,z5]),(0,[z63,z1,z8,z195,z4,z5])],[(0,[z1,z8,z2,z962,z4,z5]),(0,[z63,z202,z1,z8,z4,z5]),(0,[z1,z8,z2,z963,z4,z5])],[(0,[z1,z8,z964,z3,z4,z5]),(0,[z1,z8,z2,z3,z965,z5]),(0,[z97,z387,z1,z3,z4,z5])],[(0,[z966,z1,z8,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z967]),(0,[z1,z8,z3,z5,z342,z104])],[(0,[z7,z8,z314,z2,z3,z4]),(0,[z63,z202,z1,z8,z2,z5]),(0,[z64,z1,z8,z2,z176,z5])],[(0,[z226,z37,z8,z2,z3,z4]),(0,[z1,z8,z2,z85,z205,z5])]],
   [[(0,[z1,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z968,z4,z5]),(0,[z1,z8,z2,z4,z5,z969]),(0,[z1,z8,z2,z3,z4,z970]),(0,[z1,z2,z3,z21,z709,z5]),(0,[z971,z1,z2,z3,z4,z5]),(0,[z1,z8,z25,z3,z4,z972])],[(0,[z1,z8,z2,z3,z4,z973]),(0,[z1,z8,z349,z3,z4,z5]),(0,[z1,z8,z2,z3,z974,z5])],[(0,[z1,z8,z2,z975,z3,z4]),(0,[z1,z8,z3,z976,z4,z5]),(0,[z37,z8,z2,z126,z4,z5]),(0,[z977,z8,z2,z3,z4,z5]),(0,[z23,z1,z8,z3,z4,z972])],[(0,[z1,z978,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z979,z5]),(0,[z354,z1,z8,z2,z4,z5])],[(0,[z1,z8,z2,z3,z980,z5]),(0,[z1,z8,z2,z507,z4,z5]),(0,[z1,z8,z3,z4,z981,z5]),(0,[z8,z2,z3,z14,z5,z646]),(0,[z1,z8,z2,z982,z4,z5]),(0,[z63,z1,z8,z4,z5,z331])],[(0,[z1,z8,z2,z3,z4,z983]),(0,[z1,z8,z2,z984,z4,z5]),(0,[z55,z8,z113,z56,z3,z5]),(0,[z180,z1,z8,z2,z5,z74]),(0,[z560,z8,z2,z3,z14,z5]),(0,[z1,z8,z356,z3,z112,z5])],[(0,[z7,z8,z2,z3,z4,z165]),(0,[z985,z1,z2,z3,z4,z5]),(0,[z1,z8,z2,z201,z259,z5]),(0,[z1,z2,z60,z4,z5,z103]),(0,[z97,z37,z2,z3,z4,z6]),(0,[z293,z1,z8,z3,z571,z5]),(0,[z1,z8,z2,z205,z5,z74]),(0,[z1,z8,z3,z4,z986,z5]),(0,[z1,z2,z3,z84,z135,z18])],[(0,[z987,z1,z8,z2,z4,z5]),(0,[z1,z8,z2,z3,z988,z5]),(0,[z989,z1,z8,z2,z4,z5]),(1,[z63,z202,z1,z8,z5]),(0,[z293,z1,z8,z3,z94,z5]),(0,[z1,z8,z3,z4,z33,z36])]],
   [[(0,[z1,z8,z2,z3,z990,z4]),(0,[z1,z8,z2,z3,z4,z991]),(0,[z144,z1,z77,z3,z4,z5]),(0,[z1,z8,z2,z3,z992,z5]),(0,[z63,z1,z8,z565,z4,z5])],[(0,[z226,z1,z2,z3,z4,z6]),(0,[z1,z8,z993,z3,z4,z5]),(0,[z1,z8,z601,z98,z4,z5]),(0,[z63,z1,z8,z350,z4,z5])],[(0,[z1,z8,z2,z3,z994,z5]),(0,[z995,z8,z2,z3,z4,z5]),(0,[z37,z61,z2,z3,z4,z5])],[(0,[z226,z317,z80,z2,z3,z4]),(0,[z158,z0,z2,z3,z232,z5]),(0,[z1,z8,z2,z3,z996,z5]),(0,[z1,z2,z3,z4,z5,z997]),(0,[z64,z1,z8,z2,z115,z5]),(0,[z1,z8,z25,z3,z4,z629]),(0,[z1,z8,z2,z4,z5,z998]),(0,[z999,z1,z8,z3,z4,z5])],[(1,[z8,z2,z719,z4,z5]),(0,[z1000,z1,z8,z2,z3,z5]),(0,[z1,z134,z356,z3,z4,z5])],[(0,[z55,z8,z56,z3,z4,z5]),(0,[z1,z8,z2,z1001,z4,z5]),(0,[z180,z1,z8,z3,z125,z5]),(0,[z1,z8,z3,z4,z5,z1002]),(0,[z155,z8,z2,z3,z722,z5])],[(0,[z1,z1003,z2,z3,z4,z5]),(0,[z76,z1,z2,z3,z22,z5])],[(0,[z317,z80,z2,z3,z4,z5]),(0,[z90,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z744]),(0,[z1,z8,z2,z223,z4,z5])]],
   [[(0,[z1,z8,z145,z689,z4,z5]),(0,[z483,z1,z2,z3,z21,z5]),(0,[z1004,z1,z8,z3,z4,z5]),(0,[z352,z1,z101,z3,z4,z5]),(0,[z151,z1,z2,z60,z4,z5]),(0,[z1,z8,z3,z4,z972,z36]),(0,[z1005,z8,z2,z3,z4,z5])],[(0,[z226,z1,z8,z2,z3,z4]),(0,[z1,z385,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z5,z1006]),(0,[z121,z180,z8,z2,z48,z5]),(0,[z1,z8,z601,z126,z4,z5]),(0,[z1,z8,z3,z4,z5,z342])],[(0,[z317,z81,z80,z2,z3,z4]),(0,[z1,z8,z2,z3,z1007,z5]),(0,[z1,z8,z2,z3,z1008,z5]),(0,[z1009,z1,z2,z3,z4,z5]),(0,[z1,z8,z25,z3,z4,z568]),(0,[z1,z8,z3,z4,z5,z295])],[(0,[z1,z8,z2,z347,z4,z5]),(0,[z1,z8,z563,z3,z4,z5]),(0,[z124,z1,z2,z3,z21,z5]),(0,[z1,z8,z2,z3,z406,z5]),(0,[z63,z361,z1,z8,z4,z5])],[(0,[z1,z8,z2,z1010,z4,z5]),(0,[z234,z1,z8,z47,z3,z5]),(0,[z1,z8,z47,z3,z125,z5]),(0,[z1,z8,z2,z1011,z4,z5]),(0,[z1,z8,z349,z3,z406,z5])],[(0,[z1,z8,z38,z400,z3,z5]),(0,[z536,z8,z2,z98,z4,z5])],[(0,[z53,z160,z35,z3,z4,z5]),(0,[z59,z1,z2,z825,z4,z5])],[(0,[z329,z80,z2,z3,z4,z5]),(0,[z29,z8,z2,z30,z4,z5]),(0,[z13,z134,z2,z3,z4,z72]),(0,[z1,z8,z563,z507,z4,z5]),(0,[z387,z1,z8,z3,z4,z5]),(0,[z1,z8,z2,z1012,z4,z5]),(0,[z97,z1,z2,z3,z4,z131]),(0,[z352,z1,z3,z79,z4,z5]),(0,[z1,z8,z25,z3,z196,z26])]],
   [[(0,[z1,z8,z2,z1013,z4,z5]),(0,[z1,z1014,z2,z3,z4,z5]),(0,[z1,z1015,z2,z3,z4,z5]),(0,[z97,z354,z1,z2,z4,z5]),(0,[z97,z1,z2,z3,z4,z6])],[(0,[z1,z8,z2,z3,z1016,z5]),(0,[z159,z80,z2,z3,z4,z5]),(0,[z123,z1,z2,z3,z22,z5]),(0,[z144,z1,z601,z3,z4,z5]),(0,[z1017,z8,z2,z3,z4,z5]),(0,[z202,z1,z8,z145,z3,z5])],[(0,[z1,z8,z3,z4,z5,z1018])],[(0,[z226,z1,z8,z2,z1019,z4]),(0,[z1020,z1,z8,z2,z3,z5]),(0,[z499,z8,z2,z30,z4,z5]),(0,[z1,z8,z2,z4,z5,z1021]),(0,[z746,z1,z2,z3,z4,z5]),(0,[z1,z8,z17,z3,z84,z18])],[(0,[z1,z8,z2,z1022,z4,z5]),(0,[z1,z8,z2,z3,z1023,z5]),(0,[z1024,z1,z2,z3,z4,z5]),(0,[z127,z1,z8,z2,z4,z74])],[(0,[z1,z416,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z62,z545]),(0,[z536,z8,z2,z126,z4,z5]),(0,[z1,z1025,z2,z3,z4,z5]),(0,[z1,z8,z111,z4,z54,z5])],[(0,[z7,z8,z2,z3,z4,z808]),(0,[z1,z8,z2,z3,z5,z1026])],[(1,[z711,z2,z3,z4,z5]),(0,[z564,z80,z2,z3,z4,z5]),(0,[z1,z1027,z2,z3,z4,z5]),(0,[z1,z8,z2,z1028,z4,z5]),(0,[z1029,z1,z8,z2,z3,z5]),(0,[z1,z8,z2,z3,z1030,z5]),(0,[z23,z1,z8,z3,z4,z36])]],
   [[(0,[z1,z8,z2,z3,z4,z1031]),(0,[z1032,z1,z8,z3,z4,z5]),(0,[z1,z1033,z2,z3,z4,z5]),(0,[z1,z1034,z2,z3,z4,z5])],[(0,[z8,z857,z56,z3,z4,z5]),(0,[z64,z1,z8,z2,z182,z5]),(0,[z1,z8,z2,z39,z734,z5])],[(0,[z1,z2,z3,z4,z5,z316])],[(0,[z1,z8,z2,z1035,z4,z5]),(0,[z1,z8,z2,z3,z1036,z5]),(0,[z1037,z8,z2,z3,z4,z5]),(0,[z1,z8,z38,z3,z726,z5]),(1,[z1,z8,z2,z734,z5])],[(0,[z226,z8,z2,z3,z4,z72]),(0,[z1,z8,z2,z1038,z4,z5]),(0,[z65,z8,z2,z3,z722,z5]),(0,[z13,z8,z2,z3,z4,z808]),(0,[z63,z202,z1,z8,z3,z5]),(0,[z1,z8,z1039,z3,z4,z5])],[(0,[z132,z1,z8,z4,z5,z36]),(0,[z230,z1,z8,z3,z5,z36]),(0,[z1040,z8,z2,z3,z4,z5]),(0,[z1041,z8,z2,z3,z4,z5]),(0,[z1,z8,z250,z4,z253,z5]),(0,[z63,z1,z8,z863,z4,z5])],[(0,[z711,z8,z2,z3,z4,z5]),(0,[z483,z80,z2,z3,z4,z5]),(0,[z158,z0,z2,z3,z82,z5]),(0,[z1,z2,z3,z82,z22,z5])],[(0,[z90,z8,z2,z3,z21,z5])]],
   [[(0,[z1,z8,z2,z3,z4,z1042]),(0,[z1,z8,z1043,z3,z4,z5]),(0,[z1,z8,z17,z322,z4,z5])],[(0,[z226,z1,z8,z790,z3,z4]),(0,[z226,z1,z8,z2,z3,z1044]),(0,[z65,z8,z2,z3,z259,z5]),(0,[z1,z31,z2,z201,z4,z5]),(0,[z1,z8,z3,z1045,z4,z5]),(0,[z8,z2,z3,z4,z5,z1046]),(0,[z1047,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z84,z18])],[(0,[z1,z8,z2,z3,z1048,z5]),(0,[z1,z2,z3,z4,z268,z62]),(0,[z1,z2,z3,z4,z62,z744]),(0,[z1049,z1,z8,z2,z3,z5]),(0,[z64,z1,z8,z2,z380,z5])],[(0,[z1,z8,z2,z3,z1050,z5]),(0,[z1051,z1,z8,z3,z4,z5]),(0,[z65,z8,z2,z3,z57,z5]),(0,[z144,z1,z731,z3,z4,z5]),(0,[z97,z1,z2,z3,z406,z6]),(0,[z1,z8,z3,z4,z167,z36])],[(0,[z80,z2,z3,z4,z5,z411]),(0,[z1,z8,z2,z3,z1052,z5]),(0,[z124,z37,z2,z3,z4,z5])],[(0,[z1053,z1,z8,z3,z4,z5]),(0,[z1054,z1,z8,z2,z3,z5])],[(0,[z65,z8,z2,z3,z444,z5]),(0,[z151,z1,z2,z43,z4,z5]),(0,[z1,z2,z3,z4,z5,z1055]),(0,[z1056,z1,z8,z3,z4,z5])],[(0,[z0,z90,z2,z3,z4,z5]),(0,[z37,z100,z2,z3,z4,z5]),(0,[z1057,z8,z2,z3,z4,z5]),(0,[z1058,z8,z2,z3,z4,z5]),(0,[z1059,z1,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z205,z5]),(0,[z1,z1060,z2,z3,z4,z5])]],
   [[(0,[z1,z8,z2,z4,z5,z1061]),(0,[z1,z8,z3,z4,z5,z1062]),(0,[z1,z8,z4,z5,z295,z210])],[(0,[z536,z8,z349,z3,z4,z5]),(0,[z852,z8,z2,z3,z4,z5])],[(0,[z1,z1063,z2,z3,z4,z5]),(0,[z129,z8,z2,z3,z14,z5]),(0,[z1,z8,z2,z3,z5,z237])],[(0,[z1,z8,z2,z1064,z4,z5]),(0,[z1,z8,z2,z3,z84,z161]),(0,[z44,z1,z3,z253,z22,z5]),(0,[z1065,z1,z8,z2,z4,z5]),(0,[z353,z64,z1,z8,z4,z5])],[(0,[z1,z8,z25,z3,z196,z5])],[(0,[z1,z8,z2,z4,z5,z1066]),(0,[z1,z8,z2,z3,z722,z5]),(0,[z37,z8,z2,z3,z257,z5]),(0,[z1,z8,z863,z195,z4,z5]),(0,[z23,z352,z1,z3,z4,z36]),(0,[z1,z8,z2,z196,z5,z34]),(0,[z64,z1,z8,z2,z119,z5])],[(0,[z1,z8,z2,z322,z4,z5]),(0,[z353,z64,z1,z8,z2,z5]),(0,[z1067,z1,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z84,z766])],[(0,[z1,z1068,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z1069,z5]),(0,[z1,z212,z100,z3,z4,z5]),(0,[z1,z8,z2,z4,z5,z1070])]],
   [[(0,[z1,z8,z3,z4,z1071,z5]),(0,[z1,z2,z60,z825,z4,z5]),(1,[z1,z8,z2,z4,z712])],[(0,[z0,z529,z2,z3,z4,z5]),(0,[z132,z160,z1,z8,z4,z5]),(0,[z129,z8,z2,z3,z4,z5]),(0,[z1072,z1,z8,z2,z3,z5])],[(0,[z1,z8,z1073,z3,z4,z5]),(0,[z387,z1,z3,z4,z62,z5]),(0,[z1,z8,z2,z3,z4,z1074])],[(0,[z483,z1,z2,z3,z4,z5]),(0,[z711,z317,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z1075,z5]),(0,[z1,z8,z1076,z3,z4,z5]),(0,[z124,z90,z2,z3,z21,z5])],[(0,[z1,z8,z2,z3,z1077,z5]),(0,[z97,z1,z601,z3,z4,z6]),(0,[z1,z8,z2,z85,z4,z568])],[(0,[z1,z8,z2,z3,z1078,z5]),(0,[z55,z8,z857,z3,z4,z5]),(0,[z1,z8,z2,z1079,z4,z5])],[(0,[z1,z8,z2,z3,z1044,z5]),(0,[z387,z65,z1,z8,z3,z5]),(0,[z1,z8,z356,z3,z259,z5]),(0,[z1,z100,z601,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z1080]),(0,[z8,z2,z3,z4,z5,z1081]),(0,[z1,z8,z3,z79,z726,z5])],[(0,[z1,z8,z1082,z3,z4,z5]),(0,[z158,z711,z2,z3,z4,z5])]],
   [[(0,[z1083,z8,z2,z3,z4,z5]),(0,[z1,z8,z3,z84,z18,z295])],[(0,[z1084,z1,z2,z3,z4,z5]),(0,[z1085,z8,z2,z3,z4,z5]),(0,[z1086,z1,z2,z3,z4,z5]),(0,[z1,z8,z2,z223,z5,z237])],[(0,[z1,z8,z2,z3,z4,z1087]),(0,[z44,z1,z2,z250,z22,z5]),(0,[z387,z1,z8,z3,z84,z5])],[(0,[z453,z80,z2,z3,z4,z5]),(0,[z1,z8,z1088,z3,z4,z5]),(0,[z1,z8,z1089,z3,z4,z5]),(0,[z64,z1,z8,z11,z119,z5])],[(0,[z1,z8,z1090,z3,z4,z5]),(0,[z1,z8,z2,z3,z112,z5]),(0,[z1,z2,z3,z709,z22,z5]),(0,[z1,z8,z2,z4,z5,z1091]),(0,[z1,z8,z601,z3,z257,z5])],[(0,[z1,z1092,z2,z3,z4,z5]),(0,[z65,z558,z8,z2,z3,z5]),(0,[z1,z8,z3,z79,z255,z5]),(0,[z37,z2,z3,z4,z22,z5]),(0,[z1,z8,z2,z3,z432,z58]),(0,[z1,z8,z2,z39,z5,z399]),(0,[z95,z1,z8,z2,z3,z766])],[(0,[z1,z8,z2,z3,z232,z5]),(0,[z1,z1093,z2,z3,z4,z5]),(0,[z1,z8,z145,z4,z188,z5])],[(0,[z1,z8,z2,z3,z4,z1094]),(1,[z1,z8,z3,z4,z972])]],
   [[(0,[z387,z1,z80,z3,z4,z5]),(0,[z1,z1095,z2,z3,z4,z5]),(0,[z1,z8,z2,z507,z112,z5]),(0,[z1,z8,z1096,z3,z4,z5])],[(0,[z387,z0,z1,z3,z4,z5]),(0,[z13,z8,z2,z3,z259,z72]),(0,[z1,z8,z3,z79,z5,z442])],[(0,[z7,z61,z80,z2,z3,z4]),(0,[z234,z29,z1,z8,z4,z5]),(0,[z1,z8,z356,z201,z4,z5]),(0,[z1097,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z1098]),(0,[z1,z8,z2,z1099,z4,z5]),(0,[z1,z8,z223,z4,z5,z36]),(0,[z1,z8,z2,z3,z1100,z5]),(0,[z1,z8,z2,z3,z734,z5])],[(0,[z1,z134,z2,z3,z4,z5]),(0,[z1,z8,z2,z1101,z4,z5]),(0,[z1,z1102,z2,z3,z4,z5]),(0,[z387,z155,z1,z8,z3,z5]),(0,[z1,z2,z3,z4,z744,z6]),(0,[z1103,z8,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1104]),(0,[z1,z134,z2,z3,z112,z5]),(0,[z8,z2,z3,z4,z808,z72])],[(0,[z29,z8,z2,z569,z4,z5]),(0,[z1105,z1,z8,z3,z4,z5])],[(0,[z582,z8,z2,z3,z14,z5]),(0,[z1,z8,z2,z3,z4,z1106]),(0,[z0,z711,z2,z3,z4,z5]),(0,[z1107,z8,z2,z3,z4,z5]),(0,[z1108,z8,z2,z3,z4,z5]),(0,[z198,z1,z8,z2,z3,z58]),(0,[z1,z8,z3,z4,z5,z1109]),(0,[z1,z8,z178,z85,z4,z5])],[(0,[z1,z8,z2,z3,z1110,z5]),(0,[z1,z134,z2,z507,z4,z5]),(0,[z352,z1,z2,z3,z4,z5]),(0,[z1,z1111,z2,z3,z4,z5]),(0,[z64,z151,z1,z2,z4,z5])]],
   [[(0,[z158,z8,z2,z3,z82,z5]),(0,[z1,z2,z3,z4,z5,z1112]),(0,[z1,z8,z2,z3,z5,z1113]),(0,[z1,z100,z731,z3,z4,z5]),(0,[z536,z8,z2,z3,z257,z5])],[(0,[z1,z8,z2,z1114,z4,z5]),(0,[z160,z8,z35,z3,z4,z5]),(0,[z1,z8,z2,z3,z4,z1115]),(1,[z1,z731,z3,z4,z5]),(0,[z1116,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z1117,z5]),(0,[z124,z1,z2,z3,z406,z5]),(0,[z129,z8,z2,z3,z21,z5]),(0,[z64,z1,z8,z2,z734,z5])],[(0,[z1,z1118,z2,z3,z4,z5]),(0,[z293,z1,z8,z3,z88,z5]),(0,[z64,z1,z8,z2,z5,z310]),(0,[z1,z8,z178,z85,z4,z128])],[(0,[z1,z8,z2,z4,z5,z1119]),(0,[z1,z8,z2,z3,z1120,z5]),(0,[z1,z8,z3,z4,z26,z972])],[(0,[z1121,z1,z8,z3,z4,z5]),(0,[z1,z1122,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z5,z1123]),(0,[z1,z8,z2,z3,z84,z108])],[(0,[z1,z8,z2,z3,z1124,z5]),(0,[z1,z1125,z2,z3,z4,z5]),(0,[z13,z8,z2,z201,z4,z72]),(0,[z1126,z8,z2,z3,z4,z5]),(0,[z1,z8,z1127,z3,z4,z5])],[],[(0,[z1128,z1,z8,z2,z3,z5]),(0,[z1,z8,z563,z3,z112,z5]),(0,[z1,z8,z2,z3,z1129,z5]),(0,[z1,z2,z60,z126,z4,z5]),(0,[z1,z8,z2,z4,z5,z34]),(0,[z1,z8,z2,z1130,z4,z5])]],
   [[(0,[z37,z8,z2,z3,z4,z5]),(0,[z132,z1,z8,z2,z4,z5]),(0,[z681,z8,z56,z3,z4,z5]),(0,[z1,z8,z111,z863,z4,z5])],[(0,[z1131,z1,z2,z3,z4,z5]),(0,[z42,z1,z2,z43,z4,z5]),(0,[z37,z8,z349,z3,z4,z5]),(0,[z1,z1132,z2,z3,z4,z5]),(0,[z1133,z1,z2,z3,z4,z5])],[(0,[z226,z65,z8,z2,z3,z4]),(0,[z1,z8,z2,z1019,z4,z5]),(0,[z1,z8,z1134,z3,z4,z5]),(0,[z55,z8,z347,z56,z4,z5]),(0,[z1,z8,z1135,z3,z4,z5]),(0,[z1136,z1,z8,z2,z3,z5]),(0,[z293,z1,z8,z3,z115,z5]),(0,[z1,z8,z2,z3,z4,z972])],[(0,[z55,z230,z8,z56,z3,z5]),(0,[z230,z1,z8,z25,z3,z5]),(0,[z354,z65,z1,z8,z2,z5]),(0,[z1,z1137,z2,z3,z4,z5]),(0,[z1,z8,z145,z863,z4,z5]),(0,[z1,z8,z2,z4,z128,z712])],[(0,[z1,z2,z731,z3,z4,z5]),(0,[z1,z8,z3,z4,z5,z972]),(0,[z353,z64,z1,z8,z3,z5])],[(0,[z1,z8,z2,z1138,z4,z5]),(0,[z1,z1139,z2,z3,z4,z5]),(0,[z1,z8,z1140,z3,z4,z5]),(0,[z1,z8,z145,z4,z5,z426]),(0,[z1,z1141,z2,z3,z4,z5])],[(0,[z8,z35,z857,z3,z4,z5]),(0,[z1,z134,z563,z3,z4,z5]),(0,[z1,z61,z2,z3,z4,z62]),(0,[z1,z8,z178,z4,z5,z74])],[(0,[z1,z8,z2,z1142,z4,z5]),(0,[z76,z1,z2,z3,z4,z5]),(0,[z1,z8,z2,z322,z84,z18])]],
   [[(0,[z180,z1,z8,z2,z85,z5]),(0,[z1,z2,z3,z4,z1143,z5]),(0,[z1,z8,z2,z1144,z4,z5]),(0,[z1,z8,z2,z1145,z3,z5]),(0,[z415,z1,z2,z3,z22,z5]),(0,[z293,z1,z8,z218,z3,z5]),(0,[z1,z8,z17,z3,z84,z5])],[(0,[z1,z8,z2,z3,z82,z5]),(0,[z1,z31,z356,z3,z4,z5]),(0,[z1146,z8,z2,z3,z4,z5]),(0,[z353,z64,z1,z8,z119,z5])],[(0,[z151,z1,z2,z126,z4,z5])],[(0,[z483,z90,z2,z3,z4,z5]),(1,[z1,z8,z3,z726,z5]),(0,[z1,z8,z17,z3,z5,z58])],[(0,[z226,z144,z1,z2,z3,z4]),(0,[z1,z8,z2,z1147,z4,z5]),(0,[z1,z8,z2,z4,z93,z5]),(0,[z127,z151,z1,z2,z4,z74])],[(0,[z134,z2,z3,z14,z4,z5]),(0,[z1,z8,z2,z3,z1148,z5]),(0,[z1,z2,z3,z406,z22,z5]),(0,[z1,z2,z3,z4,z5,z1149])],[(0,[z226,z7,z8,z2,z3,z4]),(1,[z8,z857,z3,z4,z5]),(0,[z8,z2,z3,z14,z722,z5]),(0,[z293,z209,z1,z8,z94,z5]),(0,[z1,z8,z2,z3,z5,z104])],[(0,[z199,z80,z2,z3,z4,z5]),(0,[z549,z1,z2,z60,z4,z5]),(0,[z1,z8,z2,z3,z1150,z5]),(0,[z1,z8,z1151,z3,z4,z5]),(0,[z1,z8,z601,z3,z4,z5]),(0,[z1,z8,z3,z4,z5,z1152]),(0,[z293,z1,z8,z93,z94,z5]),(0,[z8,z2,z3,z1153,z4,z5])]],
   [[(0,[z226,z1,z2,z60,z3,z4]),(0,[z158,z50,z2,z3,z4,z5]),(0,[z121,z454,z8,z2,z4,z5]),(0,[z129,z1060,z2,z3,z4,z5])],[(0,[z1,z8,z2,z3,z1154,z5]),(0,[z1,z8,z2,z3,z4,z1155]),(0,[z1,z1156,z2,z3,z4,z5]),(0,[z1157,z1,z2,z3,z4,z5])],[(0,[z0,z354,z1,z2,z4,z5]),(0,[z1,z8,z2,z3,z4,z1158]),(0,[z1,z8,z2,z39,z185,z5])],[(1,[z8,z2,z3,z4,z808]),(0,[z64,z1,z8,z2,z375,z5]),(0,[z37,z8,z2,z3,z406,z5]),(0,[z1,z8,z2,z171,z5,z262])],[(0,[z1,z8,z2,z1159,z4,z5]),(0,[z227,z29,z2,z30,z4,z5]),(0,[z13,z31,z2,z3,z4,z72]),(0,[z293,z352,z1,z3,z4,z5])],[(0,[z1,z8,z81,z2,z3,z4]),(0,[z1,z8,z3,z125,z4,z5]),(0,[z1,z114,z731,z3,z4,z5]),(0,[z354,z44,z1,z2,z22,z5])],[(0,[z160,z416,z35,z3,z4,z5]),(0,[z1,z8,z3,z4,z5,z1160])],[(0,[z234,z121,z1,z8,z4,z5]),(0,[z1161,z8,z2,z3,z4,z5]),(0,[z1,z8,z2,z3,z5,z766])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 539) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 539).take 543) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1082).take 40) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1122)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [539, 543, 40] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 132).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 132).take 120).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 252).take 4).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [132, 120, 4] = true :=
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

end PEqualNP.Outside.L_meta_38791

theorem PEqualNP.Outside.L_meta_38791 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4272603136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4272603136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38791.solve
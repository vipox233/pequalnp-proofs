import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37239

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
  Nat.testBit (4277071594 * 2 ^ 32 + 4241026248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x5a0121044e244e44#64 ++ 0x9680484113891391#64 ++ 0xfd03634cfe24de4e#64 ++ 0xff40d8d33f893793#64 : BitVec 256),
   (0x04000c1120098098#64 ++ 0x0100030448026026#64 ++ 0xfbc49cb3203fe3ff#64 ++ 0xfef1272cc80ff8ff#64 : BitVec 256),
   (0x8818e0c2c2c63462#64 ++ 0x22063830b0b18d18#64 ++ 0x57b8e0c3c7c73c73#64 ++ 0xd5ee3830f1f1cf1c#64 : BitVec 256),
   (0x102f00ec05703b00#64 ++ 0xc40bc03b015c0ec0#64 ++ 0xcfbf00fc07f83f83#64 ++ 0xb3efc03f01fe0fe0#64 : BitVec 256),
   (0xe077f70007bfc000#64 ++ 0xf81dfdc001eff000#64 ++ 0x3f7fff0007ffc001#64 ++ 0x8fdfffc001fff000#64 : BitVec 256),
   (0x003edafbb0000003#64 ++ 0x000fb6beec000000#64 ++ 0xff7ffffff8000000#64 ++ 0x7fdffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [6, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [11, 8]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xff7ffffff8000000 0x7fdffffffe000000

def z1 : W := mkw 0x04000c1120098098 0x0100030448026026 0xa8441c302038c38c 0x2a11070c080e30e3

def z2 : W := mkw 0x04000c1120098098 0x0100030448026026 0xfbc49cb3203fe3ff 0xfef1272cc80ff8ff

def z3 : W := mkw 0x1027002c05300b00 0xc409c00b014c02c0 0x8807003c00380380 0x2201c00f000e00e0

def z4 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xcfbf00fc07f83f83 0xb3efc03f01fe0fe0

def z5 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xfd03634cfe24de4e 0xff40d8d33f893793

def z6 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x3f7fff0007ffc001 0x8fdfffc001fff000

def z7 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xc403634cfe001e4e 0x7100d8d33f800793

def z8 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x57b8e0c3c7c73c73 0xd5ee3830f1f1cf1c

def z9 : W := mkw 0x8037e00007b60000 0xe00df80001ed8000 0x1f3fe00007ff0001 0x87cff80001ffc000

def z10 : W := mkw 0x522f01ec0d707b04 0xd48bc07b035c1ec1 0xefbf03fc3ff8ff8f 0xbbefc0ff0ffe3fe3

def z11 : W := mkw 0x8810e002c2c63462 0x22043800b0b18d18 0x1080e003c7c73c73 0xc4203800f1f1cf1c

def z12 : W := mkw 0x0000000000000000 0x0000000000000000 0xfd03634cf8000000 0x7f40d8d33e000000

def z13 : W := mkw 0xe041250007bfc000 0xf810494001eff000 0x0000000007ffc001 0x8000000001fff000

def z14 : W := mkw 0x1e00081568000edc 0x078002055a0003b7 0xc08000fff8003ffe 0x7020003ffe000fff

def z15 : W := mkw 0x8c10ec13e28f84fa 0x23043b04f8a3e13e 0x3040fc03e007c07c 0x4c103f00f801f01f

def z16 : W := mkw 0x8c18ecd3e2cfb4fa 0x23063b34f8b3ed3e 0xfffcfcf3e7ffffff 0xffff3f3cf9ffffff

def z17 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xb803630cf824c24c 0x6e00d8c33e093093

def z18 : W := mkw 0x9801200447f63f60 0xe600480111fd8fd8 0x0080000007ff3ff3 0x8020000001ffcffc

def z19 : W := mkw 0x0000000000000000 0x0000000000000000 0xcb8400b000382383 0xb2e1002c000e08e0

def z20 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x347bff0007c7c000 0x0d1effc001f1f000

def z21 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x3b7c9c0001ffc001 0x8edf2700007ff000

def z22 : W := mkw 0x002e00e800403000 0x000b803a00100c00 0xcfbf00fc07c03c03 0xb3efc03f01f00f00

def z23 : W := mkw 0x04000c1120098098 0x0100030448026026 0x30409c032007c07c 0x4c102700c801f01f

def z24 : W := mkw 0x142f0cfd2579bb98 0xc50bc33f495e6ee6 0xffff9cff27ffffff 0xffffe73fc9ffffff

def z25 : W := mkw 0xe077f30007b64000 0xf81dfcc001ed9000 0x043b630007c00000 0x010ed8c001f00000

def z26 : W := mkw 0xe87ff7c2c7fff462 0xfa1ffdf0b1fffd18 0x7fffffc3c7fffc73 0xdffffff0f1ffff1c

def z27 : W := mkw 0xe07ffffbb7bfc003 0xf81ffffeedeff000 0xff7fffffffffc001 0xffdffffffffff000

def z28 : W := mkw 0x0036da3bb0000003 0x000db68eec000000 0xb847ff3ff8000000 0x6e11ffcffe000000

def z29 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0x000000000624de4e 0x8000000001893793

def z30 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x3f7fff0001db0001 0x0fdfffc00076c000

def z31 : W := mkw 0x043edafbb000009b 0x010fb6beec000026 0xfffffffff80023fe 0x7ffffffffe0008ff

def z32 : W := mkw 0x606717000539c000 0xd819c5c0014e7000 0x28471f000038c000 0x0a11c7c0000e3000

def z33 : W := mkw 0x080808fbf0403463 0x0202023efc100d18 0xc08000fff8003c72 0x7020003ffe000f1c

def z34 : W := mkw 0x883efafbf2c63463 0x220fbebefcb18d18 0xffffffffffc73c73 0xfffffffffff1cf1c

def z35 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0xff7fff4cffffde4f 0xffdfffd33ffff793

def z36 : W := mkw 0x0000000000000000 0x0000000000000000 0x5380808300072073 0xd4e02020c001c81c

def z37 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xff83e3cffe27fe7f 0xffe0f8f3ff89ff9f

def z38 : W := mkw 0x983fe0eec7f63f62 0xe60ff83bb1fd8fd8 0xdfbfe0ffc7ff3ff3 0xf7eff83ff1ffcffc

def z39 : W := mkw 0x4027210007344000 0xd009c84001cd1000 0x3f3f630007fcc001 0x8fcfd8c001ff3000

def z40 : W := mkw 0x8810e002c2860462 0x22043800b0a18118 0x5500e043c6071c72 0xd5403810f181c71c

def z41 : W := mkw 0x8810e002c2860462 0x22043800b0a18118 0x1000e003c0070070 0x44003800f001c01c

def z42 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x027c9c0001db0001 0x009f27000076c000

def z43 : W := mkw 0x002e1afbb0000003 0x000b86beec000000 0xe8471ffff8000000 0x7a11c7fffe000000

def z44 : W := mkw 0x100808ffb0403b03 0x0402023fec100ec0 0xc08000fff8003f82 0x7020003ffe000fe0

def z45 : W := mkw 0x103fdaffb5703b03 0xc40ff6bfed5c0ec0 0xfffffffffff83f83 0xfffffffffffe0fe0

def z46 : W := mkw 0xe050f700028fc000 0x38143dc000a3f000 0x3040ff000007c000 0x0c103fc00001f000

def z47 : W := mkw 0xe477ff1127bfc098 0xf91dffc449eff026 0xffffffb327ffe3ff 0xffffffecc9fff8ff

def z48 : W := mkw 0x8800200042c63460 0x2200080010b18d18 0x0000000007c01c00 0x0000000001f00700

def z49 : W := mkw 0x0036d20000000000 0x000db48000000000 0x3f7fff0000000000 0x0fdfffc000000000

def z50 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xcd03634cde201e02 0xb340d8d337880780

def z51 : W := mkw 0x0000040000098000 0x0000010000026000 0x30409c000007c000 0x0c1027000001f000

def z52 : W := mkw 0x080800c2c0403462 0x02020030b0100d18 0x47b800c3c7c03c73 0xd1ee0030f1f00f1c

def z53 : W := mkw 0x1a00000448000e44 0x0680000112000391 0x0000004cd8001c00 0x0000001336000700

def z54 : W := mkw 0x043edefbb009809b 0x010fb7beec026026 0xfffffffff83fe3ff 0xfffffffffe0ff8ff

def z55 : W := mkw 0x00261a3930000001 0x0009868e4c000000 0xa8471f3c38000000 0x2a11c7cf0e000000

def z56 : W := mkw 0x8800200042c63460 0x2200080010b18d18 0x0080000007c73c73 0x8020000001f1cf1c

def z57 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xff8763fcfe3cffcf 0xffe1d8ff3f8f3ff3

def z58 : W := mkw 0x520121040e244a04 0x9480484103891281 0xbd03630c3e24c20c 0xaf40d8c30f893083

def z59 : W := mkw 0xe0402500028fc000 0x3810094000a3f000 0x000000000007c000 0x000000000001f000

def z60 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0x3f7fff0007ffde4f 0x8fdfffc001fff793

def z61 : W := mkw 0x1027002c05300b00 0xc409c00b014c02c0 0x0003000c00000000 0x0000c00300000000

def z62 : W := mkw 0x4a0021004a044444 0x1280084012811111 0x30006300f804c04c 0x4c0018c03e013013

def z63 : W := mkw 0x5e012d156e2dcedc 0x97804b455b8b73b7 0xffc7fffffe3fffff 0xfff1ffffff8fffff

def z64 : W := mkw 0x002e00e801503100 0x400b803a00540c40 0x02bc00b001d82181 0x00af002c00760860

def z65 : W := mkw 0x1001000404200a00 0x8400400101080280 0xcd03004c06201e02 0xb340c01301880780

def z66 : W := mkw 0x0000040000098000 0x0000010000026000 0xfb449c00203fc24f 0xfed12700080ff093

def z67 : W := mkw 0xe477f70007bfc098 0xf91dfdc001eff026 0x3fffff0007ffe3ff 0x8fffffc001fff8ff

def z68 : W := mkw 0xa07edefbb19b8003 0x681fb7beec66e000 0x027c9cb301db0001 0x009f272cc076c000

def z69 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xfffffffff8382383 0xfffffffffe0e08e0

def z70 : W := mkw 0x1001000404200a00 0x8400400101080280 0xcf8700fc06383f83 0xb3e1c03f018e0fe0

def z71 : W := mkw 0x606717000539c000 0xd819c5c0014e7000 0x2f7f1f0007f8c001 0x8bdfc7c001fe3000

def z72 : W := mkw 0x0000000000000000 0x0000000000000000 0x5100000000040042 0xd440000000010010

def z73 : W := mkw 0xe051f70006afc000 0xb8147dc001abf000 0x3d43ff000627c000 0x8f50ffc00189f000

def z74 : W := mkw 0x1a00000448000e44 0x0680000112000391 0xc000004cf8001e4e 0x700000133e000793

def z75 : W := mkw 0x0010c00280000002 0x00043000a0000000 0x1000e003c0000000 0x44003800f0000000

def z76 : W := mkw 0x0027040005398000 0xc009c100014e6000 0x3f7f9c0007ffc001 0x8fdfe70001fff000

def z77 : W := mkw 0x04000c1120098098 0x0100030448026026 0x32c49cb3201fe1fd 0x4cb1272cc807f87f

def z78 : W := mkw 0x14010c152579bb98 0xc5004305495e6ee6 0xfbc49cb327ffffff 0xfef1272cc9ffffff

def z79 : W := mkw 0x000800c000403000 0x0002003000100c00 0xcfbc00f007f83f83 0xb3ef003c01fe0fe0

def z80 : W := mkw 0x00261a3930000001 0x0009868e4c000000 0xfd477f7cf8000000 0x7f51dfdf3e000000

def z81 : W := mkw 0x8018c0c280c23022 0x20063030a0308c08 0x02b8808301c32031 0x00ae2020c070c80c

def z82 : W := mkw 0x080800c2c0403462 0x02020030b0100d18 0x408000c3c0003c72 0x50200030f0000f1c

def z83 : W := mkw 0x100800ec00403b00 0x0402003b00100ec0 0xc08000fc00003f82 0x3020003f00000fe0

def z84 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x5738e0c3c7c01c00 0x55ce3830f1f00700

def z85 : W := mkw 0x0018c0c280000002 0x00063030a0000000 0x5738e0c3c0000000 0x55ce3830f0000000

def z86 : W := mkw 0x8018c0c280c23022 0x20063030a0308c08 0x53b8808301c72073 0xd4ee2020c071c81c

def z87 : W := mkw 0x0010da13b0000003 0x00043684ec000000 0xfd43ff4ff8000000 0x7f50ffd3fe000000

def z88 : W := mkw 0x983fe0eec7f63f62 0xe60ff83bb1fd8fd8 0x043b604cc7c01c00 0x010ed81331f00700

def z89 : W := mkw 0x1001000405703b00 0xc4004001015c0ec0 0x0080000007f83f83 0x8020000001fe0fe0

def z90 : W := mkw 0xda19e1c6cee67e66 0xb6867871b3b99f99 0xffbbe3cfffe7fe7f 0xffeef8f3fff9ff9f

def z91 : W := mkw 0x142f0cfd2579bb98 0xc50bc33f495e6ee6 0xcfff9cff07fb3fb3 0xb3ffe73fc1fecfec

def z92 : W := mkw 0x883efafbf2c63463 0x220fbebefcb18d18 0xff7fffffffc01c00 0x7fdffffffff00700

def z93 : W := mkw 0xfa77f3044fb64e44 0xfe9dfcc113ed9391 0xfd3b634cffe4de4e 0xff4ed8d33ff93793

def z94 : W := mkw 0x8010c00280820022 0x20043000a0208008 0x0000800300030030 0x00002000c000c00c

def z95 : W := mkw 0x44012d11262dc098 0x91004b44498b7026 0xffc7ffb3263fe3ff 0xfff1ffecc98ff8ff

def z96 : W := mkw 0x4001210006244000 0x9000484001891000 0x3d0363000624c000 0x8f40d8c001893000

def z97 : W := mkw 0x000808fbb0000003 0x0002023eec000000 0xc00000fff8000000 0x7000003ffe000000

def z98 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00000002000024e 0x7000000008000093

def z99 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xfb7c9cb320000000 0x7edf272cc8000000

def z100 : W := mkw 0x0001000004200000 0x8000400001080000 0x0d03000006200000 0x8340c00001880000

def z101 : W := mkw 0x0027000005300000 0xc009c000014c0000 0x0f3f000007f80001 0x83cfc00001fe0000

def z102 : W := mkw 0x502f21ec07747b00 0xd40bc87b01dd1ec0 0xffbf63fc07fcff83 0xbfefd8ff01ff3fe0

def z103 : W := mkw 0x5e012d156e2dcedc 0x97804b455b8b73b7 0xfd43ff4ffe27de7e 0xff50ffd3ff89f79f

def z104 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0x04bb004c07f83f83 0x812ec01301fe0fe0

def z105 : W := mkw 0x0010da13b0000003 0x00043684ec000000 0x3040ff03f8000000 0x4c103fc0fe000000

def z106 : W := mkw 0x04000c1120098098 0x0100030448026026 0x02c49cb3003fe3ff 0x80b1272cc00ff8ff

def z107 : W := mkw 0x0000000000000000 0x0000000000000000 0x3d03630000000000 0x0f40d8c000000000

def z108 : W := mkw 0x102f1afd35703b01 0xc40bc6bf4d5c0ec0 0xefff1ffc3ff83f83 0xbbffc7ff0ffe0fe0

def z109 : W := mkw 0x043edefbb009809b 0x010fb7beec026026 0xfffffffff81b21b1 0x7ffffffffe06c86c

def z110 : W := mkw 0x2066160001198000 0x4819858000466000 0x00441c0000180000 0x0011070000060000

def z111 : W := mkw 0x1a2f00ec4d703f44 0xc68bc03b135c0fd1 0xcfbf00fcfff83fcf 0xf3efc03f3ffe0ff3

def z112 : W := mkw 0x903fe0ec07f63b00 0xe40ff83b01fd8ec0 0xdfbfe0fc07ff3f83 0xb7eff83f01ffcfe0

def z113 : W := mkw 0xf06f25ec07fffb00 0xfc1bc97b01fffec0 0xcfbf00fc07ffff83 0xb3efc03f01ffffe0

def z114 : W := mkw 0xea77f7004fbfc444 0xfa9dfdc013eff111 0x3f7fff00ffffc04d 0xcfdfffc03ffff013

def z115 : W := mkw 0x9818e0eec2c63f62 0x2606383bb0b18fd8 0xd7b8e0ffc7c73ff3 0xf5ee383ff1f1cffc

def z116 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0x577cfcf3c0000000 0x55df3f3cf0000000

def z117 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0x043b004c07c01c00 0x010ec01301f00700

def z118 : W := mkw 0x5a2f21ec4f747f44 0xd68bc87b13dd1fd1 0xffbf63fcfffcffcf 0xffefd8ff3fff3ff3

def z119 : W := mkw 0x0400040000098098 0x0100010000026026 0x00800000001b21b1 0x002000000006c86c

def z120 : W := mkw 0xe07ff7e807bfc000 0xf81ffdfa01eff000 0xff7ffffc07ffc001 0xbfdfffff01fff000

def z121 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0xffbbe3cfffc73c73 0xffeef8f3fff1cf1c

def z122 : W := mkw 0x142f0cfd2579bb98 0xc50bc33f495e6ee6 0xefff1cfc27f8ff8f 0xbbffc73f09fe3fe3

def z123 : W := mkw 0x003ed2ea90000003 0x000fb4baa4000000 0x0038000000000000 0x000e000000000000

def z124 : W := mkw 0x5e2f2dfd6f7dffdc 0xd78bcb7f5bdf7ff7 0xffffffffffffffff 0xffffffffffffffff

def z125 : W := mkw 0x40012500062dc000 0x90004940018b7000 0x3f47ff00063fc001 0x8fd1ffc0018ff000

def z126 : W := mkw 0xde19edd7eeeffefe 0xb7867b75fbbbffbf 0xffffffffffffffff 0xffffffffffffffff

def z127 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xac7f7f7cf8000000 0x2b1fdfdf3e000000

def z128 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xdfbf80ff07ff3ff3 0xf7efe03fc1ffcffc

def z129 : W := mkw 0x003ed2ea90000003 0x000fb4baa4000000 0x043b634cd8000000 0x010ed8d336000000

def z130 : W := mkw 0x520101040c204a04 0x9480404103081281 0xf903030c3824c24e 0xfe40c0c30e093093

def z131 : W := mkw 0xda19e1c6cee67e66 0xb6867871b3b99f99 0x57b8e0c3c7e7fe7f 0xd5ee3830f1f9ff9f

def z132 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0x327cffb3f8000000 0x4c9f3fecfe000000

def z133 : W := mkw 0x803edafbb0c23023 0x200fb6beec308c08 0x02fc9cb301c32031 0x00bf272cc070c80c

def z134 : W := mkw 0xe07ff7ea97bfc003 0xf81ffdfaa5eff000 0x3f7fff4cdfffc001 0x8fdfffd337fff000

def z135 : W := mkw 0x5a3ffbfffe244e47 0x968ffeffff891391 0xff7ffffffe24de4e 0xffdfffffff893793

def z136 : W := mkw 0x0000000000000000 0x0000000000000000 0xf90000002024c24e 0xfe40000008093093

def z137 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0x0403634cde001c00 0x0100d8d337800700

def z138 : W := mkw 0x000800c000403000 0x0002003000100c00 0x57b880c307c73c73 0xd5ee2030c1f1cf1c

def z139 : W := mkw 0xe07efffbb28fc003 0x381fbffeeca3f000 0xff7ffffff807c000 0x7fdffffffe01f000

def z140 : W := mkw 0x8010e00002860000 0x2004380000a18000 0x1738e00007c70001 0x85ce380001f1c000

def z141 : W := mkw 0x1001000405300b00 0xc4004001014c02c0 0x0000000000380380 0x00000000000e00e0

def z142 : W := mkw 0x520101040c204a04 0x9480404103081281 0xa803030c3820c20c 0x2a00c0c30e083083

def z143 : W := mkw 0x000800c000403000 0x0002003000100c00 0x47b800c007c03c03 0x91ee003001f00f00

def z144 : W := mkw 0xf077f70407bfca00 0xfc1dfdc101eff280 0xff7fff4c07ffde03 0xbfdfffd301fff780

def z145 : W := mkw 0x0400040000098098 0x0100010000026026 0x00800000003fe3ff 0x80200000000ff8ff

def z146 : W := mkw 0xda0121044ee67e64 0xb680484113b99f99 0xfd83634cffe7fe7f 0xff60d8d33ff9ff9f

def z147 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0x47bb00cc07c03c03 0x91eec03301f00f00

def z148 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0x3d03634cde24dc00 0x8f40d8d337893700

def z149 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xcf7f9cff00000000 0x33dfe73fc0000000

def z150 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xfd03634cfe001c00 0x7f40d8d33f800700

def z151 : W := mkw 0x0800000040403460 0x0200000010100d18 0x0080000000003c72 0x0020000000000f1c

def z152 : W := mkw 0xe050f30002864000 0x38143cc000a19000 0x0000630000000000 0x000018c000000000

def z153 : W := mkw 0x0400081120000098 0x0100020448000026 0xcb8400b3203823ff 0xf2e1002cc80e08ff

def z154 : W := mkw 0x002e00e800000000 0x000b803a00000000 0x023c00b000000000 0x008f002c00000000

def z155 : W := mkw 0x0000081120000000 0x0000020448000000 0xfbc49cb320072073 0xfef1272cc801c81c

def z156 : W := mkw 0xe077d70005bbc000 0xf81df5c0016ef000 0x2a7f9f0001fbc001 0x0a9fe7c0007ef000

def z157 : W := mkw 0xe041250007bfc000 0xf810494001eff000 0x3d03630007ffc001 0x8f40d8c001fff000

def z158 : W := mkw 0x0000040000098000 0x0000010000026000 0x02449c00001b0001 0x009127000006c000

def z159 : W := mkw 0x0018c8d3a0000002 0x00063234e8000000 0xff7cfcf3e0000000 0x7fdf3f3cf8000000

def z160 : W := mkw 0x0037d20005300000 0xc00df480014c0000 0x3f7fff0007f80001 0x8fdfffc001fe0000

def z161 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xffbf63fcfff83f83 0xffefd8ff3ffe0fe0

def z162 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0x027c9cb300000000 0x009f272cc0000000

def z163 : W := mkw 0x04000c1120098098 0x0100030448026026 0xfb449cb32038c38c 0x7ed1272cc80e30e3

def z164 : W := mkw 0x0000000000000000 0x0000000000000000 0xfd03634cf824c24e 0xff40d8d33e093093

def z165 : W := mkw 0x0000000000000000 0x0000000000000000 0x0b04000000380001 0x82c10000000e0000

def z166 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x55386040c7c41c42 0xd54e181031f10710

def z167 : W := mkw 0x04000c1120098098 0x0100030448026026 0xf9409c032027c27e 0xfe502700c809f09f

def z168 : W := mkw 0xca18e1c2cac67466 0x32863870b2b19d19 0x77b8e3c3ffc7fc7f 0xddee38f0fff1ff1f

def z169 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xaa7f9fbf38000000 0x2a9fe7efce000000

def z170 : W := mkw 0x8810e00042860440 0x2204380010a18110 0x5738e040c7c71c43 0xd5ce381031f1c710

def z171 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xac03634cfe20de0c 0x2b00d8d33f883783

def z172 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0x0f3f004c07f81c01 0x83cfc01301fe0700

def z173 : W := mkw 0x5001210406244a00 0x9400484101891280 0xfd03634c0624de02 0xbf40d8d301893780

def z174 : W := mkw 0x0036d20000000000 0x000db48000000000 0x027c9c0000000000 0x009f270000000000

def z175 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x1438e043c7c71c70 0x450e3810f1f1c71c

def z176 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xcd3b004c07e01e02 0xb34ec01301f80780

def z177 : W := mkw 0x0000000000000000 0x0000000000000000 0x55006040c0000000 0x5540181030000000

def z178 : W := mkw 0x00000c1120098000 0x0000030448026000 0xfb449cb3203fc001 0xfed1272cc80ff000

def z179 : W := mkw 0x8c3efefbf2cfb4fb 0x230fbfbefcb3ed3e 0xffffffffffffffff 0xffffffffffffffff

def z180 : W := mkw 0x0018c0c280000002 0x00063030a0000000 0x04386040c0000000 0x010e181030000000

def z181 : W := mkw 0x5a19e1c6ce244e46 0x96867871b3891391 0xff3be3cffe24de4e 0xffcef8f3ff893793

def z182 : W := mkw 0x102e00ec00403b00 0x040b803b00100ec0 0xcfbf00fc00003f82 0x33efc03f00000fe0

def z183 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0x067fffffd8000000 0x019ffffff6000000

def z184 : W := mkw 0x1a0100044c200e44 0x8680400113080391 0xcd03004cfe201e4e 0xf340c0133f880793

def z185 : W := mkw 0x8c18ecd3e2cfb4fa 0x23063b34f8b3ed3e 0x57fcfcf3c7df3df3 0xd5ff3f3cf1f7cf7c

def z186 : W := mkw 0x0026122810000001 0x0009848a04000000 0x0003030c18000000 0x0000c0c306000000

def z187 : W := mkw 0x0000000000000000 0x0000000000000000 0x4380008000002003 0x90e0002000000800

def z188 : W := mkw 0x4001210006244000 0x9000484001891000 0x0403630006000000 0x0100d8c001800000

def z189 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xfffffffff8072073 0xfffffffffe01c81c

def z190 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0x02bc00b007f83f83 0x80af002c01fe0fe0

def z191 : W := mkw 0x140808fd20403b98 0x0502023f48100ee6 0xc08000ff20003ffe 0x7020003fc8000fff

def z192 : W := mkw 0x5e0125044e2dcedc 0x97804941138b73b7 0x00800000063fffff 0x80200000018fffff

def z193 : W := mkw 0x0c002c11620d84d8 0x03000b0458836136 0xffc4fcf3e63fffff 0xfff13f3cf98fffff

def z194 : W := mkw 0x8818e4c2c2cfb462 0x22063930b0b3ed18 0x7ffcfcc3c7fffc73 0xdfff3f30f1ffff1c

def z195 : W := mkw 0x4e002d116a0dc4dc 0x13800b445a837137 0xfbc4ffb3f83fe3ff 0xfef13fecfe0ff8ff

def z196 : W := mkw 0xa076f600039f8000 0x681dbd8000e7e000 0x177cfc0007df0001 0x85df3f0001f7c000

def z197 : W := mkw 0x103fdaffb5300b03 0xc40ff6bfed4c02c0 0xff7ffffff8380380 0x7fdffffffe0e00e0

def z198 : W := mkw 0x0036d20000000000 0x000db48000000000 0xff7fff4cf8000000 0x7fdfffd33e000000

def z199 : W := mkw 0x0000081120000000 0x0000020448000000 0xc00000b320000000 0x7000002cc8000000

def z200 : W := mkw 0x10271a3d35300b01 0xc409c68f4d4c02c0 0xa8471f3c38380380 0x2a11c7cf0e0e00e0

def z201 : W := mkw 0x1200000408000a04 0x0480000102000281 0x8000000c3800020c 0x200000030e000083

def z202 : W := mkw 0xfa4125044fbfce44 0xfe90494113eff391 0x0000000007ffde4f 0x8000000001fff793

def z203 : W := mkw 0x0c0808d3e04034fa 0x03020234f8100d3e 0xc08000f3e0003ffe 0x7020003cf8000fff

def z204 : W := mkw 0x0000040000098000 0x0000010000026000 0x3b449c00003fc001 0x8ed12700000ff000

def z205 : W := mkw 0x0400081120000098 0x0100020448000026 0xc08000b3200023fe 0x7020002cc80008ff

def z206 : W := mkw 0x8018c0c280c23022 0x20063030a0308c08 0x0038000001c00000 0x000e000000700000

def z207 : W := mkw 0x04000c1120098098 0x0100030448026026 0x02c49cb3001b21b1 0x00b1272cc006c86c

def z208 : W := mkw 0xe450ff11228fc098 0x39143fc448a3f026 0x3040ff032007c07c 0x4c103fc0c801f01f

def z209 : W := mkw 0x0026120000000000 0x0009848000000000 0x28471f0000000000 0x0a11c7c000000000

def z210 : W := mkw 0xec7fffd3e7fff4fa 0xfb1ffff4f9fffd3e 0xfffffff3e7ffffff 0xfffffffcf9ffffff

def z211 : W := mkw 0xa476de11219b8098 0x691db7844866e026 0xfbfc9cb321ffe3ff 0xfeff272cc87ff8ff

def z212 : W := mkw 0x8010e00002860000 0x2004380000a18000 0x57b8e08307c72073 0xd5ee3820c1f1c81c

def z213 : W := mkw 0xf07ff7ec07fffb00 0xfc1ffdfb01fffec0 0xfffffffc07ffff83 0xbfffffff01ffffe0

def z214 : W := mkw 0x8010c00000820000 0x2004300000208000 0x0238800001c30001 0x008e20000070c000

def z215 : W := mkw 0x1027000405300a00 0xc409c001014c0280 0xcf3f004c07f81e03 0xb3cfc01301fe0780

def z216 : W := mkw 0x8c00240042cfb4f8 0x2300090010b3ed3e 0x0080000007ffffff 0x8020000001ffffff

def z217 : W := mkw 0x002e00e801503100 0x400b803a00540c40 0x47bc00f007d83d83 0x91ef003c01f60f60

def z218 : W := mkw 0x000808fbb0000003 0x0002023eec000000 0x000000b300000000 0x0000002cc0000000

def z219 : W := mkw 0x100900c405703b00 0xc4024031015c0ec0 0x47b800c007f83f83 0x91ee003001fe0fe0

def z220 : W := mkw 0x002f00e805300000 0xc00bc03a014c0000 0xcf3f00fc07f80001 0xb3cfc03f01fe0000

def z221 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0xffffffb007ffe383 0xbfffffec01fff8e0

def z222 : W := mkw 0x1001000404200a00 0x8400400101080280 0x0403004c06001c00 0x0100c01301800700

def z223 : W := mkw 0xa050d600008b8000 0x281435800022e000 0x00409c0000030000 0x001027000000c000

def z224 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z225 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x027c9c0007ffc001 0x809f270001fff000

def z226 : W := mkw 0x9819e0c6c6e63e62 0xa6067831b1b98f98 0xdfbbe0cfc7e73e73 0xf7eef833f1f9cf9c

def z227 : W := mkw 0x14270c3d25398b98 0xc509c30f494e62e6 0xfbc79cbf203fe3ff 0xfef1e72fc80ff8ff

def z228 : W := mkw 0x0026000001100000 0x4009800000440000 0x023c000001d80001 0x008f000000760000

def z229 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0xdfbce0f3c7ff3ff3 0xf7ef383cf1ffcffc

def z230 : W := mkw 0x1a0800ec48403f44 0x0682003b12100fd1 0xc08000fcf8003fce 0x7020003f3e000ff3

def z231 : W := mkw 0x0800200042040440 0x0200080010810110 0x55006040c6041c42 0xd540181031810710

def z232 : W := mkw 0xe877f70047bfc440 0xfa1dfdc011eff110 0x7f7fff40c7ffdc43 0xdfdfffd031fff710

def z233 : W := mkw 0x0036da1120000000 0x000db68448000000 0xff7fffb320000000 0x7fdfffecc8000000

def z234 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x04386040c7c01c00 0x010e181031f00700

def z235 : W := mkw 0x8010e400028f8000 0x2004390000a3e000 0x3f7cfc0007ffc001 0x8fdf3f0001fff000

def z236 : W := mkw 0x100900ec04603b00 0x8402403b01180ec0 0xcd8300fc06203f82 0xb360c03f01880fe0

def z237 : W := mkw 0x0000000000000000 0x0000000000000000 0x0403634cd8000000 0x0100d8d336000000

def z238 : W := mkw 0x0010da13b0000003 0x00043684ec000000 0x00409c0300000000 0x00102700c0000000

def z239 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0x06bf00fc07d83d81 0x01afc03f01f60f60

def z240 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0x8c3f007c07f81f80 0x230fc01f01fe07e0

def z241 : W := mkw 0x042e0cf92159b198 0x410b833e48566c66 0x02fc9cb301db21b1 0x00bf272cc076c86c

def z242 : W := mkw 0x983fe0eec7f63f62 0xe60ff83bb1fd8fd8 0x57bbe0cfc7c73c73 0xd5eef833f1f1cf1c

def z243 : W := mkw 0x8018e0c002c63000 0x2006383000b18c00 0x57b8e0c007c73c03 0x95ee383001f1cf00

def z244 : W := mkw 0x0000000000000000 0x0000000000000000 0xfb8400b0203ce3cf 0xfee1002c080f38f3

def z245 : W := mkw 0x8018c0c280c23022 0x20063030a0308c08 0x47b880c307c33c33 0x91ee2030c1f0cf0c

def z246 : W := mkw 0x002e08fbb0000003 0x000b823eec000000 0xcf3f00fff8000000 0x73cfc03ffe000000

def z247 : W := mkw 0x0800000040000440 0x0200000010000110 0x40000040c0001c42 0x5000001030000710

def z248 : W := mkw 0x0400081120000098 0x0100020448000026 0xf98000b32024e3fe 0xfe60002cc80938ff

def z249 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x7fffff8307ffe073 0xdfffffe0c1fff81c

def z250 : W := mkw 0x04270c1125398098 0xc109c304494e6026 0xffff9cb327ffe3ff 0xffffe72cc9fff8ff

def z251 : W := mkw 0x002e00e800000000 0x000b803a00000000 0xcf3f00fc00000000 0x33cfc03f00000000

def z252 : W := mkw 0x0818e0c2c2040442 0x02063830b0810110 0x5738e0c3c6041c42 0xd5ce3830f1810710

def z253 : W := mkw 0x04080cd12049b098 0x0102033448126c26 0xfffc9cf327ffffff 0xffff273cc9ffffff

def z254 : W := mkw 0x803edafbb0c23023 0x200fb6beec308c08 0xfffffffff9c32031 0x7ffffffffe70c80c

def z255 : W := mkw 0x04000c1120098098 0x0100030448026026 0xa8c41c30203fe3ff 0xaa31070c080ff8ff

def z256 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0x3f7fffb300000000 0x0fdfffecc0000000

def z257 : W := mkw 0x04261e3930098099 0x0109878e4c026026 0xa8471f3c3838c38c 0x2a11c7cf0e0e30e3

def z258 : W := mkw 0xa077d60005bb8000 0xe81df580016ee000 0x0f7f9c0007fb0001 0x83dfe70001fec000

def z259 : W := mkw 0x0000000000000000 0x0000000000000000 0x0738000007c00001 0x81ce000001f00000

def z260 : W := mkw 0x002e1af930000001 0x000b86be4c000000 0xef7f1ffc38000000 0x3bdfc7ff0e000000

def z261 : W := mkw 0x0018c0c280000002 0x00063030a0000000 0xff3be3cff8000000 0x7fcef8f3fe000000

def z262 : W := mkw 0xa07edefbb19b8003 0x681fb7beec66e000 0xff7ffffff9db0001 0x7fdffffffe76c000

def z263 : W := mkw 0x182f00eec5703f62 0xc60bc03bb15c0fd8 0xcfbf00ffc7f83ff3 0xf3efc03ff1fe0ffc

def z264 : W := mkw 0x1027002c05300b00 0xc409c00b014c02c0 0x8f3f003c07f80381 0xa3cfc00f01fe00e0

def z265 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x3847ff00003fc000 0x0e11ffc0000ff000

def z266 : W := mkw 0x103edaffb0403b03 0x040fb6bfec100ec0 0xfffffffff8003f82 0x7ffffffffe000fe0

def z267 : W := mkw 0x4a0121004e244444 0x9280484013891111 0x3d036300fe24c04c 0xcf40d8c03f893013

def z268 : W := mkw 0x1a0800c6c8403e66 0x06820031b2100f99 0xc08000cff8003e7e 0x70200033fe000f9f

def z269 : W := mkw 0x04000c1120098098 0x0100030448026026 0xfb449cb32007c07c 0x7ed1272cc801f01f

def z270 : W := mkw 0xe050ff13b28fc003 0x38143fc4eca3f000 0x3040ff03f807c000 0x4c103fc0fe01f000

def z271 : W := mkw 0x8818c0c2c0c23462 0x22063030b0308d18 0x42b880c3c1c33c73 0x50ae2030f070cf1c

def z272 : W := mkw 0x0000081120000000 0x0000020448000000 0x02449cb300000000 0x0091272cc0000000

def z273 : W := mkw 0x0800200042040440 0x0200080010810110 0xfd03634cfe041c42 0xff40d8d33f810710

def z274 : W := mkw 0x003ed2ea90000003 0x000fb4baa4000000 0xcf3f63fcd8000000 0x33cfd8ff36000000

def z275 : W := mkw 0xda19e1c6cee67e66 0xb6867871b3b99f99 0xfd3b634cffe4de4e 0xff4ed8d33ff93793

def z276 : W := mkw 0x080800c2c0403462 0x02020030b0100d18 0x00000040c0001c00 0x0000001030000700

def z277 : W := mkw 0x080820c2c2443462 0x02020830b0910d18 0x558060c3c6043c72 0xd5601830f1810f1c

def z278 : W := mkw 0x103fc0ee85703b02 0xc40ff03ba15c0ec0 0xdfbfe0ffc7f83f83 0xf7eff83ff1fe0fe0

def z279 : W := mkw 0x4a0021004a044444 0x1280084012811111 0x00006300d8000000 0x000018c036000000

def z280 : W := mkw 0x0000000000000000 0x0000000000000000 0x390000000024c000 0x8e40000000093000

def z281 : W := mkw 0x003ed2ea90000003 0x000fb4baa4000000 0x3f7fff4cd8000000 0x0fdfffd336000000

def z282 : W := mkw 0xe877f702c7bfc462 0xfa1dfdc0b1eff118 0x3f7fff03c7ffc071 0xcfdfffc0f1fff01c

def z283 : W := mkw 0x1001000405703b00 0xc4004001015c0ec0 0xcd83004c07f83f83 0xb360c01301fe0fe0

def z284 : W := mkw 0x0010c00000000000 0x0004300000000000 0x1738e00000000000 0x05ce380000000000

def z285 : W := mkw 0x0000040000098000 0x0000010000026000 0x7bc49c83003fe073 0xdef12720c00ff81c

def z286 : W := mkw 0x0000081120000000 0x0000020448000000 0xfb449cb320000000 0x7ed1272cc8000000

def z287 : W := mkw 0xe076f700028fc000 0x381dbdc000a3f000 0x3f7fff000007c000 0x0fdfffc00001f000

def z288 : W := mkw 0x4001210006244000 0x9000484001891000 0xfd0363002624c24e 0xff40d8c009893093

def z289 : W := mkw 0x0800200042040440 0x0200080010810110 0x04006040c6001c00 0x0100181031800700

def z290 : W := mkw 0xe87ff3c2c7f67462 0xfa1ffcf0b1fd9d18 0x043b6340c7c01c00 0x010ed8d031f00700

def z291 : W := mkw 0x5a273b3d7e244e45 0x9689cecf5f891391 0xfd477f7cfe24de4e 0xff51dfdf3f893793

def z292 : W := mkw 0x5a2f21ec4f747f44 0xd68bc87b13dd1fd1 0xcfbf63fcdff83f83 0xb3efd8ff37fe0fe0

def z293 : W := mkw 0x64671f112539c098 0xd919c7c4494e7026 0xa8471f302038c38c 0x2a11c7cc080e30e3

def z294 : W := mkw 0xa0400400019b8000 0x681001000066e000 0x0000000001db0001 0x000000000076c000

def z295 : W := mkw 0x8036f20002860000 0x200dbc8000a18000 0x3f7fff0007c70001 0x8fdfffc001f1c000

def z296 : W := mkw 0x0000000000000000 0x0000000000000000 0xa80000002020c20c 0x2a00000008083083

def z297 : W := mkw 0x52271b3d3c204a05 0x9489c6cf4f081281 0xa8471f3c3820c20c 0x2a11c7cf0e083083

def z298 : W := mkw 0xf87ff7eec7ffff62 0xfe1ffdfbb1ffffd8 0xffffffffc7fffff3 0xfffffffff1fffffc

def z299 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xcf3f00fc07c01c00 0x33cfc03f01f00700

def z300 : W := mkw 0x0000000000000000 0x0000000000000000 0x4080008300002072 0x50200020c000081c

def z301 : W := mkw 0x606717000539c000 0xd819c5c0014e7000 0x3b479f00003fc001 0x8ed1e7c0000ff000

def z302 : W := mkw 0x083efafbf2040443 0x020fbebefc810110 0xff7ffffffe041c42 0xffdfffffff810710

def z303 : W := mkw 0x0000000000000000 0x0000000000000000 0x5300808300000000 0x54c02020c0000000

def z304 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xff7ffffff824c24e 0xffdffffffe093093

def z305 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xc43b63fff8000000 0x710ed8fffe000000

def z306 : W := mkw 0x1001000405703b00 0xc4004001015c0ec0 0xcb8400b007f83f83 0xb2e1002c01fe0fe0

def z307 : W := mkw 0xe077f30007b64000 0xf81dfcc001ed9000 0x3f7fff0007c00000 0x0fdfffc001f00000

def z308 : W := mkw 0xe07ff3ea97b64003 0xf81ffcfaa5ed9000 0x043b634cdfc00000 0x010ed8d337f00000

def z309 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0x3403634cfe04dc4c 0x4d00d8d33f813713

def z310 : W := mkw 0x8418ccd3a0cbb0ba 0x21063334e832ec2e 0x02fc9cb301db21b1 0x00bf272cc076c86c

def z311 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0x0000000006001c00 0x0000000001800700

def z312 : W := mkw 0x0418ccd3a009809a 0x01063334e8026026 0xfffcfcf3e03fe3ff 0xffff3f3cf80ff8ff

def z313 : W := mkw 0x4e002d116a0dc4dc 0x13800b445a837137 0x3040ff03f807c07c 0x4c103fc0fe01f01f

def z314 : W := mkw 0x000800c000403000 0x0002003000100c00 0x02b8008001c02001 0x00ae002000700800

def z315 : W := mkw 0x883efafbf2860463 0x220fbebefca18118 0xff7ffffff8070070 0x7fdffffffe01c01c

def z316 : W := mkw 0x8818e8d3e2c63462 0x22063a34f8b18d18 0xfffcfcf3e7c73c73 0xffff3f3cf9f1cf1c

def z317 : W := mkw 0x8010e00002860000 0x2004380000a18000 0x0438600007c00000 0x010e180001f00000

def z318 : W := mkw 0x5a3ff3eede244e47 0x968ffcfbb7891391 0xfd3b634cfe24de4e 0xff4ed8d33f893793

def z319 : W := mkw 0x0000000000000000 0x0000000000000000 0x028400b000182181 0x00a1002c00060860

def z320 : W := mkw 0x803ec0ea81d23122 0x600fb03aa0748c48 0x02bc80b301db21b1 0x00af202cc076c86c

def z321 : W := mkw 0xda19e1c6cee67e66 0xb6867871b3b99f99 0x043b634cdfc01c00 0x010ed8d337f00700

def z322 : W := mkw 0x604105000539c000 0xd8104140014e7000 0x000000000038c000 0x00000000000e3000

def z323 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0x5503634cde041c42 0xd540d8d337810710

def z324 : W := mkw 0x8418ccd3a0cbb0ba 0x21063334e832ec2e 0xfbfc9cb321ffe3ff 0xfeff272cc87ff8ff

def z325 : W := mkw 0x043edefbb009809b 0x010fb7beec026026 0x02fc9cb3001b21b1 0x00bf272cc006c86c

def z326 : W := mkw 0x1000000400403b00 0x0400000100100ec0 0x0080000000003f82 0x0020000000000fe0

def z327 : W := mkw 0x5a0929fffe244e47 0x96824a7fff891391 0xfd0363fffe24de4e 0xff40d8ffff893793

def z328 : W := mkw 0x002e00e801503100 0x400b803a00540c40 0xcbbc00b001f82383 0xb2ef002c007e08e0

def z329 : W := mkw 0x0026002800000000 0x0009800a00000000 0x8807003c00000000 0x2201c00f00000000

def z330 : W := mkw 0x043edefbb009809b 0x010fb7beec026026 0xff7ffffff807c07c 0x7fdffffffe01f01f

def z331 : W := mkw 0xe477ff1127bfc098 0xf91dffc449eff026 0x3f7fff0327ffc07d 0xcfdfffc0c9fff01f

def z332 : W := mkw 0x14270c3d25398b98 0xc509c30f494e62e6 0xa8471c3c2038c38c 0x2a11c70f080e30e3

def z333 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0x3f7fff4cdfffdc01 0x8fdfffd337fff700

def z334 : W := mkw 0x0410de13b009809b 0x01043784ec026026 0xfbc4ffb3f83fe3ff 0xfef13fecfe0ff8ff

def z335 : W := mkw 0x04000c1120098098 0x0100030448026026 0x00409c0300030030 0x00102700c000c00c

def z336 : W := mkw 0x0010da13b0000003 0x00043684ec000000 0xfb44ffb3f8000000 0x7ed13fecfe000000

def z337 : W := mkw 0xe077f30007b64000 0xf81dfcc001ed9000 0x173be30007c70001 0x85cef8c001f1c000

def z338 : W := mkw 0x000800e800000000 0x0002003a00000000 0xc00000fc00000000 0x3000003f00000000

def z339 : W := mkw 0x0000000000000000 0x0000000000000000 0xdb8480b3003f23f3 0xf6e1202cc00fc8fc

def z340 : W := mkw 0x0400040000098098 0x0100010000026026 0x000000000007c07c 0x000000000001f01f

def z341 : W := mkw 0x0000000000403000 0x0000000000100c00 0x0080000007c03c03 0x8020000001f00f00

def z342 : W := mkw 0xe477ff1127bfc098 0xf91dffc449eff026 0xbf7fff3027ffc38d 0xafdfffcc09fff0e3

def z343 : W := mkw 0x5a0921ec4e647f44 0x9682487b13991fd1 0xfd8363fcfe24ffce 0xff60d8ff3f893ff3

def z344 : W := mkw 0x00001a1130000001 0x000006844c000000 0x20401f0038000000 0x081007c00e000000

def z345 : W := mkw 0xa87ef6c2c3dfb462 0x6a1fbdb0b0f7ed18 0x57fcfcc3c7df3c73 0xd5ff3f30f1f7cf1c

def z346 : W := mkw 0x002e08f920000000 0x000b823e48000000 0xff7f9cff20000000 0x7fdfe73fc8000000

def z347 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x2c7f7f0007f8c000 0x0b1fdfc001fe3000

def z348 : W := mkw 0xe841250047fff460 0xfa10494011fffd18 0x0080000007fffc73 0x8020000001ffff1c

def z349 : W := mkw 0x103fd2ec05703b00 0xc40ff4bb015c0ec0 0xfffffffc07f83f83 0xbfffffff01fe0fe0

def z350 : W := mkw 0xf077f72c07bfcb00 0xfc1dfdcb01eff2c0 0xbf7fff3c07ffc381 0xafdfffcf01fff0e0

def z351 : W := mkw 0xe050f700028fc000 0x38143dc000a3f000 0x3b44ff00003fc001 0x8ed13fc0000ff000

def z352 : W := mkw 0x0000000000000000 0x0000000000000000 0xcb0400b000000000 0x32c1002c00000000

def z353 : W := mkw 0x142f08fd25703b98 0xc50bc23f495c0ee6 0xcfbf00ff27f83fff 0xf3efc03fc9fe0fff

def z354 : W := mkw 0x4801210046244440 0x9200484011891110 0x7d036340c624dc42 0xdf40d8d031893710

def z355 : W := mkw 0xe4412d1127bfc098 0xf9104b4449eff026 0xfbc49cb327ffe3ff 0xfef1272cc9fff8ff

def z356 : W := mkw 0xe076f700039fc000 0x781dbdc000e7f000 0x327cff0001dfc001 0x0c9f3fc00077f000

def z357 : W := mkw 0x002f00c005703000 0xc00bc030015c0c00 0x4fbf00c007f83c03 0x93efc03001fe0f00

def z358 : W := mkw 0x706f17ec0579fb00 0xdc1bc5fb015e7ec0 0xefff1ffc07f8ff83 0xbbffc7ff01fe3fe0

def z359 : W := mkw 0x04000c1120098098 0x0100030448026026 0x20401c002000c00c 0x0810070008003003

def z360 : W := mkw 0x000808fbb0000003 0x0002023eec000000 0xfd0363fff8000000 0x7f40d8fffe000000

def z361 : W := mkw 0x100900ec05703b00 0xc402403b015c0ec0 0xc08000fc07f83f83 0xb020003f01fe0fe0

def z362 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x44b860c3c7c03c72 0x512e1830f1f00f1c

def z363 : W := mkw 0x1a00000448000e44 0x0680000112000391 0xf900004cf824de4e 0xfe4000133e093793

def z364 : W := mkw 0xe450ff11228fc098 0x39143fc448a3f026 0xfbc4ffb3203fe3ff 0xfef13fecc80ff8ff

def z365 : W := mkw 0x4a0021004a044444 0x1280084012811111 0xf9006300f824c24e 0xfe4018c03e093093

def z366 : W := mkw 0x003ed2e800000000 0x000fb4ba00000000 0xff7ffffc00000000 0x3fdfffff00000000

def z367 : W := mkw 0x8810e002c2860462 0x22043800b0a18118 0x1738e003c7c70071 0xc5ce3800f1f1c01c

def z368 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080000000072073 0x802000000001c81c

def z369 : W := mkw 0x4000210002044000 0x1000084000811000 0x300063000004c000 0x0c0018c000013000

def z370 : W := mkw 0x0000000000000000 0x0000000000000000 0x1300800000070001 0x84c020000001c000

def z371 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x5080e0c3c0073c72 0x54203830f001cf1c

def z372 : W := mkw 0x0000081120000000 0x0000020448000000 0xfb449cb32024c24e 0xfed1272cc8093093

def z373 : W := mkw 0x04000c1120098098 0x0100030448026026 0xf9441c30203cc3ce 0xfe51070c080f30f3

def z374 : W := mkw 0x0000040000098000 0x0000010000026000 0x00000000003fc001 0x80000000000ff000

def z375 : W := mkw 0x0000000000000000 0x0000000000000000 0x300000002004c04c 0x4c00000008013013

def z376 : W := mkw 0x8c18ecd3e2cfb4fa 0x23063b34f8b3ed3e 0x77f8fcc3e7c7fc7f 0xddfe3f30f9f1ff1f

def z377 : W := mkw 0x000800c280000002 0x00020030a0000000 0x400000c3c0000000 0x50000030f0000000

def z378 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x1738e040c7c71c01 0x85ce381031f1c700

def z379 : W := mkw 0x60673700073dc000 0xd819cdc001cf7000 0x3d477f00063cc000 0x8f51dfc0018f3000

def z380 : W := mkw 0x04000c1120098098 0x0100030448026026 0xbb449c30203fc38d 0xaed1270c080ff0e3

def z381 : W := mkw 0x5a11fb17fe244e47 0x96847ec5ff891391 0xfd43ff4ffe24de4e 0xff50ffd3ff893793

def z382 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x47b860c0c7c03c03 0x91ee183031f00f00

def z383 : W := mkw 0x003edefbb0098003 0x000fb7beec026000 0xff7ffffff83fc001 0xffdffffffe0ff000

def z384 : W := mkw 0xe07ff7c007fff000 0xf81ffdf001fffc00 0x7fffffc007fffc03 0x9ffffff001ffff00

def z385 : W := mkw 0x002e00e800000000 0x000b803a00000000 0xcfbf00fc00382383 0xb3efc03f000e08e0

def z386 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xf90000002624de4e 0xfe40000009893793

def z387 : W := mkw 0x9819e0c6c7f63f62 0xe6067831b1fd8fd8 0x57b8e0c3c7ff3ff3 0xd5ee3830f1ffcffc

def z388 : W := mkw 0xea50f7004a8fc444 0x3a943dc012a3f111 0x3040ff00f807c04c 0x4c103fc03e01f013

def z389 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000024c24e 0x8000000000093093

def z390 : W := mkw 0x1a0808fff8000e47 0x0682023ffe000391 0xc00000fff8001e4e 0x7000003ffe000793

def z391 : W := mkw 0x0400081120000098 0x0100020448000026 0x800000302000038c 0x2000000c080000e3

def z392 : W := mkw 0x003ed2ea90000003 0x000fb4baa4000000 0x573be3cfd8000000 0x55cef8f3f6000000

def z393 : W := mkw 0xe859e5c2c7fff462 0xfa167970b1fffd18 0x57b8e0c3c7fffc73 0xd5ee3830f1ffff1c

def z394 : W := mkw 0x04000c1120098098 0x0100030448026026 0x73c09c832007e07f 0xdcf02720c801f81f

def z395 : W := mkw 0xe47ffffbb7bfc09b 0xf91ffffeedeff026 0xffffffffffffe3ff 0xfffffffffffff8ff

def z396 : W := mkw 0x0036d60000098000 0x000db58000026000 0x3f7fff00003fc001 0x8fdfffc0000ff000

def z397 : W := mkw 0x0000000000000000 0x0000000000000000 0x4500004006001c02 0x9140001001800700

def z398 : W := mkw 0xfa7ff7c6cffffe66 0xfe9ffdf1b3ffff99 0xffffffcffffffe7f 0xfffffff3ffffff9f

def z399 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x043b630007ffc001 0x810ed8c001fff000

def z400 : W := mkw 0x1a00000448000e44 0x0680000112000391 0xfd03634cf8001e4e 0x7f40d8d33e000793

def z401 : W := mkw 0xf277f7040fbfca04 0xfc9dfdc103eff281 0xbf7fff0c3fffc20d 0xafdfffc30ffff083

def z402 : W := mkw 0x142f04ec0579bb98 0xc50bc13b015e6ee6 0xcfbf00fc07ffffff 0xb3efc03f01ffffff

def z403 : W := mkw 0x803efafbb2860003 0x200fbebeeca18000 0xff7fffffffc70001 0xffdffffffff1c000

def z404 : W := mkw 0x8410ec11228f8098 0x21043b0448a3e026 0xfffcfcb327ffe3ff 0xffff3f2cc9fff8ff

def z405 : W := mkw 0x0400040000098098 0x0100010000026026 0x000000000038c38c 0x00000000000e30e3

def z406 : W := mkw 0x003ed2c280000002 0x000fb4b0a0000000 0x7f7fffc3c0000000 0x5fdffff0f0000000

def z407 : W := mkw 0x102f08fd25703b00 0xc40bc23f495c0ec0 0xffff9cff27f83f83 0xffffe73fc9fe0fe0

def z408 : W := mkw 0x003edafbb1503103 0x400fb6beec540c40 0xfffffffff9d82181 0x7ffffffffe760860

def z409 : W := mkw 0x0000200002040000 0x0000080000810000 0x1500600006040000 0x8540180001810000

def z410 : W := mkw 0x8018e0c282c63022 0x20063830a0b18c08 0x17b8e08307c72031 0x85ee3820c1f1c80c

def z411 : W := mkw 0x042e0cf920098098 0x010b833e48026026 0xffff9cff203fe3ff 0xffffe73fc80ff8ff

def z412 : W := mkw 0x1001000405703b00 0xc4004001015c0ec0 0x0000000007c01c00 0x0000000001f00700

def z413 : W := mkw 0x5e0125044e2dcedc 0x97804941138b73b7 0xfd83634cfe3fffff 0xff60d8d33f8fffff

def z414 : W := mkw 0x5a0121044f747f44 0xd680484113dd1fd1 0xfd83634cfffcffcf 0xff60d8d33fff3ff3

def z415 : W := mkw 0x1001000404200a00 0x8400400101080280 0x8803000c00200200 0x2200c00300080080

def z416 : W := mkw 0x0036d20000000000 0x000db48000000000 0x043b630000000000 0x010ed8c000000000

def z417 : W := mkw 0x4a0021004a044444 0x1280084012811111 0x75006340fe04dc4e 0xdd4018d03f813713

def z418 : W := mkw 0xa476de11219b8098 0x691db7844866e026 0x02fc9cb301db21b1 0x00bf272cc076c86c

def z419 : W := mkw 0x000808fbb0000003 0x0002023eec000000 0xfb449cfff8000000 0x7ed1273ffe000000

def z420 : W := mkw 0xda3fe1eecff67f66 0xf68ff87bb3fd9fd9 0xffbfe3ffffffffff 0xffeff8ffffffffff

def z421 : W := mkw 0xe07ff7c287fff022 0xf81ffdf0a1fffc08 0x3fffff8307ffe031 0x8fffffe0c1fff80c

def z422 : W := mkw 0xe077f30007b64000 0xf81dfcc001ed9000 0x3d3b630007e4c000 0x8f4ed8c001f93000

def z423 : W := mkw 0x7067172c0539cb00 0xdc19c5cb014e72c0 0xa8471f3c0038c380 0x2a11c7cf000e30e0

def z424 : W := mkw 0x5e012d156e2dcedc 0x97804b455b8b73b7 0xfd477f7cfe3cdfce 0xff51dfdf3f8f37f3

def z425 : W := mkw 0x04261e3930098099 0x0109878e4c026026 0xfbc79fbf383fe3ff 0xfef1e7efce0ff8ff

def z426 : W := mkw 0x0000083930000001 0x0000020e4c000000 0x8000003c38000000 0x2000000f0e000000

def z427 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0x8abf00bc01f82381 0x22afc02f007e08e0

def z428 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0x3d0363000624de4e 0x8f40d8c001893793

def z429 : W := mkw 0x0410de13b009809b 0x01043784ec026026 0x3040ff03f807c07c 0x4c103fc0fe01f01f

def z430 : W := mkw 0x5a27212c4f344f44 0xd689c84b13cd13d1 0xfd07637cfe3cdfce 0xff41d8df3f8f37f3

def z431 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xcd03004c0624de4e 0xb340c01301893793

def z432 : W := mkw 0x5a3ffbfffe244e47 0x968ffeffff891391 0xff7ffffffe001c00 0x7fdfffffff800700

def z433 : W := mkw 0x0000081120000000 0x0000020448000000 0xfbc49cb320382383 0xfef1272cc80e08e0

def z434 : W := mkw 0x0800200042040440 0x0200080010810110 0x0000000006041c42 0x8000000001810710

def z435 : W := mkw 0x080800c2c0403462 0x02020030b0100d18 0x538080c3c0073c73 0xd4e02030f001cf1c

def z436 : W := mkw 0x002e00e801503100 0x400b803a00540c40 0x0038000001c00000 0x000e000000700000

def z437 : W := mkw 0xfa77f3044fb64e44 0xfe9dfcc113ed9391 0x043b634cdfc01c00 0x010ed8d337f00700

def z438 : W := mkw 0x000800c000403000 0x0002003000100c00 0x408000c000003c02 0x1020003000000f00

def z439 : W := mkw 0x04000c1120098098 0x0100030448026026 0x3b449c03203fc07d 0xced12700c80ff01f

def z440 : W := mkw 0x8818e8fbf2c63463 0x22063a3efcb18d18 0xd7b8e0ffffc73c73 0xf5ee383ffff1cf1c

def z441 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0xffb8e0c3e7e7fe7f 0xffee3830f9f9ff9f

def z442 : W := mkw 0x0026002801100100 0x4009800a00440040 0x0004003000180180 0x0001000c00060060

def z443 : W := mkw 0xe067250007bfc000 0xf819c94001eff000 0x0f3f000007ffc001 0x83cfc00001fff000

def z444 : W := mkw 0x5a0101044c204e44 0x9680404113081391 0xe803034cf820de4e 0x7a00c0d33e083793

def z445 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xa803030c3e24de4e 0xaa00c0c30f893793

def z446 : W := mkw 0x0400040000098098 0x0100010000026026 0x53808083003fe3ff 0xd4e02020c00ff8ff

def z447 : W := mkw 0x0400081120000098 0x0100020448000026 0x000000032000007c 0x40000000c800001f

def z448 : W := mkw 0xe877f70047fff460 0xfa1dfdc011fffd18 0x3fffff0007fffc73 0x8fffffc001ffff1c

def z449 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000800300070070 0x44002000c001c01c

def z450 : W := mkw 0x0800200042040440 0x0200080010810110 0x5780e0c3c6073c73 0xd5e03830f181cf1c

def z451 : W := mkw 0x1027002c05300b00 0xc409c00b014c02c0 0xcd07007c06381f82 0xb341c01f018e07e0

def z452 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080000000382383 0x80200000000e08e0

def z453 : W := mkw 0xf07ff7ec07fffb00 0xfc1ffdfb01fffec0 0x3f7fff4c07ffdc01 0x8fdfffd301fff700

def z454 : W := mkw 0x0036da3930000001 0x000db68e4c000000 0xbf7fff3c38000000 0x2fdfffcf0e000000

def z455 : W := mkw 0x1027002c05300b00 0xc409c00b014c02c0 0xcb8700bc00382383 0xb2e1c02f000e08e0

def z456 : W := mkw 0xa07ed6c281dbb022 0x681fb5b0a076ec08 0x02fc9c8301db2031 0x00bf2720c076c80c

def z457 : W := mkw 0x0001000005300000 0xc0004000014c0000 0x0000000007f80001 0x8000000001fe0000

def z458 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x02b8808307c73c73 0x80ae2020c1f1cf1c

def z459 : W := mkw 0x5a3ff3eede244e47 0x968ffcfbb7891391 0x043b634cde001c00 0x010ed8d337800700

def z460 : W := mkw 0x8c002c1162cfb4f8 0x23000b0458b3ed3e 0xfbc49cb327ffffff 0xfef1272cc9ffffff

def z461 : W := mkw 0x0000081120000000 0x0000020448000000 0xff47fffff8000000 0x7fd1fffffe000000

def z462 : W := mkw 0x100800ec00403b00 0x0402003b00100ec0 0xcb8400fc00383f83 0xb2e1003f000e0fe0

def z463 : W := mkw 0xe077ff1127bfc000 0xf81dffc449eff000 0xff7fffb327ffc001 0xffdfffecc9fff000

def z464 : W := mkw 0xe041210007b64000 0xf810484001ed9000 0x0000000007c00000 0x0000000001f00000

def z465 : W := mkw 0x103fd2ee95703b03 0xc40ff4bba55c0ec0 0xcfbf63fcdff83f83 0xb3efd8ff37fe0fe0

def z466 : W := mkw 0x0018c0c280000002 0x00063030a0000000 0x0238808300000000 0x008e2020c0000000

def z467 : W := mkw 0x883ee0eac3d63562 0x620fb83ab0f58d58 0x57bce0f3c7df3df3 0xd5ef383cf1f7cf7c

def z468 : W := mkw 0x56010d152c29ca9c 0x958043454b0a72a7 0xfbc79fbf383fe3ff 0xfef1e7efce0ff8ff

def z469 : W := mkw 0x102f04ec0579bb00 0xc40bc13b015e6ec0 0xffff9cfc07ffff83 0xbfffe73f01ffffe0

def z470 : W := mkw 0x520101040c204a04 0x9480404103081281 0xed03034c3e20de0e 0xbb40c0d30f883783

def z471 : W := mkw 0x0018dafbb0000003 0x000636beec000000 0xf040fffff8000000 0x7c103ffffe000000

def z472 : W := mkw 0x100900c404603a00 0x8402403101180e80 0xcfbb00cc07e03e03 0xb3eec03301f80f80

def z473 : W := mkw 0x883ee0eac2c63462 0x220fb83ab0b18d18 0xdfbfe0ffc7c73c73 0xf7eff83ff1f1cf1c

def z474 : W := mkw 0x4a0021004a044444 0x1280084012811111 0xfd03634cf804c04c 0x7f40d8d33e013013

def z475 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0x55006040c624de4e 0xd540181031893793

def z476 : W := mkw 0x9a18e0c6cac63e66 0x26863831b2b18f99 0xd7b8e0cfffc73e7f 0xf5ee3833fff1cf9f

def z477 : W := mkw 0x7a6737044f3dce44 0xde99cdc113cf7391 0xfd477f4cfe3cde4e 0xff51dfd33f8f3793

def z478 : W := mkw 0xe077ff13b7bfc003 0xf81dffc4edeff000 0x3f7fff03ffffc001 0xcfdfffc0fffff000

def z479 : W := mkw 0x04000c1120098098 0x0100030448026026 0xffc7fffff83fe3ff 0xfff1fffffe0ff8ff

def z480 : W := mkw 0x04000c1120098098 0x0100030448026026 0xf0c09cb32007e3fe 0x7c30272cc801f8ff

def z481 : W := mkw 0x182f20ec47743f40 0xc60bc83b11dd0fd0 0xdfbf60fcc7fc3fc3 0xf7efd83f31ff0ff0

def z482 : W := mkw 0x1a3edafff8000e47 0x068fb6bffe000391 0xff7ffffff8001e4e 0x7fdffffffe000793

def z483 : W := mkw 0x003edafbb1503103 0x400fb6beec540c40 0x02fc9cb301d82181 0x00bf272cc0760860

def z484 : W := mkw 0x103fdaffb4200a03 0x840ff6bfed080280 0xff7ffffffe201e02 0xffdfffffff880780

def z485 : W := mkw 0x00000813b0000003 0x00000204ec000000 0x00000003f8000000 0x40000000fe000000

def z486 : W := mkw 0x5a0125044e2dce44 0x96804941138b7391 0xff47ff4cfe3fde4f 0xffd1ffd33f8ff793

def z487 : W := mkw 0xe87ff3c2c7f67462 0xfa1ffcf0b1fd9d18 0x57bbe3c3c7c73c73 0xd5eef8f0f1f1cf1c

def z488 : W := mkw 0xda0121044ee67e64 0xb680484113b99f99 0x0080000007e7fe7f 0x8020000001f9ff9f

def z489 : W := mkw 0x903fc0ee85f23b22 0xe40ff03ba17c8ec8 0xcfbf80ff07fb3fb3 0xb3efe03fc1fecfec

def z490 : W := mkw 0x102f00ec04200a00 0x840bc03b01080280 0xcf3f00fc06201e02 0xb3cfc03f01880780

def z491 : W := mkw 0x8010e00002860000 0x2004380000a18000 0x1000e00000070000 0x040038000001c000

def z492 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0x30006300fe24de4e 0xcc0018c03f893793

def z493 : W := mkw 0x040808fbb000009b 0x0102023eec000026 0xc08000fff80023fe 0x7020003ffe0008ff

def z494 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xc000004cfe24de4e 0xf00000133f893793

def z495 : W := mkw 0x143fdeffb579bb9b 0xc50ff7bfed5e6ee6 0xffffffffffffffff 0xffffffffffffffff

def z496 : W := mkw 0xe051e50007bfc000 0xf814794001eff000 0x1738e00007ffc001 0x85ce380001fff000

def z497 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0x347bff4ff8000000 0x4d1effd3fe000000

def z498 : W := mkw 0x726717040d39ca04 0xdc99c5c1034e7281 0xa8471f0c3838c20c 0x2a11c7c30e0e3083

def z499 : W := mkw 0x0010d20290000003 0x00043480a4000000 0x00006300d8000000 0x000018c036000000

def z500 : W := mkw 0x043edefbb009809b 0x010fb7beec026026 0xfbfc9cb3203fe3ff 0xfeff272cc80ff8ff

def z501 : W := mkw 0x002e00e801503100 0x400b803a00540c40 0xcfbf00fc01d82181 0x33efc03f00760860

def z502 : W := mkw 0x000800c000403000 0x0002003000100c00 0x0438004007c01c00 0x010e001001f00700

def z503 : W := mkw 0x04000c1120098098 0x0100030448026026 0xcbc49cb3003b23b3 0xb2f1272cc00ec8ec

def z504 : W := mkw 0xe87ffffbf7fff463 0xfa1ffffefdfffd18 0xfffffffffffffc73 0xffffffffffffff1c

def z505 : W := mkw 0x003ec0ea80000002 0x000fb03aa0000000 0xdf3fe0ffc0000000 0x77cff83ff0000000

def z506 : W := mkw 0x0400040000098098 0x0100010000026026 0xcb8400b0003fe3ff 0xb2e1002c000ff8ff

def z507 : W := mkw 0xe077f30007b64000 0xf81dfcc001ed9000 0x0f3f630007f80001 0x83cfd8c001fe0000

def z508 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x067fff0007db0001 0x019fffc001f6c000

def z509 : W := mkw 0x04000c1120098098 0x0100030448026026 0x00441c3000180180 0x0011070c00060060

def z510 : W := mkw 0x0036da13b0000003 0x000db684ec000000 0x3f7fff03f8000000 0x4fdfffc0fe000000

def z511 : W := mkw 0x002e00e800000000 0x000b803a00000000 0x043b004c00000000 0x010ec01300000000

def z512 : W := mkw 0x883ef2ead2c63463 0x220fbcbab4b18d18 0x043b634cdfc01c00 0x010ed8d337f00700

def z513 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xffbf00fc27fcffcf 0xffefc03f09ff3ff3

def z514 : W := mkw 0x0027000005300000 0xc009c000014c0000 0xcfbf00b007f82383 0xb3efc02c01fe08e0

def z515 : W := mkw 0x180800eec0403f62 0x0602003bb0100fd8 0xc08000ffc0003ff2 0x7020003ff0000ffc

def z516 : W := mkw 0x604017000009c000 0x181005c000027000 0x20401f000000c000 0x081007c000003000

def z517 : W := mkw 0xf041250407fffb00 0xfc10494101fffec0 0x0080000007ffff83 0x8020000001ffffe0

def z518 : W := mkw 0x0018c0c280403002 0x00063030a0100c00 0x57b8e0c3c7c03c03 0xd5ee3830f1f00f00

def z519 : W := mkw 0x0800200042040440 0x0200080010810110 0x10006000c0040040 0x4400180030010010

def z520 : W := mkw 0x0a00000048000444 0x0280000012000111 0x00000000f800004c 0x400000003e000013

def z521 : W := mkw 0x04000c1120098098 0x0100030448026026 0x3bc49cb3003fe1b1 0x8ef1272cc00ff86c

def z522 : W := mkw 0x8c18e4c2c2cfb4fa 0x23063930b0b3ed3e 0x57b8e0c3c7ffffff 0xd5ee3830f1ffffff

def z523 : W := mkw 0x0018dad3b0000003 0x000636b4ec000000 0x7778ffc3f8000000 0x5dde3ff0fe000000

def z524 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0xff7fff4cffffc001 0xffdfffd33ffff000

def z525 : W := mkw 0x103fdaffb5703b03 0xc40ff6bfed5c0ec0 0xcfff9cff07f83f83 0xb3ffe73fc1fe0fe0

def z526 : W := mkw 0xca10e102ca864466 0x32843840b2a19119 0x3000e303f807c07c 0x4c0038c0fe01f01f

def z527 : W := mkw 0x8810e00042c63460 0x2204380010b18d18 0x17b8e00007c73c73 0x85ee380001f1cf1c

def z528 : W := mkw 0x0026000000000000 0x0009800000000000 0x0f3f000000000000 0x03cfc00000000000

def z529 : W := mkw 0xf47ffffd27fffb98 0xfd1fffff49fffee6 0xffffffff27ffffff 0xffffffffc9ffffff

def z530 : W := mkw 0x04000c1120098098 0x0100030448026026 0xebc41cb02038e38f 0xbaf1072c080e38e3

def z531 : W := mkw 0x003fdafbb5300003 0xc00ff6beed4c0000 0xff7ffffffff80001 0xffdffffffffe0000

def z532 : W := mkw 0xe858f7c2c2cff462 0x3a163df0b0b3fd18 0x77f8ffc3c7c7fc73 0xddfe3ff0f1f1ff1c

def z533 : W := mkw 0xfa7fffffffbfce47 0xfe9fffffffeff391 0xff7fffffffffde4f 0xffdffffffffff793

def z534 : W := mkw 0x04000c1120098098 0x0100030448026026 0xb8449c33203fc3fc 0x6e11270cc80ff0ff

def z535 : W := mkw 0x880820c042c63460 0x2202083010b18d18 0x47b800c007c73c73 0x91ee003001f1cf1c

def z536 : W := mkw 0x1a00000448000e44 0x0680000112000391 0x0000000000001e4e 0x0000000000000793

def z537 : W := mkw 0x1801200446240e40 0x8600480111890390 0xdd03604cc6241e42 0xf740d81331890790

def z538 : W := mkw 0xe067370007bfc000 0xf819cdc001eff000 0x28471f0007ffc001 0x8a11c7c001fff000

def z539 : W := mkw 0x8810e002c2860462 0x22043800b0a18118 0x5380e083c0072073 0xd4e03820f001c81c

def z540 : W := mkw 0xa076d20001920000 0x681db48000648000 0x0038000001c00000 0x000e000000700000

def z541 : W := mkw 0x520101040c204a04 0x9480404103081281 0x0003030c18000000 0x0000c0c306000000

def z542 : W := mkw 0x000800c000000000 0x0002003000000000 0x473800c000000000 0x11ce003000000000

def z543 : W := mkw 0x0000000000000000 0x0000000000000000 0x0280808300032031 0x00a02020c000c80c

def z544 : W := mkw 0x5a0921c44e647e44 0x9682487113991f91 0xffbb63ccffe4fe4f 0xffeed8f33ff93f93

def z545 : W := mkw 0x0018c0c280000002 0x00063030a0000000 0x57b8e0c3c0072073 0xd5ee3830f001c81c

def z546 : W := mkw 0x04000c1120098098 0x0100030448026026 0xfbc49cb3201b21b1 0x7ef1272cc806c86c

def z547 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x06b8e0c3c7c33c31 0x01ae3830f1f0cf0c

def z548 : W := mkw 0x14080cfd2049bb98 0x0502033f48126ee6 0xfbc49cff203fffff 0xfef1273fc80fffff

def z549 : W := mkw 0xe07ffffbb7bfc003 0xf81ffffeedeff000 0x3f7fffb307ffc001 0x8fdfffecc1fff000

def z550 : W := mkw 0x6077d7000539c000 0xd81df5c0014e7000 0x3f7fff000038c000 0x0fdfffc0000e3000

def z551 : W := mkw 0x1027000405703b00 0xc409c001015c0ec0 0x0fbf000007f83f83 0x83efc00001fe0fe0

def z552 : W := mkw 0x140104040579bb98 0xc5004101015e6ee6 0x0080000007ffffff 0x8020000001ffffff

def z553 : W := mkw 0x0000040000098000 0x0000010000026000 0x28441c000038c000 0x0a110700000e3000

def z554 : W := mkw 0x4a3efbfbfa044447 0x128fbefefe811111 0xff7ffffff804c04c 0x7fdffffffe013013

def z555 : W := mkw 0x883fe0c2c7f63462 0xe20ff830b1fd8d18 0x5fbfe0c3c7ff3c73 0xd7eff830f1ffcf1c

def z556 : W := mkw 0x880820c2c2c63462 0x22020830b0b18d18 0x408000c3c7c73c73 0xd0200030f1f1cf1c

def z557 : W := mkw 0x403ffbfbb6244003 0x900ffefeed891000 0xff7ffffffe24c000 0xffdfffffff893000

def z558 : W := mkw 0x56010d152c29ca9c 0x958043454b0a72a7 0xa8471f3c3838c38c 0x2a11c7cf0e0e30e3

def z559 : W := mkw 0x04000c1120098098 0x0100030448026026 0x53c49cb3001f21f3 0xd4f1272cc007c87c

def z560 : W := mkw 0x5e3ffffffe2dcedf 0x978fffffff8b73b7 0xfffffffffe3fffff 0xffffffffff8fffff

def z561 : W := mkw 0x5a2f21ec4e244e44 0x968bc87b13891391 0xff3f63fcfe24de4e 0xffcfd8ff3f893793

def z562 : W := mkw 0x5a3ffbffff747f47 0xd68ffeffffdd1fd1 0xfffffffffffcffcf 0xffffffffffff3ff3

def z563 : W := mkw 0x8810fa13f2860463 0x22043e84fca18118 0x3040ff03f8070070 0x4c103fc0fe01c01c

def z564 : W := mkw 0x003edafbb0403003 0x000fb6beec100c00 0xffffffffffc03c03 0xfffffffffff00f00

def z565 : W := mkw 0x6067130005304000 0xd819c4c0014c1000 0x0003030000000000 0x0000c0c000000000

def z566 : W := mkw 0x5e0129156e244edc 0x97804a455b8913b7 0xfd8363fffe24fffe 0xff60d8ffff893fff

def z567 : W := mkw 0x103fd2ee95703b03 0xc40ff4bba55c0ec0 0x043b634cdfc01c00 0x010ed8d337f00700

def z568 : W := mkw 0x4001010004204000 0x9000404001081000 0x280303000020c000 0x0a00c0c000083000

def z569 : W := mkw 0x04000c1120098098 0x0100030448026026 0xc2c49cb3201b23ff 0x70b1272cc806c8ff

def z570 : W := mkw 0x520101040c204a04 0x9480404103081281 0xfd03634cf820c20c 0x7f40d8d33e083083

def z571 : W := mkw 0x0000081120000000 0x0000020448000000 0x30409c0320000000 0x4c102700c8000000

def z572 : W := mkw 0x003ed2ea90000003 0x000fb4baa4000000 0xfd3b634cf8000000 0x7f4ed8d33e000000

def z573 : W := mkw 0xf07ff3ec07f67b00 0xfc1ffcfb01fd9ec0 0xcfbf63fc07f83f83 0xb3efd8ff01fe0fe0

def z574 : W := mkw 0x0027000005300000 0xc009c000014c0000 0x0807000000380000 0x0201c000000e0000

def z575 : W := mkw 0xe050f700028fc000 0x38143dc000a3f000 0x3778ff0007c7c001 0x8dde3fc001f1f000

def z576 : W := mkw 0x100800ec00403b00 0x0402003b00100ec0 0x0000004c00001c00 0x0000001300000700

def z577 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0xff7fff0027ffc24f 0xffdfffc009fff093

def z578 : W := mkw 0x0000000001503100 0x4000000000540c40 0x0080000001d82181 0x0020000000760860

def z579 : W := mkw 0x00261a3930000001 0x0009868e4c000000 0x00441c3000000000 0x0011070c00000000

def z580 : W := mkw 0x080820c042443440 0x0202083010910d10 0x57b860c0c7c43c43 0xd5ee183031f10f10

def z581 : W := mkw 0x8c10ec13e28f84fa 0x23043b04f8a3e13e 0xfbc4fcb3e03fe3ff 0xfef13f2cf80ff8ff

def z582 : W := mkw 0x1001000404200a00 0x8400400101080280 0xfd03004c2624de4e 0xff40c01309893793

def z583 : W := mkw 0xe051f70007bfc000 0xf8147dc001eff000 0x3040ff0007ffc001 0x8c103fc001fff000

def z584 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000004cf8000000 0x700000133e000000

def z585 : W := mkw 0x002f00e805703100 0xc00bc03a015c0c40 0x0fbf00b007f82181 0x83efc02c01fe0860

def z586 : W := mkw 0xe07ffbfbb7b64003 0xf81ffefeeded9000 0xff7fffffffc00000 0x7fdffffffff00000

def z587 : W := mkw 0xc819e1c2c6e67462 0xb2067870b1b99d18 0x7fbbe3c3c7e7fc73 0xdfeef8f0f1f9ff1c

def z588 : W := mkw 0xb07fd6ec05fbbb00 0xec1ff5bb017eeec0 0xcfff9cfc07fb3f83 0xb3ffe73f01fecfe0

def z589 : W := mkw 0x0010d20000000000 0x0004348000000000 0x3040ff0000000000 0x0c103fc000000000

def z590 : W := mkw 0x14010c1524298a98 0x85004305490a62a6 0xffc79cff263fffff 0xfff1e73fc98fffff

def z591 : W := mkw 0xda19e1c6cee67e66 0xb6867871b3b99f99 0x57bbe3cfdfc73c73 0xd5eef8f3f7f1cf1c

def z592 : W := mkw 0x5227012c0d304b04 0xd489c04b034c12c1 0xa807033c3838c38c 0x2a01c0cf0e0e30e3

def z593 : W := mkw 0x9c3fecffe7ffbffa 0xe70ffb3ff9ffeffe 0xfffffcffe7ffffff 0xffffff3ff9ffffff

def z594 : W := mkw 0x002e00e800000000 0x000b803a00000000 0xff3f63fcf8000000 0x7fcfd8ff3e000000

def z595 : W := mkw 0x1001000404200a00 0x8400400101080280 0xfd03634cfe201e02 0xff40d8d33f880780

def z596 : W := mkw 0x103fdaffb5703b03 0xc40ff6bfed5c0ec0 0xff7fffffffc01c00 0x7fdffffffff00700

def z597 : W := mkw 0xf07ff3ec07f67b00 0xfc1ffcfb01fd9ec0 0x043b634c07c01c00 0x010ed8d301f00700

def z598 : W := mkw 0xda11e1044ea64e44 0xb684784113a99391 0xff3be34cffe7de4f 0xffcef8d33ff9f793

def z599 : W := mkw 0x0400081120000098 0x0100020448000026 0xd38080b3200723ff 0xf4e0202cc801c8ff

def z600 : W := mkw 0x0000000000000000 0x0000000000000000 0x8804003000380380 0x2201000c000e00e0

def z601 : W := mkw 0x042e0cf92159b198 0x410b833e48566c66 0xfbfc9cb321ffe3ff 0xfeff272cc87ff8ff

def z602 : W := mkw 0x0000040000098000 0x0000010000026000 0xfbc49cb0003fe383 0xbef1272c000ff8e0

def z603 : W := mkw 0x000800ea90000003 0x0002003aa4000000 0x0000004cd8000000 0x0000001336000000

def z604 : W := mkw 0xe850f702c28fc462 0x3a143dc0b0a3f118 0x3040ff03c007c070 0x4c103fc0f001f01c

def z605 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x04b86040c7c73c73 0x812e181031f1cf1c

def z606 : W := mkw 0x4a0021004a044444 0x1280084012811111 0x000000000004c04c 0x0000000000013013

def z607 : W := mkw 0x1001000404200a00 0x8400400101080280 0x0000000006201e02 0x8000000001880780

def z608 : W := mkw 0x8800200042c63460 0x2200080010b18d18 0x55806040c7c73c73 0xd560181031f1cf1c

def z609 : W := mkw 0xe87ff7c2c7fff462 0xfa1ffdf0b1fffd18 0x3f7fff40c7ffdc01 0x8fdfffd031fff700

def z610 : W := mkw 0xfe77ff156fbfcedc 0xff9dffc55beff3b7 0xffffffffffffffff 0xffffffffffffffff

def z611 : W := mkw 0x4001210006244000 0x9000484001891000 0x000000000624c000 0x8000000001893000

def z612 : W := mkw 0x0818c0c2c0403462 0x02063030b0100d18 0x57b8e0c3c0003c72 0x55ee3830f0000f1c

def z613 : W := mkw 0x1a0020044a040e44 0x0680080112810391 0xd500604cfe041e4e 0xf54018133f810793

def z614 : W := mkw 0x0000081120000000 0x0000020448000000 0xa8441c3020000000 0x2a11070c08000000

def z615 : W := mkw 0x8800200042860460 0x2200080010a18118 0x0000000000070070 0x000000000001c01c

def z616 : W := mkw 0x5a2f21ec4f747f44 0xd68bc87b13dd1fd1 0xcfbf00fc07fcffcf 0xb3efc03f01ff3ff3

def z617 : W := mkw 0x5a0921c6ce647e66 0x96824871b3991f99 0xfd8363cffe24fe7e 0xff60d8f3ff893f9f

def z618 : W := mkw 0x1000000400000a00 0x0400000100000280 0xc000004c00001e02 0x3000001300000780

def z619 : W := mkw 0xc011e10006a64000 0xb004784001a99000 0x3f3be30007e7c001 0x8fcef8c001f9f000

def z620 : W := mkw 0x000800c280403022 0x00020030a0100c08 0x0080008300002030 0x00200020c000080c

def z621 : W := mkw 0x0000000000000000 0x0000000000000000 0xc08000b000002382 0x3020002c000008e0

def z622 : W := mkw 0xda3ffbfffee67e67 0xb68ffeffffb99f99 0xffffffffffe7fe7f 0xfffffffffff9ff9f

def z623 : W := mkw 0xe077ff3937bfc001 0xf81dffce4deff000 0xbf7fff3c3fffc001 0xafdfffcf0ffff000

def z624 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x12b8e083c1c72071 0x44ae3820f071c81c

def z625 : W := mkw 0xda11e106cea64e66 0xb6847841b3a99399 0xfd03e34ffe27de7e 0xff40f8d3ff89f79f

def z626 : W := mkw 0x0018c8fbb0000003 0x0006323eec000000 0xd738e0fff8000000 0x75ce383ffe000000

def z627 : W := mkw 0x8810e002c2860462 0x22043800b0a18118 0x00006000c0000000 0x0000180030000000

def z628 : W := mkw 0x8c18e8d3e2c634fa 0x23063a34f8b18d3e 0xd7b8e0f3e7c73fff 0xf5ee383cf9f1cfff

def z629 : W := mkw 0x0400081120000098 0x0100020448000026 0xfbc49cb3200023fe 0x7ef1272cc80008ff

def z630 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xc88700fc00383f82 0x3221c03f000e0fe0

def z631 : W := mkw 0x8818fad3f2c63463 0x22063eb4fcb18d18 0x77f8ffc3ffc73c73 0xddfe3ff0fff1cf1c

def z632 : W := mkw 0x5a37f3044e244e44 0x968dfcc113891391 0xff7fff4cfe24de4e 0xffdfffd33f893793

def z633 : W := mkw 0xe477ff1127bfc098 0xf91dffc449eff026 0x3fffffb307ffe1b1 0x8fffffecc1fff86c

def z634 : W := mkw 0xe041250007bfc000 0xf810494001eff000 0x3b449c0007ffc001 0x8ed1270001fff000

def z635 : W := mkw 0x0400040000098098 0x0100010000026026 0xf9800000203fe3ff 0xfe600000080ff8ff

def z636 : W := mkw 0x983fe0eec7f63f62 0xe60ff83bb1fd8fd8 0xcfbf60fcc7f83f83 0xb3efd83f31fe0fe0

def z637 : W := mkw 0x102e00ec01503b00 0x440b803b00540ec0 0xc2bc00fc01d83f83 0x30af003f00760fe0

def z638 : W := mkw 0x5a0129156e244e44 0x96804a455b891391 0xff47fffffe24de4e 0xffd1ffffff893793

def z639 : W := mkw 0x883ef2ead2c63463 0x220fbcbab4b18d18 0x57bbe3cfdfc73c73 0xd5eef8f3f7f1cf1c

def z640 : W := mkw 0x8818e0c2c2860462 0x22063830b0a18118 0x5738e0c3c0070070 0x55ce3830f001c01c

def z641 : W := mkw 0xe07ff7c287bfc002 0xf81ffdf0a1eff000 0x7f7fffc3c7ffc001 0xdfdffff0f1fff000

def z642 : W := mkw 0x0800200042040440 0x0200080010810110 0xfd006040e624de4e 0xff40181039893793

def z643 : W := mkw 0xf077f70407fffb00 0xfc1dfdc101fffec0 0x3fffff0007ffff83 0x8fffffc001ffffe0

def z644 : W := mkw 0x8000000000c23020 0x2000000000308c08 0x0080000001c32031 0x002000000070c80c

def z645 : W := mkw 0x8800200042c63460 0x2200080010b18d18 0x5380808307c73c73 0xd4e02020c1f1cf1c

def z646 : W := mkw 0x4001210006244000 0x9000484001891000 0xfd03634cfe24c000 0xff40d8d33f893000

def z647 : W := mkw 0x4200010008004004 0x1080004002001001 0x200003003800c00c 0x080000c00e003003

def z648 : W := mkw 0x0000000000000000 0x0000000000000000 0xfb8080832027e27f 0xfee02020c809f89f

def z649 : W := mkw 0x0000000000000000 0x0000000000000000 0xf900000020000000 0x7e40000008000000

def z650 : W := mkw 0x5e012d156e2dcedc 0x97804b455b8b73b7 0xfbc49cb3263fffff 0xfef1272cc98fffff

def z651 : W := mkw 0x60671f393539c001 0xd819c7ce4d4e7000 0xa8471f3c3838c000 0x2a11c7cf0e0e3000

def z652 : W := mkw 0x00261a3930000001 0x0009868e4c000000 0xfb479fbf38000000 0x7ed1e7efce000000

def z653 : W := mkw 0x0027000005300000 0xc009c000014c0000 0x043b000007c00000 0x010ec00001f00000

def z654 : W := mkw 0x5a2721044f344e44 0xd689c84113cd1391 0xff3f634cfffcde4f 0xffcfd8d33fff3793

def z655 : W := mkw 0x523fdbffbc204a07 0x948ff6ffef081281 0xff7ffffff820c20c 0x7fdffffffe083083

def z656 : W := mkw 0x1000002c00000b00 0x0400000b000002c0 0x8000003c00000380 0x2000000f000000e0

def z657 : W := mkw 0x0c080cd3e049b4fa 0x03020334f8126d3e 0xfbc49cf3e03fffff 0xfef1273cf80fffff

def z658 : W := mkw 0x04000c1120098098 0x0100030448026026 0xc08000b3203fe3ff 0xf020002cc80ff8ff

def z659 : W := mkw 0x083edafbf0403463 0x020fb6befc100d18 0xfffffffff8003c72 0x7ffffffffe000f1c

def z660 : W := mkw 0xfa4125044fbfce44 0xfe90494113eff391 0xfd03634cffffde4f 0xff40d8d33ffff793

def z661 : W := mkw 0x0000000000000000 0x0000000000000000 0xc900000000200202 0xb240000000080080

def z662 : W := mkw 0xa07ed6e801dbb100 0x681fb5ba0076ec40 0x02fc9cb001db2181 0x00bf272c0076c860

def z663 : W := mkw 0x883ef2c2c2c63462 0x220fbcb0b0b18d18 0x7fffffc3c7c73c73 0xdffffff0f1f1cf1c

def z664 : W := mkw 0x04000c1120098098 0x0100030448026026 0x30c09c03203fe3ff 0xcc302700c80ff8ff

def z665 : W := mkw 0x8018c0c280c23022 0x20063030a0308c08 0x57b8e0c3c1c32031 0x55ee3830f070c80c

def z666 : W := mkw 0x64671f112539c098 0xd919c7c4494e7026 0xfbc79fb3203fe3ff 0xfef1e7ecc80ff8ff

def z667 : W := mkw 0x883efafbf2c63463 0x220fbebefcb18d18 0x57fcfcf3c7c73c73 0xd5ff3f3cf1f1cf1c

def z668 : W := mkw 0x1e000c1568098edc 0x078003055a0263b7 0xfbc49cfff83fffff 0xfef1273ffe0fffff

def z669 : W := mkw 0x607fdffbb539c003 0xd81ff7feed4e7000 0xff7ffffff838c000 0x7fdffffffe0e3000

def z670 : W := mkw 0x0000000000000000 0x0000000000000000 0x30006300f8000000 0x4c0018c03e000000

def z671 : W := mkw 0x5a0121044f747f44 0xd680484113dd1fd1 0x0080000007fcffcf 0x8020000001ff3ff3

def z672 : W := mkw 0x08000002c0000462 0x02000000b0000118 0x00000003c0000070 0x40000000f000001c

def z673 : W := mkw 0x102f00ec05300b00 0xc40bc03b014c02c0 0xcf3f00fc00380380 0x33cfc03f000e00e0

def z674 : W := mkw 0x04080cfbb009809b 0x0102033eec026026 0xfbc49cfff83fe3ff 0xfef1273ffe0ff8ff

def z675 : W := mkw 0x1027002c05703b00 0xc409c00b015c0ec0 0x8887003c07f83f83 0xa221c00f01fe0fe0

def z676 : W := mkw 0x8000200002860000 0x2000080000a18000 0x0000000007c70001 0x8000000001f1c000

def z677 : W := mkw 0x5a2f21ec4f747f44 0xd68bc87b13dd1fd1 0x043b634cdfc01c00 0x010ed8d337f00700

def z678 : W := mkw 0x000800e800403100 0x0002003a00100c40 0x008000b000002180 0x0020002c00000860

def z679 : W := mkw 0x0000000000000000 0x0000000000000000 0xcd03004c00000000 0x3340c01300000000

def z680 : W := mkw 0xfa51f7044eafce44 0xbe947dc113abf391 0xfd43ff4cfe27de4e 0xff50ffd33f89f793

def z681 : W := mkw 0x04000c1120098098 0x0100030448026026 0xe8c41cb32038e3fe 0x7a31072cc80e38ff

def z682 : W := mkw 0x983ffafff7f63f63 0xe60ffebffdfd8fd8 0xffffffffffff3ff3 0xffffffffffffcffc

def z683 : W := mkw 0x0400040000098098 0x0100010000026026 0x3bc49c00003fe3ff 0x8ef12700000ff8ff

def z684 : W := mkw 0xfa7ff7ec4fffff44 0xfe9ffdfb13ffffd1 0xfffffffcffffffcf 0xffffffff3ffffff3

def z685 : W := mkw 0xe441250007bfc098 0xf910494001eff026 0x0080000007ffe3ff 0x8020000001fff8ff

def z686 : W := mkw 0x0400081120000098 0x0100020448000026 0x008000b3000021b0 0x0020002cc000086c

def z687 : W := mkw 0x0436de1120098098 0x010db78448026026 0xffffffb3203fe3ff 0xffffffecc80ff8ff

def z688 : W := mkw 0x5a2f21ec4f747f44 0xd68bc87b13dd1fd1 0xfd3b634cffe4de4e 0xff4ed8d33ff93793

def z689 : W := mkw 0x0400000000000098 0x0100000000000026 0x00800000000023fe 0x00200000000008ff

def z690 : W := mkw 0xf07fffffb7fffb03 0xfc1fffffedfffec0 0xffffffffffffff83 0xffffffffffffffe0

def z691 : W := mkw 0x04000c1120098098 0x0100030448026026 0xaac49cb3203be3bd 0x2ab1272cc80ef8ef

def z692 : W := mkw 0x982f20ec47f63f60 0xe60bc83b11fd8fd8 0xcfbf00fc07ff3ff3 0xb3efc03f01ffcffc

def z693 : W := mkw 0x0000000000000000 0x0000000000000000 0xa803030c38000000 0x2a00c0c30e000000

def z694 : W := mkw 0x043edefbb009809b 0x010fb7beec026026 0xff7ffffff838c38c 0x7fdffffffe0e30e3

def z695 : W := mkw 0x8018e0c282860002 0x20063830a0a18000 0x5738e0c3c7c70001 0xd5ce3830f1f1c000

def z696 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xc27c9cfff8000000 0x709f273ffe000000

def z697 : W := mkw 0x4a10fb13fa044447 0x12843ec4fe811111 0x3040ff03f804c04c 0x4c103fc0fe013013

def z698 : W := mkw 0x520101040c204a04 0x9480404103081281 0x000000000020c20c 0x0000000000083083

def z699 : W := mkw 0x0000000000000000 0x0000000000000000 0x3b449c0000000000 0x0ed1270000000000

def z700 : W := mkw 0x4037f30006244000 0x900dfcc001891000 0x3f7fff000624c000 0x8fdfffc001893000

def z701 : W := mkw 0x102f08ffb5703b03 0xc40bc23fed5c0ec0 0xcfbf00fffff83f83 0xf3efc03ffffe0fe0

def z702 : W := mkw 0x5a0021044a044e44 0x1680084112811391 0xf000634cf804de4e 0x7c0018d33e013793

def z703 : W := mkw 0xe07ff7e807fff100 0xf81ffdfa01fffc40 0x3fffffb007ffe181 0x8fffffec01fff860

def z704 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0x0403634cde24de4e 0x8100d8d337893793

def z705 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xc4bb00fc07c03f82 0x312ec03f01f00fe0

def z706 : W := mkw 0x100800ec00403b00 0x0402003b00100ec0 0xc7b800fc07c03f83 0xb1ee003f01f00fe0

def z707 : W := mkw 0x180808fff0403f63 0x0602023ffc100fd8 0xc08000fff8003ff2 0x7020003ffe000ffc

def z708 : W := mkw 0x142f0cfd2579bb98 0xc50bc33f495e6ee6 0x347b9c4f27c7dc7c 0x4d1ee713c9f1f71f

def z709 : W := mkw 0xfa4125044fbfce44 0xfe90494113eff391 0x0000000007ffdc01 0x8000000001fff700

def z710 : W := mkw 0xd219c1c68ce27a26 0xb4867071a3389e89 0xaabb838f39e3e23d 0x2aaee0e3ce78f88f

def z711 : W := mkw 0x04000c1120098098 0x0100030448026026 0xffc4fcf3e03fe3ff 0xfff13f3cf80ff8ff

def z712 : W := mkw 0x003edafbb0403003 0x000fb6beec100c00 0xff7fffffffc01c00 0x7fdffffffff00700

def z713 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0x3f7fff00ffffde4f 0xcfdfffc03ffff793

def z714 : W := mkw 0xe877f70047bfc460 0xfa1dfdc011eff118 0x3f7fff0007ffc071 0x8fdfffc001fff01c

def z715 : W := mkw 0xe077f70287bfc002 0xf81dfdc0a1eff000 0x3f7fff03c7ffc001 0xcfdfffc0f1fff000

def z716 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x44b860c3c7c73c73 0xd12e1830f1f1cf1c

def z717 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0xffffffb027ffe3cf 0xffffffec09fff8f3

def z718 : W := mkw 0x0000040000098000 0x0000010000026000 0x3f7c9c0007ffc001 0x8fdf270001fff000

def z719 : W := mkw 0x686f17c2c579f462 0xda1bc5f0b15e7d18 0x68c71fc3c038fc72 0x5a31c7f0f00e3f1c

def z720 : W := mkw 0x0026120000000000 0x0009848000000000 0xfd477f4cf8000000 0x7f51dfd33e000000

def z721 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xcf3f00fc07f81f80 0x33cfc03f01fe07e0

def z722 : W := mkw 0x04000c1120098098 0x0100030448026026 0xcbc49cb3003fe3ff 0xb2f1272cc00ff8ff

def z723 : W := mkw 0x5a0021044a044e44 0x1680084112811391 0xfd03634cf804de4e 0x7f40d8d33e013793

def z724 : W := mkw 0xe0492dfbb7bfc003 0xf8124b7eedeff000 0xc00000ffffffc001 0xf000003ffffff000

def z725 : W := mkw 0x043ed6ea9009809b 0x010fb5baa4026026 0x04bb634cd83fe3ff 0x812ed8d3360ff8ff

def z726 : W := mkw 0x040808d3a04030ba 0x01020234e8100c2e 0xc08000b3200023fe 0x7020002cc80008ff

def z727 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xed03634cfe20de0e 0xbb40d8d33f883783

def z728 : W := mkw 0x003edafbb1503103 0x400fb6beec540c40 0xffffffffffd83d83 0xfffffffffff60f60

def z729 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x2f7f7f0007f8c001 0x8bdfdfc001fe3000

def z730 : W := mkw 0x100808fd20403b00 0x0402023f48100ec0 0xc08000ff20003f82 0x7020003fc8000fe0

def z731 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x57b8e0c3c7ff3ff3 0xd5ee3830f1ffcffc

def z732 : W := mkw 0xe076f700039fc000 0x781dbdc000e7f000 0x3f7fff0001dfc001 0x0fdfffc00077f000

def z733 : W := mkw 0x0027000005300000 0xc009c000014c0000 0x3f7f9c0007f80001 0x8fdfe70001fe0000

def z734 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xae7ffffff8000000 0x2b9ffffffe000000

def z735 : W := mkw 0x8810e002c2c63462 0x22043800b0b18d18 0x17b8e003c7c73c73 0xc5ee3800f1f1cf1c

def z736 : W := mkw 0xe877f70047bfc440 0xfa1dfdc011eff110 0xff7fff4cffffdc43 0xffdfffd33ffff710

def z737 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x2a7f9f0001db0001 0x0a9fe7c00076c000

def z738 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x3c7fff0007ffc000 0x0f1fffc001fff000

def z739 : W := mkw 0x8010e00002860000 0x2004380000a18000 0x3f7cfc0007c70001 0x8fdf3f0001f1c000

def z740 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x5738e0c3c7c71c70 0x55ce3830f1f1c71c

def z741 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xefbf03fc3ff83f83 0xbbefc0ff0ffe0fe0

def z742 : W := mkw 0x8836f20042860440 0x220dbc8010a18110 0xff7fff4cffc71c43 0xffdfffd33ff1c710

def z743 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0x367ffffff8000000 0x4d9ffffffe000000

def z744 : W := mkw 0x0010d20000000000 0x0004348000000000 0xfd43ff4cf8000000 0x7f50ffd33e000000

def z745 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x0f7f9c0007ffc001 0x83dfe70001fff000

def z746 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0x3f7fff4ff8000000 0x4fdfffd3fe000000

def z747 : W := mkw 0xfe77f7044fbfcedc 0xff9dfdc113eff3b7 0x3fffff0007ffffff 0x8fffffc001ffffff

def z748 : W := mkw 0x9837e02ec7b60f62 0xe60df80bb1ed83d8 0x9807e03fc03f03f0 0x6601f80ff00fc0fc

def z749 : W := mkw 0x7a6737044f3dce44 0xde99cdc113cf7391 0xff7f7f4cfffcde4f 0xffdfdfd33fff3793

def z750 : W := mkw 0x1027002c05300b00 0xc409c00b014c02c0 0xcf3f007c07f81f83 0xb3cfc01f01fe07e0

def z751 : W := mkw 0x003ed2ea90000003 0x000fb4baa4000000 0xff7fff4cf8000000 0x7fdfffd33e000000

def z752 : W := mkw 0x1011da17b5703b03 0xc4047685ed5c0ec0 0x30c0ff03fff83f83 0xcc303fc0fffe0fe0

def z753 : W := mkw 0x003ed2ea90000003 0x000fb4baa4000000 0x067fff4cd8000000 0x019fffd336000000

def z754 : W := mkw 0x003edafbb1503103 0x400fb6beec540c40 0xfffffffff9f82383 0xfffffffffe7e08e0

def z755 : W := mkw 0xe077d70005bbc000 0xf81df5c0016ef000 0x3b7f9f0001ffc001 0x8edfe7c0007ff000

def z756 : W := mkw 0xa076f600039f8000 0x681dbd8000e7e000 0x3f7cfc0007ffc001 0x8fdf3f0001fff000

def z757 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0x0fbf00fc07f83d81 0x83efc03f01fe0f60

def z758 : W := mkw 0x522f01ec0d707b04 0xd48bc07b035c1ec1 0xcfbf00fc07f8ff8f 0xb3efc03f01fe3fe3

def z759 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xff7ffffff8380380 0x7fdffffffe0e00e0

def z760 : W := mkw 0x8c18ecd3e2cfb4fa 0x23063b34f8b3ed3e 0xac7c7c70e7f8df8c 0x2b1f1f1c39fe37e3

def z761 : W := mkw 0x60673700073dc000 0xd819cdc001cf7000 0x3f7f7f0007fcc001 0x8fdfdfc001ff3000

def z762 : W := mkw 0x5a3ffbfffe244e47 0x968ffeffff891391 0x027c9cb30624de4e 0x809f272cc1893793

def z763 : W := mkw 0x8010e400028f8000 0x2004390000a3e000 0x177cfc0007df0001 0x85df3f0001f7c000

def z764 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0x3f7fff0007ffdc01 0x8fdfffc001fff700

def z765 : W := mkw 0x102f12ec05703b00 0xc40bc4bb015c0ec0 0xefff1ffc07f83f83 0xbbffc7ff01fe0fe0

def z766 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xfffffffff8002003 0xfffffffffe000800

def z767 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0xcbfc9cb001fb2383 0xb2ff272c007ec8e0

def z768 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0xff7fff0007ffc203 0xbfdfffc001fff080

def z769 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xf47bfffff8000000 0x7d1efffffe000000

def z770 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xc67ffffff8000000 0x719ffffffe000000

def z771 : W := mkw 0xe077f30007b64000 0xf81dfcc001ed9000 0x347bff0007c00000 0x0d1effc001f00000

def z772 : W := mkw 0x003edafbb0403003 0x000fb6beec100c00 0xffffffffffc73c73 0xfffffffffff1cf1c

def z773 : W := mkw 0x4a2e21e84b547544 0x528b887a12d51d51 0x32bc63b0f9dce1cd 0x4caf18ec3e773873

def z774 : W := mkw 0x5a0929fffe647e67 0x96824a7fff991f99 0xfd8363fffe24fe7e 0xff60d8ffff893f9f

def z775 : W := mkw 0x04080cd12049b098 0x0102033448126c26 0x77f89cc327c7fc7f 0xddfe2730c9f1ff1f

def z776 : W := mkw 0x003edafbb1503103 0x400fb6beec540c40 0xff7ffffff9c00000 0x7fdffffffe700000

def z777 : W := mkw 0xfa51f7044eafce44 0xbe947dc113abf391 0xff7bff4cffe7de4f 0xffdeffd33ff9f793

def z778 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0x3f7fff4cffffdc4d 0xcfdfffd33ffff713

def z779 : W := mkw 0xa476d600019b8098 0x691db5800066e026 0x02fc9c0001db21b1 0x00bf27000076c86c

def z780 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0xdfbbe0cfc7c73c73 0xf7eef833f1f1cf1c

def z781 : W := mkw 0x8018c0c280c23022 0x20063030a0308c08 0x57b8e0c3c7c33c33 0xd5ee3830f1f0cf0c

def z782 : W := mkw 0xf077f70407bfca00 0xfc1dfdc101eff280 0xfffffffc07ffff83 0xbfffffff01ffffe0

def z783 : W := mkw 0xe051f70006afc000 0xb8147dc001abf000 0x3f7bff0007e7c001 0x8fdeffc001f9f000

def z784 : W := mkw 0xfa4125044ffffe64 0xfe90494113ffff99 0x0080000007fffe7f 0x8020000001ffff9f

def z785 : W := mkw 0x520101040c204a04 0x9480404103081281 0xfd03634cfe20de0e 0xff40d8d33f883783

def z786 : W := mkw 0x0c0808d3e04034fa 0x03020234f8100d3e 0x408000f3c0003df2 0x5020003cf0000f7c

def z787 : W := mkw 0x8818c0c2c0c23462 0x22063030b0308d18 0x47b880c3c7c33c73 0xd1ee2030f1f0cf1c

def z788 : W := mkw 0x000808fbb0403003 0x0002023eec100c00 0xc08000fff8003c02 0x7020003ffe000f00

def z789 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x02b8808307c33c31 0x00ae2020c1f0cf0c

def z790 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x2a7f9f0007ffc001 0x8a9fe7c001fff000

def z791 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0x067fff4cdfdb1c01 0x019fffd337f6c700

def z792 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x2a7c9c0001fbc001 0x0a9f2700007ef000

def z793 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xcfbf00fc07ff3ff3 0xb3efc03f01ffcffc

def z794 : W := mkw 0x88263a3972c63461 0x22098e8e5cb18d18 0xa8c71f3c3fc73c73 0xaa31c7cf0ff1cf1c

def z795 : W := mkw 0x5e012d156e2dcedc 0x97804b455b8b73b7 0x06c7ffffde1b3db1 0x01b1fffff786cf6c

def z796 : W := mkw 0x1027002c05703b00 0xc409c00b015c0ec0 0x8fbf003c07f83f83 0xa3efc00f01fe0fe0

def z797 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x00789c0001c30000 0x001e27000070c000

def z798 : W := mkw 0xfa4125044eafce44 0xbe90494113abf391 0x000000000627de4e 0x800000000189f793

def z799 : W := mkw 0x080808d3f0403463 0x02020234fc100d18 0x408000c3f8003c72 0x50200030fe000f1c

def z800 : W := mkw 0x5e0125044e2dcedc 0x97804941138b73b7 0x00000000063cdfce 0x80000000018f37f3

def z801 : W := mkw 0x5a0129156e244e44 0x96804a455b891391 0xfb449cb32624de4e 0xfed1272cc9893793

def z802 : W := mkw 0x002f00c005703000 0xc00bc030015c0c00 0xcfbf00f007f83f83 0xb3efc03c01fe0fe0

def z803 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xba7fffbff8000000 0x6e9fffeffe000000

def z804 : W := mkw 0x003edafbb1100103 0x400fb6beec440040 0xff7ffffff8180180 0x7fdffffffe060060

def z805 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x57b8e0c3c7e7fe7f 0xd5ee3830f1f9ff9f

def z806 : W := mkw 0xfa77f3044fb64e44 0xfe9dfcc113ed9391 0xff7fff4cffc01c00 0x7fdfffd33ff00700

def z807 : W := mkw 0x522f01ec0d707b04 0xd48bc07b035c1ec1 0xffbf63fcfff8ff8f 0xffefd8ff3ffe3fe3

def z808 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xff7ffffff800024e 0x7fdffffffe000093

def z809 : W := mkw 0x5e0929fd6e647fdc 0x97824a7f5b991ff7 0xfd8363fffe24fffe 0xff60d8ffff893fff

def z810 : W := mkw 0x140808fd20403b98 0x0502023f48100ee6 0xc08000ff00003fb2 0x3020003fc0000fec

def z811 : W := mkw 0x002e00e801503100 0x400b803a00540c40 0xcfbc00f007f83f83 0xb3ef003c01fe0fe0

def z812 : W := mkw 0x100804ec0049bb00 0x0402013b00126ec0 0xfbc49cfc003fff83 0xbef1273f000fffe0

def z813 : W := mkw 0xea50f7004a8fc444 0x3a943dc012a3f111 0x7778ff40ffc7dc4f 0xddde3fd03ff1f713

def z814 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0xbf7fff4cffffde0d 0xafdfffd33ffff783

def z815 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xccbf00fc07f83f82 0x332fc03f01fe0fe0

def z816 : W := mkw 0x0010da13b0000003 0x00043684ec000000 0xb843ff0ff8000000 0x6e10ffc3fe000000

def z817 : W := mkw 0x8036d20000820000 0x200db48000208000 0x3f7fff0001c30001 0x0fdfffc00070c000

def z818 : W := mkw 0xf277f7040fbfca04 0xfc9dfdc103eff281 0x3f7fff0007ffc20d 0x8fdfffc001fff083

def z819 : W := mkw 0x522f01ec0d707b04 0xd48bc07b035c1ec1 0xcfbf03fc1ff83f83 0xb3efc0ff07fe0fe0

def z820 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x1738e043c7c71c71 0xc5ce3810f1f1c71c

def z821 : W := mkw 0xe051f70007bfc000 0xf8147dc001eff000 0x3778ff0007ffc001 0x8dde3fc001fff000

def z822 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xfd83634cfe27fe7f 0xff60d8d33f89ff9f

def z823 : W := mkw 0x6077d7000539c000 0xd81df5c0014e7000 0x3f7fff0007f8c001 0x8fdfffc001fe3000

def z824 : W := mkw 0x8010e400028f8000 0x2004390000a3e000 0x3778fc0007c7c001 0x8dde3f0001f1f000

def z825 : W := mkw 0x0c0828d3e24434fa 0x03020a34f8910d3e 0xfd8060f3e624fffe 0xff60183cf9893fff

def z826 : W := mkw 0xe067250007bfc000 0xf819c94001eff000 0x3f7f9c0007ffc001 0x8fdfe70001fff000

def z827 : W := mkw 0x04000c1120098098 0x0100030448026026 0xffc7ffb3203fe3ff 0xfff1ffecc80ff8ff

def z828 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xfffffffff83f23f3 0xfffffffffe0fc8fc

def z829 : W := mkw 0x000808fbb0403023 0x0002023eec100c08 0xc08000fff8002030 0x7020003ffe00080c

def z830 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0xffbce0f3e7ffffff 0xffef383cf9ffffff

def z831 : W := mkw 0x002e1afbb0000003 0x000b86beec000000 0xfd477ffff8000000 0x7f51dffffe000000

def z832 : W := mkw 0x100900c405703b00 0xc4024031015c0ec0 0xcfbc00f007f83f83 0xb3ef003c01fe0fe0

def z833 : W := mkw 0x8018c0c280c23022 0x20063030a0308c08 0x57b880c307c73c73 0xd5ee2030c1f1cf1c

def z834 : W := mkw 0xf277f7040fbfca04 0xfc9dfdc103eff281 0xff7fff0c3fffc24f 0xffdfffc30ffff093

def z835 : W := mkw 0x00001a1130000001 0x000006844c000000 0xfd437f4cf8000000 0x7f50dfd33e000000

def z836 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x3b7c9c0007ffc001 0x8edf270001fff000

def z837 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0x8abf00bc07f83f83 0xa2afc02f01fe0fe0

def z838 : W := mkw 0x100808ffb0403b03 0x0402023fec100ec0 0xc00000fff8001c00 0x7000003ffe000700

def z839 : W := mkw 0x04000c1120098098 0x0100030448026026 0xfbc79fbf383fe3ff 0xfef1e7efce0ff8ff

def z840 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xcfbf80ff07fb3fb3 0xb3efe03fc1fecfec

def z841 : W := mkw 0x04000c1120098098 0x0100030448026026 0x32c49cb3203fe3ff 0xccb1272cc80ff8ff

def z842 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0xff7fff4c07ffc001 0xbfdfffd301fff000

def z843 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x5fbce0c3c7ff3c73 0xd7ef3830f1ffcf1c

def z844 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xfd7f7f7cf8000000 0x7f5fdfdf3e000000

def z845 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xcd3f007c07f81f82 0xb34fc01f01fe07e0

def z846 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0xffffffcffffffe7f 0xfffffff3ffffff9f

def z847 : W := mkw 0x803edafbb0c23023 0x200fb6beec308c08 0xffffffffffc33c33 0xfffffffffff0cf0c

def z848 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0xbf7fff0cffffc24d 0xefdfffc33ffff093

def z849 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x47b8e0c3c7c33c33 0x91ee3830f1f0cf0c

def z850 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xbf7fff7cf8000000 0x2fdfffdf3e000000

def z851 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xff7ffffffe001c02 0xffdfffffff800700

def z852 : W := mkw 0x043edafbb000009b 0x010fb6beec000026 0xfffffffff824e3fe 0xfffffffffe0938ff

def z853 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x2e7fff0007fbc001 0x0b9fffc001fef000

def z854 : W := mkw 0xa076f600039f8000 0x681dbd8000e7e000 0x127cfc0001df0001 0x049f3f000077c000

def z855 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xffbf63fc07f83f83 0xbfefd8ff01fe0fe0

def z856 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x047bff0007c30000 0x011effc001f0c000

def z857 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xff7ffffff8070070 0x7fdffffffe01c01c

def z858 : W := mkw 0x0018dafbb0000003 0x000636beec000000 0xfd43fffff8000000 0x7f50fffffe000000

def z859 : W := mkw 0x002f00e805703100 0xc00bc03a015c0c40 0x4fbf00f007f83d83 0x93efc03c01fe0f60

def z860 : W := mkw 0x102f12ec15703b01 0xc40bc4bb055c0ec0 0xcfbf03fc1ff83f83 0xb3efc0ff07fe0fe0

def z861 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0xd7b8e0f3c7c73ff3 0xf5ee383cf1f1cffc

def z862 : W := mkw 0x40272500073dc000 0xd009c94001cf7000 0x3f7fff0007ffc001 0x8fdfffc001fff000

def z863 : W := mkw 0xf877f70447bfce40 0xfe1dfdc111eff390 0xff7fff4cc7ffde43 0xffdfffd331fff790

def z864 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x0f7f9c0001db0001 0x03dfe7000076c000

def z865 : W := mkw 0xda37f3044ea64e44 0xb68dfcc113a99391 0xff7fff4cffe7de4f 0xffdfffd33ff9f793

def z866 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xefbf00fc27f8ff8f 0xbbefc03f09fe3fe3

def z867 : W := mkw 0xe077f72807bfc000 0xf81dfdca01eff000 0xbf7fff3c07ffc001 0xafdfffcf01fff000

def z868 : W := mkw 0xf077f72c07bfcb00 0xfc1dfdcb01eff2c0 0x3f7fff0c07ffc001 0x8fdfffc301fff000

def z869 : W := mkw 0x0036d20000000000 0x000db48000000000 0x3f7fff0007c00001 0x8fdfffc001f00000

def z870 : W := mkw 0x726717040d39ca04 0xdc99c5c1034e7281 0xef7f1f4c3ff8de0f 0xbbdfc7d30ffe3783

def z871 : W := mkw 0x003ed2e800000000 0x000fb4ba00000000 0xff7ffffcf8000000 0x7fdfffff3e000000

def z872 : W := mkw 0xba76d604499b8e44 0x6e9db5811266e391 0xc27c9c4cf9db1e4f 0x709f27133e76c793

def z873 : W := mkw 0x5a0121044f344f44 0xd680484113cd13d1 0xfd03634cfe3cdfce 0xff40d8d33f8f37f3

def z874 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xdfbf60fcc7f83f83 0xf7efd83f31fe0fe0

def z875 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xc2bc00fc07f83f83 0xb0af003f01fe0fe0

def z876 : W := mkw 0xc037f30006a64000 0xb00dfcc001a99000 0x3f7fff0007e7c001 0x8fdfffc001f9f000

def z877 : W := mkw 0x74671f3d2539cb98 0xdd19c7cf494e72e6 0xa8471f3c2038c38c 0x2a11c7cf080e30e3

def z878 : W := mkw 0xe051e50007bfc000 0xf814794001eff000 0x3f7cfc0007ffc001 0x8fdf3f0001fff000

def z879 : W := mkw 0x04000c1120098098 0x0100030448026026 0xfbc4ffb3f83fe3ff 0xfef13fecfe0ff8ff

def z880 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xff7ffffff8200202 0xffdffffffe080080

def z881 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xffbf00fc07fcff83 0xbfefc03f01ff3fe0

def z882 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x02fc9c8301db2031 0x00bf2720c076c80c

def z883 : W := mkw 0xf058f7ec02cffb00 0x3c163dfb00b3fec0 0xf0c0fffc0007ff82 0x3c303fff0001ffe0

def z884 : W := mkw 0xe077f30007b64000 0xf81dfcc001ed9000 0x2c7f7f0007c00000 0x0b1fdfc001f00000

def z885 : W := mkw 0xe277f7000fbfc004 0xf89dfdc003eff001 0x3f7fff003fffc00d 0x8fdfffc00ffff003

def z886 : W := mkw 0xa476d600019b8098 0x691db5800066e026 0x02fc9c0001ffe3ff 0x80bf2700007ff8ff

def z887 : W := mkw 0x080808fbf0403463 0x0202023efc100d18 0x408000f3c0003c72 0x5020003cf0000f1c

def z888 : W := mkw 0xe877f70047bfc440 0xfa1dfdc011eff110 0x3f7fff0007ffdc43 0x8fdfffc001fff710

def z889 : W := mkw 0x2066160001198000 0x4819858000466000 0x027c1c0001d80001 0x009f070000760000

def z890 : W := mkw 0xb077d62c05bb8b00 0xec1df58b016ee2c0 0x8a7f9c3c01fb0381 0x229fe70f007ec0e0

def z891 : W := mkw 0xe067370007bfc000 0xf819cdc001eff000 0x2f7f1f0007ffc001 0x8bdfc7c001fff000

def z892 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0x0fbf00b007f83f83 0x83efc02c01fe0fe0

def z893 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0xfffffffcffffffcf 0xffffffff3ffffff3

def z894 : W := mkw 0x0036da3bb0000003 0x000db68eec000000 0x3043ff0ff8000000 0x4c10ffc3fe000000

def z895 : W := mkw 0x8c10fe13f28f84fb 0x23043f84fca3e13e 0x3040ff03f807c07c 0x4c103fc0fe01f01f

def z896 : W := mkw 0xc011e50006afc000 0xb004794001abf000 0x3f7fff0007ffc001 0x8fdfffc001fff000

def z897 : W := mkw 0x0036da3bb0000003 0x000db68eec000000 0xfd47ff7ff8000000 0x7f51ffdffe000000

def z898 : W := mkw 0x8018e0c282c63022 0x20063830a0b18c08 0x57b8e0c307c73c33 0x95ee3830c1f1cf0c

def z899 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x7f7fff4007ffdc03 0x9fdfffd001fff700

def z900 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x247b7f0007c0c000 0x091edfc001f03000

def z901 : W := mkw 0xee50ff116a8fc4dc 0x3b943fc45aa3f137 0x3040ff03f807c07c 0x4c103fc0fe01f01f

def z902 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x47b880c307c73c73 0x91ee2030c1f1cf1c

def z903 : W := mkw 0x000808fbb0000003 0x0002023eec000000 0xff47fffff8000000 0x7fd1fffffe000000

def z904 : W := mkw 0xe877f70047bfc440 0xfa1dfdc011eff110 0x3f7fff40c7ffdc01 0x8fdfffd031fff700

def z905 : W := mkw 0x1027000405300a00 0xc409c001014c0280 0xcfbf00fc07f83f83 0xb3efc03f01fe0fe0

def z906 : W := mkw 0xfa77f3044fb64e44 0xfe9dfcc113ed9391 0xff7fff4cffe4de4e 0xffdfffd33ff93793

def z907 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x3f7fff0307ffc071 0xcfdfffc0c1fff01c

def z908 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x7fb8e0c3c7e7fc73 0xdfee3830f1f9ff1c

def z909 : W := mkw 0x043edafbb000009b 0x010fb6beec000026 0xff7ffffff800038c 0x7fdffffffe0000e3

def z910 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x027c9c0001ffc001 0x809f2700007ff000

def z911 : W := mkw 0xe077f30007b64000 0xf81dfcc001ed9000 0x3f7fff0007e4c000 0x8fdfffc001f93000

def z912 : W := mkw 0x880820c2c2c63462 0x22020830b0b18d18 0x47b800c3c7c73c73 0xd1ee0030f1f1cf1c

def z913 : W := mkw 0xe477f70007bfc098 0xf91dfdc001eff026 0xffffff0027ffe3ff 0xffffffc009fff8ff

def z914 : W := mkw 0x0018c8d3a0000002 0x00063234e8000000 0xff7ffffff8000000 0x7fdffffffe000000

def z915 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xec7f7ffff8000000 0x7b1fdffffe000000

def z916 : W := mkw 0xf077f70407bfcb00 0xfc1dfdc101eff2c0 0x3f7fff0007ffc381 0x8fdfffc001fff0e0

def z917 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0x47bc00f007f83f83 0x91ef003c01fe0fe0

def z918 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0xbf7fff3007ffc381 0xafdfffcc01fff0e0

def z919 : W := mkw 0x706f13ec05707b00 0xdc1bc4fb015c1ec0 0xcfbf03fc07f83f83 0xb3efc0ff01fe0fe0

def z920 : W := mkw 0xf277f72c0fbfcb04 0xfc9dfdcb03eff2c1 0xbf7fff3c3fffc38d 0xafdfffcf0ffff0e3

def z921 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x53b8808307c73c73 0xd4ee2020c1f1cf1c

def z922 : W := mkw 0x080828fbf2443463 0x02020a3efc910d18 0xfd8363fffe043c72 0xff60d8ffff810f1c

def z923 : W := mkw 0xe076f700039fc000 0x781dbdc000e7f000 0x027cff0001db0001 0x009f3fc00076c000

def z924 : W := mkw 0xa076d628019b8100 0x681db58a0066e040 0x027c9c3001db0181 0x009f270c0076c060

def z925 : W := mkw 0x8010c400008b8000 0x200431000022e000 0x3b7c9c0001ffc001 0x8edf2700007ff000

def z926 : W := mkw 0xfa4121044fb64e44 0xfe90484113ed9391 0xfd03634cffe4de4e 0xff40d8d33ff93793

def z927 : W := mkw 0xa076d20001920000 0x681db48000648000 0x3f7fff0001c00000 0x0fdfffc000700000

def z928 : W := mkw 0x00261a3930000001 0x0009868e4c000000 0xb8477f3cf8000000 0x6e11dfcf3e000000

def z929 : W := mkw 0x5a0121044f344e44 0xd680484113cd1391 0xfd03634cfffcde4f 0xff40d8d33fff3793

def z930 : W := mkw 0xca18e1c2cac67466 0x32863870b2b19d19 0x57b8e3c3dfc73c73 0xd5ee38f0f7f1cf1c

def z931 : W := mkw 0x140908fd24603b98 0x8502423f49180ee6 0xfd8300ff2624fffe 0xff60c03fc9893fff

def z932 : W := mkw 0x8810e400428f8440 0x2204390010a3e110 0xff7cfc40e7ffde4f 0xffdf3f1039fff793

def z933 : W := mkw 0xa050f600028f8000 0x28143d8000a3e000 0x1778fc0007c70001 0x85de3f0001f1c000

def z934 : W := mkw 0x080808d3e0403462 0x02020234f8100d18 0xc08000f3e0003c72 0x7020003cf8000f1c

def z935 : W := mkw 0x803edafbb0820003 0x200fb6beec208000 0xff7ffffff9c30001 0x7fdffffffe70c000

def z936 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xff7ffffff8040042 0xffdffffffe010010

def z937 : W := mkw 0xfa77f706cfbfce66 0xfe9dfdc1b3eff399 0xff7fff4fffffde7f 0xffdfffd3fffff79f

def z938 : W := mkw 0xa076f600039f8000 0x681dbd8000e7e000 0x027c9c0007df0001 0x809f270001f7c000

def z939 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0x777bffcff8000000 0x5ddefff3fe000000

def z940 : W := mkw 0x043edafbb000009b 0x010fb6beec000026 0xff7ffffff800007c 0x7fdffffffe00001f

def z941 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0xff7fff0027ffc001 0xffdfffc009fff000

def z942 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xcfbf00fcfff83f83 0xf3efc03f3ffe0fe0

def z943 : W := mkw 0xe077f70287bfc022 0xf81dfdc0a1eff008 0x3f7fff0307ffc031 0x8fdfffc0c1fff00c

def z944 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xffff9cfc07f83f83 0xbfffe73f01fe0fe0

def z945 : W := mkw 0x8036f20002860000 0x200dbc8000a18000 0x177cfc0007c70001 0x85df3f0001f1c000

def z946 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0xffbbe3cfffe7fe7f 0xffeef8f3fff9ff9f

def z947 : W := mkw 0x040808f920403198 0x0102023e48100c66 0x008000b3000021b0 0x0020002cc000086c

def z948 : W := mkw 0x2067160005398000 0xc819c580014e6000 0x0f7f1c0007f80001 0x83dfc70001fe0000

def z949 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0x06bf00fc07f83f83 0x81afc03f01fe0fe0

def z950 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xcfbf00fc07d83d81 0x33efc03f01f60f60

def z951 : W := mkw 0x1027000405703b00 0xc409c001015c0ec0 0xcfbf00b007f83f83 0xb3efc02c01fe0fe0

def z952 : W := mkw 0xf077f70407bfca00 0xfc1dfdc101eff280 0xff7fff4cffffde03 0xffdfffd33ffff780

def z953 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0x347bff4cffc7dc4c 0x4d1effd33ff1f713

def z954 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x3f7fff0007f8c000 0x0fdfffc001fe3000

def z955 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0x247b7f4cf8000000 0x091edfd33e000000

def z956 : W := mkw 0x706f17ec0579fb00 0xdc1bc5fb015e7ec0 0xe8c71ffc0038ff82 0x3a31c7ff000e3fe0

def z957 : W := mkw 0xa077d60005bb8000 0xe81df580016ee000 0x3f7fff0007fb0001 0x8fdfffc001fec000

def z958 : W := mkw 0xf077f70407bfca00 0xfc1dfdc101eff280 0xff7fff4c27ffde4f 0xffdfffd309fff793

def z959 : W := mkw 0x0000081120000000 0x0000020448000000 0xfd43ff4ff8000000 0x7f50ffd3fe000000

def z960 : W := mkw 0x043edefbb159b19b 0x410fb7beec566c66 0x02fc9cb301db21b1 0x00bf272cc076c86c

def z961 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x067fff0007ffc001 0x819fffc001fff000

def z962 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x3b7c9c0001db0001 0x0edf27000076c000

def z963 : W := mkw 0xe477f70007bfc098 0xf91dfdc001eff026 0x3f7fff0007ffc38d 0x8fdfffc001fff0e3

def z964 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x17b8e0c3c7c73c31 0x85ee3830f1f1cf0c

def z965 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x17b8e08307c73c73 0x85ee3820c1f1cf1c

def z966 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x7fffff8007ffe003 0x9fffffe001fff800

def z967 : W := mkw 0xa050d600008b8000 0x281435800022e000 0x02789c0001c30001 0x009e27000070c000

def z968 : W := mkw 0x043edafbb000009b 0x010fb6beec000026 0xfffffffff80021b0 0x7ffffffffe00086c

def z969 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0xff7fff4cffffc24f 0xffdfffd33ffff093

def z970 : W := mkw 0x04080cd12049b098 0x0102033448126c26 0xeffc1cf027f8ff8f 0xbbff073c09fe3fe3

def z971 : W := mkw 0x0037d60005398000 0xc00df580014e6000 0x3f7fff0007ffc001 0x8fdfffc001fff000

def z972 : W := mkw 0xe076f700039fc000 0x781dbdc000e7f000 0x027c9c0001dfc001 0x009f27000077f000

def z973 : W := mkw 0xa07edafbb1920003 0x681fb6beec648000 0xff7ffffff9c00000 0x7fdffffffe700000

def z974 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0xdfbce0f3c7c73c73 0xf7ef383cf1f1cf1c

def z975 : W := mkw 0xe077f30007b64000 0xf81dfcc001ed9000 0x3f7fff0007c70001 0x8fdfffc001f1c000

def z976 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x007c1c0001d80000 0x001f070000760000

def z977 : W := mkw 0xda0121044ea64e44 0xb680484113a99391 0xfd03634cffe7de4f 0xff40d8d33ff9f793

def z978 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0xff7fff4cdfffde03 0xbfdfffd337fff780

def z979 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xfd03634cfe04dc4c 0x7f40d8d33f813713

def z980 : W := mkw 0x0027040005398000 0xc009c100014e6000 0x0f7f9c0007fb0001 0x83dfe70001fec000

def z981 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0x3403634cfe24de4e 0xcd00d8d33f893793

def z982 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0xff7fff4c07ffde4f 0xbfdfffd301fff793

def z983 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xfd07637cfe3cdfce 0xff41d8df3f8f37f3

def z984 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xdfbf80fc07ff3f83 0xb7efe03f01ffcfe0

def z985 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xff3b634cffe4de4f 0xffced8d33ff93793

def z986 : W := mkw 0xe077d70005bbc000 0xf81df5c0016ef000 0x3f7fff0001fbc001 0x0fdfffc0007ef000

def z987 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xff7ffffff820c20c 0x7fdffffffe083083

def z988 : W := mkw 0x8810e002c2860462 0x22043800b0a18118 0x5738e043c7c71c73 0xd5ce3810f1f1c71c

def z989 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xcbbc00b007f83f83 0xb2ef002c01fe0fe0

def z990 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x377bff0007c7c001 0x8ddeffc001f1f000

def z991 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x7f7fff0007ffc043 0xdfdfffc001fff010

def z992 : W := mkw 0x080800c2c0403462 0x02020030b0100d18 0x57b880c3c7c73c73 0xd5ee2030f1f1cf1c

def z993 : W := mkw 0x0036d20000000000 0x000db48000000000 0x3f7fff4cd8000000 0x0fdfffd336000000

def z994 : W := mkw 0xe877f70047bfc440 0xfa1dfdc011eff110 0x3f7fff00c7ffc041 0xcfdfffc031fff010

def z995 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0xffffff8327ffe27f 0xffffffe0c9fff89f

def z996 : W := mkw 0xf077f72c07bfcb00 0xfc1dfdcb01eff2c0 0xffffffbc07ffe383 0xbfffffef01fff8e0

def z997 : W := mkw 0x0036da3bb0000003 0x000db68eec000000 0xbf7fff3ff8000000 0x6fdfffcffe000000

def z998 : W := mkw 0xa077d60005bb8000 0xe81df580016ee000 0x3f7f9c0007ffc001 0x8fdfe70001fff000

def z999 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x57b8e0c3c7c33c31 0x55ee3830f1f0cf0c

def z1000 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x7f7fff40c7ffc001 0xdfdfffd031fff000

def z1001 : W := mkw 0x00261a3930000001 0x0009868e4c000000 0xff47fffff8000000 0x7fd1fffffe000000

def z1002 : W := mkw 0xe050f700028fc000 0x38143dc000a3f000 0x3278ff0001c7c001 0x0c9e3fc00071f000

def z1003 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x3f7fff0007db0001 0x0fdfffc001f6c000

def z1004 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x54b8e0c3c7c73c72 0x552e3830f1f1cf1c

def z1005 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xfffffffff83ce3cf 0xfffffffffe0f38f3

def z1006 : W := mkw 0x080804c2c049b462 0x02020130b0126d18 0x7bc49cc3c03ffc73 0xdef12730f00fff1c

def z1007 : W := mkw 0x0036da3930000001 0x000db68e4c000000 0xff7fff7cf8000000 0x7fdfffdf3e000000

def z1008 : W := mkw 0xfa4125044fffff44 0xfe90494113ffffd1 0x0080000007ffffcf 0x8020000001fffff3

def z1009 : W := mkw 0xe877f70047bfc440 0xfa1dfdc011eff110 0x7fffffc3c7fffc73 0xdffffff0f1ffff1c

def z1010 : W := mkw 0x00261a3930000001 0x0009868e4c000000 0xac477f7cf8000000 0x2b11dfdf3e000000

def z1011 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x047f7f0007d80000 0x011fdfc001f60000

def z1012 : W := mkw 0x1001000404200a00 0x8400400101080280 0xfd03634cfe24de4e 0xff40d8d33f893793

def z1013 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0x8ebf00fc07f83f81 0x23afc03f01fe0fe0

def z1014 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xf803634cf824de4e 0x7e00d8d33e093793

def z1015 : W := mkw 0x0c0808fbf04034fb 0x0302023efc100d3e 0xc08000fff8003ffe 0x7020003ffe000fff

def z1016 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x0b7c9c0001fb0001 0x82df2700007ec000

def z1017 : W := mkw 0xe050f700028fc000 0x38143dc000a3f000 0x3478ff0007c7c000 0x0d1e3fc001f1f000

def z1018 : W := mkw 0x0427081125300098 0xc109c204494c0026 0xcfbf00b327f823ff 0xf3efc02cc9fe08ff

def z1019 : W := mkw 0x880820c042c63460 0x2202083010b18d18 0x57b880c307c73c73 0xd5ee2030c1f1cf1c

def z1020 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xff07634cfe3cde4f 0xffc1d8d33f8f3793

def z1021 : W := mkw 0x0026040001198000 0x4009810000466000 0x027c9c0001db0001 0x009f27000076c000

def z1022 : W := mkw 0x8a18e0c2cac63466 0x22863830b2b18d19 0x57b8e0c3ffc73c7f 0xd5ee3830fff1cf1f

def z1023 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0xffffffb307ffe3f3 0xffffffecc1fff8fc

def z1024 : W := mkw 0x002e00e801503100 0x400b803a00540c40 0x02bc00b007d83d83 0x80af002c01f60f60

def z1025 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xff7ffffff804c04c 0x7fdffffffe013013

def z1026 : W := mkw 0x003edafbb0403003 0x000fb6beec100c00 0xfffffffff8003c02 0x7ffffffffe000f00

def z1027 : W := mkw 0xf277f7040fbfca04 0xfc9dfdc103eff281 0x3f7fff0c1fffc001 0x8fdfffc307fff000

def z1028 : W := mkw 0x8810e002c2860462 0x22043800b0a18118 0xdb84e0b3c03f23f3 0xf6e1382cf00fc8fc

def z1029 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x7fbbe3c3c7c73c73 0xdfeef8f0f1f1cf1c

def z1030 : W := mkw 0xe858f3c2c2c67462 0x3a163cf0b0b19d18 0x57b8e3c3c7c73c73 0xd5ee38f0f1f1cf1c

def z1031 : W := mkw 0xe050f700028fc000 0x38143dc000a3f000 0x3f7cff0007ffc001 0x8fdf3fc001fff000

def z1032 : W := mkw 0x4037f30007344000 0xd00dfcc001cd1000 0x3f7fff0007fcc001 0x8fdfffc001ff3000

def z1033 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0xbf7fff0027ffc20d 0xafdfffc009fff083

def z1034 : W := mkw 0x522f01ec0d707b04 0xd48bc07b035c1ec1 0xffbf03fc3ffcffcf 0xffefc0ff0fff3ff3

def z1035 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xfffffffff827e27f 0xfffffffffe09f89f

def z1036 : W := mkw 0x502f01ec05707b00 0xd40bc07b015c1ec0 0xefbf03fc07f8ff83 0xbbefc0ff01fe3fe0

def z1037 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x327cff0007ffc001 0x8c9f3fc001fff000

def z1038 : W := mkw 0x100808ffb0403b03 0x0402023fec100ec0 0xc08000ff00003f82 0x3020003fc0000fe0

def z1039 : W := mkw 0x003edafbb0403003 0x000fb6beec100c00 0xfffffffffff83f83 0xfffffffffffe0fe0

def z1040 : W := mkw 0xe477fb1127b64098 0xf91dfec449ed9026 0xc4bb63b327c023fe 0x712ed8ecc9f008ff

def z1041 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0x027c9c0007ffde4f 0x809f270001fff793

def z1042 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xff03e3cffe24de4e 0xffc0f8f3ff893793

def z1043 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xfd83634cfe3cffcf 0xff60d8d33f8f3ff3

def z1044 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x137c9c0001df0001 0x84df27000077c000

def z1045 : W := mkw 0x040808d3a04030ba 0x01020234e8100c2e 0x008000b3000021b0 0x0020002cc000086c

def z1046 : W := mkw 0x100800ec00403b00 0x0402003b00100ec0 0xcfbc00fc07f83f83 0xb3ef003f01fe0fe0

def z1047 : W := mkw 0xe077d70005bbc000 0xf81df5c0016ef000 0x2f7f9f0007fbc001 0x8bdfe7c001fef000

def z1048 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0xff7fff0027ffde4f 0xffdfffc009fff793

def z1049 : W := mkw 0x8018e0c002c63000 0x2006383000b18c00 0x57b8e0c307c73c73 0xd5ee3830c1f1cf1c

def z1050 : W := mkw 0x0036da13b0000003 0x000db684ec000000 0xff7fff4ff8000000 0x7fdfffd3fe000000

def z1051 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x3fffff0007ffe383 0x8fffffc001fff8e0

def z1052 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x42b880c3c7c73c73 0xd0ae2030f1f1cf1c

def z1053 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x067fff0001db0001 0x019fffc00076c000

def z1054 : W := mkw 0x003ed2ea90000003 0x000fb4baa4000000 0x347bff4cd8000000 0x0d1effd336000000

def z1055 : W := mkw 0xe477f70007bfc098 0xf91dfdc001eff026 0x7fffff8307ffe3ff 0xdfffffe0c1fff8ff

def z1056 : W := mkw 0x8037e40007bf8000 0xe00df90001efe000 0x3f7ffc0007ffc001 0x8fdfff0001fff000

def z1057 : W := mkw 0xa076d20001920000 0x681db48000648000 0x027c9c0001c00000 0x009f270000700000

def z1058 : W := mkw 0x002e08f920000000 0x000b823e48000000 0xff7ffffff8000000 0x7fdffffffe000000

def z1059 : W := mkw 0xea77f7004fbfc444 0xfa9dfdc013eff111 0xff7fff00ffffc24f 0xffdfffc03ffff093

def z1060 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x77b8e3c3ffc73c73 0xddee38f0fff1cf1c

def z1061 : W := mkw 0x76671f152d39ca9c 0xdd99c7c54b4e72a7 0xa8471f3c3838c38c 0x2a11c7cf0e0e30e3

def z1062 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xbc7fff7ff8000000 0x6f1fffdffe000000

def z1063 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xff03e34cfe27de4f 0xffc0f8d33f89f793

def z1064 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0xffb8e0c3e7c73c73 0xffee3830f9f1cf1c

def z1065 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xcfbf63fcdff83f83 0xb3efd8ff37fe0fe0

def z1066 : W := mkw 0x5a0125044e2dce44 0x96804941138b7391 0x00000000063fde4f 0x80000000018ff793

def z1067 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0xbf7fff0c3fffc001 0xafdfffc30ffff000

def z1068 : W := mkw 0x080820c042443440 0x0202083010910d10 0x57b8e0c3c7c73c73 0xd5ee3830f1f1cf1c

def z1069 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x3fffffb007ffe181 0x8fffffec01fff860

def z1070 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xcfbf00fc27f83fcf 0xf3efc03f09fe0ff3

def z1071 : W := mkw 0x003edafbb1100003 0x400fb6beec440000 0xff7ffffff9d80001 0x7fdffffffe760000

def z1072 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x347bff0007ffc001 0x8d1effc001fff000

def z1073 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xff7ffffff824c000 0xffdffffffe093000

def z1074 : W := mkw 0xec50ff13e28fc4fa 0x3b143fc4f8a3f13e 0x3040ff03e007c07c 0x4c103fc0f801f01f

def z1075 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0x047bff4fd8000000 0x011effd3f6000000

def z1076 : W := mkw 0x003ed2c280000002 0x000fb4b0a0000000 0xff7fffcff8000000 0x7fdffff3fe000000

def z1077 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x3f7fff0007ffc24f 0x8fdfffc001fff093

def z1078 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x7f7fff8307ffc001 0xdfdfffe0c1fff000

def z1079 : W := mkw 0xfe77f7044fbfcedc 0xff9dfdc113eff3b7 0xffffff4cffffffff 0xffffffd33fffffff

def z1080 : W := mkw 0x0036da3bb0000003 0x000db68eec000000 0xfb47ffbff8000000 0x7ed1ffeffe000000

def z1081 : W := mkw 0x0000000000000000 0x0000000000000000 0xff47ff4cf8000000 0x7fd1ffd33e000000

def z1082 : W := mkw 0xf077f72c07bfcb00 0xfc1dfdcb01eff2c0 0xff7fff7c07ffdf83 0xbfdfffdf01fff7e0

def z1083 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xdfbf00fc07fc3fc3 0xf7efc03f01ff0ff0

def z1084 : W := mkw 0x0010da13b0000003 0x00043684ec000000 0x3443ff4ff8000000 0x4d10ffd3fe000000

def z1085 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xff7ffffff8070001 0xffdffffffe01c000

def z1086 : W := mkw 0x04000c1120098098 0x0100030448026026 0x3bc49cb3003fe3ff 0x8ef1272cc00ff8ff

def z1087 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0xfb7c9c0021ffc24f 0xfedf2700087ff093

def z1088 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x0438e043c7c31c30 0x010e3810f1f0c70c

def z1089 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x06b8e0c3c7c73c73 0x81ae3830f1f1cf1c

def z1090 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x177cfc0001db0001 0x05df3f000076c000

def z1091 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x177fff0007df0001 0x85dfffc001f7c000

def z1092 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xec03634cfe20de4e 0x7b00d8d33f883793

def z1093 : W := mkw 0x5e0929d7ee647efe 0x97824a75fb991fbf 0xfd8363fffe24fffe 0xff60d8ffff893fff

def z1094 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0x2403634cfe00dc0c 0x0900d8d33f803703

def z1095 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0xfd7bff4cffe7de4e 0xff5effd33ff9f793

def z1096 : W := mkw 0x0036da3bb0000003 0x000db68eec000000 0xa8477f3cf8000000 0x2a11dfcf3e000000

def z1097 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xc6bf00fc07d83f83 0x31afc03f01f60fe0

def z1098 : W := mkw 0x0027040005398000 0xc009c100014e6000 0x2f7f1c0007f8c001 0x8bdfc70001fe3000

def z1099 : W := mkw 0x8818e0eac2c63462 0x2206383ab0b18d18 0xd7b8e0ffc7c73c73 0xf5ee383ff1f1cf1c

def z1100 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xff7fffffffc00001 0xffdffffffff00000

def z1101 : W := mkw 0x043edafbb000009b 0x010fb6beec000026 0xfffffffff83823ff 0xfffffffffe0e08ff

def z1102 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x3d7bff0007e7c000 0x8f5effc001f9f000

def z1103 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0x02bc00b007d83d81 0x00af002c01f60f60

def z1104 : W := mkw 0x8037f20007b60000 0xe00dfc8001ed8000 0x3f7fff0007ff0001 0x8fdfffc001ffc000

def z1105 : W := mkw 0x002e00e801503100 0x400b803a00540c40 0xcfbf00fc07d83d83 0xb3efc03f01f60f60

def z1106 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xff87e3fffe3fffff 0xffe1f8ffff8fffff

def z1107 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0xff7fff4cffffdc01 0xffdfffd33ffff700

def z1108 : W := mkw 0x122f00ec0d703b04 0xc48bc03b035c0ec1 0xcfbf00fc3ff83f8f 0xb3efc03f0ffe0fe3

def z1109 : W := mkw 0xe077f30007b64000 0xf81dfcc001ed9000 0x067fff0007c00000 0x019fffc001f00000

def z1110 : W := mkw 0x000800c000403000 0x0002003000100c00 0x47bc00f007d83d83 0x91ef003c01f60f60

def z1111 : W := mkw 0x8036f20002860000 0x200dbc8000a18000 0x3f7fff0007c00000 0x0fdfffc001f00000

def z1112 : W := mkw 0xe477f70007bfc098 0xf91dfdc001eff026 0x3f7fff0007ffc07d 0x8fdfffc001fff01f

def z1113 : W := mkw 0x5a0101044c204e44 0x9680404113081391 0xfd03634cf820de4e 0x7f40d8d33e083793

def z1114 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xff0763fcfe24de4e 0xffc1d8ff3f893793

def z1115 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0x7f7fff40c7ffde4f 0xdfdfffd031fff793

def z1116 : W := mkw 0x002e1af930000001 0x000b86be4c000000 0xff7f7ffcf8000000 0x7fdfdfff3e000000

def z1117 : W := mkw 0x140808ffb0403b9b 0x0502023fec100ee6 0xc08000fff8003ffe 0x7020003ffe000fff

def z1118 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xcfbf00ff07f83ff3 0xf3efc03fc1fe0ffc

def z1119 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xdfbf80ff07f83f83 0xf7efe03fc1fe0fe0

def z1120 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0x8cbf007c07f83f83 0xa32fc01f01fe0fe0

def z1121 : W := mkw 0xea77f7004fbfc444 0xfa9dfdc013eff111 0xff7fff4cffffc04d 0xffdfffd33ffff013

def z1122 : W := mkw 0x4a0021004a044444 0x1280084012811111 0xfd03634cfe04dc4e 0xff40d8d33f813713

def z1123 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0xac7f7f4cfff8de0c 0x2b1fdfd33ffe3783

def z1124 : W := mkw 0x803edafbb0c23023 0x200fb6beec308c08 0xff7ffffff9c00000 0x7fdffffffe700000

def z1125 : W := mkw 0x04000c1120098098 0x0100030448026026 0x53c49cb3003fe3ff 0xd4f1272cc00ff8ff

def z1126 : W := mkw 0xe077d70005bbc000 0xf81df5c0016ef000 0x027f9f0001db0001 0x009fe7c00076c000

def z1127 : W := mkw 0x000808fbb0403103 0x0002023eec100c40 0xc08000fff8002180 0x7020003ffe000860

def z1128 : W := mkw 0x14270c3d25398b98 0xc509c30f494e62e6 0x88471c3c00380380 0x2211c70f000e00e0

def z1129 : W := mkw 0xa076f600039f8000 0x681dbd8000e7e000 0x067cfc0007db0001 0x019f3f0001f6c000

def z1130 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x46b8e0c3c7c33c73 0x51ae3830f1f0cf1c

def z1131 : W := mkw 0xce10ed13ea8fc4fe 0x33843b44faa3f13f 0x3040ff03f807c07c 0x4c103fc0fe01f01f

def z1132 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0x043f007c07d81d80 0x010fc01f01f60760

def z1133 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x3f7fff4cdfffc001 0x8fdfffd337fff000

def z1134 : W := mkw 0x8810e00042c63460 0x2204380010b18d18 0x57b8e08307c73c73 0xd5ee3820c1f1cf1c

def z1135 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0x047f7f7cd8000000 0x011fdfdf36000000

def z1136 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xef7f7ffcf8000000 0x3bdfdfff3e000000

def z1137 : W := mkw 0x0800200042040440 0x0200080010810110 0xfd03634cfe24de4e 0xff40d8d33f893793

def z1138 : W := mkw 0x843edefbb0cbb0bb 0x210fb7beec32ec2e 0x02fc9cb301db21b1 0x00bf272cc076c86c

def z1139 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x327cff0001db0001 0x0c9f3fc00076c000

def z1140 : W := mkw 0x606717000539c000 0xd819c5c0014e7000 0x2a7f1f0001f8c001 0x0a9fc7c0007e3000

def z1141 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x57bce0f3c7df3df3 0xd5ef383cf1f7cf7c

def z1142 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xfd8363fcfe24ffce 0xff60d8ff3f893ff3

def z1143 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0xd7b8e0c3e7c73e7f 0xf5ee3830f9f1cf9f

def z1144 : W := mkw 0x1a00000448000e44 0x0680000112000391 0xfd03634cf824de4e 0xff40d8d33e093793

def z1145 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x177cfc0007ffc001 0x85df3f0001fff000

def z1146 : W := mkw 0x1e0808fd68403fdc 0x0782023f5a100ff7 0xc08000fff8003ffe 0x7020003ffe000fff

def z1147 : W := mkw 0x100900c404603a00 0x8402403101180e80 0xcfbf00fc07f83f83 0xb3efc03f01fe0fe0

def z1148 : W := mkw 0x8010c400008b8000 0x200431000022e000 0x027c9c0001db0001 0x009f27000076c000

def z1149 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x7ffcfcc3c7c73c73 0xdfff3f30f1f1cf1c

def z1150 : W := mkw 0xa077d60005bb8000 0xe81df580016ee000 0x027c9c0007fb0001 0x809f270001fec000

def z1151 : W := mkw 0x606717000539c000 0xd819c5c0014e7000 0x2c7f1f0007f8c000 0x0b1fc7c001fe3000

def z1152 : W := mkw 0x002e00e801503100 0x400b803a00540c40 0x06bc00f007d83d81 0x01af003c01f60f60

def z1153 : W := mkw 0x803edafbb0820023 0x200fb6beec208008 0xff7ffffff8030030 0x7fdffffffe00c00c

def z1154 : W := mkw 0x043edafbb000009b 0x010fb6beec000026 0xfffffffff80723ff 0xfffffffffe01c8ff

def z1155 : W := mkw 0xe076f700039fc000 0x781dbdc000e7f000 0x3b7cff0001ffc001 0x8edf3fc0007ff000

def z1156 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x53fc9c8301df2073 0xd4ff2720c077c81c

def z1157 : W := mkw 0x04000c1120098098 0x0100030448026026 0xfffc9cb327ffe3ff 0xffff272cc9fff8ff

def z1158 : W := mkw 0x102e00ec01503b00 0x440b803b00540ec0 0xc7bc00fc07d83f83 0xb1ef003f01f60fe0

def z1159 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xff7ffffff8380001 0xffdffffffe0e0000

def z1160 : W := mkw 0x1027040405398a00 0xc409c101014e6280 0xff7f9c4c27ffde4f 0xffdfe71309fff793

def z1161 : W := mkw 0xe877f70047bfc440 0xfa1dfdc011eff110 0xff7fff40e7ffde4f 0xffdfffd039fff793

def z1162 : W := mkw 0x0000081120000000 0x0000020448000000 0xfd477f7cf8000000 0x7f51dfdf3e000000

def z1163 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xf847fffff8000000 0x7e11fffffe000000

def z1164 : W := mkw 0x003edafbb0403103 0x000fb6beec100c40 0xfffffffff8002180 0x7ffffffffe000860

def z1165 : W := mkw 0x003edafbb0403023 0x000fb6beec100c08 0xfffffffff8002030 0x7ffffffffe00080c

def z1166 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x2c7f7f0007ffc001 0x8b1fdfc001fff000

def z1167 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xfffffffff8002382 0x7ffffffffe0008e0

def z1168 : W := mkw 0xea77f7004fbfc444 0xfa9dfdc013eff111 0x7f7fff40ffffdc4f 0xdfdfffd03ffff713

def z1169 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xf403634cfe04de4e 0x7d00d8d33f813793

def z1170 : W := mkw 0xe877f702c7bfc462 0xfa1dfdc0b1eff118 0x3f7fff00c7ffc001 0x8fdfffc031fff000

def z1171 : W := mkw 0xca18e1c2cac67466 0x32863870b2b19d19 0x57b8e0c3c7c7fc7f 0xd5ee3830f1f1ff1f

def z1172 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0xdfb8e0c3c7e73e73 0xf7ee3830f1f9cf9c

def z1173 : W := mkw 0x1c0808ffe0403ffa 0x0702023ff8100ffe 0xc08000ffe0003ffe 0x7020003ff8000fff

def z1174 : W := mkw 0xe076f700028fc000 0x381dbdc000a3f000 0x3f7fff0007c7c001 0x8fdfffc001f1f000

def z1175 : W := mkw 0x003ed2ea90000003 0x000fb4baa4000000 0x2c7f7f4cd8000000 0x0b1fdfd336000000

def z1176 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x3a7fff0001ffc001 0x0e9fffc0007ff000

def z1177 : W := mkw 0xf077f70407bfca00 0xfc1dfdc101eff280 0xbf7fff0c07ffc201 0xafdfffc301fff080

def z1178 : W := mkw 0xa876f602c39f8462 0x6a1dbd80b0e7e118 0x127cfc03c1df0071 0x449f3f00f077c01c

def z1179 : W := mkw 0x000808fbb0403103 0x0002023eec100c40 0x008000b300002180 0x0020002cc0000860

def z1180 : W := mkw 0xe077d70005bbc000 0xf81df5c0016ef000 0x027c9c0001fbc001 0x009f2700007ef000

def z1181 : W := mkw 0x000808fbb0403023 0x0002023eec100c08 0x008000b300002030 0x0020002cc000080c

def z1182 : W := mkw 0x8018c0c280c23022 0x20063030a0308c08 0x06b880c307c33c31 0x01ae2030c1f0cf0c

def z1183 : W := mkw 0x04000c1120098098 0x0100030448026026 0xfbc49cfff83fe3ff 0xfef1273ffe0ff8ff

def z1184 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x327c9c0001dfc001 0x0c9f27000077f000

def z1185 : W := mkw 0xea76f7004b9fc444 0x7a9dbdc012e7f111 0x327cff00f9dfc04d 0x4c9f3fc03e77f013

def z1186 : W := mkw 0x0037d20005300000 0xc00df480014c0000 0x0f7f9c0007f80001 0x83dfe70001fe0000

def z1187 : W := mkw 0x0018dad3b0000003 0x000636b4ec000000 0xff7bffcff8000000 0x7fdefff3fe000000

def z1188 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0xbf7fff0c3fffde4f 0xafdfffc30ffff793

def z1189 : W := mkw 0xa077d60005bb8000 0xe81df580016ee000 0x067f9c0007db0001 0x019fe70001f6c000

def z1190 : W := mkw 0x0027120005300000 0xc009c480014c0000 0x2f7f1f0007f80001 0x8bdfc7c001fe0000

def z1191 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xff8363ccfe24fe4f 0xffe0d8f33f893f93

def z1192 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0x8f3f007c07f81f81 0xa3cfc01f01fe07e0

def z1193 : W := mkw 0x0400040000098098 0x0100010000026026 0xfd83634cf83fe3ff 0xff60d8d33e0ff8ff

def z1194 : W := mkw 0x0018c0c280403002 0x00063030a0100c00 0x57b8e0c3c7c73c73 0xd5ee3830f1f1cf1c

def z1195 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x5538e043c7c71c72 0xd54e3810f1f1c71c

def z1196 : W := mkw 0xfa77f72c4fbfcf44 0xfe9dfdcb13eff3d1 0xff7fff7cffffdfcf 0xffdfffdf3ffff7f3

def z1197 : W := mkw 0x56270d3d2d39cb9c 0xd589c34f4b4e72e7 0xa8471f3c3838c38c 0x2a11c7cf0e0e30e3

def z1198 : W := mkw 0xe077f72807bfc100 0xf81dfdca01eff040 0x3f7fff3007ffc181 0x8fdfffcc01fff060

def z1199 : W := mkw 0xf277f7040fbfca04 0xfc9dfdc103eff281 0xff7fff4c3fffde0f 0xbfdfffd30ffff783

def z1200 : W := mkw 0xea77f702cfbfc466 0xfa9dfdc0b3eff119 0x3f7fff03ffffc07d 0xcfdfffc0fffff01f

def z1201 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x027c9c0007db0001 0x009f270001f6c000

def z1202 : W := mkw 0x1a0808fff8403e67 0x0682023ffe100f99 0xc08000fff8003e7e 0x7020003ffe000f9f

def z1203 : W := mkw 0x5e0125044e2dcedc 0x97804941138b73b7 0x000000000627de7e 0x800000000189f79f

def z1204 : W := mkw 0xe076f700039fc000 0x781dbdc000e7f000 0x377cff0007dfc001 0x8ddf3fc001f7f000

def z1205 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xffbf80ff27ffffff 0xffefe03fc9ffffff

def z1206 : W := mkw 0x102f00ee95703b03 0xc40bc03ba55c0ec0 0xcfbf00fcdff83f83 0xb3efc03f37fe0fe0

def z1207 : W := mkw 0x1a0808fff8403f47 0x0682023ffe100fd1 0xc08000fff8003fce 0x7020003ffe000ff3

def z1208 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0x3d03634cfe24dc4c 0xcf40d8d33f893713

def z1209 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x3fffff0007ffe073 0x8fffffc001fff81c

def z1210 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x3f7fff00ffffc001 0xcfdfffc03ffff000

def z1211 : W := mkw 0x8018c0c280c23022 0x20063030a0308c08 0x02b8808307c33c33 0x80ae2020c1f0cf0c

def z1212 : W := mkw 0xca18e1c2cac67466 0x32863870b2b19d19 0xffb8e3c3ffe7fe7f 0xffee38f0fff9ff9f

def z1213 : W := mkw 0x8410e81122860098 0x21043a0448a18026 0xd7b8e0b327c723ff 0xf5ee382cc9f1c8ff

def z1214 : W := mkw 0xe877f702c7bfc462 0xfa1dfdc0b1eff118 0x7f7fff43c7ffdc73 0xdfdfffd0f1fff71c

def z1215 : W := mkw 0xc818e1c2c2c67462 0x32063870b0b19d18 0x77b8e3c3c7c7fc73 0xddee38f0f1f1ff1c

def z1216 : W := mkw 0x102f00ee85703b22 0xc40bc03ba15c0ec8 0xcfbf00ff07f83fb3 0xb3efc03fc1fe0fec

def z1217 : W := mkw 0x04000c1120098098 0x0100030448026026 0xaac49cb3203fe3ff 0xaab1272cc80ff8ff

def z1218 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xbc03634cfe24de4c 0x6f00d8d33f893793

def z1219 : W := mkw 0xf277d7040dbbca04 0xfc9df5c1036ef281 0xaa7f9f0c39fbc20d 0x2a9fe7c30e7ef083

def z1220 : W := mkw 0x7a4125044f3dce44 0xde90494113cf7391 0x00000000063cde4e 0x80000000018f3793

def z1221 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xc403634cfe24de4e 0xf100d8d33f893793

def z1222 : W := mkw 0xf077f70407bfca00 0xfc1dfdc101eff280 0x3f7fff0007ffde03 0x8fdfffc001fff780

def z1223 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x3f7fff0027ffc04d 0xcfdfffc009fff013

def z1224 : W := mkw 0x080808fbf0403463 0x0202023efc100d18 0xc00000fff8001c00 0x7000003ffe000700

def z1225 : W := mkw 0x002e00e800403000 0x000b803a00100c00 0xcfbf00fc07f83f83 0xb3efc03f01fe0fe0

def z1226 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x14b8e043c7c73c73 0xc52e3810f1f1cf1c

def z1227 : W := mkw 0xe077f72817bfc001 0xf81dfdca05eff000 0x3f7fff0c1fffc001 0x8fdfffc307fff000

def z1228 : W := mkw 0xe477f70007bfc098 0xf91dfdc001eff026 0xffffffb007ffe3ff 0xbfffffec01fff8ff

def z1229 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x02fc9cb001db2181 0x00bf272c0076c860

def z1230 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xcfbf00fc07fcffcf 0xb3efc03f01ff3ff3

def z1231 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x16b8e0c3c7c73c71 0x45ae3830f1f1cf1c

def z1232 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x367fff0007dfc001 0x0d9fffc001f7f000

def z1233 : W := mkw 0x040808f920403198 0x0102023e48100c66 0xc08000b3200023fe 0x7020002cc80008ff

def z1234 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xfd7bff4ff8000000 0x7f5effd3fe000000

def z1235 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x57bbe3cfdfc73c73 0xd5eef8f3f7f1cf1c

def z1236 : W := mkw 0x040808d120403098 0x0102023448100c26 0xc08000f320003ffe 0x7020003cc8000fff

def z1237 : W := mkw 0x0036d20001100000 0x400db48000440000 0x027c9c0001d80001 0x009f270000760000

def z1238 : W := mkw 0x100808fd30403b01 0x0402023f4c100ec0 0xc08000fc38003f82 0x3020003f0e000fe0

def z1239 : W := mkw 0x14271e3d35398b99 0xc509c78f4d4e62e6 0xa8471f3c3838c38c 0x2a11c7cf0e0e30e3

def z1240 : W := mkw 0xea77f7004fbfc444 0xfa9dfdc013eff111 0x3f7fff00dfffc001 0x8fdfffc037fff000

def z1241 : W := mkw 0xa076d602819b8022 0x681db580a066e008 0x027c9c0301db0031 0x009f2700c076c00c

def z1242 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xc4bb00fc07f83f83 0xb12ec03f01fe0fe0

def z1243 : W := mkw 0xe477f70007bfc098 0xf91dfdc001eff026 0x3fffff0007ffe1b1 0x8fffffc001fff86c

def z1244 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0x3f7fffffd8000000 0x0fdffffff6000000

def z1245 : W := mkw 0xe076d700019bc000 0x781db5c00066f000 0x227c9f0001dbc001 0x089f27c00076f000

def z1246 : W := mkw 0x803edafbb1d23123 0x600fb6beec748c48 0xfffffffff9db21b1 0x7ffffffffe76c86c

def z1247 : W := mkw 0xea77f7004fbfc444 0xfa9dfdc013eff111 0x3f7fff0007ffc04d 0x8fdfffc001fff013

def z1248 : W := mkw 0x5a2725044f3dce44 0xd689c94113cf7391 0xff7fff4cffffde4f 0xffdfffd33ffff793

def z1249 : W := mkw 0x8c10ec13e28f84fa 0x23043b04f8a3e13e 0x1040fc03c0070070 0x44103f00f001c01c

def z1250 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0xfd7f7f4cfffcde4e 0xff5fdfd33fff3793

def z1251 : W := mkw 0xe077f30007b64000 0xf81dfcc001ed9000 0x3f7fff0007f80001 0x8fdfffc001fe0000

def z1252 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xfd03634cfe20de0c 0x7f40d8d33f883783

def z1253 : W := mkw 0x5a0929fffe647f47 0x96824a7fff991fd1 0xfd8363fffe24ffce 0xff60d8ffff893ff3

def z1254 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xff47ff4cfe24de4e 0xffd1ffd33f893793

def z1255 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x3d7f7f0007fcc000 0x8f5fdfc001ff3000

def z1256 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0xff7fffb007ffc001 0xbfdfffec01fff000

def z1257 : W := mkw 0x003ed2ea90000003 0x000fb4baa4000000 0xff7ffffcd8000000 0x3fdfffff36000000

def z1258 : W := mkw 0x8810e00042860440 0x2204380010a18110 0x57b8e0c3c7c73c73 0xd5ee3830f1f1cf1c

def z1259 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0x3f7fff4cdfffde4f 0x8fdfffd337fff793

def z1260 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x3f7fff0007c7c000 0x0fdfffc001f1f000

def z1261 : W := mkw 0x140808fd20403b98 0x0502023f48100ee6 0xc08000fc20003f8e 0x3020003f08000fe3

def z1262 : W := mkw 0x04000c1120098098 0x0100030448026026 0xc2c49cb3203fe3ff 0xf0b1272cc80ff8ff

def z1263 : W := mkw 0x000800c000403000 0x0002003000100c00 0x47b880c307c33c33 0x91ee2030c1f0cf0c

def z1264 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xfd8363cffe24fe7e 0xff60d8f3ff893f9f

def z1265 : W := mkw 0x04000c1120098098 0x0100030448026026 0xbac49cb3203fe3fd 0x6eb1272cc80ff8ff

def z1266 : W := mkw 0xa077f60007bf8000 0xe81dfd8001efe000 0x1f7ffc0007ff0001 0x87dfff0001ffc000

def z1267 : W := mkw 0x606717000539c000 0xd819c5c0014e7000 0x3f7f9f0007ffc001 0x8fdfe7c001fff000

def z1268 : W := mkw 0xe858f7c2c2cff462 0x3a163df0b0b3fd18 0x70c0ffc3c007fc72 0x5c303ff0f001ff1c

def z1269 : W := mkw 0xe077f70297bfc003 0xf81dfdc0a5eff000 0x3f7fff00dfffc001 0x8fdfffc037fff000

def z1270 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x12b8e083c7c73c73 0xc4ae3820f1f1cf1c

def z1271 : W := mkw 0x003edafbb0403003 0x000fb6beec100c00 0xfffffffff9c02001 0x7ffffffffe700800

def z1272 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xffbf63fcfffcffcf 0xffefd8ff3fff3ff3

def z1273 : W := mkw 0x8818f2c2d2c63463 0x22063cb0b4b18d18 0x57b8e3c3dfc73c73 0xd5ee38f0f7f1cf1c

def z1274 : W := mkw 0x8818f2c2c2c63462 0x22063cb0b0b18d18 0x77f8ffc3c7c73c73 0xddfe3ff0f1f1cf1c

def z1275 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0xd7b8e0cfffc73c73 0xf5ee3833fff1cf1c

def z1276 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xcf7fffffd8000000 0x33dffffff6000000

def z1277 : W := mkw 0x0c0808d3e04034fa 0x03020234f8100d3e 0x408000c3e0003c7e 0x50200030f8000f1f

def z1278 : W := mkw 0x0036d20001100000 0x400db48000440000 0x3f7fff0001d80001 0x0fdfffc000760000

def z1279 : W := mkw 0xe877f702c7bfc462 0xfa1dfdc0b1eff118 0x7fffff83c7ffe073 0xdfffffe0f1fff81c

def z1280 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0x577fffffd8000000 0x55dffffff6000000

def z1281 : W := mkw 0xa876f600439f8440 0x6a1dbd8010e7e110 0x577cfc40c7df1c43 0xd5df3f1031f7c710

def z1282 : W := mkw 0x100900ec05703b00 0xc402403b015c0ec0 0xc7b800fc07f83f83 0xb1ee003f01fe0fe0

def z1283 : W := mkw 0xf077f70407bfca00 0xfc1dfdc101eff280 0x3f7fff4c07ffdc01 0x8fdfffd301fff700

def z1284 : W := mkw 0x1027002c05300b00 0xc409c00b014c02c0 0xdb8780bf003f23f3 0xf6e1e02fc00fc8fc

def z1285 : W := mkw 0x0010da13b0000003 0x00043684ec000000 0xff47fffff8000000 0x7fd1fffffe000000

def z1286 : W := mkw 0x8818e0ead2c63463 0x2206383ab4b18d18 0x57b8e0cfdfc73c73 0xd5ee3833f7f1cf1c

def z1287 : W := mkw 0x1037d20405300a00 0xc40df481014c0280 0xff7fff4cfff81e03 0xffdfffd33ffe0780

def z1288 : W := mkw 0xca18e1c2cac67466 0x32863870b2b19d19 0xffbbe3cfffc7fc7f 0xffeef8f3fff1ff1f

def z1289 : W := mkw 0xe077d70005bbc000 0xf81df5c0016ef000 0x287f1f0001f8c000 0x0a1fc7c0007e3000

def z1290 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xfd03e34ffe27de7e 0xff40f8d3ff89f79f

def z1291 : W := mkw 0xda0121044ea64e64 0xb680484113a99399 0xfd03634cfe27de7e 0xff40d8d33f89f79f

def z1292 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xfffffffff8182181 0x7ffffffffe060860

def z1293 : W := mkw 0xde0125044eeffefc 0xb780494113bbffbf 0x0080000007ffffff 0x8020000001ffffff

def z1294 : W := mkw 0xfe4125044fbfcedc 0xff90494113eff3b7 0x0080000007ffffff 0x8020000001ffffff

def z1295 : W := mkw 0x8036d20000820000 0x200db48000208000 0x027c9c0001c30001 0x009f27000070c000

def z1296 : W := mkw 0xa077d60005bb8000 0xe81df580016ee000 0x0a7f9c0001fb0001 0x029fe700007ec000

def z1297 : W := mkw 0x8818e0eac2c63562 0x2206383ab0b18d58 0x57b8e0f3c7c73df3 0xd5ee383cf1f1cf7c

def z1298 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x3f7fff0001ffc001 0x8fdfffc0007ff000

def z1299 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0xff7fff4cf9db0001 0x7fdfffd33e76c000

def z1300 : W := mkw 0x5e0125044f7dffdc 0xd780494113df7ff7 0x0080000007ffffff 0x8020000001ffffff

def z1301 : W := mkw 0xe076f700039fc000 0x781dbdc000e7f000 0x3078ff0001c7c000 0x0c1e3fc00071f000

def z1302 : W := mkw 0x04000c1120098098 0x0100030448026026 0xffc49cf3263fffff 0xfff1273cc98fffff

def z1303 : W := mkw 0x8036f600028f8000 0x200dbd8000a3e000 0x3f7fff0007ffc001 0x8fdfffc001fff000

def z1304 : W := mkw 0x5a37f3044f344e44 0xd68dfcc113cd1391 0xff7fff4cfffcde4f 0xffdfffd33fff3793

def z1305 : W := mkw 0x1e0808d7e8403efe 0x07820235fa100fbf 0xc08000fff8003ffe 0x7020003ffe000fff

def z1306 : W := mkw 0x04000c1120098098 0x0100030448026026 0xffc79cff203fe3ff 0xfff1e73fc80ff8ff

def z1307 : W := mkw 0x100908ffb4603b03 0x8402423fed180ec0 0xfd8363fffe203f82 0xff60d8ffff880fe0

def z1308 : W := mkw 0xf277f7040fbfca04 0xfc9dfdc103eff281 0xff7fff4cffffc20d 0xffdfffd33ffff083

def z1309 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0x47bf00fc07d83d83 0x91efc03f01f60f60

def z1310 : W := mkw 0x04000c1120098098 0x0100030448026026 0xf8c49cb3203fe3fe 0x7e31272cc80ff8ff

def z1311 : W := mkw 0x0026040001198000 0x4009810000466000 0x3b7c9c0001ffc001 0x8edf2700007ff000

def z1312 : W := mkw 0xfa77f7044fbfce44 0xfe9dfdc113eff391 0x7f7fff4cdfffdc43 0xdfdfffd337fff710

def z1313 : W := mkw 0xb077d60405bb8a00 0xec1df581016ee280 0xcf7f9c4c07fb1e03 0xb3dfe71301fec780

def z1314 : W := mkw 0x0036da1120000000 0x000db68448000000 0xff7ffffff8000000 0x7fdffffffe000000

def z1315 : W := mkw 0x803edafbb0c23023 0x200fb6beec308c08 0xfffffffff9c72073 0xfffffffffe71c81c

def z1316 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xbd03634cfe24de0c 0xaf40d8d33f893783

def z1317 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0xac03634cfe24de4e 0xab00d8d33f893793

def z1318 : W := mkw 0x8818e0c2c2c63462 0x22063830b0b18d18 0x77b8e0c3e7c7fc7f 0xddee3830f9f1ff1f

def z1319 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x0f7fff0007fb0001 0x83dfffc001fec000

def z1320 : W := mkw 0x102f00ec05703b00 0xc40bc03b015c0ec0 0xffbf00fc27f83f83 0xffefc03f09fe0fe0

def z1321 : W := mkw 0x5a0121044e244e44 0x9680484113891391 0x7503634cfe04dc4e 0xdd40d8d33f813713

def z1322 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xfffffffff8002072 0x7ffffffffe00081c

def z1323 : W := mkw 0x003ed2ea90000003 0x000fb4baa4000000 0x7f7fffcfd8000000 0x5fdffff3f6000000

def z1324 : W := mkw 0xa076f600039f8000 0x681dbd8000e7e000 0x3f7fff0007df0001 0x8fdfffc001f7c000

def z1325 : W := mkw 0xe077f70007bfc000 0xf81dfdc001eff000 0x3fffff8307ffe031 0x8fffffe0c1fff80c

def z1326 : W := mkw 0x8010f20002860000 0x20043c8000a18000 0x3778ff0007c70001 0x8dde3fc001f1c000

def z1327 : W := mkw 0xa076d600019b8000 0x681db5800066e000 0x077c9c0007db0001 0x81df270001f6c000

def z1328 : W := mkw 0x102f00ee85703b02 0xc40bc03ba15c0ec0 0xcfbf00ffc7f83f83 0xf3efc03ff1fe0fe0

def z1329 : W := mkw 0x003edafbb0000003 0x000fb6beec000000 0xfffffffff8032031 0x7ffffffffe00c80c

def z1330 : W := mkw 0xda11e5044eafce44 0xb684794113abf391 0xff7fff4cffffde4f 0xffdfffd33ffff793

def z1331 : W := mkw 0x0037d20005300000 0xc00df480014c0000 0x3f7fff0007c00000 0x0fdfffc001f00000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z7,z5,z8,z6]),(0,[z0,z2,z4,z5,z9,z8,z6]),(1,[z0,z2,z10,z5,z8,z6])],[(0,[z0,z2,z4,z5,z11,z8,z6]),(0,[z12,z2,z4,z5,z8,z13,z6]),(0,[z0,z2,z4,z14,z5,z8,z6]),(0,[z0,z2,z5,z8,z15,z16,z6]),(0,[z0,z2,z4,z17,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z18,z6])],[(0,[z19,z0,z2,z4,z5,z8,z20]),(1,[z0,z2,z4,z5,z8,z21])],[(0,[z22,z0,z2,z4,z5,z8,z6]),(0,[z0,z23,z2,z24,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z25,z26])],[(0,[z2,z4,z5,z8,z13,z6,z27]),(1,[z28,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z26])],[(0,[z0,z2,z4,z29,z5,z8,z30]),(0,[z0,z2,z31,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z32,z6,z26])],[(0,[z0,z2,z33,z4,z5,z8,z34]),(0,[z19,z0,z2,z4,z5,z8,z35]),(0,[z36,z0,z2,z4,z37,z8,z6]),(0,[z0,z2,z4,z5,z16,z38,z6]),(0,[z0,z2,z4,z39,z5,z8,z6]),(0,[z0,z2,z4,z5,z40,z8,z6]),(0,[z0,z2,z4,z5,z41,z8,z42]),(0,[z43,z0,z2,z4,z5,z8,z6])],[(0,[z0,z2,z44,z4,z5,z8,z6]),(0,[z0,z2,z4,z45,z5,z8,z42]),(0,[z0,z2,z4,z5,z8,z46,z47])]],
   [[(0,[z0,z2,z4,z5,z48,z8,z6]),(0,[z49,z2,z4,z29,z5,z8,z6]),(0,[z19,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z50,z5,z8,z6]),(0,[z51,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z52,z4,z5,z8,z6])],[(0,[z0,z2,z4,z53,z5,z8,z6])],[(0,[z2,z54,z4,z45,z5,z8,z6]),(0,[z55,z2,z4,z5,z56,z8,z6]),(1,[z0,z2,z4,z57,z8,z6]),(0,[z0,z2,z3,z4,z5,z41,z6]),(0,[z0,z2,z4,z58,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z59,z6]),(0,[z0,z2,z4,z29,z5,z8,z60]),(0,[z0,z2,z61,z4,z5,z8,z6]),(0,[z0,z2,z4,z62,z63,z8,z6]),(0,[z64,z0,z2,z65,z5,z8,z6]),(0,[z66,z0,z2,z4,z5,z8,z35])],[(1,[z0,z2,z4,z5,z8,z67]),(0,[z55,z0,z2,z4,z5,z8,z42]),(0,[z0,z2,z4,z5,z8,z68,z6]),(1,[z69,z2,z4,z5,z8,z6]),(0,[z0,z2,z70,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z71,z8,z6])],[(0,[z55,z0,z2,z4,z5,z56,z6]),(0,[z72,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z73,z6]),(0,[z66,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z74,z5,z8,z42])],[(0,[z75,z0,z2,z4,z5,z8,z6]),(0,[z0,z69,z2,z4,z5,z8,z6]),(1,[z76,z0,z2,z4,z5,z8]),(0,[z0,z77,z2,z4,z5,z8,z6])],[(0,[z0,z2,z4,z78,z5,z8,z6]),(0,[z36,z0,z2,z4,z5,z8,z42]),(1,[z79,z0,z2,z5,z8,z6]),(0,[z80,z2,z4,z5,z81,z8,z6]),(0,[z0,z2,z82,z4,z5,z32,z6])]],
   [[(0,[z0,z2,z4,z5,z41,z16,z6]),(0,[z0,z2,z83,z4,z5,z8,z26]),(0,[z0,z2,z83,z4,z5,z32,z8])],[(0,[z0,z2,z4,z5,z84,z8,z6]),(0,[z85,z0,z2,z4,z5,z56,z6]),(0,[z0,z2,z4,z5,z86,z8,z6]),(0,[z87,z64,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z88,z6])],[(0,[z0,z2,z89,z4,z5,z8,z42]),(0,[z0,z2,z4,z63,z8,z90,z6]),(0,[z0,z2,z4,z91,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z92,z6])],[(0,[z0,z2,z4,z5,z8,z6,z93]),(0,[z0,z2,z4,z5,z94,z8,z6]),(0,[z0,z2,z83,z4,z5,z8,z46]),(0,[z0,z2,z4,z95,z5,z8,z6]),(0,[z0,z2,z4,z96,z5,z8,z42])],[(0,[z97,z0,z2,z82,z4,z5,z8]),(0,[z98,z0,z2,z4,z5,z8,z6]),(0,[z99,z0,z2,z4,z5,z8,z6]),(0,[z100,z0,z2,z4,z5,z8,z6]),(1,[z0,z2,z4,z5,z71,z8]),(0,[z101,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z102,z5,z8,z6]),(1,[z0,z2,z4,z5,z8,z35])],[(0,[z19,z0,z2,z24,z5,z8,z6]),(0,[z0,z2,z4,z5,z103,z8,z6])],[(1,[z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z104,z4,z5,z8,z6]),(0,[z105,z55,z2,z4,z5,z8,z6]),(1,[z0,z106,z4,z5,z8,z6]),(0,[z49,z0,z2,z4,z5,z8,z13])],[(0,[z107,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z108,z5,z8,z6]),(0,[z0,z2,z109,z4,z5,z8,z6]),(0,[z0,z2,z4,z110,z5,z8,z6]),(0,[z0,z2,z4,z111,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z112,z6])]],
   [[(0,[z0,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z113]),(0,[z0,z2,z4,z62,z5,z8,z114]),(0,[z0,z2,z4,z5,z8,z115,z6]),(0,[z116,z0,z2,z4,z5,z8,z6])],[(0,[z0,z2,z117,z5,z118,z8,z6]),(0,[z36,z0,z2,z4,z5,z16,z6]),(0,[z0,z2,z82,z4,z5,z8,z26])],[(0,[z0,z119,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z120]),(0,[z12,z0,z2,z4,z5,z121,z6]),(0,[z0,z2,z4,z29,z5,z8,z42]),(0,[z0,z2,z4,z122,z5,z8,z6])],[(0,[z123,z0,z2,z4,z5,z8,z6]),(0,[z64,z0,z2,z45,z5,z8,z6]),(0,[z0,z2,z4,z5,z124,z8,z6]),(0,[z0,z2,z4,z125,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z126,z6]),(1,[z127,z2,z4,z5,z8,z6]),(0,[z36,z0,z2,z128,z5,z8,z6]),(0,[z0,z2,z82,z4,z5,z8,z46])],[(0,[z129,z0,z2,z4,z5,z8,z35]),(0,[z0,z2,z4,z130,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z131,z6]),(0,[z0,z2,z4,z5,z8,z34,z6]),(0,[z132,z0,z2,z4,z5,z8,z6])],[(0,[z129,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z133,z8,z6]),(0,[z0,z23,z2,z117,z5,z8,z6])]],
   [[(0,[z2,z54,z4,z5,z8,z34,z6]),(0,[z0,z2,z4,z5,z8,z6,z134]),(0,[z0,z2,z4,z5,z135,z8,z42]),(1,[z97,z2,z4,z5,z8,z13]),(0,[z136,z0,z2,z4,z137,z8,z6])],[(1,[z138,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z8,z6,z139]),(0,[z0,z2,z4,z5,z140,z8,z26])],[(0,[z0,z2,z141,z4,z5,z8,z6]),(0,[z97,z0,z2,z4,z5,z8,z27]),(0,[z0,z2,z4,z5,z8,z27,z35]),(0,[z136,z0,z2,z4,z5,z8,z35]),(0,[z0,z2,z4,z142,z63,z8,z6]),(0,[z143,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z65,z4,z5,z8,z144])],[(0,[z0,z145,z4,z5,z63,z8,z6]),(0,[z0,z2,z4,z5,z8,z146,z6]),(0,[z97,z0,z2,z4,z5,z140,z8]),(0,[z0,z2,z147,z4,z5,z8,z6]),(0,[z0,z2,z4,z148,z5,z8,z6]),(0,[z149,z0,z2,z4,z5,z8,z6]),(0,[z143,z0,z2,z4,z5,z8,z42])],[(0,[z0,z2,z4,z150,z5,z8,z6]),(0,[z0,z2,z151,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z152,z6]),(0,[z136,z0,z2,z4,z5,z8,z6]),(0,[z0,z153,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z26,z35])],[(0,[z129,z2,z4,z5,z8,z34,z6]),(0,[z154,z0,z2,z4,z5,z8,z6]),(0,[z155,z0,z2,z4,z5,z8,z6]),(0,[z97,z2,z4,z5,z8,z13,z6]),(1,[z0,z2,z4,z5,z8,z156])],[(0,[z0,z2,z4,z5,z8,z157,z6]),(0,[z158,z0,z2,z4,z5,z8,z6]),(0,[z159,z0,z2,z4,z5,z8,z6])],[(0,[z160,z0,z2,z4,z45,z5,z8]),(1,[z0,z2,z161,z5,z8,z6]),(0,[z162,z0,z2,z4,z5,z8,z35]),(0,[z0,z163,z2,z4,z5,z8,z6]),(0,[z0,z2,z65,z4,z62,z8,z6])]],
   [[(0,[z164,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z67]),(0,[z165,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z166,z8,z6]),(0,[z0,z167,z2,z4,z5,z8,z6]),(0,[z143,z0,z2,z3,z5,z8,z6])],[(0,[z162,z0,z2,z4,z5,z8,z6]),(0,[z143,z64,z0,z2,z5,z8,z6]),(1,[z0,z2,z4,z5,z168,z6]),(0,[z0,z2,z4,z62,z5,z8,z42]),(0,[z169,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z35,z35]),(0,[z0,z2,z4,z5,z170,z8,z35])],[(0,[z2,z4,z29,z5,z135,z8,z6]),(0,[z97,z0,z2,z4,z5,z8,z47]),(0,[z0,z2,z4,z137,z5,z8,z21]),(0,[z36,z0,z2,z4,z171,z8,z6]),(0,[z0,z2,z172,z4,z5,z8,z6]),(0,[z0,z2,z4,z173,z5,z8,z6])],[(0,[z12,z0,z2,z4,z5,z8,z42]),(0,[z174,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z81,z34,z6]),(0,[z19,z0,z2,z4,z5,z175,z6]),(0,[z0,z2,z176,z4,z5,z8,z6]),(0,[z0,z1,z2,z4,z5,z8,z35]),(0,[z0,z2,z4,z5,z170,z8,z6])],[(0,[z177,z0,z2,z4,z5,z8,z6]),(0,[z162,z2,z4,z29,z5,z8,z6]),(0,[z178,z0,z2,z4,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z179,z6]),(0,[z180,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z181,z8,z6]),(0,[z0,z2,z182,z4,z5,z8,z6]),(0,[z183,z0,z2,z4,z5,z8,z6]),(0,[z0,z1,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z118,z8,z42]),(0,[z0,z2,z4,z184,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z13,z35]),(0,[z0,z2,z4,z5,z8,z42,z13]),(0,[z0,z2,z4,z5,z8,z185,z6]),(0,[z0,z2,z4,z137,z8,z90,z6])],[(0,[z186,z0,z2,z4,z5,z8,z6]),(0,[z187,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z188,z5,z8,z6]),(1,[z189,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z25,z35])]],
   [[(0,[z12,z0,z2,z190,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z13,z6]),(0,[z0,z2,z4,z191,z24,z5,z8]),(1,[z2,z4,z5,z192,z8,z6]),(0,[z0,z2,z193,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z35])],[(0,[z64,z0,z2,z89,z5,z8,z6]),(0,[z19,z0,z2,z117,z5,z8,z6]),(0,[z19,z0,z4,z24,z5,z8,z6]),(0,[z0,z2,z4,z128,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z194,z6]),(0,[z0,z2,z4,z5,z8,z25,z6]),(0,[z0,z2,z4,z195,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z168,z6]),(0,[z0,z2,z4,z142,z5,z8,z196])],[(0,[z2,z4,z45,z29,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z6]),(0,[z0,z2,z4,z5,z8,z16,z42]),(0,[z0,z2,z4,z197,z5,z8,z6]),(0,[z0,z2,z3,z4,z5,z90,z6]),(0,[z198,z2,z4,z5,z8,z6,z35]),(0,[z0,z2,z4,z8,z42,z6,z35]),(0,[z0,z2,z4,z5,z8,z42,z26])],[(0,[z199,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z200,z4,z5,z8,z6]),(0,[z0,z2,z4,z201,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z202])],[(0,[z105,z0,z2,z4,z5,z8,z35]),(1,[z12,z2,z4,z135,z8,z6]),(1,[z0,z2,z203,z4,z5,z8]),(0,[z204,z0,z2,z4,z5,z8,z35]),(0,[z0,z205,z4,z5,z8,z25,z6])],[(0,[z0,z2,z4,z5,z206,z8,z6]),(0,[z0,z207,z2,z4,z5,z8,z35]),(1,[z204,z0,z4,z5,z8,z47]),(0,[z0,z2,z4,z5,z8,z6,z208]),(0,[z0,z2,z4,z5,z8,z42,z46])],[(0,[z105,z0,z2,z4,z5,z8,z6]),(0,[z209,z0,z2,z4,z5,z8,z6]),(0,[z19,z0,z23,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z210]),(0,[z204,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z211,z6])],[(0,[z129,z2,z4,z5,z8,z13,z6]),(0,[z0,z2,z4,z5,z212,z8,z6]),(0,[z64,z0,z2,z4,z5,z8,z42])]],
   [[(0,[z0,z23,z2,z4,z5,z8,z42]),(0,[z0,z2,z4,z5,z8,z213,z35]),(0,[z0,z2,z4,z5,z214,z8,z6]),(0,[z0,z2,z215,z4,z5,z8,z35])],[(0,[z0,z2,z4,z5,z8,z216,z6]),(0,[z217,z0,z2,z4,z5,z8,z6]),(0,[z218,z0,z2,z4,z5,z8,z35])],[(0,[z0,z2,z219,z4,z5,z8,z6]),(0,[z220,z0,z2,z4,z5,z8,z6]),(0,[z19,z0,z2,z4,z5,z8,z221]),(0,[z0,z2,z222,z4,z5,z8,z6]),(0,[z101,z0,z2,z83,z5,z8,z6]),(0,[z0,z2,z215,z4,z5,z8,z6])],[(0,[z218,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z223,z6]),(0,[z224,z0,z2,z4,z5,z8,z35])],[(0,[z105,z2,z4,z5,z8,z34,z6]),(0,[z0,z2,z4,z5,z8,z225,z6]),(0,[z138,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z137,z5,z8,z35]),(0,[z0,z2,z4,z5,z8,z226,z6]),(0,[z0,z2,z4,z227,z5,z8,z6]),(0,[z0,z2,z83,z4,z5,z8,z35]),(0,[z228,z0,z2,z4,z5,z8,z42])],[(0,[z224,z0,z2,z4,z5,z8,z6]),(0,[z19,z0,z2,z4,z5,z229,z6]),(0,[z76,z0,z2,z4,z24,z5,z8]),(0,[z204,z0,z2,z82,z4,z5,z8]),(0,[z0,z2,z4,z230,z5,z8,z6]),(0,[z0,z2,z231,z4,z5,z8,z232])],[(0,[z233,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z83,z4,z5,z8,z6])],[(0,[z0,z4,z5,z234,z8,z16,z6]),(1,[z0,z2,z4,z5,z235,z8]),(0,[z0,z2,z236,z4,z5,z8,z42])]],
   [[(0,[z0,z2,z2,z4,z5,z8,z6]),(0,[z19,z143,z0,z2,z5,z8,z6]),(0,[z0,z2,z4,z142,z5,z8,z42])],[(0,[z237,z0,z2,z4,z5,z8,z6]),(0,[z238,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z239,z4,z5,z8,z6]),(0,[z36,z0,z2,z240,z5,z8,z6]),(0,[z0,z205,z2,z4,z5,z8,z35]),(0,[z64,z0,z2,z4,z62,z8,z6])],[(0,[z0,z2,z241,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z242,z6]),(0,[z0,z205,z2,z83,z4,z5,z8]),(0,[z0,z2,z3,z4,z5,z8,z35]),(0,[z0,z2,z4,z5,z243,z8,z6])],[(1,[z0,z2,z4,z5,z8,z30]),(0,[z36,z0,z1,z4,z5,z8,z6]),(0,[z244,z0,z2,z4,z5,z8,z6]),(1,[z0,z2,z4,z5,z245,z6]),(0,[z246,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z247,z4,z5,z8,z6]),(0,[z0,z248,z2,z4,z5,z8,z42])],[(0,[z55,z0,z2,z4,z5,z34,z6]),(1,[z0,z2,z4,z5,z8,z249]),(0,[z0,z2,z250,z4,z5,z8,z6])],[(0,[z251,z0,z2,z45,z5,z8,z6]),(0,[z0,z2,z252,z4,z5,z8,z6]),(0,[z204,z0,z4,z5,z8,z6,z47]),(0,[z0,z2,z253,z4,z5,z8,z6]),(0,[z2,z4,z5,z81,z254,z8,z6]),(0,[z0,z2,z82,z4,z5,z8,z35])],[(0,[z0,z54,z4,z5,z63,z8,z6]),(0,[z0,z255,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z56,z90,z6]),(0,[z49,z0,z2,z4,z5,z8,z35]),(0,[z97,z0,z2,z4,z5,z8,z25]),(1,[z2,z31,z4,z5,z8,z6]),(0,[z0,z2,z83,z5,z8,z46,z6]),(1,[z0,z2,z4,z142,z81,z6]),(0,[z256,z0,z2,z4,z5,z8,z6])],[(0,[z0,z2,z257,z4,z5,z8,z6]),(1,[z0,z2,z4,z5,z121,z6]),(0,[z49,z0,z2,z83,z4,z5,z8]),(0,[z0,z2,z4,z5,z8,z47,z213]),(1,[z0,z2,z4,z5,z8,z258]),(0,[z259,z0,z2,z4,z5,z8,z6]),(0,[z260,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z82,z4,z5,z8,z6])]],
   [[(0,[z85,z0,z2,z4,z5,z34,z6]),(0,[z49,z0,z2,z4,z5,z8,z6]),(1,[z0,z2,z4,z5,z8,z221]),(1,[z0,z2,z4,z191,z5,z8]),(1,[z136,z0,z4,z63,z8,z6]),(0,[z136,z0,z2,z4,z63,z8,z6]),(1,[z0,z205,z4,z5,z8,z25]),(0,[z0,z2,z231,z4,z5,z8,z42]),(0,[z261,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z262,z6]),(0,[z0,z2,z4,z263,z5,z8,z6]),(0,[z0,z2,z264,z4,z5,z8,z6])],[(1,[z0,z2,z4,z5,z8,z60]),(1,[z0,z2,z33,z4,z5,z8]),(0,[z0,z2,z240,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z265,z6]),(0,[z0,z2,z4,z266,z5,z8,z6]),(0,[z0,z2,z4,z267,z5,z8,z6]),(0,[z0,z2,z4,z268,z5,z8,z6])],[(0,[z0,z269,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z270,z6]),(0,[z19,z0,z2,z4,z5,z8,z42]),(0,[z0,z2,z4,z5,z271,z8,z6])],[(0,[z272,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z273,z4,z5,z8,z6]),(1,[z0,z2,z4,z5,z229,z6]),(0,[z274,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z63,z8,z42]),(0,[z0,z2,z4,z5,z8,z275,z6]),(0,[z0,z2,z276,z4,z5,z8,z6])],[(1,[z0,z2,z239,z5,z8,z6]),(0,[z204,z0,z2,z4,z5,z140,z8]),(0,[z0,z2,z277,z4,z5,z8,z42])],[(0,[z0,z2,z4,z278,z5,z8,z6]),(0,[z0,z2,z4,z279,z5,z8,z6]),(0,[z280,z0,z2,z4,z5,z8,z6]),(0,[z281,z205,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z90,z35]),(0,[z0,z2,z142,z10,z5,z8,z6]),(0,[z0,z2,z4,z5,z140,z8,z35])],[(0,[z143,z0,z23,z2,z5,z8,z6]),(0,[z36,z143,z0,z2,z4,z5,z6]),(0,[z0,z2,z5,z118,z41,z8,z6]),(0,[z0,z2,z4,z5,z41,z8,z282])],[(0,[z0,z2,z283,z4,z5,z8,z6]),(0,[z284,z0,z2,z4,z5,z8,z6]),(0,[z49,z0,z2,z82,z4,z5,z8]),(0,[z97,z0,z2,z4,z5,z8,z42]),(1,[z0,z2,z4,z37,z8,z6]),(0,[z0,z2,z4,z5,z8,z90,z6]),(0,[z0,z2,z4,z5,z140,z8,z6]),(0,[z285,z0,z2,z4,z5,z8,z6])]],
   [[(0,[z286,z129,z2,z4,z5,z8,z6]),(0,[z105,z129,z2,z4,z5,z8,z6]),(0,[z0,z145,z2,z4,z5,z8,z67]),(0,[z0,z2,z4,z5,z8,z287,z6]),(0,[z0,z2,z4,z5,z41,z234,z6]),(0,[z0,z2,z4,z288,z5,z8,z6])],[(0,[z12,z0,z2,z4,z29,z8,z6]),(0,[z0,z2,z3,z24,z5,z8,z6]),(0,[z0,z2,z289,z4,z5,z8,z6])],[(0,[z12,z105,z2,z4,z5,z8,z6]),(0,[z0,z2,z117,z4,z5,z8,z42]),(0,[z0,z2,z4,z5,z8,z6,z290])],[(0,[z0,z2,z4,z5,z291,z8,z6]),(0,[z0,z2,z4,z5,z57,z8,z6]),(1,[z0,z2,z4,z5,z8,z20]),(0,[z0,z2,z4,z5,z292,z8,z6]),(0,[z204,z0,z2,z4,z5,z8,z47]),(0,[z0,z2,z4,z5,z293,z8,z6]),(0,[z0,z2,z82,z4,z5,z140,z6])],[(0,[z0,z2,z4,z5,z8,z294,z6]),(0,[z0,z2,z4,z5,z295,z8,z6]),(0,[z296,z0,z2,z4,z5,z8,z6]),(1,[z0,z2,z83,z5,z8,z46])],[(0,[z0,z2,z4,z297,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z298])],[(0,[z0,z2,z299,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z30,z6]),(0,[z0,z2,z4,z5,z56,z8,z35]),(0,[z300,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z301,z8,z6]),(0,[z101,z0,z2,z4,z5,z8,z42]),(0,[z0,z2,z302,z4,z5,z8,z6])],[]],
   [[(0,[z303,z0,z2,z4,z5,z8,z6]),(0,[z0,z145,z2,z4,z5,z8,z35]),(0,[z0,z2,z4,z5,z56,z8,z6]),(0,[z0,z304,z2,z4,z5,z8,z6]),(0,[z305,z0,z2,z4,z5,z8,z6]),(0,[z28,z0,z2,z4,z5,z8,z6])],[(0,[z0,z2,z306,z4,z5,z8,z6]),(1,[z0,z2,z4,z5,z8,z307]),(0,[z0,z2,z4,z5,z8,z6,z308]),(0,[z19,z0,z2,z4,z309,z8,z6]),(0,[z36,z0,z2,z4,z5,z234,z6]),(0,[z0,z2,z4,z5,z310,z8,z6])],[(0,[z0,z145,z2,z4,z5,z8,z6]),(0,[z55,z2,z54,z4,z5,z8,z6]),(0,[z0,z2,z4,z311,z5,z8,z6]),(0,[z0,z2,z312,z4,z5,z8,z6]),(0,[z136,z0,z2,z239,z5,z8,z6]),(0,[z0,z2,z4,z313,z5,z8,z6]),(0,[z314,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z315,z6])],[(0,[z0,z2,z4,z5,z8,z316,z6]),(0,[z286,z0,z54,z4,z5,z8,z6]),(0,[z251,z0,z2,z89,z5,z8,z6]),(0,[z0,z2,z4,z5,z317,z8,z6])],[(0,[z0,z2,z4,z5,z318,z8,z6]),(0,[z105,z0,z2,z45,z5,z8,z6]),(0,[z319,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z320,z8,z6]),(0,[z0,z2,z4,z5,z8,z321,z6]),(0,[z0,z2,z82,z4,z5,z32,z8])],[(1,[z0,z2,z190,z5,z8,z6]),(0,[z0,z2,z4,z5,z322,z8,z6]),(0,[z49,z0,z2,z4,z5,z8,z27]),(0,[z36,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z323,z5,z8,z6]),(0,[z0,z2,z4,z5,z324,z8,z6])],[(0,[z0,z2,z325,z4,z5,z8,z6]),(0,[z0,z2,z326,z4,z5,z8,z6]),(0,[z49,z0,z2,z4,z5,z140,z8]),(0,[z0,z2,z4,z5,z327,z8,z6]),(0,[z328,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z42,z35])],[(0,[z329,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z330,z4,z5,z8,z6]),(0,[z0,z2,z4,z96,z8,z6,z35])]],
   [[(0,[z0,z2,z4,z5,z8,z34,z42]),(0,[z0,z2,z4,z5,z8,z6,z331]),(0,[z0,z2,z4,z5,z8,z6,z249]),(0,[z0,z2,z4,z5,z8,z42,z6]),(0,[z0,z2,z4,z5,z32,z8,z35])],[(0,[z251,z0,z2,z4,z5,z8,z42]),(0,[z0,z2,z4,z5,z8,z8,z6]),(0,[z0,z2,z4,z332,z5,z8,z6]),(1,[z0,z2,z4,z5,z8,z333]),(0,[z0,z2,z4,z74,z96,z8,z6])],[(0,[z49,z129,z2,z4,z5,z8,z6]),(0,[z0,z2,z334,z4,z5,z8,z6]),(0,[z0,z335,z2,z4,z5,z8,z6]),(0,[z336,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z337,z6]),(0,[z0,z2,z4,z5,z32,z8,z6])],[(0,[z338,z0,z2,z4,z5,z8,z6]),(0,[z339,z0,z2,z4,z5,z8,z6])],[(0,[z0,z340,z2,z4,z5,z8,z6]),(0,[z341,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z221]),(0,[z0,z2,z4,z5,z8,z6,z342]),(0,[z143,z0,z2,z4,z5,z41,z6]),(0,[z0,z2,z4,z5,z343,z8,z6])],[(0,[z344,z0,z2,z4,z5,z8,z6]),(0,[z162,z0,z2,z4,z135,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z60]),(0,[z49,z0,z2,z4,z5,z8,z47]),(0,[z0,z2,z4,z5,z8,z42,z345])],[(0,[z346,z0,z2,z4,z5,z8,z6]),(0,[z36,z0,z2,z4,z5,z8,z347]),(0,[z0,z2,z4,z5,z8,z6,z348])],[(0,[z105,z251,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z349,z5,z8,z6]),(1,[z0,z2,z4,z5,z8,z350]),(0,[z0,z2,z3,z4,z5,z81,z6]),(0,[z0,z2,z4,z5,z140,z8,z46])]],
   [[(0,[z0,z2,z4,z5,z8,z351,z6]),(0,[z158,z0,z2,z4,z5,z8,z42])],[(0,[z352,z0,z2,z4,z5,z8,z6]),(0,[z12,z286,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z353,z5,z8,z6]),(0,[z0,z2,z3,z5,z41,z8,z6]),(0,[z0,z2,z4,z5,z8,z42,z211]),(0,[z0,z2,z4,z354,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z6,z355]),(1,[z0,z2,z4,z5,z8,z356]),(0,[z101,z0,z2,z4,z5,z8,z213])],[(0,[z85,z55,z2,z4,z5,z8,z6]),(0,[z97,z49,z2,z4,z5,z8,z6]),(0,[z357,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z358,z8,z6])],[(0,[z0,z2,z4,z5,z175,z8,z6]),(0,[z0,z359,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z81,z8,z35]),(0,[z360,z0,z2,z4,z5,z8,z42])],[(0,[z0,z2,z4,z161,z5,z8,z6]),(0,[z0,z2,z361,z4,z5,z8,z6]),(1,[z0,z23,z117,z5,z8,z6]),(0,[z0,z2,z3,z117,z5,z8,z6]),(0,[z0,z2,z4,z5,z362,z8,z6]),(0,[z0,z2,z4,z363,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z364])],[(0,[z12,z145,z2,z4,z5,z8,z6]),(1,[z0,z2,z4,z5,z8,z225]),(0,[z0,z2,z4,z365,z5,z8,z6]),(0,[z366,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z367,z8,z6]),(0,[z0,z2,z4,z5,z81,z8,z6])],[(0,[z368,z0,z2,z4,z5,z8,z6]),(0,[z101,z49,z0,z2,z4,z5,z8]),(0,[z204,z0,z2,z4,z5,z8,z25]),(0,[z0,z2,z4,z369,z5,z8,z6])]],
   [[(0,[z0,z2,z231,z4,z8,z90,z6])],[(0,[z370,z0,z2,z4,z5,z8,z6])],[(1,[z19,z0,z24,z5,z8,z6]),(0,[z0,z2,z4,z332,z24,z5,z6]),(0,[z0,z1,z4,z5,z234,z8,z6])],[(1,[z0,z2,z44,z4,z5,z8]),(0,[z0,z2,z4,z5,z234,z90,z6])],[(0,[z145,z2,z54,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z371,z8,z6]),(0,[z0,z2,z4,z5,z254,z8,z6]),(1,[z2,z4,z5,z8,z6,z202])],[(0,[z2,z54,z4,z5,z8,z13,z6]),(0,[z372,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z42,z27]),(1,[z0,z2,z65,z118,z8,z6]),(0,[z0,z2,z4,z5,z8,z38,z35]),(0,[z0,z373,z2,z4,z5,z8,z6])],[(0,[z374,z0,z2,z4,z5,z8,z6]),(0,[z0,z207,z2,z4,z137,z8,z6]),(0,[z80,z0,z2,z4,z5,z8,z6])],[(0,[z55,z2,z4,z45,z5,z8,z6]),(0,[z79,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z38,z6])]],
   [[(0,[z286,z0,z2,z4,z5,z8,z42]),(0,[z2,z4,z45,z5,z8,z34,z6]),(0,[z375,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z376,z6]),(0,[z0,z207,z4,z137,z5,z8,z6]),(0,[z204,z0,z2,z4,z5,z8,z42]),(0,[z0,z2,z4,z5,z32,z140,z8])],[(1,[z162,z2,z4,z29,z8,z6]),(0,[z377,z0,z2,z4,z5,z8,z6]),(0,[z0,z1,z2,z4,z5,z16,z6]),(0,[z0,z2,z4,z5,z378,z8,z6]),(0,[z0,z2,z4,z5,z379,z8,z6]),(0,[z0,z380,z2,z4,z5,z8,z6])],[(0,[z0,z2,z4,z5,z381,z8,z6]),(0,[z0,z2,z4,z5,z382,z8,z6]),(0,[z0,z207,z2,z4,z5,z8,z6]),(1,[z36,z0,z4,z5,z16,z6]),(0,[z0,z383,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z384])],[(0,[z385,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z386,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z387,z6]),(0,[z0,z2,z4,z5,z8,z6,z388])],[(0,[z389,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z390,z5,z8,z6]),(1,[z55,z2,z4,z5,z56,z6]),(1,[z0,z2,z4,z5,z175,z6]),(0,[z0,z391,z2,z4,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z6,z333]),(0,[z392,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z42,z47]),(0,[z0,z2,z4,z5,z8,z223,z42])],[(0,[z0,z2,z4,z5,z8,z6,z393]),(1,[z0,z2,z231,z4,z90,z6])],[(0,[z0,z2,z4,z5,z32,z8,z47]),(0,[z0,z394,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z41,z8,z35]),(0,[z224,z0,z2,z4,z5,z8,z42])]],
   [[(0,[z0,z2,z4,z5,z8,z6,z395]),(0,[z129,z0,z145,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z47,z26]),(0,[z0,z2,z83,z4,z5,z8,z42])],[(0,[z396,z0,z2,z4,z5,z8,z6]),(0,[z49,z0,z2,z4,z5,z8,z25]),(0,[z0,z2,z4,z137,z5,z8,z6]),(0,[z397,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z41,z8,z6]),(0,[z0,z2,z4,z5,z8,z35,z398]),(1,[z0,z2,z82,z4,z5,z32])],[(0,[z0,z2,z4,z5,z8,z399,z6]),(0,[z0,z2,z4,z400,z5,z8,z6]),(0,[z0,z2,z4,z142,z5,z8,z401])],[(0,[z286,z2,z54,z4,z5,z8,z6]),(0,[z0,z2,z4,z402,z5,z8,z6]),(0,[z0,z23,z117,z4,z5,z8,z6]),(0,[z0,z2,z4,z171,z5,z8,z6]),(0,[z0,z2,z4,z5,z234,z8,z35]),(0,[z0,z2,z4,z5,z8,z6,z350]),(1,[z80,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z403,z8,z6]),(0,[z0,z2,z4,z5,z404,z8,z6])],[(0,[z0,z405,z2,z4,z5,z8,z6]),(0,[z0,z2,z24,z5,z8,z38,z6]),(0,[z406,z0,z2,z4,z5,z8,z6])],[(0,[z0,z2,z4,z407,z5,z8,z6]),(0,[z55,z0,z2,z4,z5,z8,z35]),(0,[z0,z2,z4,z5,z234,z8,z6]),(0,[z64,z408,z2,z4,z5,z8,z6]),(0,[z409,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z410,z8,z6])],[(0,[z0,z2,z411,z4,z5,z8,z6]),(0,[z0,z205,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z74,z5,z8,z35])],[(0,[z129,z0,z54,z4,z5,z8,z6]),(0,[z0,z2,z412,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z413,z8,z6]),(0,[z0,z2,z4,z5,z414,z8,z6]),(0,[z55,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z137,z118,z8,z6]),(0,[z0,z2,z4,z5,z8,z25,z213]),(0,[z0,z2,z415,z4,z5,z8,z6]),(0,[z0,z2,z3,z4,z5,z8,z6])]],
   [[(0,[z416,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z44,z4,z45,z5,z8]),(0,[z36,z0,z2,z4,z5,z8,z35]),(0,[z0,z2,z4,z417,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z398])],[(0,[z85,z0,z2,z4,z5,z8,z35]),(0,[z0,z2,z4,z10,z5,z8,z6]),(0,[z0,z2,z4,z74,z8,z42,z6])],[(0,[z12,z49,z2,z4,z5,z8,z6]),(0,[z55,z2,z4,z29,z5,z8,z6]),(0,[z0,z2,z33,z4,z5,z8,z6]),(0,[z49,z0,z2,z4,z5,z8,z42]),(0,[z0,z2,z4,z5,z8,z6,z27]),(0,[z36,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z418,z6]),(0,[z419,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z420,z6]),(1,[z0,z2,z4,z5,z8,z114]),(0,[z0,z2,z4,z5,z8,z6,z421])],[(0,[z85,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z422,z6]),(0,[z0,z2,z4,z5,z423,z8,z6])],[(1,[z0,z2,z4,z5,z8,z196])],[(1,[z85,z2,z4,z5,z34,z6]),(0,[z0,z2,z4,z5,z424,z8,z6]),(0,[z0,z205,z2,z82,z4,z5,z8])],[(0,[z0,z2,z425,z4,z5,z8,z6]),(0,[z426,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z427,z4,z5,z8,z6])],[(0,[z0,z2,z4,z428,z5,z8,z6])]],
   [[(0,[z0,z2,z429,z4,z5,z8,z6]),(0,[z138,z0,z2,z4,z24,z5,z6]),(1,[z183,z2,z4,z5,z8,z6]),(0,[z36,z127,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z430,z8,z6]),(1,[z0,z2,z4,z5,z8,z232])],[(0,[z0,z2,z4,z431,z5,z8,z6]),(0,[z85,z2,z4,z5,z8,z34,z6]),(0,[z0,z2,z4,z5,z432,z8,z6])],[(0,[z433,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z121,z6]),(0,[z0,z2,z434,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z47]),(0,[z0,z2,z435,z4,z5,z8,z6])],[(0,[z2,z89,z4,z45,z5,z8,z6]),(0,[z436,z0,z2,z4,z5,z8,z6]),(0,[z136,z0,z207,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z437,z35])],[(0,[z438,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z83,z4,z5,z8,z213]),(0,[z0,z439,z2,z4,z5,z8,z6])],[(1,[z160,z0,z2,z4,z5,z8]),(0,[z0,z2,z4,z5,z8,z440,z6]),(1,[z0,z2,z4,z5,z441,z6]),(0,[z442,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z3,z4,z5,z8,z350]),(0,[z0,z2,z4,z81,z8,z90,z6])],[(0,[z12,z2,z4,z45,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z443,z6]),(0,[z0,z2,z4,z5,z8,z229,z6]),(0,[z0,z2,z65,z4,z5,z8,z35]),(0,[z0,z2,z4,z5,z8,z294,z42]),(0,[z0,z2,z4,z444,z5,z8,z6])],[(0,[z286,z0,z145,z4,z5,z8,z6]),(0,[z0,z2,z4,z445,z5,z8,z6]),(0,[z0,z446,z2,z4,z5,z8,z6]),(0,[z0,z447,z2,z4,z5,z8,z6]),(0,[z0,z2,z62,z5,z118,z8,z6])]],
   [[(0,[z0,z2,z4,z5,z8,z6,z448]),(0,[z449,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z450,z4,z5,z8,z6]),(0,[z0,z2,z65,z4,z5,z8,z6]),(0,[z217,z0,z2,z142,z5,z8,z6]),(0,[z0,z2,z451,z4,z5,z8,z6])],[(0,[z452,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z135,z8,z35]),(0,[z0,z2,z4,z5,z8,z6,z453]),(1,[z304,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z42,z25]),(0,[z454,z0,z2,z4,z5,z8,z6])],[(0,[z0,z2,z4,z5,z56,z8,z42]),(0,[z0,z2,z455,z4,z5,z8,z6]),(1,[z0,z2,z4,z5,z8,z401]),(0,[z0,z2,z4,z5,z8,z456,z6])],[(0,[z457,z0,z2,z4,z5,z8,z6]),(0,[z12,z0,z2,z4,z5,z458,z6]),(0,[z0,z2,z4,z5,z135,z8,z6]),(0,[z0,z2,z4,z5,z459,z8,z6]),(0,[z0,z2,z4,z5,z8,z460,z6]),(1,[z461,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z16,z90,z6]),(0,[z0,z2,z4,z5,z234,z38,z6]),(0,[z0,z2,z462,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z32,z8,z25]),(1,[z0,z2,z4,z5,z8,z42])],[(0,[z0,z2,z4,z5,z8,z6,z463]),(0,[z0,z2,z4,z5,z8,z464,z6]),(0,[z0,z2,z4,z465,z5,z8,z6]),(0,[z466,z0,z2,z4,z5,z8,z6]),(0,[z0,z205,z2,z4,z5,z140,z8]),(0,[z0,z2,z4,z5,z8,z467,z6]),(0,[z0,z2,z4,z110,z5,z8,z42])],[(0,[z2,z4,z5,z192,z63,z8,z6]),(0,[z0,z4,z5,z8,z25,z6,z47]),(0,[z0,z2,z3,z4,z5,z38,z6]),(0,[z0,z2,z82,z4,z5,z8,z213]),(0,[z0,z2,z4,z468,z5,z8,z6])],[(0,[z136,z183,z2,z4,z5,z8,z6]),(0,[z0,z207,z2,z4,z63,z8,z6]),(0,[z0,z2,z65,z4,z118,z8,z6]),(0,[z0,z2,z4,z5,z8,z202,z35])],[(0,[z0,z207,z54,z4,z5,z8,z6]),(0,[z0,z2,z4,z4,z5,z8,z6]),(0,[z0,z2,z4,z469,z5,z8,z6]),(0,[z101,z0,z205,z2,z4,z5,z8]),(0,[z0,z2,z4,z470,z5,z8,z6]),(0,[z471,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z472,z4,z5,z8,z6])]],
   [[(0,[z0,z2,z4,z5,z8,z473,z6]),(0,[z0,z2,z4,z474,z5,z8,z6]),(0,[z0,z2,z4,z475,z5,z8,z6]),(1,[z0,z2,z4,z5,z8,z144]),(0,[z0,z2,z4,z5,z5,z8,z35]),(0,[z0,z2,z4,z5,z8,z476,z6]),(0,[z0,z2,z4,z5,z477,z8,z6])],[(0,[z12,z162,z2,z4,z5,z8,z6]),(0,[z0,z2,z65,z5,z118,z8,z6])],[(0,[z0,z2,z4,z5,z8,z6,z478]),(0,[z12,z0,z479,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z5,z8,z6]),(0,[z0,z480,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z481,z5,z8,z6]),(0,[z0,z2,z4,z482,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z42,z262]),(0,[z0,z2,z4,z5,z8,z42,z42])],[(0,[z0,z483,z2,z4,z5,z8,z6]),(0,[z136,z0,z2,z4,z5,z441,z6]),(0,[z36,z189,z2,z4,z5,z8,z6]),(0,[z0,z205,z2,z4,z5,z8,z47]),(0,[z0,z2,z4,z484,z5,z8,z6])],[(0,[z129,z145,z2,z4,z5,z8,z6]),(0,[z129,z0,z2,z4,z5,z8,z42]),(0,[z145,z2,z4,z29,z5,z8,z6]),(0,[z485,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z486,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z487]),(0,[z0,z2,z4,z5,z8,z488,z6]),(0,[z0,z2,z4,z5,z8,z489,z6]),(0,[z0,z2,z4,z5,z32,z8,z42])],[(0,[z0,z2,z490,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z491,z8,z6]),(0,[z0,z2,z4,z5,z140,z8,z213]),(0,[z0,z2,z4,z5,z8,z46,z35])],[(0,[z0,z2,z54,z4,z5,z8,z35]),(0,[z0,z2,z4,z492,z5,z8,z6]),(0,[z160,z0,z2,z4,z5,z8,z6]),(0,[z97,z101,z0,z2,z4,z5,z8]),(0,[z0,z2,z4,z5,z118,z8,z35]),(0,[z0,z2,z4,z5,z8,z6,z114])],[(0,[z0,z2,z493,z4,z5,z8,z6]),(0,[z136,z304,z2,z4,z5,z8,z6]),(1,[z143,z0,z2,z5,z38,z6]),(0,[z0,z2,z4,z5,z8,z46,z6])]],
   [[(0,[z0,z2,z54,z4,z5,z8,z6]),(0,[z0,z2,z4,z494,z5,z8,z6]),(1,[z0,z2,z128,z5,z8,z6]),(0,[z0,z2,z4,z5,z118,z8,z6])],[(0,[z0,z2,z4,z495,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z496,z6]),(0,[z497,z0,z2,z4,z5,z8,z6]),(0,[z136,z0,z2,z4,z5,z8,z42])],[(1,[z0,z2,z4,z309,z8,z6]),(0,[z0,z2,z4,z24,z5,z8,z35]),(0,[z136,z0,z4,z5,z63,z8,z6])],[(0,[z0,z2,z4,z5,z8,z16,z35]),(0,[z0,z2,z4,z5,z498,z8,z35])],[(0,[z499,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z500,z4,z5,z8,z6]),(0,[z501,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z24,z5,z8,z6]),(0,[z502,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z47,z35]),(0,[z0,z503,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z232])],[(0,[z2,z4,z29,z5,z8,z34,z6]),(0,[z0,z2,z4,z5,z8,z6,z504]),(0,[z0,z2,z4,z5,z8,z16,z6]),(0,[z505,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z498,z8,z6])],[(0,[z0,z506,z2,z4,z5,z8,z6]),(0,[z162,z0,z2,z4,z5,z8,z42])],[(0,[z12,z2,z4,z5,z135,z8,z6]),(0,[z0,z2,z4,z5,z8,z507,z6]),(1,[z0,z2,z4,z5,z8,z508]),(0,[z0,z509,z2,z4,z5,z8,z6]),(0,[z510,z0,z2,z4,z5,z8,z6])]],
   [[(0,[z511,z0,z2,z4,z5,z8,z6]),(1,[z251,z2,z45,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z512,z6]),(1,[z0,z2,z513,z5,z8,z6]),(0,[z0,z2,z4,z118,z63,z8,z6]),(0,[z64,z0,z2,z4,z5,z8,z35]),(1,[z217,z0,z2,z5,z8,z6]),(0,[z0,z2,z4,z5,z81,z8,z42]),(0,[z174,z0,z2,z4,z5,z8,z42])],[(0,[z514,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z515,z5,z8,z6]),(0,[z0,z2,z4,z5,z516,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z517]),(0,[z0,z2,z231,z4,z5,z90,z6])],[(0,[z518,z0,z2,z4,z5,z8,z6]),(0,[z0,z1,z2,z4,z5,z8,z42]),(0,[z64,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z519,z4,z5,z8,z6]),(0,[z0,z2,z520,z4,z5,z8,z6]),(1,[z101,z0,z2,z5,z8,z213]),(0,[z0,z521,z2,z4,z5,z8,z6])],[(0,[z286,z2,z4,z29,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z522,z6]),(0,[z523,z0,z2,z4,z5,z8,z6])],[(0,[z12,z0,z2,z4,z5,z8,z524]),(0,[z0,z2,z4,z525,z5,z8,z6]),(0,[z19,z497,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z20,z6]),(0,[z0,z2,z4,z5,z8,z526,z6])],[(0,[z105,z0,z2,z89,z5,z8,z6]),(0,[z0,z2,z4,z5,z527,z8,z6]),(0,[z0,z2,z24,z5,z118,z8,z6]),(1,[z0,z2,z5,z8,z15,z6]),(1,[z2,z4,z5,z254,z8,z6])],[(0,[z528,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z529]),(1,[z0,z2,z4,z171,z8,z6]),(0,[z0,z530,z2,z4,z5,z8,z6]),(0,[z0,z531,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z42,z213]),(0,[z0,z2,z4,z5,z8,z6,z532]),(0,[z0,z2,z4,z5,z8,z6,z401]),(0,[z0,z2,z4,z5,z8,z35,z533])],[(0,[z0,z2,z4,z62,z5,z168,z6]),(0,[z0,z534,z2,z4,z5,z8,z6])]],
   [[(0,[z0,z2,z4,z5,z535,z8,z6]),(0,[z0,z2,z4,z536,z5,z8,z6]),(0,[z36,z0,z2,z4,z5,z8,z249]),(0,[z0,z2,z4,z537,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z538,z6]),(0,[z19,z0,z2,z4,z57,z8,z6]),(0,[z0,z2,z4,z5,z539,z8,z6]),(0,[z0,z2,z4,z5,z8,z540,z6]),(0,[z0,z2,z4,z541,z5,z8,z6]),(0,[z143,z0,z2,z5,z8,z38,z6])],[(0,[z542,z0,z2,z4,z5,z8,z6]),(0,[z0,z106,z2,z4,z5,z8,z6]),(0,[z49,z2,z4,z5,z8,z6,z27]),(0,[z543,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z21,z6]),(0,[z127,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z81,z16,z6]),(0,[z0,z2,z4,z5,z544,z8,z6]),(0,[z0,z2,z4,z5,z8,z345,z6])],[(0,[z105,z0,z2,z4,z5,z8,z42]),(0,[z0,z2,z4,z5,z8,z42,z90])],[(0,[z0,z207,z2,z4,z5,z8,z42]),(0,[z0,z2,z4,z5,z8,z6,z144])],[(0,[z545,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z533]),(0,[z0,z546,z2,z4,z5,z8,z6]),(0,[z136,z0,z2,z4,z5,z8,z508]),(0,[z2,z4,z5,z8,z6,z202,z35]),(0,[z0,z2,z4,z5,z214,z8,z42])],[(0,[z136,z0,z2,z513,z5,z8,z6]),(0,[z0,z2,z4,z5,z547,z8,z6]),(0,[z0,z2,z4,z5,z8,z347,z6]),(0,[z0,z2,z4,z548,z5,z8,z6]),(0,[z0,z248,z2,z4,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z6,z549]),(0,[z2,z4,z29,z5,z8,z13,z6]),(0,[z2,z4,z5,z56,z8,z34,z6]),(0,[z0,z2,z4,z5,z550,z8,z6]),(0,[z0,z2,z551,z4,z5,z8,z6]),(0,[z0,z2,z4,z552,z5,z8,z6]),(0,[z0,z117,z4,z24,z5,z8,z6]),(0,[z64,z0,z2,z24,z5,z8,z6]),(0,[z0,z2,z203,z4,z5,z8,z16]),(0,[z553,z0,z2,z4,z5,z8,z6]),(0,[z0,z205,z2,z4,z5,z8,z25])]],
   [[(0,[z0,z2,z4,z554,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z555,z6])],[(0,[z0,z2,z4,z5,z556,z8,z6]),(0,[z143,z0,z2,z4,z5,z81,z6]),(0,[z0,z2,z231,z4,z5,z8,z35]),(0,[z0,z2,z4,z557,z5,z8,z6])],[(1,[z497,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z558,z5,z8,z6]),(0,[z0,z559,z2,z4,z5,z8,z6])],[(0,[z0,z2,z4,z5,z560,z8,z6]),(0,[z0,z2,z4,z5,z561,z8,z6]),(0,[z0,z2,z4,z5,z562,z8,z6]),(0,[z0,z2,z4,z45,z5,z8,z35]),(0,[z0,z2,z4,z5,z563,z8,z6]),(0,[z0,z2,z4,z137,z5,z8,z42]),(0,[z143,z564,z2,z4,z5,z8,z6]),(0,[z0,z2,z231,z4,z5,z8,z6])],[(0,[z0,z2,z4,z5,z63,z8,z35]),(1,[z0,z207,z4,z137,z8,z6]),(0,[z0,z2,z4,z5,z565,z8,z6]),(0,[z0,z2,z4,z5,z566,z8,z6])],[(0,[z0,z2,z4,z45,z5,z8,z6]),(0,[z0,z2,z4,z567,z5,z8,z6]),(0,[z0,z2,z4,z568,z5,z8,z6]),(0,[z0,z569,z2,z4,z5,z8,z6])],[(0,[z105,z2,z54,z4,z5,z8,z6]),(0,[z0,z2,z4,z570,z5,z8,z6]),(0,[z0,z2,z4,z5,z63,z8,z6]),(0,[z0,z2,z4,z5,z8,z258,z6]),(0,[z0,z2,z4,z5,z8,z196,z6]),(1,[z0,z2,z4,z74,z8,z42])],[(0,[z571,z0,z2,z4,z5,z8,z6]),(0,[z572,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z234,z8,z42]),(0,[z0,z2,z4,z5,z8,z6,z573]),(0,[z574,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z277,z4,z5,z8,z6])]],
   [[(1,[z0,z2,z4,z5,z458,z6]),(0,[z97,z0,z2,z4,z5,z8,z35]),(0,[z79,z0,z2,z5,z8,z16,z6]),(0,[z0,z205,z2,z4,z5,z8,z42]),(1,[z0,z2,z4,z5,z8,z575])],[(0,[z0,z145,z207,z4,z5,z8,z6]),(0,[z12,z55,z2,z4,z5,z8,z6]),(0,[z97,z0,z2,z83,z4,z5,z8]),(0,[z0,z2,z576,z4,z5,z8,z6]),(1,[z0,z2,z4,z5,z8,z577]),(0,[z0,z2,z3,z4,z5,z8,z42])],[(0,[z578,z0,z2,z4,z5,z8,z6]),(0,[z579,z0,z2,z4,z5,z8,z6]),(0,[z97,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z580,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z581,z6]),(0,[z0,z2,z4,z142,z81,z8,z6])],[(0,[z0,z2,z582,z4,z5,z8,z6]),(0,[z0,z2,z117,z4,z5,z8,z35]),(1,[z281,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z213]),(0,[z0,z2,z4,z74,z5,z8,z6])],[(0,[z129,z2,z4,z45,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z583,z6]),(0,[z251,z2,z4,z45,z5,z8,z6]),(0,[z584,z0,z2,z4,z5,z8,z6]),(1,[z49,z2,z4,z5,z8,z27]),(0,[z0,z2,z4,z137,z5,z8,z333]),(0,[z0,z2,z4,z5,z235,z8,z16]),(0,[z0,z2,z4,z5,z8,z356,z6]),(0,[z0,z2,z4,z5,z8,z156,z6]),(0,[z585,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z82,z4,z5,z8,z42])],[(0,[z85,z0,z2,z4,z5,z8,z42]),(0,[z0,z2,z117,z4,z5,z8,z6]),(1,[z0,z2,z240,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z586]),(0,[z0,z2,z4,z5,z8,z587,z6])],[(0,[z0,z2,z89,z4,z5,z8,z35]),(0,[z0,z2,z5,z41,z8,z38,z6]),(0,[z0,z2,z4,z5,z8,z588,z6])],[(0,[z589,z0,z2,z4,z5,z8,z6]),(1,[z0,z479,z4,z5,z8,z6]),(0,[z204,z101,z0,z2,z4,z5,z8]),(0,[z0,z2,z4,z590,z5,z8,z6]),(0,[z143,z28,z2,z4,z5,z8,z6]),(0,[z143,z0,z2,z4,z5,z90,z6]),(0,[z101,z0,z2,z4,z5,z8,z35]),(0,[z0,z2,z4,z96,z5,z8,z35])]],
   [[(0,[z0,z2,z89,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z295,z8,z34]),(0,[z0,z2,z4,z5,z8,z591,z6]),(0,[z0,z2,z4,z592,z5,z8,z6]),(0,[z0,z2,z231,z4,z142,z8,z6])],[(0,[z0,z2,z4,z5,z8,z593,z6]),(0,[z205,z2,z31,z4,z5,z8,z6]),(0,[z594,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z62,z5,z245,z6]),(0,[z0,z2,z4,z96,z5,z8,z6])],[(0,[z0,z2,z595,z4,z5,z8,z6]),(0,[z0,z2,z4,z191,z5,z8,z6]),(0,[z0,z2,z4,z596,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z597]),(0,[z0,z2,z231,z4,z5,z8,z156]),(1,[z0,z2,z4,z8,z42,z35]),(0,[z0,z2,z4,z5,z8,z598,z6]),(0,[z0,z599,z2,z4,z5,z8,z6])],[(0,[z600,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z601,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z575,z6]),(0,[z602,z0,z2,z4,z5,z8,z6])],[(0,[z603,z0,z2,z4,z5,z8,z6]),(0,[z162,z0,z2,z4,z29,z8,z6]),(0,[z0,z2,z4,z5,z140,z8,z42]),(0,[z0,z2,z4,z5,z8,z6,z604])],[(0,[z0,z2,z4,z5,z605,z8,z6]),(0,[z0,z2,z4,z62,z5,z8,z258]),(0,[z198,z0,z2,z4,z5,z8,z35])],[(0,[z0,z2,z4,z606,z5,z8,z6]),(0,[z0,z2,z607,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z608,z8,z6]),(0,[z0,z2,z4,z29,z5,z8,z35]),(0,[z0,z2,z4,z5,z8,z6,z609]),(0,[z0,z2,z4,z5,z8,z35,z610])],[(0,[z129,z162,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z611,z5,z8,z6]),(0,[z0,z2,z4,z5,z34,z90,z6]),(0,[z0,z2,z612,z4,z5,z8,z6]),(0,[z136,z0,z2,z4,z5,z8,z577]),(0,[z64,z0,z2,z5,z41,z8,z6]),(0,[z198,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z613,z5,z8,z6])]],
   [[(0,[z614,z0,z2,z4,z5,z8,z6]),(0,[z49,z2,z54,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z615,z8,z6]),(0,[z0,z2,z4,z29,z5,z8,z6]),(0,[z0,z2,z4,z5,z616,z8,z6]),(0,[z0,z2,z4,z309,z5,z8,z6]),(0,[z0,z23,z2,z5,z41,z8,z6]),(0,[z0,z2,z4,z5,z8,z508,z6]),(0,[z0,z2,z4,z5,z617,z8,z6])],[(0,[z0,z2,z89,z5,z118,z8,z6]),(0,[z0,z2,z4,z5,z8,z34,z35]),(0,[z0,z2,z618,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z619,z6]),(0,[z620,z0,z2,z4,z5,z8,z35])],[(0,[z251,z0,z2,z4,z5,z8,z35]),(0,[z621,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z65,z4,z5,z8,z42])],[(0,[z0,z2,z4,z5,z8,z622,z6]),(0,[z0,z2,z4,z5,z8,z6,z623]),(0,[z97,z0,z2,z4,z5,z8,z13]),(0,[z64,z0,z2,z117,z5,z8,z6]),(0,[z0,z2,z4,z5,z37,z8,z6]),(0,[z620,z0,z2,z4,z5,z8,z6])],[(0,[z251,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z624,z8,z6]),(0,[z0,z2,z4,z5,z8,z625,z6]),(0,[z0,z2,z4,z5,z71,z41,z8]),(0,[z0,z2,z4,z5,z8,z388,z35]),(0,[z626,z0,z2,z4,z5,z8,z6])],[(0,[z0,z2,z190,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z627,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z610]),(0,[z0,z2,z4,z5,z8,z628,z6])],[(0,[z0,z629,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z142,z5,z81,z6]),(0,[z0,z2,z630,z4,z5,z8,z6])],[(0,[z0,z145,z2,z4,z5,z8,z42]),(0,[z0,z2,z4,z5,z8,z631,z6]),(0,[z0,z2,z4,z5,z632,z8,z6]),(0,[z76,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z633]),(0,[z281,z0,z2,z4,z5,z8,z6]),(0,[z143,z0,z2,z4,z5,z8,z35]),(1,[z2,z4,z5,z8,z202,z35])]],
   [[(0,[z2,z54,z4,z5,z135,z8,z6]),(0,[z0,z2,z4,z5,z8,z634,z6]),(0,[z0,z145,z2,z4,z5,z8,z307]),(0,[z0,z2,z45,z5,z118,z8,z6]),(0,[z0,z635,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z441,z6]),(0,[z0,z2,z203,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z636,z6]),(0,[z0,z2,z4,z5,z8,z46,z25]),(1,[z0,z2,z3,z5,z41,z6]),(0,[z0,z2,z637,z4,z5,z8,z6])],[(0,[z0,z2,z4,z5,z638,z8,z6]),(0,[z0,z2,z4,z5,z8,z639,z6]),(0,[z0,z2,z4,z5,z8,z307,z6]),(0,[z0,z2,z4,z5,z640,z8,z6]),(1,[z0,z2,z4,z5,z8,z524]),(0,[z0,z2,z4,z5,z8,z6,z641]),(0,[z143,z0,z2,z4,z5,z8,z6])],[(0,[z12,z0,z2,z4,z135,z8,z6]),(0,[z0,z2,z642,z4,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z6,z643]),(0,[z0,z2,z4,z5,z458,z8,z6]),(0,[z0,z2,z4,z5,z644,z8,z6]),(0,[z0,z2,z4,z62,z137,z8,z6]),(1,[z0,z2,z4,z5,z8,z282])],[(0,[z0,z2,z4,z5,z645,z8,z6]),(0,[z55,z129,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z646,z5,z8,z6]),(0,[z0,z2,z4,z647,z5,z8,z6]),(0,[z648,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z5,z8,z42])],[(0,[z649,z0,z2,z4,z5,z8,z6]),(0,[z129,z2,z4,z5,z135,z8,z6]),(0,[z0,z2,z4,z5,z650,z8,z6]),(0,[z0,z2,z4,z5,z651,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z577]),(0,[z652,z0,z2,z4,z5,z8,z6]),(1,[z87,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z62,z5,z8,z35])],[(1,[z0,z2,z4,z332,z5,z6]),(0,[z653,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z654,z8,z6]),(0,[z101,z0,z2,z4,z5,z8,z26]),(0,[z101,z0,z2,z4,z5,z32,z8]),(0,[z0,z2,z231,z4,z5,z81,z6]),(0,[z0,z2,z4,z655,z5,z8,z6])],[(0,[z12,z0,z2,z4,z5,z8,z35]),(0,[z0,z2,z4,z62,z5,z8,z6]),(0,[z0,z2,z656,z4,z5,z8,z6]),(0,[z0,z2,z5,z8,z46,z6,z213]),(0,[z0,z2,z4,z5,z8,z42,z588]),(0,[z360,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z657,z4,z5,z8,z6])]],
   [[(0,[z0,z658,z2,z4,z5,z8,z6]),(0,[z0,z2,z117,z5,z8,z38,z6]),(0,[z461,z2,z4,z5,z63,z8,z6]),(1,[z198,z2,z4,z5,z8,z35]),(0,[z0,z2,z659,z4,z5,z8,z6])],[(0,[z12,z0,z2,z4,z5,z8,z6]),(0,[z12,z0,z106,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z660]),(0,[z661,z0,z2,z4,z5,z8,z6]),(1,[z0,z2,z4,z5,z547,z6]),(1,[z408,z2,z4,z5,z8,z6]),(0,[z101,z0,z2,z4,z5,z8,z46]),(0,[z0,z2,z4,z5,z8,z662,z6])],[(0,[z0,z2,z54,z4,z5,z8,z42]),(0,[z0,z2,z4,z5,z8,z663,z6]),(0,[z19,z0,z2,z5,z41,z8,z6]),(0,[z143,z0,z2,z5,z118,z8,z6]),(1,[z198,z2,z4,z5,z8,z6])],[(0,[z0,z408,z2,z4,z5,z8,z6])],[(0,[z0,z664,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z665,z8,z6]),(0,[z204,z0,z205,z4,z5,z8,z6]),(0,[z0,z2,z65,z4,z5,z8,z356]),(0,[z0,z2,z4,z142,z5,z90,z6]),(0,[z0,z2,z4,z5,z666,z8,z6])],[(0,[z0,z2,z4,z5,z8,z667,z6]),(0,[z0,z2,z4,z5,z235,z8,z6]),(0,[z87,z0,z2,z4,z5,z8,z6]),(1,[z64,z0,z2,z62,z8,z6]),(1,[z0,z2,z4,z96,z8,z35]),(0,[z0,z2,z4,z668,z5,z8,z6])],[(0,[z105,z2,z89,z4,z5,z8,z6]),(0,[z0,z2,z4,z24,z5,z8,z42]),(0,[z0,z189,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z669,z8,z6])],[(0,[z670,z0,z2,z4,z5,z8,z6]),(0,[z12,z2,z4,z5,z8,z34,z6]),(0,[z0,z2,z4,z5,z192,z8,z6]),(0,[z0,z2,z4,z5,z671,z8,z6])]],
   [[(0,[z0,z2,z672,z4,z5,z8,z6])],[(0,[z286,z0,z2,z4,z5,z8,z35]),(0,[z0,z2,z673,z4,z5,z8,z6]),(0,[z0,z2,z674,z4,z5,z8,z6])],[(0,[z0,z2,z675,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z676,z8,z6]),(1,[z0,z2,z4,z5,z8,z347]),(0,[z204,z0,z2,z83,z4,z5,z8]),(0,[z0,z2,z4,z5,z140,z6,z26])],[(0,[z286,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z677,z8,z6]),(0,[z0,z2,z4,z5,z245,z8,z6]),(0,[z678,z0,z2,z4,z5,z8,z35])],[(0,[z679,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z81,z56,z6]),(0,[z0,z23,z2,z4,z5,z8,z35]),(0,[z0,z2,z4,z5,z8,z6,z680]),(0,[z0,z681,z2,z4,z5,z8,z6]),(1,[z0,z2,z4,z5,z140,z26])],[(0,[z0,z2,z4,z5,z8,z682,z6]),(0,[z0,z683,z2,z4,z5,z8,z6]),(0,[z678,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z35,z684])],[(0,[z105,z2,z4,z29,z5,z8,z6]),(0,[z0,z23,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z513,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z685]),(0,[z0,z2,z3,z4,z5,z8,z575]),(0,[z0,z686,z2,z4,z5,z8,z35])],[(0,[z0,z2,z687,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z688,z8,z6]),(0,[z136,z0,z2,z4,z5,z547,z6]),(0,[z461,z0,z2,z4,z5,z8,z6]),(0,[z36,z0,z4,z5,z8,z16,z6]),(0,[z143,z0,z2,z4,z5,z38,z6])]],
   [[(0,[z0,z689,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z690]),(1,[z0,z2,z4,z5,z295,z8]),(0,[z0,z686,z2,z4,z5,z8,z6]),(1,[z564,z2,z4,z5,z8,z6]),(0,[z0,z691,z2,z4,z5,z8,z6])],[(0,[z0,z2,z479,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z692,z6]),(0,[z0,z2,z4,z5,z8,z6,z437])],[(0,[z12,z0,z2,z161,z5,z8,z6]),(0,[z693,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z142,z137,z8,z6]),(0,[z0,z2,z694,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z81,z234,z6]),(0,[z228,z0,z2,z4,z5,z8,z6]),(0,[z64,z0,z2,z62,z5,z8,z6]),(0,[z0,z564,z2,z4,z5,z8,z6])],[(0,[z0,z2,z4,z5,z695,z8,z6]),(0,[z0,z4,z137,z5,z63,z8,z6]),(0,[z0,z2,z4,z5,z8,z15,z6]),(0,[z64,z0,z2,z4,z118,z8,z6]),(0,[z696,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z540,z42])],[(0,[z162,z2,z54,z4,z5,z8,z6]),(0,[z0,z2,z4,z697,z5,z8,z6]),(0,[z0,z2,z4,z698,z5,z8,z6]),(0,[z0,z1,z2,z4,z5,z234,z6]),(0,[z0,z2,z4,z5,z8,z6,z684]),(0,[z0,z2,z4,z5,z8,z38,z42]),(0,[z0,z2,z4,z142,z5,z8,z35])],[(0,[z699,z0,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z524]),(0,[z0,z2,z4,z700,z5,z8,z6]),(0,[z0,z2,z4,z701,z5,z8,z6]),(0,[z0,z2,z4,z702,z5,z8,z6]),(0,[z101,z0,z2,z5,z8,z6,z213]),(0,[z0,z2,z236,z4,z5,z8,z6])],[(1,[z286,z54,z4,z5,z8,z6]),(1,[z105,z2,z89,z5,z8,z6]),(0,[z12,z0,z2,z4,z5,z8,z225]),(0,[z19,z69,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z703]),(0,[z0,z2,z4,z142,z5,z8,z6])],[(0,[z0,z2,z4,z704,z5,z8,z6]),(0,[z0,z2,z705,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z6,z282]),(0,[z0,z2,z706,z4,z5,z8,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z127,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z707,z5,z8]),(0,[z0,z117,z708,z5,z8,z6]),(0,[z2,z4,z5,z8,z6,z709]),(0,[z64,z0,z2,z17,z8,z6]),(0,[z0,z2,z4,z710,z90,z6])],[(0,[z0,z711,z4,z5,z8,z6]),(0,[z12,z2,z4,z5,z295,z8]),(0,[z0,z2,z4,z646,z8,z35]),(0,[z712,z2,z4,z5,z8,z6]),(0,[z620,z0,z2,z4,z5,z498])],[(0,[z0,z2,z4,z5,z8,z713]),(0,[z0,z2,z4,z5,z8,z714]),(0,[z0,z2,z4,z5,z8,z715]),(0,[z502,z0,z2,z5,z38,z6]),(0,[z304,z2,z4,z5,z8,z42]),(0,[z0,z2,z4,z37,z234,z6])],[(0,[z0,z2,z4,z5,z716,z6]),(0,[z0,z2,z239,z5,z547,z6]),(0,[z0,z2,z4,z5,z8,z717]),(0,[z718,z0,z2,z4,z5,z8]),(0,[z0,z2,z4,z5,z719,z8]),(0,[z720,z2,z4,z5,z8,z6])],[(0,[z0,z2,z721,z5,z8,z6]),(0,[z0,z722,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z458,z225]),(0,[z461,z2,z4,z5,z8,z42])],[(0,[z0,z2,z4,z723,z8,z6]),(0,[z479,z4,z5,z8,z34,z6]),(1,[z2,z4,z5,z8,z724]),(0,[z49,z2,z4,z5,z8,z308]),(0,[z36,z0,z203,z4,z5,z16]),(0,[z204,z0,z4,z5,z8,z211]),(0,[z0,z2,z3,z5,z41,z35]),(0,[z0,z2,z83,z5,z8,z604])],[(0,[z0,z725,z4,z5,z8,z6]),(0,[z0,z503,z4,z137,z8,z6]),(0,[z0,z2,z4,z654,z8,z42]),(0,[z0,z2,z726,z4,z5,z8])],[(0,[z0,z479,z161,z5,z8,z6]),(0,[z0,z2,z4,z727,z8,z6]),(0,[z198,z2,z4,z5,z8,z25]),(0,[z0,z2,z3,z5,z41,z6]),(0,[z728,z2,z4,z5,z8,z6])]],
   [[(0,[z105,z2,z219,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z524]),(0,[z85,z2,z4,z5,z295,z34]),(0,[z0,z2,z4,z5,z8,z729]),(0,[z0,z2,z128,z37,z8,z6]),(0,[z602,z0,z4,z5,z8,z47]),(0,[z281,z2,z4,z5,z140,z8])],[(0,[z0,z2,z730,z4,z5,z8]),(0,[z105,z2,z306,z5,z8,z6]),(0,[z0,z2,z4,z5,z731,z6]),(0,[z0,z2,z4,z5,z8,z732]),(0,[z0,z2,z161,z5,z8,z35]),(0,[z0,z2,z4,z137,z168,z6]),(0,[z0,z2,z630,z5,z8,z46])],[(0,[z733,z0,z2,z4,z5,z8]),(0,[z49,z531,z2,z4,z5,z8]),(0,[z734,z2,z4,z5,z8,z6]),(0,[z36,z0,z253,z4,z5,z6]),(0,[z0,z2,z4,z5,z258,z168]),(0,[z217,z0,z2,z5,z8,z196]),(0,[z0,z686,z4,z5,z8,z437])],[(0,[z55,z2,z4,z5,z645,z6]),(0,[z0,z2,z4,z5,z735,z6]),(0,[z0,z2,z161,z5,z8,z6]),(0,[z0,z106,z161,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z736]),(0,[z0,z2,z4,z5,z8,z737]),(0,[z0,z2,z4,z428,z8,z35]),(0,[z0,z2,z4,z5,z8,z738]),(0,[z0,z2,z4,z5,z168,z35]),(0,[z0,z2,z4,z5,z710,z6]),(0,[z174,z2,z4,z5,z8,z262])],[(0,[z0,z2,z4,z5,z739,z8]),(0,[z0,z2,z4,z5,z740,z6]),(0,[z0,z2,z190,z5,z8,z524]),(0,[z0,z2,z741,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z742]),(0,[z743,z2,z4,z5,z8,z6]),(0,[z0,z2,z239,z5,z8,z508]),(0,[z36,z189,z4,z5,z16,z6]),(0,[z744,z2,z4,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z745]),(0,[z12,z2,z4,z135,z458,z6]),(0,[z746,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z168,z6]),(0,[z564,z2,z4,z5,z90,z6])],[(0,[z183,z2,z513,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z747]),(0,[z0,z2,z240,z171,z8,z6]),(0,[z408,z2,z4,z5,z8,z35]),(0,[z143,z0,z2,z5,z748,z6]),(0,[z0,z2,z4,z5,z749,z8]),(0,[z0,z2,z750,z5,z8,z35]),(0,[z0,z2,z236,z5,z8,z223])],[(0,[z281,z2,z4,z5,z8,z47]),(0,[z751,z2,z4,z5,z8,z35])]],
   [[(0,[z2,z54,z4,z5,z8,z307]),(0,[z2,z752,z45,z5,z8,z6]),(0,[z408,z2,z4,z5,z8,z6]),(0,[z87,z2,z190,z5,z8,z6]),(0,[z19,z497,z24,z5,z8,z6]),(0,[z143,z0,z2,z5,z38,z42]),(0,[z0,z2,z750,z5,z8,z6]),(0,[z753,z2,z4,z5,z8,z42])],[(0,[z49,z2,z4,z5,z8,z60]),(0,[z751,z2,z4,z5,z8,z6]),(0,[z754,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z755]),(0,[z189,z2,z4,z5,z8,z35]),(0,[z0,z2,z128,z5,z8,z42]),(0,[z0,z2,z231,z4,z42,z90])],[(0,[z0,z2,z4,z400,z8,z42]),(0,[z138,z0,z2,z4,z191,z5]),(0,[z0,z2,z4,z5,z441,z508]),(0,[z2,z4,z5,z192,z8,z35]),(0,[z0,z2,z4,z5,z8,z756]),(0,[z79,z0,z1,z2,z5,z6]),(0,[z64,z0,z2,z62,z8,z35]),(1,[z0,z2,z4,z5,z719])],[(0,[z189,z2,z4,z5,z8,z6]),(0,[z251,z2,z752,z5,z8,z6]),(0,[z0,z2,z4,z309,z8,z42]),(0,[z0,z2,z513,z5,z441,z6])],[(0,[z162,z2,z4,z386,z8,z6]),(0,[z12,z479,z4,z135,z8,z6]),(0,[z0,z2,z757,z5,z8,z6]),(0,[z64,z0,z2,z62,z8,z6])],[(0,[z0,z2,z758,z5,z8,z6]),(0,[z759,z2,z4,z5,z8,z6]),(0,[z138,z0,z2,z5,z38,z6]),(0,[z36,z0,z240,z5,z16,z6]),(0,[z0,z2,z4,z5,z760,z6]),(0,[z0,z2,z4,z5,z761,z8])],[(0,[z2,z4,z762,z135,z8,z6]),(0,[z304,z2,z4,z5,z8,z508]),(0,[z79,z0,z2,z5,z81,z6]),(0,[z0,z2,z4,z5,z170,z398])],[(0,[z479,z4,z5,z8,z13,z6]),(0,[z0,z2,z117,z57,z8,z6]),(0,[z304,z2,z513,z5,z8,z6]),(0,[z0,z2,z4,z5,z763,z8])]],
   [[(0,[z0,z2,z4,z5,z8,z764]),(0,[z0,z2,z765,z5,z8,z6]),(0,[z766,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z767]),(0,[z0,z2,z4,z142,z710,z6]),(0,[z198,z2,z82,z4,z5,z8])],[(0,[z251,z2,z45,z5,z8,z42]),(0,[z80,z2,z4,z5,z458,z6]),(0,[z0,z2,z4,z5,z8,z768]),(0,[z769,z2,z4,z5,z8,z6]),(0,[z0,z2,z513,z5,z8,z42]),(0,[z770,z2,z4,z5,z8,z6]),(0,[z217,z0,z2,z5,z8,z42])],[(0,[z0,z2,z4,z5,z8,z771]),(0,[z772,z2,z4,z5,z8,z6]),(0,[z0,z559,z4,z137,z8,z6]),(0,[z0,z4,z5,z760,z16,z6]),(0,[z64,z0,z2,z773,z8,z6]),(0,[z0,z2,z62,z773,z8,z6])],[(0,[z433,z54,z4,z5,z8,z6]),(0,[z2,z4,z45,z5,z121,z6]),(0,[z0,z2,z4,z5,z774,z8]),(0,[z497,z2,z4,z5,z8,z221]),(0,[z0,z2,z775,z5,z8,z6]),(0,[z776,z2,z4,z5,z8,z6]),(0,[z0,z2,z128,z5,z16,z6]),(0,[z0,z2,z4,z5,z8,z777]),(0,[z0,z2,z4,z5,z140,z26])],[(0,[z0,z2,z4,z5,z8,z778]),(0,[z79,z0,z2,z5,z235,z8])],[(0,[z0,z2,z4,z5,z8,z779]),(0,[z0,z2,z4,z5,z780,z6]),(0,[z0,z2,z4,z5,z781,z6]),(0,[z19,z0,z191,z24,z5,z8]),(0,[z0,z2,z4,z5,z8,z782]),(0,[z0,z2,z4,z5,z8,z783]),(0,[z564,z2,z4,z5,z8,z35]),(0,[z0,z2,z3,z5,z748,z6]),(0,[z2,z4,z5,z8,z784,z35])],[(0,[z497,z2,z4,z5,z229,z6]),(0,[z0,z2,z5,z8,z15,z42]),(1,[z0,z2,z773,z8,z6]),(0,[z2,z4,z5,z254,z8,z42])],[(0,[z251,z160,z2,z45,z5,z8]),(0,[z564,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z785,z8,z6]),(0,[z0,z2,z786,z4,z5,z8]),(0,[z0,z2,z4,z171,z8,z42]),(0,[z648,z0,z4,z5,z16,z6]),(0,[z0,z2,z231,z4,z90,z232])]],
   [[(0,[z0,z2,z4,z414,z8,z35]),(0,[z2,z4,z5,z8,z13,z524]),(0,[z0,z2,z4,z5,z8,z724]),(0,[z49,z2,z4,z5,z8,z262]),(0,[z0,z2,z4,z57,z8,z221]),(0,[z0,z2,z4,z5,z787,z6]),(0,[z788,z564,z2,z4,z5,z8]),(0,[z228,z0,z2,z5,z8,z588])],[(0,[z0,z2,z4,z5,z789,z6]),(0,[z0,z2,z4,z5,z8,z790]),(0,[z0,z2,z4,z5,z8,z791]),(0,[z36,z79,z0,z2,z5,z6]),(0,[z0,z2,z203,z5,z8,z15]),(0,[z0,z2,z4,z5,z8,z792])],[(0,[z0,z2,z793,z5,z8,z6]),(1,[z2,z4,z5,z794,z6]),(0,[z0,z4,z795,z63,z8,z6]),(1,[z0,z2,z5,z748,z6])],[(0,[z286,z54,z4,z5,z8,z35]),(0,[z105,z2,z89,z5,z8,z35]),(0,[z0,z2,z796,z5,z8,z6]),(0,[z0,z2,z4,z57,z229,z6]),(0,[z0,z2,z4,z5,z8,z797]),(0,[z0,z2,z10,z137,z8,z6]),(0,[z0,z2,z4,z5,z235,z8]),(0,[z0,z2,z4,z8,z418,z35]),(0,[z285,z0,z4,z5,z8,z47]),(0,[z2,z4,z5,z8,z6,z798])],[(0,[z0,z2,z799,z4,z5,z8]),(0,[z80,z2,z4,z5,z34,z6]),(0,[z2,z4,z5,z800,z8,z6])],[(0,[z286,z54,z4,z5,z8,z6]),(0,[z2,z4,z5,z801,z8,z6]),(0,[z105,z2,z89,z5,z8,z6]),(0,[z802,z0,z2,z5,z8,z6]),(0,[z803,z2,z4,z5,z8,z6]),(0,[z804,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z245,z35]),(0,[z0,z2,z10,z5,z8,z35])],[(0,[z0,z2,z4,z5,z805,z6]),(0,[z0,z2,z4,z5,z8,z806]),(0,[z12,z2,z4,z135,z8,z524]),(0,[z0,z2,z807,z5,z8,z6]),(0,[z198,z2,z4,z5,z8,z27]),(0,[z143,z0,z2,z57,z8,z6]),(0,[z0,z2,z239,z5,z8,z577]),(0,[z808,z2,z4,z5,z8,z6]),(0,[z0,z2,z264,z5,z8,z213])],[(0,[z0,z479,z4,z5,z121,z6]),(0,[z19,z138,z0,z24,z5,z6]),(0,[z0,z2,z4,z5,z809,z8]),(0,[z0,z2,z4,z810,z5,z8]),(0,[z0,z2,z4,z5,z245,z6]),(0,[z0,z2,z10,z5,z8,z6]),(0,[z198,z2,z4,z5,z140,z8])]],
   [[(0,[z2,z190,z45,z5,z8,z6]),(0,[z811,z0,z2,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z249]),(0,[z0,z2,z812,z4,z5,z8]),(0,[z2,z31,z4,z5,z8,z35]),(0,[z564,z2,z5,z118,z8,z6]),(0,[z0,z2,z4,z5,z8,z813]),(0,[z0,z2,z4,z142,z81,z35])],[(0,[z0,z2,z4,z5,z121,z35]),(0,[z0,z2,z4,z5,z8,z21]),(0,[z0,z2,z4,z171,z8,z814]),(0,[z0,z2,z815,z5,z8,z6]),(0,[z816,z217,z2,z5,z8,z6]),(0,[z0,z2,z4,z5,z817,z8])],[(0,[z2,z31,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z818]),(0,[z136,z0,z4,z63,z8,z35]),(0,[z0,z2,z819,z5,z8,z6]),(0,[z0,z2,z4,z142,z81,z6])],[(0,[z28,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z121,z6]),(0,[z0,z106,z4,z5,z121,z6]),(0,[z497,z2,z4,z5,z8,z42]),(0,[z0,z2,z4,z57,z8,z20]),(0,[z0,z2,z4,z5,z820,z6]),(0,[z281,z2,z4,z5,z8,z25]),(0,[z0,z2,z4,z5,z8,z258])],[(0,[z0,z2,z4,z5,z8,z821]),(0,[z136,z183,z4,z63,z8,z6]),(0,[z136,z0,z4,z63,z8,z6]),(0,[z0,z2,z4,z5,z441,z577]),(0,[z0,z2,z128,z171,z8,z6]),(0,[z0,z2,z773,z5,z8,z6])],[(0,[z0,z2,z4,z822,z8,z6]),(0,[z0,z2,z4,z5,z823,z8]),(0,[z0,z2,z33,z4,z5,z8]),(0,[z244,z0,z24,z5,z8,z6]),(0,[z0,z2,z4,z5,z824,z8]),(0,[z0,z2,z513,z5,z8,z508]),(0,[z0,z207,z4,z137,z8,z42]),(0,[z36,z0,z4,z5,z760,z6]),(0,[z0,z2,z825,z4,z5,z8])],[(0,[z2,z725,z4,z5,z8,z6]),(0,[z160,z2,z54,z4,z5,z8]),(0,[z0,z2,z4,z5,z8,z826]),(0,[z55,z2,z161,z5,z8,z6]),(0,[z0,z827,z4,z5,z8,z6]),(0,[z127,z2,z4,z5,z8,z249]),(0,[z198,z2,z4,z5,z8,z47]),(0,[z828,z2,z4,z5,z8,z6]),(0,[z829,z2,z4,z5,z254,z8]),(0,[z0,z2,z4,z617,z8,z35])],[(0,[z0,z2,z4,z5,z830,z6]),(0,[z831,z2,z4,z5,z8,z6])]],
   [[(0,[z0,z2,z832,z5,z8,z6]),(0,[z483,z2,z4,z29,z8,z6]),(0,[z0,z2,z4,z5,z833,z6]),(0,[z304,z2,z4,z5,z8,z577]),(0,[z0,z2,z4,z5,z8,z834]),(0,[z835,z2,z4,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z836]),(0,[z0,z2,z837,z5,z8,z6]),(0,[z0,z2,z4,z5,z458,z42]),(0,[z69,z2,z4,z5,z8,z35]),(0,[z0,z2,z838,z4,z5,z8]),(0,[z0,z2,z4,z5,z719,z140])],[(0,[z0,z839,z4,z5,z8,z6]),(0,[z0,z2,z840,z5,z8,z6]),(0,[z0,z2,z4,z7,z8,z42])],[(0,[z0,z2,z4,z5,z8,z67]),(0,[z69,z2,z4,z5,z8,z6]),(0,[z0,z841,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z842]),(0,[z0,z2,z4,z5,z843,z6]),(0,[z19,z76,z0,z24,z5,z8]),(0,[z844,z2,z4,z5,z8,z6]),(0,[z0,z2,z845,z5,z8,z6]),(0,[z36,z0,z128,z5,z16,z6]),(0,[z0,z2,z4,z37,z8,z846]),(0,[z0,z2,z83,z353,z5,z8]),(0,[z2,z4,z5,z847,z8,z6]),(0,[z0,z2,z4,z5,z8,z848]),(0,[z0,z2,z4,z8,z456,z35])],[(0,[z0,z2,z4,z5,z849,z6]),(0,[z850,z2,z4,z5,z8,z6]),(0,[z281,z2,z4,z5,z8,z42]),(0,[z851,z2,z4,z5,z8,z6]),(0,[z2,z852,z4,z5,z8,z42])],[(0,[z0,z2,z4,z5,z8,z853]),(0,[z0,z2,z4,z5,z8,z854])],[(0,[z0,z2,z855,z5,z8,z6]),(0,[z49,z2,z4,z5,z8,z586]),(0,[z79,z0,z2,z5,z8,z6]),(0,[z183,z2,z4,z5,z441,z6]),(0,[z0,z2,z240,z5,z8,z42]),(0,[z0,z4,z5,z8,z760,z6])],[(0,[z0,z2,z4,z5,z8,z20]),(0,[z0,z2,z4,z5,z8,z856]),(0,[z0,z2,z82,z4,z5,z719])]],
   [[(0,[z461,z479,z4,z5,z8,z6]),(0,[z0,z479,z4,z5,z8,z42]),(0,[z2,z4,z5,z8,z13,z724]),(0,[z138,z0,z2,z5,z118,z6]),(0,[z857,z2,z4,z5,z8,z6]),(0,[z858,z2,z4,z5,z8,z6]),(0,[z859,z0,z2,z5,z8,z6])],[(0,[z0,z2,z860,z5,z8,z6]),(0,[z0,z2,z4,z5,z861,z6]),(0,[z0,z2,z4,z862,z5,z8]),(0,[z143,z564,z2,z5,z38,z6]),(0,[z0,z2,z4,z5,z8,z863])],[(0,[z0,z2,z4,z5,z8,z864]),(0,[z12,z2,z4,z381,z8,z6]),(0,[z2,z161,z5,z8,z34,z6]),(0,[z85,z2,z4,z5,z794,z6]),(0,[z0,z2,z4,z5,z8,z865]),(0,[z497,z2,z4,z309,z8,z6]),(0,[z0,z2,z866,z5,z8,z6]),(0,[z36,z0,z4,z5,z16,z347])],[(0,[z0,z2,z4,z5,z8,z35]),(0,[z0,z2,z4,z5,z8,z867]),(0,[z0,z106,z4,z5,z8,z35]),(0,[z0,z2,z4,z5,z8,z868]),(0,[z869,z0,z2,z4,z5,z8]),(0,[z0,z2,z4,z5,z71,z8]),(0,[z0,z2,z4,z5,z870,z8]),(0,[z871,z2,z4,z5,z8,z35]),(0,[z0,z2,z4,z8,z42,z872])],[(0,[z0,z2,z4,z873,z8,z6]),(0,[z0,z2,z161,z5,z121,z6]),(0,[z0,z2,z874,z5,z8,z6]),(0,[z0,z2,z875,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z876]),(0,[z0,z2,z4,z5,z877,z6]),(0,[z0,z248,z4,z5,z8,z540])],[(0,[z0,z2,z4,z5,z8,z6]),(0,[z0,z106,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z878]),(0,[z0,z479,z190,z5,z8,z6]),(0,[z0,z2,z4,z5,z794,z6]),(0,[z97,z2,z4,z5,z8,z685])],[(0,[z155,z54,z4,z5,z8,z6]),(0,[z0,z879,z4,z5,z8,z6]),(0,[z880,z2,z4,z5,z8,z6]),(0,[z0,z2,z881,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z882]),(0,[z0,z2,z5,z8,z6,z883])],[(0,[z0,z2,z190,z5,z8,z35]),(0,[z0,z2,z4,z5,z8,z884]),(0,[z0,z2,z4,z5,z8,z885]),(0,[z0,z2,z4,z417,z90,z6]),(0,[z0,z2,z4,z8,z662,z35])]],
   [[(0,[z2,z4,z29,z5,z8,z307]),(0,[z0,z2,z4,z5,z8,z886]),(0,[z0,z2,z887,z4,z5,z8]),(0,[z0,z2,z4,z5,z8,z888]),(0,[z0,z205,z657,z4,z5,z8]),(0,[z0,z2,z4,z889,z5,z8])],[(0,[z0,z2,z190,z5,z8,z6]),(0,[z0,z106,z190,z5,z8,z6]),(0,[z189,z2,z4,z5,z8,z249]),(0,[z64,z0,z2,z62,z245,z6]),(0,[z0,z2,z4,z5,z8,z890])],[(0,[z0,z2,z4,z5,z8,z891]),(0,[z0,z2,z892,z5,z8,z6]),(0,[z0,z2,z4,z57,z8,z893]),(0,[z894,z2,z4,z5,z8,z6]),(0,[z514,z0,z2,z5,z8,z213])],[(0,[z0,z2,z5,z8,z895,z6]),(0,[z0,z2,z4,z5,z8,z896]),(0,[z0,z2,z470,z118,z8,z6]),(0,[z897,z2,z4,z5,z8,z6])],[(0,[z2,z4,z29,z8,z6,z660]),(0,[z244,z0,z4,z63,z8,z6]),(0,[z0,z2,z4,z5,z898,z6]),(1,[z0,z2,z4,z8,z872])],[(0,[z0,z2,z4,z5,z8,z899]),(0,[z64,z0,z2,z62,z8,z258]),(0,[z0,z2,z4,z5,z8,z900]),(0,[z0,z2,z4,z5,z32,z719])],[(0,[z138,z0,z2,z4,z5,z35]),(0,[z304,z4,z5,z63,z8,z6]),(0,[z328,z0,z2,z62,z8,z6]),(0,[z0,z2,z5,z8,z901,z35])],[(0,[z0,z2,z325,z4,z8,z35]),(0,[z0,z2,z4,z5,z902,z6]),(0,[z97,z2,z4,z5,z8,z13]),(0,[z2,z4,z5,z8,z724,z6]),(0,[z183,z2,z4,z5,z547,z6]),(0,[z0,z2,z513,z5,z8,z577]),(0,[z218,z2,z4,z5,z8,z202]),(0,[z903,z2,z4,z5,z8,z42])]],
   [[(0,[z87,z2,z89,z5,z8,z6]),(0,[z138,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z8,z904]),(0,[z0,z2,z905,z5,z8,z35])],[(0,[z0,z2,z4,z5,z8,z906]),(0,[z0,z2,z4,z5,z8,z907]),(0,[z0,z2,z4,z5,z908,z6]),(0,[z2,z909,z4,z5,z8,z6]),(0,[z0,z2,z3,z5,z41,z42])],[(0,[z0,z2,z4,z5,z8,z910]),(0,[z19,z0,z24,z57,z8,z6]),(0,[z0,z2,z905,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z911]),(0,[z0,z2,z4,z5,z912,z6]),(0,[z105,z2,z752,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z913]),(0,[z0,z2,z10,z63,z8,z6]),(0,[z914,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z350])],[(0,[z915,z2,z4,z5,z8,z6]),(0,[z79,z0,z2,z5,z38,z6]),(0,[z0,z2,z4,z5,z8,z156])],[(0,[z0,z2,z4,z5,z8,z916]),(0,[z0,z2,z917,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z918]),(0,[z0,z2,z5,z919,z8,z6]),(0,[z0,z2,z4,z5,z8,z920])],[(0,[z0,z2,z4,z5,z921,z6]),(0,[z0,z479,z4,z5,z8,z225]),(0,[z0,z2,z922,z4,z5,z8]),(0,[z0,z2,z4,z5,z8,z893]),(0,[z0,z2,z4,z5,z8,z923]),(0,[z0,z2,z4,z5,z8,z356]),(0,[z87,z2,z4,z5,z8,z42]),(0,[z0,z2,z4,z5,z8,z924]),(0,[z0,z2,z4,z5,z925,z8]),(0,[z0,z2,z4,z5,z140,z345])],[(0,[z0,z2,z4,z8,z6,z926]),(0,[z0,z2,z4,z474,z8,z35]),(0,[z0,z2,z83,z701,z5,z8]),(0,[z497,z2,z4,z5,z175,z6]),(0,[z0,z2,z4,z332,z5,z42]),(0,[z2,z4,z5,z192,z8,z927]),(0,[z928,z2,z4,z5,z8,z6])]],
   [[(0,[z0,z2,z4,z929,z8,z6]),(0,[z0,z2,z4,z5,z930,z6]),(0,[z0,z2,z4,z931,z5,z8]),(0,[z304,z2,z4,z5,z547,z6]),(0,[z183,z2,z4,z5,z8,z508]),(0,[z0,z2,z4,z5,z932,z8]),(0,[z0,z248,z4,z5,z8,z25]),(0,[z0,z2,z4,z5,z8,z933])],[(0,[z0,z2,z934,z4,z5,z8]),(0,[z2,z4,z5,z935,z8,z6])],[(0,[z0,z2,z4,z5,z8,z225]),(0,[z0,z106,z4,z5,z8,z225]),(0,[z936,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z547,z42]),(0,[z0,z2,z4,z37,z8,z347]),(0,[z408,z2,z4,z5,z8,z42]),(0,[z0,z2,z5,z748,z38,z6]),(0,[z0,z2,z215,z5,z8,z684])],[(0,[z0,z2,z4,z544,z8,z35]),(0,[z0,z2,z4,z5,z8,z937]),(0,[z198,z2,z4,z5,z8,z42])],[(0,[z0,z2,z4,z5,z8,z938]),(0,[z0,z2,z4,z57,z175,z6]),(0,[z0,z2,z5,z41,z229,z6]),(0,[z939,z2,z4,z5,z8,z6]),(0,[z19,z0,z24,z5,z8,z35]),(0,[z2,z940,z4,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z941]),(0,[z0,z2,z942,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z943])],[(0,[z0,z2,z944,z5,z8,z6]),(0,[z0,z2,z4,z5,z945,z8]),(0,[z64,z0,z2,z62,z8,z42]),(0,[z0,z2,z4,z96,z8,z872])],[(0,[z0,z2,z4,z5,z946,z6]),(0,[z2,z4,z5,z192,z8,z6]),(0,[z0,z2,z947,z4,z5,z8]),(0,[z0,z2,z65,z118,z8,z35]),(0,[z0,z2,z4,z948,z5,z8]),(0,[z0,z2,z142,z10,z81,z6])]],
   [[(0,[z0,z2,z949,z5,z8,z6]),(0,[z0,z2,z950,z5,z8,z6]),(0,[z2,z4,z5,z8,z6,z202]),(0,[z0,z2,z4,z5,z245,z258]),(0,[z0,z2,z3,z5,z41,z350])],[(0,[z0,z2,z951,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z952]),(0,[z12,z2,z4,z135,z8,z35]),(0,[z85,z2,z33,z4,z5,z34]),(0,[z0,z2,z4,z5,z8,z953]),(0,[z0,z2,z65,z118,z8,z6]),(0,[z198,z2,z4,z5,z8,z533])],[(0,[z0,z2,z4,z5,z8,z954]),(0,[z0,z2,z4,z494,z8,z42]),(0,[z955,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z956,z8]),(0,[z0,z2,z10,z5,z8,z196]),(0,[z2,z4,z5,z817,z254,z8])],[(0,[z0,z2,z4,z5,z8,z957]),(0,[z12,z2,z4,z135,z8,z6]),(0,[z12,z106,z4,z135,z8,z6]),(0,[z162,z2,z4,z29,z8,z35]),(0,[z0,z2,z4,z5,z8,z958]),(0,[z0,z2,z128,z5,z234,z6]),(0,[z0,z2,z203,z4,z5,z8]),(0,[z217,z0,z2,z5,z8,z401])],[(0,[z55,z2,z4,z5,z535,z6]),(0,[z12,z2,z4,z632,z8,z6]),(0,[z97,z2,z4,z5,z8,z724]),(0,[z360,z2,z4,z5,z8,z13]),(0,[z959,z2,z4,z5,z8,z6]),(0,[z204,z0,z4,z5,z8,z47])],[(0,[z0,z2,z960,z4,z8,z6]),(0,[z162,z2,z4,z29,z8,z6]),(0,[z0,z2,z4,z795,z8,z6]),(0,[z0,z2,z4,z566,z8,z35])],[(0,[z0,z2,z4,z5,z8,z961]),(0,[z12,z2,z4,z638,z8,z6]),(0,[z0,z2,z4,z5,z8,z962]),(0,[z0,z2,z4,z5,z8,z963]),(0,[z0,z2,z4,z5,z175,z35]),(0,[z0,z2,z4,z5,z964,z6]),(0,[z204,z0,z4,z5,z404,z8])],[(0,[z0,z207,z4,z150,z8,z6]),(0,[z105,z479,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z965,z6]),(0,[z0,z2,z4,z5,z8,z966]),(0,[z19,z0,z332,z24,z5,z6]),(0,[z0,z2,z4,z5,z8,z967]),(0,[z2,z968,z4,z5,z8,z35]),(0,[z0,z2,z4,z58,z8,z35])]],
   [[(0,[z0,z2,z4,z5,z8,z969]),(0,[z55,z2,z4,z5,z794,z6]),(0,[z0,z2,z970,z4,z5,z6])],[(0,[z971,z0,z2,z4,z5,z8]),(0,[z0,z2,z4,z5,z8,z972]),(0,[z2,z968,z4,z5,z8,z6]),(0,[z564,z2,z4,z5,z8,z42])],[(0,[z12,z2,z4,z5,z8,z307]),(0,[z0,z2,z4,z8,z68,z35]),(0,[z0,z683,z4,z5,z8,z47]),(0,[z2,z4,z5,z8,z973,z6]),(0,[z339,z0,z4,z5,z16,z6])],[(0,[z0,z2,z4,z5,z974,z6]),(0,[z0,z2,z4,z5,z8,z975]),(0,[z0,z2,z161,z5,z8,z225]),(0,[z0,z2,z4,z5,z8,z976])],[(0,[z0,z2,z273,z4,z90,z6]),(0,[z0,z2,z4,z8,z977,z6]),(0,[z0,z2,z4,z5,z8,z978])],[(0,[z372,z54,z4,z5,z8,z6]),(0,[z0,z2,z4,z979,z8,z6]),(0,[z69,z2,z4,z5,z8,z221]),(0,[z980,z0,z2,z4,z5,z8]),(0,[z80,z2,z4,z5,z8,z35]),(0,[z0,z2,z82,z4,z5,z32])],[(0,[z0,z2,z4,z981,z8,z6]),(0,[z0,z2,z4,z5,z8,z982]),(0,[z49,z2,z4,z5,z8,z524]),(0,[z0,z2,z4,z983,z8,z6]),(0,[z0,z2,z4,z5,z547,z508]),(0,[z0,z2,z984,z5,z8,z6]),(0,[z0,z2,z4,z985,z8,z6]),(0,[z339,z143,z0,z2,z5,z6])],[(0,[z725,z54,z4,z5,z8,z6]),(0,[z286,z54,z4,z5,z8,z42]),(0,[z145,z4,z5,z650,z8,z6]),(0,[z501,z2,z45,z5,z8,z6]),(0,[z105,z2,z89,z5,z8,z42]),(0,[z80,z2,z4,z5,z8,z6]),(0,[z0,z2,z513,z5,z547,z6]),(0,[z0,z2,z462,z5,z8,z46])]],
   [[(0,[z0,z2,z4,z5,z8,z986]),(0,[z69,z2,z4,z5,z229,z6]),(0,[z138,z0,z2,z3,z5,z6]),(0,[z987,z2,z4,z5,z8,z6]),(0,[z0,z2,z128,z5,z8,z347]),(0,[z0,z2,z4,z5,z8,z883]),(0,[z0,z2,z4,z5,z988,z35]),(0,[z0,z2,z4,z444,z8,z42])],[(0,[z0,z2,z989,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z990]),(0,[z0,z2,z4,z5,z8,z991]),(0,[z0,z2,z10,z5,z8,z42])],[(0,[z0,z2,z595,z118,z8,z6]),(0,[z0,z2,z4,z5,z8,z30]),(0,[z183,z2,z4,z5,z8,z577]),(1,[z0,z4,z795,z8,z6]),(0,[z0,z2,z4,z5,z988,z6]),(0,[z0,z2,z193,z4,z90,z6])],[(0,[z629,z54,z4,z5,z8,z6]),(0,[z2,z4,z5,z762,z8,z6]),(0,[z101,z0,z2,z349,z5,z8]),(0,[z79,z0,z2,z5,z229,z6]),(0,[z136,z0,z4,z795,z8,z6])],[(0,[z2,z54,z4,z5,z295,z8]),(0,[z12,z2,z161,z135,z8,z6]),(0,[z97,z2,z4,z266,z5,z8]),(0,[z0,z2,z4,z5,z229,z20]),(0,[z0,z2,z992,z4,z5,z6]),(0,[z993,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z994]),(0,[z0,z2,z4,z5,z8,z995])],[(0,[z0,z2,z4,z5,z8,z996]),(0,[z28,z2,z4,z5,z8,z42]),(0,[z997,z2,z4,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z998]),(0,[z0,z2,z4,z5,z8,z114]),(0,[z0,z2,z4,z173,z8,z35])],[(0,[z0,z2,z4,z5,z999,z6]),(0,[z261,z2,z4,z5,z34,z6]),(0,[z49,z2,z4,z5,z403,z8]),(0,[z0,z2,z4,z8,z42,z660]),(0,[z0,z2,z4,z5,z8,z221]),(0,[z0,z2,z57,z41,z8,z6]),(0,[z0,z2,z4,z191,z5,z8]),(0,[z0,z205,z4,z5,z8,z25])]],
   [[(0,[z0,z2,z4,z5,z8,z60]),(0,[z69,z2,z4,z5,z8,z20]),(0,[z0,z2,z4,z5,z229,z35]),(0,[z0,z2,z5,z8,z6,z901]),(0,[z0,z2,z4,z5,z8,z196])],[(0,[z0,z2,z4,z5,z8,z1000]),(0,[z0,z2,z239,z5,z8,z35]),(0,[z1001,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z1002])],[(0,[z0,z2,z4,z5,z8,z1003]),(0,[z0,z2,z190,z5,z121,z6]),(0,[z0,z2,z4,z5,z229,z6]),(0,[z0,z2,z4,z5,z1004,z6]),(0,[z1005,z2,z4,z5,z8,z6])],[(0,[z0,z2,z239,z5,z8,z6]),(0,[z0,z2,z4,z57,z8,z42]),(0,[z0,z2,z708,z5,z8,z6]),(0,[z36,z79,z0,z5,z16,z6]),(0,[z0,z2,z1006,z4,z5,z8]),(0,[z0,z2,z5,z118,z245,z6]),(0,[z1007,z2,z4,z5,z8,z35])],[(0,[z0,z2,z4,z63,z168,z6]),(0,[z0,z2,z4,z37,z8,z35])],[(0,[z69,z2,z4,z5,z8,z42]),(0,[z0,z2,z773,z118,z8,z6]),(0,[z2,z4,z5,z8,z6,z1008]),(0,[z0,z2,z4,z5,z32,z371]),(0,[z1007,z2,z4,z5,z8,z6])],[(0,[z286,z479,z4,z5,z8,z6]),(0,[z22,z2,z45,z5,z8,z6]),(0,[z0,z2,z4,z37,z8,z6]),(0,[z0,z2,z4,z5,z8,z1009]),(0,[z0,z2,z4,z171,z8,z347]),(0,[z0,z2,z82,z4,z5,z628]),(0,[z0,z2,z3,z5,z41,z575])],[(0,[z0,z2,z4,z5,z458,z524]),(0,[z1010,z2,z4,z5,z8,z6]),(0,[z0,z599,z4,z5,z8,z25]),(0,[z0,z2,z4,z5,z8,z1011])]],
   [[(0,[z0,z2,z1012,z4,z8,z6]),(0,[z0,z2,z1013,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z927]),(0,[z79,z0,z2,z5,z8,z42]),(0,[z2,z4,z5,z8,z6,z784])],[(0,[z160,z0,z2,z4,z5,z8]),(0,[z0,z2,z5,z41,z376,z6]),(0,[z0,z2,z4,z1014,z8,z6]),(0,[z198,z2,z4,z5,z8,z610])],[(0,[z0,z2,z4,z638,z8,z35]),(0,[z0,z2,z1015,z4,z5,z8]),(0,[z2,z4,z29,z133,z8,z6]),(0,[z97,z2,z4,z5,z8,z202]),(0,[z0,z2,z4,z309,z8,z1016]),(0,[z0,z2,z4,z5,z8,z1017]),(0,[z0,z2,z1018,z4,z5,z8]),(0,[z0,z2,z4,z8,z42,z680])],[(0,[z0,z2,z4,z5,z1019,z6]),(0,[z145,z479,z4,z5,z8,z6]),(0,[z0,z2,z4,z1020,z8,z6]),(0,[z1021,z0,z2,z4,z5,z8]),(0,[z304,z2,z4,z5,z8,z35]),(0,[z0,z2,z4,z5,z1022,z6]),(0,[z0,z2,z4,z5,z8,z1023]),(0,[z0,z2,z83,z5,z8,z46]),(0,[z0,z2,z4,z5,z367,z26])],[(0,[z1024,z0,z2,z5,z8,z6]),(0,[z1025,z2,z4,z5,z8,z6]),(0,[z127,z2,z4,z37,z8,z6]),(0,[z204,z0,z250,z4,z5,z8]),(0,[z928,z2,z4,z5,z245,z6]),(0,[z1026,z2,z4,z5,z8,z6])],[(0,[z304,z2,z4,z5,z8,z6]),(0,[z461,z2,z4,z5,z8,z35]),(0,[z0,z2,z4,z5,z8,z1027]),(0,[z0,z2,z4,z5,z8,z872])],[],[(0,[z0,z2,z4,z5,z8,z42]),(0,[z461,z2,z4,z5,z8,z6]),(0,[z0,z106,z4,z5,z8,z42]),(0,[z0,z2,z24,z5,z229,z6]),(0,[z19,z0,z708,z5,z8,z6]),(0,[z0,z2,z5,z1028,z8,z6])]],
   [[(0,[z0,z2,z4,z5,z8,z307]),(0,[z0,z2,z4,z5,z1029,z6]),(1,[z0,z708,z5,z8,z6]),(0,[z0,z2,z4,z5,z6,z1030]),(0,[z64,z0,z2,z365,z8,z6]),(0,[z0,z2,z4,z5,z8,z1031]),(0,[z0,z2,z4,z5,z547,z577]),(0,[z871,z2,z4,z5,z8,z6])],[(0,[z0,z2,z4,z1032,z5,z8]),(0,[z0,z2,z4,z5,z8,z1033]),(0,[z0,z2,z1034,z5,z8,z6]),(0,[z0,z2,z4,z486,z8,z42]),(0,[z0,z2,z4,z5,z168,z114]),(0,[z1035,z2,z4,z5,z8,z6]),(0,[z0,z2,z1036,z5,z8,z6])],[(0,[z164,z0,z2,z4,z8,z35]),(0,[z0,z2,z4,z5,z8,z1037]),(0,[z0,z2,z1038,z4,z5,z8]),(0,[z79,z1039,z2,z5,z8,z6]),(0,[z217,z0,z2,z5,z90,z6])],[(0,[z0,z2,z4,z5,z121,z225])],[(0,[z0,z2,z4,z704,z8,z35]),(0,[z69,z2,z4,z309,z8,z6]),(0,[z0,z2,z4,z148,z8,z35]),(0,[z0,z4,z5,z8,z25,z1040])],[(0,[z0,z2,z4,z5,z8,z1041]),(0,[z127,z2,z4,z5,z8,z42]),(0,[z0,z2,z231,z4,z710,z6])],[(0,[z54,z4,z5,z638,z8,z6]),(0,[z0,z2,z4,z1042,z8,z6]),(0,[z286,z725,z4,z5,z8,z6]),(0,[z0,z2,z289,z4,z90,z6]),(0,[z2,z4,z5,z8,z42,z202])],[(0,[z0,z2,z4,z1043,z8,z6]),(0,[z0,z2,z4,z5,z8,z1044]),(0,[z0,z2,z1045,z4,z5,z8]),(0,[z0,z2,z1046,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z1047])]],
   [[(0,[z0,z2,z4,z5,z8,z1048]),(0,[z2,z4,z5,z8,z13,z60]),(0,[z0,z2,z4,z5,z1049,z6]),(0,[z0,z2,z4,z5,z8,z333]),(0,[z0,z2,z4,z288,z8,z35]),(0,[z64,z0,z2,z62,z8,z114])],[(0,[z49,z2,z4,z5,z8,z134]),(0,[z143,z0,z2,z5,z38,z35]),(0,[z101,z0,z2,z5,z358,z8]),(0,[z1050,z2,z4,z5,z8,z35]),(0,[z360,z2,z4,z5,z8,z294])],[(0,[z385,z2,z45,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z1051]),(0,[z0,z2,z4,z5,z1052,z6]),(0,[z162,z2,z4,z29,z8,z30]),(0,[z138,z0,z2,z4,z5,z42]),(0,[z0,z2,z4,z5,z140,z532]),(0,[z198,z2,z4,z8,z42,z35])],[(0,[z0,z2,z4,z5,z8,z1053]),(0,[z19,z0,z24,z5,z229,z6]),(0,[z1050,z2,z4,z5,z8,z6]),(0,[z143,z0,z2,z5,z38,z6]),(0,[z1054,z2,z4,z5,z8,z6]),(0,[z753,z2,z4,z5,z8,z6])],[(0,[z12,z2,z4,z135,z121,z6]),(0,[z0,z2,z4,z5,z8,z1055]),(0,[z0,z2,z4,z309,z8,z35]),(0,[z0,z2,z4,z5,z1056,z8]),(0,[z36,z0,z4,z5,z16,z249]),(0,[z0,z205,z4,z5,z8,z1040])],[(0,[z0,z2,z4,z5,z8,z1057]),(0,[z1058,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z1059]),(0,[z0,z2,z240,z5,z8,z347])],[(0,[z0,z2,z4,z5,z1060,z6]),(0,[z0,z2,z4,z309,z8,z6]),(0,[z0,z2,z4,z5,z1061,z35])],[(0,[z97,z2,z659,z4,z5,z8]),(0,[z1062,z2,z4,z5,z8,z6]),(0,[z0,z4,z708,z5,z8,z6]),(0,[z189,z2,z4,z37,z8,z6]),(0,[z0,z2,z4,z1063,z8,z6])]],
   [[(0,[z0,z2,z4,z5,z1064,z6]),(0,[z0,z2,z1065,z5,z8,z6]),(0,[z0,z2,z161,z5,z8,z42]),(0,[z162,z2,z4,z29,z8,z60]),(0,[z0,z2,z513,z137,z8,z6]),(0,[z0,z2,z4,z5,z1061,z6]),(0,[z2,z4,z5,z1066,z8,z6]),(0,[z143,z0,z2,z5,z320,z6])],[(0,[z0,z2,z4,z5,z8,z1067]),(0,[z0,z2,z3,z5,z41,z282])],[(0,[z251,z2,z45,z5,z8,z35]),(0,[z0,z2,z1068,z4,z5,z6]),(0,[z0,z23,z117,z5,z8,z35]),(0,[z0,z2,z513,z5,z8,z35]),(0,[z127,z2,z128,z5,z8,z6]),(0,[z217,z0,z2,z5,z8,z35]),(0,[z0,z2,z4,z5,z170,z26])],[(0,[z0,z2,z4,z5,z8,z1069]),(0,[z19,z0,z24,z5,z8,z20]),(0,[z0,z2,z4,z5,z8,z508]),(0,[z0,z2,z1070,z5,z8,z6]),(0,[z0,z2,z455,z5,z41,z6]),(0,[z1071,z2,z4,z5,z8,z6]),(0,[z2,z4,z5,z935,z8,z42])],[(0,[z0,z2,z4,z5,z8,z1072]),(0,[z251,z2,z45,z5,z8,z6]),(0,[z0,z23,z117,z5,z8,z6]),(0,[z0,z2,z513,z5,z8,z6]),(0,[z1073,z2,z4,z5,z8,z6]),(0,[z0,z207,z4,z137,z8,z21]),(0,[z0,z2,z5,z8,z6,z1074]),(0,[z1075,z2,z4,z5,z8,z6]),(0,[z1076,z2,z4,z5,z8,z35])],[(0,[z0,z2,z4,z5,z8,z1077]),(0,[z204,z0,z4,z5,z8,z1040]),(0,[z198,z2,z4,z5,z8,z437])],[(0,[z0,z2,z4,z5,z8,z1078]),(0,[z0,z2,z4,z5,z8,z1079]),(0,[z518,z2,z4,z5,z34,z6]),(0,[z1080,z2,z4,z5,z8,z6]),(0,[z1081,z2,z4,z5,z8,z6]),(0,[z101,z0,z2,z5,z8,z213]),(0,[z1076,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z1082])],[(0,[z49,z479,z4,z5,z8,z6]),(0,[z0,z2,z1083,z5,z8,z6]),(0,[z0,z2,z5,z8,z15,z35]),(0,[z80,z2,z4,z142,z81,z6]),(0,[z2,z4,z5,z254,z8,z35])]],
   [[(0,[z1084,z2,z4,z5,z8,z6]),(0,[z189,z2,z4,z5,z8,z42]),(0,[z0,z2,z4,z171,z8,z35]),(0,[z1085,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z17,z81,z6]),(0,[z0,z2,z5,z8,z748,z6])],[(0,[z64,z0,z2,z474,z8,z6]),(0,[z0,z2,z190,z5,z8,z225]),(0,[z198,z2,z4,z5,z8,z524]),(0,[z0,z1086,z4,z5,z8,z6]),(0,[z162,z2,z4,z762,z8,z6]),(0,[z69,z2,z4,z5,z175,z6]),(0,[z19,z0,z24,z5,z8,z6]),(0,[z0,z2,z5,z8,z15,z6]),(0,[z0,z2,z4,z5,z8,z1087]),(0,[z2,z4,z5,z192,z8,z42]),(0,[z0,z2,z4,z8,z42,z93]),(0,[z101,z198,z2,z4,z5,z8])],[(0,[z129,z2,z4,z5,z8,z307]),(0,[z0,z2,z44,z4,z5,z8]),(0,[z2,z89,z752,z5,z8,z6]),(0,[z497,z2,z4,z57,z8,z6]),(0,[z0,z2,z4,z171,z8,z6]),(0,[z0,z2,z4,z142,z86,z6]),(0,[z0,z2,z4,z5,z1088,z6])],[(0,[z0,z2,z4,z5,z1089,z6]),(0,[z0,z2,z4,z5,z8,z1090]),(0,[z0,z2,z117,z5,z229,z6]),(0,[z0,z2,z4,z5,z8,z1091]),(0,[z0,z2,z4,z1092,z8,z6]),(0,[z0,z2,z4,z5,z1093,z8]),(0,[z0,z2,z4,z5,z245,z114]),(0,[z0,z2,z4,z1094,z8,z6])],[(0,[z2,z4,z29,z5,z295,z8]),(0,[z198,z2,z4,z5,z8,z13]),(0,[z0,z2,z4,z5,z8,z1095]),(0,[z1096,z2,z4,z5,z8,z6]),(0,[z0,z2,z1097,z5,z8,z6]),(0,[z0,z2,z4,z37,z8,z976]),(0,[z1098,z0,z2,z4,z5,z8])],[(0,[z0,z2,z4,z5,z1099,z6]),(0,[z12,z2,z4,z135,z8,z42]),(0,[z0,z2,z4,z5,z175,z20]),(0,[z1100,z2,z4,z5,z8,z6]),(0,[z2,z1101,z4,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z1102]),(0,[z0,z4,z137,z795,z8,z6]),(0,[z143,z0,z2,z5,z420,z6]),(0,[z0,z2,z4,z267,z8,z35]),(0,[z198,z2,z4,z5,z170,z8])],[(0,[z272,z54,z4,z5,z8,z6]),(0,[z0,z2,z1103,z5,z8,z6]),(0,[z0,z2,z752,z5,z8,z6]),(0,[z0,z2,z4,z5,z1104,z8]),(0,[z1105,z0,z2,z5,z8,z6]),(0,[z2,z4,z5,z8,z724,z27]),(0,[z19,z69,z24,z5,z8,z6]),(0,[z36,z0,z4,z5,z16,z35]),(0,[z0,z2,z4,z1106,z8,z6])]],
   [[(0,[z0,z2,z4,z5,z8,z1107]),(0,[z127,z2,z4,z171,z8,z6]),(0,[z0,z2,z3,z5,z71,z41]),(0,[z0,z2,z1108,z5,z8,z6]),(0,[z0,z2,z4,z142,z81,z196])],[(0,[z0,z2,z4,z5,z8,z1109]),(0,[z2,z4,z29,z762,z8,z6]),(0,[z55,z2,z4,z5,z56,z35]),(0,[z0,z708,z24,z5,z8,z6]),(0,[z0,z23,z708,z5,z8,z6]),(0,[z0,z2,z3,z5,z539,z6]),(0,[z36,z0,z4,z5,z16,z6])],[(0,[z12,z2,z190,z135,z8,z6]),(0,[z1110,z0,z2,z5,z8,z6]),(0,[z0,z2,z4,z5,z1111,z8]),(0,[z0,z2,z435,z4,z5,z32])],[(0,[z0,z2,z4,z5,z8,z1112]),(0,[z55,z2,z4,z5,z56,z6]),(0,[z0,z2,z4,z1113,z8,z6]),(0,[z0,z2,z4,z5,z175,z6]),(0,[z0,z2,z231,z4,z90,z35])],[(0,[z0,z2,z4,z1114,z8,z6]),(0,[z0,z2,z4,z5,z8,z1115]),(0,[z0,z2,z4,z5,z229,z221]),(0,[z0,z2,z450,z4,z90,z6]),(0,[z0,z2,z4,z37,z8,z249]),(0,[z0,z2,z5,z235,z8,z15]),(0,[z1116,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z42,z168])],[(0,[z136,z0,z239,z63,z8,z6]),(0,[z143,z0,z2,z128,z5,z6]),(0,[z0,z2,z231,z4,z90,z6]),(0,[z198,z2,z4,z96,z8,z35])],[(0,[z0,z2,z4,z1117,z5,z8]),(0,[z0,z207,z4,z137,z8,z35]),(0,[z0,z2,z1118,z5,z8,z6])],[(0,[z0,z2,z1119,z5,z8,z6]),(0,[z0,z2,z1120,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z1121]),(0,[z36,z0,z5,z15,z16,z6]),(0,[z0,z2,z642,z4,z90,z6]),(0,[z101,z0,z2,z469,z5,z8]),(0,[z66,z0,z4,z5,z8,z47])]],
   [[(0,[z0,z2,z4,z1122,z8,z6]),(0,[z0,z479,z4,z5,z458,z6]),(0,[z0,z2,z4,z570,z81,z6]),(0,[z0,z207,z4,z137,z8,z6]),(0,[z0,z2,z4,z5,z8,z1123]),(0,[z0,z2,z4,z74,z8,z872])],[(0,[z0,z2,z70,z118,z8,z6]),(0,[z2,z4,z5,z1124,z8,z6]),(0,[z205,z31,z4,z5,z8,z25])],[(0,[z0,z1125,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z458,z35]),(0,[z143,z0,z2,z5,z229,z6]),(0,[z0,z2,z4,z5,z8,z1126]),(0,[z1127,z408,z2,z4,z5,z8]),(0,[z0,z2,z4,z74,z8,z42])],[(0,[z136,z0,z4,z63,z441,z6]),(0,[z0,z2,z4,z1128,z5,z6]),(0,[z0,z2,z4,z5,z8,z1129]),(0,[z0,z2,z4,z702,z8,z42]),(0,[z0,z2,z10,z5,z8,z401])],[(0,[z479,z4,z45,z5,z8,z6]),(0,[z76,z0,z2,z4,z332,z5]),(0,[z0,z2,z4,z5,z1130,z6]),(0,[z0,z2,z5,z8,z1131,z6]),(0,[z0,z2,z4,z5,z245,z42]),(0,[z0,z2,z4,z5,z8,z575]),(0,[z0,z2,z1132,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z1133]),(0,[z0,z2,z4,z5,z1134,z6]),(0,[z138,z1096,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z8,z577]),(0,[z281,z2,z4,z5,z8,z35]),(0,[z0,z2,z65,z118,z8,z356]),(0,[z1135,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z354,z8,z35])],[(0,[z162,z479,z4,z5,z8,z6]),(0,[z1136,z2,z4,z5,z8,z6]),(0,[z281,z2,z83,z4,z5,z8]),(0,[z101,z0,z2,z5,z8,z883]),(0,[z0,z2,z4,z142,z81,z401])],[(0,[z281,z2,z4,z5,z8,z6]),(0,[z0,z2,z1137,z4,z8,z6]),(0,[z0,z2,z4,z1138,z8,z6]),(0,[z0,z2,z4,z5,z8,z1139]),(0,[z0,z167,z117,z5,z8,z6]),(0,[z0,z2,z240,z5,z8,z35]),(0,[z2,z31,z4,z5,z8,z42]),(0,[z0,z2,z4,z5,z1140,z8]),(0,[z0,z2,z4,z142,z81,z42]),(0,[z198,z2,z215,z4,z5,z8])]],
   [[(0,[z0,z2,z4,z5,z121,z42]),(0,[z0,z2,z4,z5,z1141,z6]),(0,[z0,z2,z4,z309,z8,z778]),(0,[z0,z2,z4,z1142,z8,z6]),(0,[z0,z2,z4,z5,z1143,z6]),(0,[z143,z0,z2,z5,z467,z6])],[(0,[z0,z2,z4,z1144,z8,z6]),(0,[z0,z2,z4,z5,z8,z1145]),(0,[z0,z2,z240,z5,z8,z6]),(0,[z0,z2,z4,z1146,z5,z8]),(0,[z136,z0,z4,z63,z8,z42]),(0,[z0,z2,z1147,z5,z8,z6]),(0,[z0,z2,z4,z5,z1148,z8]),(0,[z816,z2,z4,z5,z8,z6])],[(0,[z85,z2,z4,z5,z34,z35]),(0,[z64,z0,z2,z5,z245,z6])],[(0,[z0,z2,z4,z5,z1149,z6]),(0,[z0,z2,z4,z5,z8,z1150]),(0,[z12,z2,z4,z135,z8,z225]),(0,[z0,z2,z4,z5,z1151,z8]),(0,[z189,z2,z4,z171,z8,z6]),(0,[z1152,z0,z2,z5,z8,z6]),(0,[z2,z4,z5,z1153,z8,z6]),(0,[z0,z2,z5,z8,z46,z883])],[(0,[z85,z2,z4,z5,z34,z6]),(0,[z0,z2,z4,z5,z229,z42]),(0,[z0,z2,z3,z128,z5,z6]),(0,[z0,z2,z231,z4,z90,z156]),(0,[z831,z2,z4,z5,z8,z42]),(0,[z0,z2,z277,z4,z5,z32]),(0,[z2,z1154,z4,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z1155]),(0,[z183,z2,z4,z5,z8,z35]),(0,[z0,z2,z239,z5,z8,z42]),(0,[z0,z2,z4,z5,z8,z1156]),(0,[z788,z0,z2,z4,z5,z8])],[(0,[z251,z2,z44,z45,z5,z8]),(0,[z0,z2,z590,z118,z8,z6]),(0,[z0,z2,z4,z17,z8,z35]),(0,[z0,z1157,z4,z5,z8,z6]),(0,[z0,z2,z82,z4,z5,z423]),(0,[z217,z728,z2,z5,z8,z6]),(0,[z0,z2,z1158,z5,z8,z6]),(0,[z678,z0,z2,z5,z8,z388])],[(0,[z183,z2,z4,z5,z8,z6]),(0,[z1159,z2,z4,z5,z8,z6]),(0,[z0,z2,z1160,z4,z5,z8]),(0,[z993,z2,z4,z5,z8,z333]),(0,[z127,z2,z240,z5,z8,z6]),(0,[z0,z205,z4,z548,z5,z8]),(0,[z0,z2,z4,z5,z8,z232]),(0,[z217,z0,z2,z5,z81,z6])]],
   [[(0,[z0,z2,z4,z137,z441,z6]),(0,[z0,z2,z4,z37,z8,z42]),(0,[z0,z2,z4,z5,z8,z1161]),(0,[z1162,z2,z4,z5,z8,z6]),(0,[z1163,z2,z4,z5,z8,z6]),(0,[z143,z0,z2,z5,z489,z6]),(0,[z1164,z2,z4,z5,z8,z35]),(0,[z1165,z2,z4,z5,z8,z35])],[(0,[z0,z2,z4,z5,z8,z1166]),(0,[z594,z2,z45,z5,z8,z6]),(0,[z1167,z2,z4,z5,z8,z6]),(0,[z79,z0,z2,z5,z41,z6]),(0,[z0,z2,z4,z5,z8,z1168])],[(0,[z0,z2,z4,z1169,z8,z6]),(0,[z0,z2,z4,z5,z441,z35]),(0,[z0,z205,z4,z5,z8,z437]),(0,[z1164,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z343,z8,z35]),(0,[z1165,z2,z4,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z1170])],[(0,[z0,z2,z4,z5,z1171,z6]),(0,[z0,z2,z4,z8,z146,z35]),(0,[z0,z2,z4,z632,z8,z42]),(0,[z0,z2,z4,z5,z1172,z6]),(0,[z19,z0,z24,z5,z175,z6]),(0,[z138,z64,z0,z2,z5,z6]),(0,[z0,z2,z4,z1173,z5,z8]),(0,[z0,z2,z4,z5,z441,z6])],[(0,[z0,z2,z4,z5,z8,z1174]),(0,[z0,z2,z161,z5,z458,z6]),(0,[z136,z304,z4,z63,z8,z6]),(0,[z858,z2,z4,z5,z8,z42])],[(0,[z1175,z2,z4,z5,z8,z6])],[(0,[z0,z4,z5,z795,z8,z6]),(0,[z0,z2,z4,z5,z8,z1176]),(0,[z0,z2,z4,z5,z8,z1177]),(0,[z87,z64,z2,z62,z8,z6]),(0,[z0,z2,z253,z5,z38,z6]),(0,[z0,z2,z4,z5,z8,z1178])]],
   [[(0,[z1179,z0,z2,z4,z5,z8]),(0,[z0,z2,z4,z5,z8,z1180]),(0,[z1181,z0,z2,z4,z5,z8]),(0,[z2,z4,z5,z56,z794,z6]),(0,[z0,z2,z4,z309,z8,z221]),(0,[z0,z2,z4,z5,z1182,z6]),(0,[z136,z461,z4,z63,z8,z6]),(0,[z0,z2,z4,z477,z8,z42])],[(0,[z0,z479,z4,z5,z8,z524]),(0,[z49,z2,z4,z5,z8,z724]),(0,[z0,z2,z4,z184,z8,z42]),(0,[z0,z2,z4,z5,z8,z401]),(0,[z0,z2,z4,z613,z8,z42])],[(0,[z0,z1183,z4,z5,z8,z6]),(0,[z2,z4,z5,z794,z34,z6]),(0,[z0,z2,z4,z5,z8,z1184]),(0,[z903,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z37,z16,z6]),(0,[z143,z0,z2,z4,z37,z6]),(0,[z0,z2,z4,z5,z8,z1185])],[(0,[z12,z2,z4,z762,z8,z6]),(0,[z1186,z0,z2,z4,z5,z8]),(0,[z0,z2,z4,z309,z229,z6]),(0,[z143,z0,z359,z2,z5,z6]),(0,[z1187,z2,z4,z5,z8,z6]),(0,[z2,z4,z5,z8,z202,z35])],[(0,[z0,z2,z4,z5,z8,z1188]),(0,[z0,z2,z4,z5,z8,z1189]),(0,[z217,z0,z2,z142,z81,z6])],[(0,[z479,z4,z5,z135,z8,z6]),(0,[z0,z106,z4,z5,z8,z524]),(0,[z2,z4,z5,z458,z34,z6]),(0,[z1190,z0,z2,z4,z5,z8]),(0,[z0,z2,z4,z1191,z8,z6]),(0,[z136,z0,z4,z63,z8,z508]),(0,[z36,z127,z4,z5,z16,z6]),(0,[z0,z2,z1192,z5,z8,z6]),(0,[z2,z4,z8,z42,z202,z35])],[(0,[z0,z2,z190,z5,z8,z42]),(1,[z2,z4,z762,z8,z6]),(0,[z0,z2,z4,z570,z8,z35]),(0,[z136,z0,z513,z63,z8,z6]),(0,[z678,z198,z2,z4,z5,z8])],[(0,[z1193,z2,z4,z5,z8,z6]),(0,[z1194,z0,z2,z4,z5,z6]),(1,[z2,z752,z5,z8,z6]),(0,[z0,z2,z4,z5,z1195,z6]),(0,[z0,z4,z5,z8,z1040,z47]),(0,[z0,z2,z4,z5,z8,z144]),(0,[z87,z2,z4,z5,z8,z35]),(0,[z0,z2,z4,z5,z8,z282]),(0,[z0,z2,z4,z5,z8,z1196]),(0,[z101,z0,z2,z5,z8,z588])]],
   [[(0,[z0,z2,z4,z1197,z5,z6]),(0,[z0,z2,z4,z332,z5,z35]),(0,[z0,z2,z4,z171,z8,z249]),(0,[z0,z4,z5,z8,z6,z1040])],[(0,[z87,z2,z4,z5,z8,z6]),(0,[z2,z4,z5,z8,z794,z6]),(0,[z0,z2,z4,z5,z8,z1198]),(0,[z0,z2,z4,z5,z8,z1199]),(0,[z0,z2,z4,z5,z8,z1200])],[(0,[z0,z2,z4,z5,z8,z1201]),(0,[z0,z2,z4,z1202,z5,z8]),(0,[z0,z2,z4,z332,z5,z6]),(0,[z2,z4,z5,z1203,z8,z6]),(0,[z189,z2,z240,z5,z8,z6]),(0,[z0,z2,z4,z8,z710,z6])],[(0,[z0,z2,z4,z309,z8,z20]),(0,[z19,z0,z24,z5,z8,z221]),(0,[z0,z2,z4,z5,z547,z35]),(0,[z64,z408,z2,z62,z8,z6]),(0,[z0,z2,z4,z5,z719,z26])],[(0,[z0,z207,z4,z795,z8,z6]),(0,[z0,z2,z4,z5,z8,z814]),(0,[z0,z153,z4,z5,z8,z25]),(0,[z0,z2,z4,z5,z8,z1204]),(0,[z0,z2,z1205,z5,z8,z6]),(0,[z198,z2,z4,z5,z8,z35])],[(0,[z545,z2,z4,z5,z34,z6]),(0,[z19,z138,z0,z2,z5,z6]),(0,[z0,z2,z4,z5,z547,z6]),(0,[z0,z2,z128,z5,z8,z35]),(0,[z36,z0,z4,z5,z235,z16]),(0,[z0,z2,z4,z130,z81,z6]),(0,[z198,z2,z83,z4,z5,z8]),(0,[z158,z0,z4,z5,z8,z211])],[(0,[z0,z2,z1206,z5,z8,z6]),(0,[z0,z2,z4,z1207,z5,z8]),(0,[z198,z2,z4,z5,z8,z6]),(0,[z2,z4,z5,z665,z34,z6]),(0,[z0,z2,z4,z1208,z8,z6])],[(0,[z0,z2,z4,z5,z8,z1209]),(0,[z0,z2,z4,z5,z8,z1210]),(0,[z0,z2,z4,z5,z1211,z6]),(0,[z55,z2,z4,z5,z458,z6]),(0,[z0,z658,z4,z5,z8,z25]),(0,[z0,z2,z128,z5,z8,z6]),(0,[z0,z2,z4,z5,z1212,z6]),(0,[z0,z2,z4,z5,z1213,z8]),(0,[z0,z2,z4,z5,z8,z1214]),(0,[z0,z2,z4,z5,z1215,z6]),(0,[z198,z2,z4,z5,z8,z202]),(0,[z0,z2,z1216,z5,z8,z35])]],
   [[(0,[z0,z1217,z4,z5,z8,z6]),(0,[z12,z2,z4,z291,z8,z6]),(0,[z0,z2,z4,z1218,z8,z6]),(0,[z0,z2,z4,z5,z8,z1219]),(0,[z2,z4,z5,z1220,z8,z6])],[(0,[z0,z2,z4,z1221,z8,z6]),(0,[z0,z2,z4,z5,z8,z1222]),(0,[z0,z2,z4,z5,z8,z1223]),(0,[z0,z2,z3,z4,z37,z6]),(0,[z0,z2,z1224,z4,z5,z8]),(0,[z0,z2,z83,z5,z8,z883]),(0,[z0,z2,z1216,z5,z8,z6]),(0,[z0,z2,z4,z96,z8,z35])],[(0,[z1225,z0,z2,z5,z8,z6]),(0,[z0,z2,z222,z118,z8,z6]),(0,[z79,z0,z2,z203,z5,z8]),(0,[z0,z2,z4,z773,z8,z6]),(1,[z0,z2,z4,z710,z6])],[],[(0,[z0,z2,z4,z5,z1226,z6]),(0,[z0,z2,z4,z57,z8,z797])],[(0,[z0,z2,z4,z5,z8,z1227]),(0,[z0,z2,z4,z5,z8,z1228]),(0,[z0,z2,z4,z5,z175,z221]),(0,[z0,z2,z4,z5,z8,z1229]),(0,[z2,z4,z5,z8,z42,z973]),(0,[z1071,z2,z4,z5,z8,z42])],[(0,[z0,z2,z1230,z5,z8,z6]),(0,[z55,z479,z4,z5,z8,z6]),(0,[z0,z2,z161,z5,z8,z524]),(0,[z0,z2,z4,z5,z1231,z6]),(0,[z0,z2,z4,z5,z8,z1232]),(0,[z0,z23,z117,z5,z8,z42]),(0,[z0,z2,z4,z5,z8,z347]),(0,[z0,z2,z4,z5,z8,z1040]),(0,[z0,z2,z1233,z4,z5,z8]),(0,[z0,z2,z4,z5,z748,z6])],[(0,[z105,z2,z4,z5,z121,z6]),(0,[z1234,z2,z4,z5,z8,z6]),(0,[z217,z0,z2,z5,z8,z6]),(0,[z0,z2,z3,z5,z526,z6]),(0,[z0,z2,z4,z81,z710,z6])]],
   [[(0,[z0,z2,z4,z5,z1235,z6]),(0,[z0,z530,z4,z5,z234,z6]),(0,[z0,z2,z4,z5,z212,z26]),(0,[z0,z2,z1236,z4,z5,z8])],[(0,[z1237,z0,z2,z4,z5,z8]),(0,[z0,z2,z1238,z4,z5,z8]),(0,[z0,z2,z4,z5,z140,z663]),(0,[z0,z23,z5,z8,z581,z6])],[(0,[z0,z2,z4,z1239,z5,z6]),(0,[z160,z129,z2,z4,z5,z8]),(0,[z0,z2,z4,z5,z8,z1240]),(0,[z36,z0,z4,z37,z16,z6]),(0,[z0,z2,z4,z5,z8,z1241]),(0,[z2,z4,z142,z81,z254,z6])],[(0,[z0,z2,z1242,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z1243]),(0,[z19,z0,z24,z5,z8,z42]),(0,[z1244,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z1245]),(0,[z2,z4,z5,z1246,z8,z6])],[(0,[z0,z2,z4,z5,z8,z1247]),(0,[z2,z4,z5,z254,z8,z6]),(0,[z0,z2,z4,z5,z295,z8]),(0,[z0,z2,z4,z5,z1248,z8]),(0,[z0,z2,z5,z8,z1249,z6]),(0,[z127,z2,z4,z5,z8,z347]),(0,[z0,z2,z4,z5,z8,z1250]),(0,[z620,z198,z2,z4,z5,z8])],[(0,[z2,z493,z4,z5,z8,z13]),(0,[z0,z2,z4,z5,z8,z1251]),(0,[z0,z2,z4,z1252,z8,z6]),(0,[z0,z2,z4,z5,z1253,z8]),(0,[z0,z2,z236,z5,z8,z46])],[(0,[z0,z2,z4,z1254,z8,z6]),(0,[z164,z2,z4,z135,z8,z6]),(0,[z0,z2,z4,z5,z8,z1255]),(0,[z101,z281,z2,z4,z5,z8]),(0,[z0,z2,z65,z118,z8,z42]),(0,[z143,z28,z2,z5,z38,z6]),(0,[z0,z2,z215,z5,z8,z213])],[(0,[z0,z2,z4,z5,z8,z1256]),(0,[z49,z2,z4,z5,z8,z202]),(0,[z138,z0,z23,z2,z5,z6]),(0,[z1257,z2,z4,z5,z8,z6]),(0,[z136,z0,z4,z63,z8,z577]),(0,[z0,z2,z240,z5,z8,z249]),(0,[z0,z2,z4,z5,z1258,z35]),(0,[z2,z4,z5,z8,z1008,z35])]],
   [[(0,[z0,z2,z4,z5,z8,z1259]),(0,[z0,z2,z4,z5,z8,z1260]),(0,[z461,z145,z4,z5,z8,z6]),(0,[z339,z0,z24,z5,z8,z6]),(0,[z0,z2,z4,z63,z441,z6]),(0,[z0,z2,z4,z1261,z5,z8])],[(0,[z0,z1262,z4,z5,z8,z6]),(0,[z0,z2,z4,z762,z8,z6]),(0,[z0,z2,z4,z5,z1258,z6]),(0,[z1263,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z1264,z8,z6]),(0,[z79,z0,z2,z5,z90,z6]),(0,[z281,z205,z4,z5,z8,z25]),(0,[z0,z1265,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z1266])],[(0,[z2,z4,z29,z413,z8,z6]),(0,[z162,z2,z4,z29,z8,z42]),(0,[z2,z4,z5,z8,z709,z333])],[(0,[z497,z2,z4,z5,z8,z20]),(0,[z36,z0,z4,z5,z16,z42]),(1,[z0,z4,z5,z8,z1040]),(0,[z0,z2,z65,z118,z8,z144])],[(0,[z69,z2,z4,z57,z8,z6]),(0,[z0,z2,z4,z5,z1267,z8]),(0,[z0,z2,z4,z171,z8,z1044]),(0,[z64,z0,z2,z62,z168,z6]),(0,[z0,z2,z4,z5,z8,z1268])],[(0,[z0,z2,z4,z5,z8,z1269]),(0,[z0,z2,z4,z5,z1270,z6]),(0,[z12,z160,z2,z4,z5,z8]),(0,[z55,z2,z4,z5,z56,z42]),(0,[z0,z2,z4,z5,z175,z42]),(0,[z2,z4,z5,z192,z8,z747]),(0,[z1271,z2,z4,z5,z8,z6])],[(0,[z0,z2,z4,z5,z8,z1016]),(0,[z0,z2,z4,z191,z332,z5]),(0,[z28,z2,z4,z5,z8,z35]),(0,[z0,z2,z5,z8,z883,z213])],[(0,[z461,z54,z4,z5,z8,z6]),(0,[z0,z2,z1272,z5,z8,z6]),(0,[z0,z2,z4,z5,z1273,z6]),(0,[z0,z2,z4,z5,z1274,z6]),(0,[z497,z2,z4,z5,z8,z35])]],
   [[(0,[z0,z2,z4,z5,z1275,z6]),(0,[z1276,z2,z4,z5,z8,z6]),(0,[z0,z2,z1277,z4,z5,z8]),(0,[z189,z2,z128,z5,z8,z6]),(0,[z0,z2,z65,z773,z8,z6]),(0,[z1278,z408,z2,z4,z5,z8]),(0,[z0,z2,z4,z5,z214,z345])],[(0,[z497,z2,z4,z5,z8,z6]),(0,[z49,z2,z4,z5,z8,z395]),(0,[z0,z2,z4,z5,z8,z1279]),(0,[z869,z564,z2,z4,z5,z8]),(0,[z0,z2,z82,z4,z5,z498])],[(0,[z2,z752,z4,z5,z8,z6]),(0,[z19,z0,z24,z309,z8,z6]),(0,[z138,z76,z0,z2,z4,z5]),(0,[z0,z394,z117,z5,z8,z6]),(0,[z1280,z2,z4,z5,z8,z6]),(0,[z0,z2,z240,z37,z8,z6]),(0,[z0,z2,z4,z5,z8,z1281])],[(0,[z0,z2,z1282,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z1283]),(0,[z0,z2,z1284,z4,z5,z6])],[(0,[z0,z2,z4,z57,z8,z35]),(0,[z138,z0,z2,z128,z5,z6]),(0,[z1285,z2,z4,z5,z8,z6]),(0,[z304,z207,z4,z5,z8,z6]),(0,[z80,z2,z4,z5,z8,z42])],[(0,[z0,z2,z4,z5,z1286,z6]),(0,[z0,z2,z4,z1287,z5,z8]),(0,[z105,z2,z190,z5,z8,z6]),(0,[z0,z2,z4,z5,z1288,z6]),(0,[z80,z2,z4,z5,z56,z6]),(0,[z0,z2,z82,z4,z5,z440]),(0,[z183,z2,z239,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z1289])],[(0,[z164,z0,z4,z63,z8,z6]),(0,[z0,z2,z4,z57,z8,z6]),(0,[z0,z2,z4,z1290,z8,z6]),(0,[z79,z894,z2,z5,z8,z6]),(0,[z1278,z0,z2,z4,z5,z8])],[(0,[z87,z2,z45,z5,z8,z6]),(0,[z0,z2,z4,z8,z1291,z6]),(0,[z0,z2,z4,z5,z458,z6]),(0,[z0,z106,z4,z5,z458,z6]),(0,[z1292,z2,z4,z5,z8,z6]),(0,[z2,z4,z5,z8,z1293,z6]),(0,[z189,z2,z4,z5,z8,z347]),(0,[z0,z2,z83,z5,z8,z388]),(0,[z2,z4,z5,z8,z35,z1294])]],
   [[(0,[z0,z2,z4,z5,z1295,z8]),(0,[z64,z564,z2,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z1296])],[(0,[z79,z0,z2,z5,z8,z35]),(0,[z0,z2,z3,z122,z5,z6]),(0,[z0,z2,z592,z5,z41,z6]),(0,[z0,z2,z4,z5,z1297,z35])],[(0,[z0,z2,z4,z5,z8,z1298]),(0,[z0,z2,z4,z5,z8,z1299]),(0,[z76,z0,z2,z4,z5,z8]),(0,[z2,z4,z5,z1300,z8,z6]),(0,[z0,z2,z239,z5,z441,z6]),(0,[z0,z2,z4,z5,z8,z1301]),(0,[z0,z1302,z4,z5,z8,z6]),(0,[z2,z4,z96,z8,z202,z35]),(0,[z0,z2,z4,z8,z872,z35]),(0,[z66,z0,z4,z5,z8,z610]),(0,[z2,z852,z4,z5,z8,z6])],[(0,[z0,z2,z4,z5,z1303,z8]),(0,[z0,z2,z4,z5,z1304,z8]),(0,[z0,z2,z190,z5,z458,z6]),(0,[z49,z2,z4,z5,z8,z27]),(0,[z0,z2,z582,z118,z8,z6]),(0,[z0,z207,z4,z137,z8,z333]),(0,[z1127,z0,z2,z4,z5,z8]),(0,[z0,z2,z4,z5,z1297,z6]),(0,[z829,z0,z2,z4,z5,z8]),(0,[z0,z2,z277,z4,z110,z5])],[(0,[z0,z479,z4,z5,z8,z35]),(0,[z0,z2,z4,z309,z175,z6]),(0,[z0,z2,z4,z1305,z5,z8]),(0,[z0,z373,z4,z5,z234,z6]),(0,[z0,z2,z4,z8,z872,z6])],[(0,[z0,z1306,z4,z5,z8,z6]),(0,[z0,z2,z1307,z4,z5,z8]),(0,[z0,z2,z4,z5,z8,z1308]),(0,[z0,z2,z1309,z5,z8,z6]),(0,[z136,z4,z192,z63,z8,z6]),(0,[z0,z1310,z4,z5,z8,z6])],[(0,[z0,z479,z4,z5,z8,z6]),(0,[z129,z2,z4,z5,z295,z8]),(0,[z0,z2,z4,z5,z121,z524]),(0,[z85,z2,z4,z5,z34,z42]),(0,[z304,z2,z239,z5,z8,z6]),(0,[z2,z4,z5,z8,z6,z1294]),(0,[z0,z2,z4,z5,z140,z194]),(0,[z1311,z0,z2,z4,z5,z8])],[(0,[z0,z2,z4,z327,z8,z35]),(0,[z648,z0,z4,z63,z8,z6]),(0,[z1039,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z1312]),(0,[z0,z2,z4,z363,z8,z42]),(1,[z0,z2,z5,z8,z883])]],
   [[(0,[z2,z4,z5,z8,z202,z60]),(0,[z19,z0,z253,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z1313]),(0,[z2,z4,z5,z245,z847,z6]),(0,[z1314,z2,z4,z5,z8,z35])],[(0,[z138,z772,z2,z4,z5,z6]),(0,[z183,z2,z4,z5,z8,z42]),(0,[z2,z4,z5,z1315,z8,z6]),(0,[z0,z2,z4,z1316,z8,z6]),(0,[z281,z2,z82,z4,z5,z8]),(0,[z0,z2,z4,z8,z42,z35]),(0,[z0,z2,z4,z5,z719,z6])],[(0,[z0,z2,z4,z1317,z8,z6]),(0,[z0,z2,z4,z5,z1318,z6]),(0,[z0,z2,z4,z5,z8,z1319]),(0,[z1314,z2,z4,z5,z8,z6]),(0,[z0,z2,z4,z5,z8,z846])],[(0,[z0,z2,z1320,z5,z8,z6]),(0,[z0,z2,z24,z57,z8,z6]),(0,[z0,z2,z4,z1321,z8,z6]),(0,[z0,z2,z513,z63,z8,z6]),(0,[z1322,z2,z4,z5,z8,z6]),(0,[z1323,z2,z4,z5,z8,z6]),(0,[z0,z2,z5,z41,z748,z6])],[(0,[z0,z2,z4,z5,z8,z1324]),(0,[z304,z2,z4,z5,z441,z6]),(0,[z0,z2,z4,z5,z8,z1325])],[(0,[z0,z2,z4,z5,z1326,z8]),(0,[z0,z2,z128,z5,z8,z249]),(0,[z0,z2,z4,z5,z8,z1327])],[(0,[z0,z2,z1328,z5,z8,z6]),(0,[z0,z2,z4,z5,z441,z42]),(0,[z1329,z2,z4,z5,z8,z6]),(0,[z127,z2,z4,z5,z8,z35]),(0,[z36,z0,z4,z171,z16,z6]),(0,[z0,z2,z4,z5,z8,z1330]),(0,[z0,z2,z4,z8,z42,z598])],[(0,[z160,z2,z4,z29,z5,z8]),(0,[z1331,z0,z2,z4,z5,z8]),(0,[z136,z0,z4,z63,z547,z6]),(0,[z564,z2,z4,z5,z81,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 522) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 522).take 521) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1043).take 249) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1292)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [522, 521, 249] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 92).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 92).take 97).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 189).take 67).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [92, 97, 67] = true :=
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

end PEqualNP.Outside.L_meta_37239

theorem PEqualNP.Outside.L_meta_37239 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4241026248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4241026248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37239.solve
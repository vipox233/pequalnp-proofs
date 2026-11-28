import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37807

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
  Nat.testBit (4277074602 * 2 ^ 32 + 4242602112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0044204acc4331b8#64 ++ 0x40044204acc4331b#64 ++ 0xe0cc61ffcc4733ff#64 ++ 0xae0cc61ffcc4733f#64 : BitVec 256),
   (0x1115992605d8c2d6#64 ++ 0x81115992605d8c2d#64 ++ 0x333799260ff8c3ff#64 ++ 0x7333799260ff8c3f#64 : BitVec 256),
   (0x04380a38102d5463#64 ++ 0x004380a38102d546#64 ++ 0xec381e38707ffc7e#64 ++ 0xfec381e38707ffc7#64 : BitVec 256),
   (0x2bc015c06a80ab04#64 ++ 0x02bc015c06a80ab0#64 ++ 0xefc01fc07f80ff8d#64 ++ 0xfefc01fc07f80ff8#64 : BitVec 256),
   (0x4eeee0007f760008#64 ++ 0x04eeee0007f76000#64 ++ 0x5fffe0007fff000b#64 ++ 0xf5fffe0007fff000#64 : BitVec 256),
   (0x8fbb5fb500000000#64 ++ 0x08fbb5fb50000000#64 ++ 0x9fffffff80000007#64 ++ 0xe9fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [10, 3]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xe0cc61ffcc4733ff 0xae0cc61ffcc4733f

def z1 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xec381e38707ffc7e 0xfec381e38707ffc7

def z2 : W := mkw 0x04682258d8273529 0x404682258d827352 0xccc866d9f0073c00 0x8ccc866d9f0073c0

def z3 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x333799260ff8c3ff 0x7333799260ff8c3f

def z4 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xefc01fc07f80ff8d 0xfefc01fc07f80ff8

def z5 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x5fffe0007fff000b 0xf5fffe0007fff000

def z6 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x9fffffff80000007 0xe9fffffff8000000

def z7 : W := mkw 0x1115992405d8c246 0x81115992405d8c24 0x133798000ff8c00b 0x7133798000ff8c00

def z8 : W := mkw 0x0000000000000000 0x0000000000000000 0x80cc61ff80000007 0xa80cc61ff8000000

def z9 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x1f339e0000000000 0x41f339e000000000

def z10 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0xff379f267ff8ffff 0xfff379f267ff8fff

def z11 : W := mkw 0x4ac6e0006f520008 0x04ac6e0006f52000 0x5fc7e0007f800009 0xf5fc7e0007f80000

def z12 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0x00380038007f0072 0x000380038007f007

def z13 : W := mkw 0x10158826055840d2 0x810158826055840d 0x1037802600780072 0x0103780260078007

def z14 : W := mkw 0x0004800005500000 0x0000480000550000 0x133780000ff8000b 0x7133780000ff8000

def z15 : W := mkw 0x4044a0007f760008 0x04044a0007f76000 0x400000007fff0008 0x1400000007fff000

def z16 : W := mkw 0x0000000000000000 0x0000000000000000 0xec001e007000fc0c 0xfec001e007000fc0

def z17 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x133781260ff803f3 0x0133781260ff803f

def z18 : W := mkw 0x4efeea387f7f546b 0x04efeea387f7f546 0xfffffe387ffffc7f 0xffffffe387ffffc7

def z19 : W := mkw 0x442a600010260008 0x0442a60001026000 0x0008600000070000 0x0000860000007000

def z20 : W := mkw 0x2bd11de46a80ab04 0x02bd11de46a80ab0 0xfff79fe67f80ff8f 0xffff79fe67f80ff8

def z21 : W := mkw 0x4eee60007e660008 0x04eee60007e66000 0x4ccc60007c47000b 0xa4ccc60007c47000

def z22 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0x600000004c4733f8 0x0600000004c4733f

def z23 : W := mkw 0x8b83558500000000 0x08b8355850000000 0x13c7e1c780000001 0x013c7e1c78000000

def z24 : W := mkw 0x3bd11de66a88ebd6 0x83bd11de66a88ebd 0xefc01fe67f80fffd 0xfefc01fe67f80fff

def z25 : W := mkw 0x9fbbdfb50198c246 0x89fbbdfb50198c24 0x1f339e0003b8c000 0x51f339e0003b8c00

def z26 : W := mkw 0x4eeae0007b360008 0x04eeae0007b36000 0x5ffbe00073bf0000 0xd5ffbe00073bf000

def z27 : W := mkw 0x0111192400000000 0x0011119240000000 0x1337992600000007 0x6133799260000000

def z28 : W := mkw 0x2ff81ff87aadff67 0x02ff81ff87aadff6 0xeff81ff87fffffff 0xfeff81ff87ffffff

def z29 : W := mkw 0x00100a3800095463 0x000100a380009546 0xa0001e380000fc74 0x0a0001e380000fc7

def z30 : W := mkw 0x111119260088c2d6 0x8111119260088c2d 0x200019260000c3f4 0x0200019260000c3f

def z31 : W := mkw 0x153d9b3605d8c2d6 0x8153d9b3605d8c2d 0xbf3f9f3e0ff8c3ff 0xfbf3f9f3e0ff8c3f

def z32 : W := mkw 0x4ffff9247f760008 0x04ffff9247f76000 0x5ffff9267fff000f 0xf5ffff9267fff000

def z33 : W := mkw 0x0000000800011020 0x0000000080001102 0xe00800384047307e 0xae00800384047307

def z34 : W := mkw 0x153d9b3615fcc6d7 0x8153d9b3615fcc6d 0x3f379f263ff8cfff 0x73f379f263ff8cff

def z35 : W := mkw 0x0000000000000000 0x0000000000000000 0x0004012600000007 0x2000401260000000

def z36 : W := mkw 0xaffb5ff56a80ab04 0x0affb5ff56a80ab0 0xffffffffff80ff8f 0xfffffffffff80ff8

def z37 : W := mkw 0x4ac6e0006f520008 0x04ac6e0006f52000 0x13c7e0000f800001 0x013c7e0000f80000

def z38 : W := mkw 0x00442042cc422198 0x400442042cc42219 0x80cc61ff8c000387 0xa80cc61ff8c00038

def z39 : W := mkw 0x8eaa469100000000 0x08eaa46910000000 0x9fffe6d980000003 0xe9fffe6d98000000

def z40 : W := mkw 0x00100a3000084443 0x000100a300008444 0x00001e000000cc00 0x000001e000000cc0

def z41 : W := mkw 0x4eeee048ff773128 0x44eeee048ff77312 0xdfffe0d9ffff300b 0xfdfffe0d9ffff300

def z42 : W := mkw 0x0428000010240000 0x0042800001024000 0x4c380000707f000a 0xf4c380000707f000

def z43 : W := mkw 0x4eaac00033340000 0x04eaac0003334000 0x1f33800033b80000 0x51f33800033b8000

def z44 : W := mkw 0x8fbb5fbd102d5463 0x08fbb5fbd102d546 0xff3b9e38707ffc7e 0xfff3b9e38707ffc7

def z45 : W := mkw 0x0010082000084042 0x0001008200008404 0x0030002000780072 0x0003000200078007

def z46 : W := mkw 0x0428000010240000 0x0042800001024000 0x4c08000070070000 0x84c0800007007000

def z47 : W := mkw 0x843f6a3f844310b8 0x4843f6a3f844310b 0x103fe03f80470072 0x0103fe03f8047007

def z48 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xe00800384c4733fe 0xae00800384c4733f

def z49 : W := mkw 0x00000008102d5463 0x000000008102d546 0x60000000707ffc78 0x160000000707ffc7

def z50 : W := mkw 0x04380a30102c4443 0x004380a30102c444 0x0c301e003038cc00 0x50c301e003038cc0

def z51 : W := mkw 0x4eea6048fa273128 0x44eea6048fa27312 0xccc860d9f0073000 0x8ccc860d9f007300

def z52 : W := mkw 0x4eeee04aff7731b8 0x44eeee04aff7731b 0xffffe1ffffff33ff 0xfffffe1ffffff33f

def z53 : W := mkw 0x2bc015c87aadff67 0x02bc015c87aadff6 0xefc01fc07ffffffd 0xfefc01fc07ffffff

def z54 : W := mkw 0x00402048c8033128 0x400402048c803312 0xc0c860d9c0073000 0x8c0c860d9c007300

def z55 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xac301e383038fc74 0x5ac301e383038fc7

def z56 : W := mkw 0x9fbfdfbf15fdd6f7 0x89fbfdfbf15fdd6f 0xffffffffffffffff 0xffffffffffffffff

def z57 : W := mkw 0x4eeee0027f760098 0x04eeee0027f76009 0x7fffe1267fff03ff 0xf7fffe1267fff03f

def z58 : W := mkw 0x843b4a3500000000 0x0843b4a350000000 0x1033800000000000 0x0103380000000000

def z59 : W := mkw 0x0010082000084042 0x0001008200008404 0x203018200078c07e 0x7203018200078c07

def z60 : W := mkw 0x153d9b3e15fdd6f7 0x8153d9b3e15fdd6f 0xff3f9f3e7fffffff 0xfff3f9f3e7ffffff

def z61 : W := mkw 0x5feff1067ff6829c 0x85feff1067ff6829 0x5fffe1067fff038b 0xf5fffe1067fff038

def z62 : W := mkw 0x8fbb5fb510240000 0x08fbb5fb51024000 0xdffffffff07f000f 0xfdffffffff07f000

def z63 : W := mkw 0x4044a0007f760008 0x04044a0007f76000 0x533780007fff000b 0x7533780007fff000

def z64 : W := mkw 0x4004a00015760008 0x04004a0001576000 0x00000000007f0000 0x000000000007f000

def z65 : W := mkw 0x0428021810251421 0x0042802181025142 0xcc08061870073c00 0x8cc08061870073c0

def z66 : W := mkw 0x0010082000084042 0x0001008200008404 0x200018200000c074 0x0200018200000c07

def z67 : W := mkw 0x011019200088c246 0x0011019200088c24 0x233019200ff8c3ff 0x7233019200ff8c3f

def z68 : W := mkw 0x0fb81fb000000000 0x00fb81fb00000000 0x8ff81ff800000007 0xe8ff81ff80000000

def z69 : W := mkw 0x1055a86ecd5b71fa 0xc1055a86ecd5b71f 0xf0ffe1ffcc7f33ff 0xaf0ffe1ffcc7f33f

def z70 : W := mkw 0x0428021810251421 0x0042802181025142 0xcc380618707f3c0a 0xfcc380618707f3c0

def z71 : W := mkw 0x204000406a80ab04 0x0204000406a80ab0 0x600000007f80ff88 0x1600000007f80ff8

def z72 : W := mkw 0x843b4a3500000000 0x0843b4a350000000 0x103fe03f80000002 0x0103fe03f8000000

def z73 : W := mkw 0x4000800033340000 0x0400080003334000 0x0000000033b80000 0x10000000033b8000

def z74 : W := mkw 0x4ac6e0006f520008 0x04ac6e0006f52000 0x13f7e0000ff8000b 0x713f7e0000ff8000

def z75 : W := mkw 0x0000000800011020 0x0000000080001102 0xe0cc61ffc047307f 0xae0cc61ffc047307

def z76 : W := mkw 0xbfffdff76fd8ebd6 0x8bfffdff76fd8ebd 0xfffffffffff8ffff 0xffffffffffff8fff

def z77 : W := mkw 0x1044a04acddbf3fe 0xc1044a04acddbf3f 0xe0cc61ffcffff3ff 0xbe0cc61ffcffff3f

def z78 : W := mkw 0xabd11ff56a80ab04 0x0abd11ff56a80ab0 0xefc01fffff80ff8d 0xfefc01fffff80ff8

def z79 : W := mkw 0x1105910605d08294 0x81105910605d0829 0x130781060f800381 0x0130781060f80038

def z80 : W := mkw 0x3bd59de66fd8ebd6 0x83bd59de66fd8ebd 0xfff79fe67ff8ffff 0xffff79fe67ff8fff

def z81 : W := mkw 0x2b80158022808a04 0x02b80158022808a0 0x0f001e003380cc00 0x50f001e003380cc0

def z82 : W := mkw 0x00100a3800095463 0x000100a380009546 0xec001e387000fc7c 0xfec001e387000fc7

def z83 : W := mkw 0x004420004c420008 0x0004420004c42000 0x40cc60004c47000b 0xa40cc60004c47000

def z84 : W := mkw 0x2ac004c06a002900 0x02ac004c06a00290 0xecc007c07c003f8d 0xaecc007c07c003f8

def z85 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0xfffffe007ffffc0f 0xffffffe007ffffc0

def z86 : W := mkw 0x0b80158000808204 0x00b8015800080820 0xafc01fc00f80c38d 0xfafc01fc00f80c38

def z87 : W := mkw 0x6bc6f5c06fd2ab0c 0x06bc6f5c06fd2ab0 0x13c7e1c00f800381 0x013c7e1c00f80038

def z88 : W := mkw 0x204000406a80ab04 0x0204000406a80ab0 0xec001e007f80ff8c 0xfec001e007f80ff8

def z89 : W := mkw 0x5fbbd92433bcc246 0x85fbbd92433bcc24 0x1f33980033b8c000 0x51f33980033b8c00

def z90 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xe0c001c04c4733fd 0xae0c001c04c4733f

def z91 : W := mkw 0x91159fb705d8c2d6 0x891159fb705d8c2d 0xb3379fff8ff8c3ff 0x7b3379fff8ff8c3f

def z92 : W := mkw 0x004420004c420008 0x0004420004c42000 0x00c460000c000001 0x000c460000c00000

def z93 : W := mkw 0x2bc035c8ea83bb2c 0x42bc035c8ea83bb2 0xefc87fd9ff87ff8d 0xfefc87fd9ff87ff8

def z94 : W := mkw 0x0000000010240000 0x0000000001024000 0x40000000707f0008 0x140000000707f000

def z95 : W := mkw 0x0eba4a38102d5463 0x00eba4a38102d546 0xfffffe38707ffc7f 0xffffffe38707ffc7

def z96 : W := mkw 0x0000000800011020 0x0000000080001102 0x0008003800470072 0x0000800380047007

def z97 : W := mkw 0x0040000048000000 0x0004000004800000 0x40c000004c000009 0xa40c000004c00000

def z98 : W := mkw 0x442ac00011340000 0x0442ac0001134000 0x1033800000380000 0x0103380000038000

def z99 : W := mkw 0x442ee00015760008 0x0442ee0001576000 0x103fe000007f0002 0x0103fe000007f000

def z100 : W := mkw 0x8fbb5fb5102c4443 0x08fbb5fb5102c444 0x9fffffffb038cc07 0xf9fffffffb038cc0

def z101 : W := mkw 0x0000004a800131b0 0x40000004a800131b 0xa0cc61ff800033f7 0xaa0cc61ff800033f

def z102 : W := mkw 0x4efeea307f760008 0x04efeea307f76000 0xdffffe387fff000f 0xfdffffe387fff000

def z103 : W := mkw 0x81111fb500000000 0x081111fb50000000 0x80001fff80000004 0x080001fff8000000

def z104 : W := mkw 0x8fbb5fbd102d5463 0x08fbb5fbd102d546 0xfffffffff07ffc7f 0xffffffffff07ffc7

def z105 : W := mkw 0x9fbfdfb705d8c2d6 0x89fbfdfb705d8c2d 0xbfffffff8ff8c3ff 0xfbfffffff8ff8c3f

def z106 : W := mkw 0x3bc595c66fd0ab94 0x83bc595c66fd0ab9 0xffc79fc67f80ff8d 0xfffc79fc67f80ff8

def z107 : W := mkw 0x8fbb5fb500808204 0x08fbb5fb50080820 0xbfffffff8f80c38f 0xfbfffffff8f80c38

def z108 : W := mkw 0x2ac424caee4339b8 0x42ac424caee4339b 0xeccc67fffc473fff 0xaeccc67fffc473ff

def z109 : W := mkw 0x0004800005500000 0x0000480000550000 0x000000000ff80008 0x1000000000ff8000

def z110 : W := mkw 0x00402040c8022108 0x400402040c802210 0x00c060c180000000 0x000c060c18000000

def z111 : W := mkw 0x1101110600808294 0x8110111060080829 0x0000010600000380 0x0000001060000038

def z112 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0xfffffffff000fc0f 0xffffffffff000fc0

def z113 : W := mkw 0x4044a0087f7f546b 0x04044a0087f7f546 0x600000007ffffc78 0x1600000007ffffc7

def z114 : W := mkw 0x0ac420006e420008 0x00ac420006e42000 0x4fcc60007fc7000b 0xf4fcc60007fc7000

def z115 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0xdfffe1ffffff000f 0xfdfffe1ffffff000

def z116 : W := mkw 0x853b5fb500000000 0x0853b5fb50000000 0x903fffff80000006 0x0903fffff8000000

def z117 : W := mkw 0x0b80158000000000 0x00b8015800000000 0x8fc01fc000000005 0xe8fc01fc00000000

def z118 : W := mkw 0x0004000204400090 0x0000400020440009 0x200401260c4003ff 0x2200401260c4003f

def z119 : W := mkw 0x1155b96ecddbf3fe 0xc1155b96ecddbf3f 0xf3fff9ffcffff3ff 0xff3fff9ffcffff3f

def z120 : W := mkw 0x00100a3800095463 0x000100a380009546 0xe0081e384047fc7e 0xae0081e384047fc7

def z121 : W := mkw 0x4a82c00023100000 0x04a82c0002310000 0x1303800003800000 0x0130380000380000

def z122 : W := mkw 0x0010082800095062 0x0001008280009506 0xe0381838407ff07e 0xfe0381838407ff07

def z123 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xcfc007c07f803f81 0x8cfc007c07f803f8

def z124 : W := mkw 0x6feef5c07ff6ab0c 0x06feef5c07ff6ab0 0xffffffc07fffff8f 0xfffffffc07fffff8

def z125 : W := mkw 0x6eeee4c07f762908 0x06eeee4c07f76290 0xdfffe6c07fff3c0b 0xfdfffe6c07fff3c0

def z126 : W := mkw 0x8fbf5fb704400090 0x08fbf5fb70440009 0xbfffffff8c4003ff 0xebfffffff8c4003f

def z127 : W := mkw 0x0040004048002100 0x0004000404800210 0xe0c001c04c00338d 0xae0c001c04c00338

def z128 : W := mkw 0x2bc435caeec3bbbc 0x42bc435caeec3bbb 0xefcc7fffffc7ffff 0xfefcc7fffffc7fff

def z129 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c001e0000000004 0xe8c001e000000000

def z130 : W := mkw 0x2ee806d87a253d21 0x02ee806d87a253d2 0xccc806d870073c00 0x8ccc806d870073c0

def z131 : W := mkw 0x043c2a3a946f54fb 0x4043c2a3a946f54f 0x003c603f807f0072 0x0003c603f807f007

def z132 : W := mkw 0x0040004048002100 0x0004000404800210 0x600000004c003388 0x0600000004c00338

def z133 : W := mkw 0x2000000022808a04 0x02000000022808a0 0x000000003380cc00 0x1000000003380cc0

def z134 : W := mkw 0x4eea60007a260008 0x04eea60007a26000 0x4cc8600070070000 0x84cc860007007000

def z135 : W := mkw 0x04380a3010240000 0x004380a301024000 0xcc381e38707f000e 0xfcc381e38707f000

def z136 : W := mkw 0x04782a78d82f756b 0x404782a78d82f756 0xecf87ef9f07ffc7e 0xfecf87ef9f07ffc7

def z137 : W := mkw 0x00442042cc422198 0x400442042cc42219 0x40cc61c7cc47038b 0xa40cc61c7cc47038

def z138 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0x63c001c07f80ff89 0x163c001c07f80ff8

def z139 : W := mkw 0x0a80048000000000 0x00a8004800000000 0x8cc006c000000000 0x88cc006c00000000

def z140 : W := mkw 0x8eee66dbcc4331b8 0x48eee66dbcc4331b 0xeccc67ffcc4733ff 0xaeccc67ffcc4733f

def z141 : W := mkw 0x0000000a800110b0 0x40000000a800110b 0x0000003f80000070 0x00000003f8000007

def z142 : W := mkw 0xafff7fffeec3bbbc 0x4afff7fffeec3bbb 0xffffffffffc7ffff 0xfffffffffffc7fff

def z143 : W := mkw 0x443eea38157f546b 0x0443eea38157f546 0x103fe038007f0072 0x0103fe038007f007

def z144 : W := mkw 0x2bc015c86a81bb24 0x02bc015c86a81bb2 0xefc81ff87fc7ffff 0xfefc81ff87fc7fff

def z145 : W := mkw 0x4eeee0407f762108 0x04eeee0407f76210 0xffffe1c07fff338f 0xfffffe1c07fff338

def z146 : W := mkw 0x0044a04acd5331b8 0x40044a04acd5331b 0xf3ffe1ffcfff33ff 0xff3ffe1ffcfff33f

def z147 : W := mkw 0x0000000000000000 0x0000000000000000 0xe00000004000300c 0xae00000004000300

def z148 : W := mkw 0x0044a0004d520008 0x00044a0004d52000 0x53ffe0004fff000b 0xf53ffe0004fff000

def z149 : W := mkw 0x043c2a3a946f54fb 0x4043c2a3a946f54f 0xec3c7e3ff07ffc7e 0xfec3c7e3ff07ffc7

def z150 : W := mkw 0x04380a3000000000 0x004380a300000000 0x8c381e3800000006 0xe8c381e380000000

def z151 : W := mkw 0x0000000000000000 0x0000000000000000 0x030000000f800009 0x7030000000f80000

def z152 : W := mkw 0x0004004a844131b0 0x40004004a844131b 0xa00401ff8c4033ff 0x2a00401ff8c4033f

def z153 : W := mkw 0x1bd599266fd8c2d6 0x81bd599266fd8c2d 0x7ff799267ff8c3ff 0xf7ff799267ff8c3f

def z154 : W := mkw 0x1004800205d8c2d6 0x81004800205d8c2d 0x333780000ff8c3fb 0x7333780000ff8c3f

def z155 : W := mkw 0x042c800015740000 0x0042c80001574000 0x5f3f80007fff000b 0xf5f3f80007fff000

def z156 : W := mkw 0xcfbfffb515760008 0x0cfbfffb51576000 0x9fffffff807f0007 0xe9fffffff807f000

def z157 : W := mkw 0x04280218102d5463 0x004280218102d546 0xec080618707ffc78 0x9ec080618707ffc7

def z158 : W := mkw 0x210015c00080ab04 0x0210015c00080ab0 0xa0001fc00000ff84 0x0a0001fc00000ff8

def z159 : W := mkw 0x4044a04aff7731b8 0x44044a04aff7731b 0xe0cc61ffffff33ff 0xbe0cc61ffffff33f

def z160 : W := mkw 0x8fff7ff7cc422198 0x48fff7ff7cc42219 0x9fffffff8c000387 0xe9fffffff8c00038

def z161 : W := mkw 0x0ac000006a000000 0x00ac000006a00000 0x4fc000007f800009 0xf4fc000007f80000

def z162 : W := mkw 0x157dbb7eddfff7ff 0xc157dbb7eddfff7f 0xffffffffffffffff 0xffffffffffffffff

def z163 : W := mkw 0xcfffffb57f760008 0x0cfffffb57f76000 0xdfffffffffff000f 0xfdfffffffffff000

def z164 : W := mkw 0x014011404880a304 0x0014011404880a30 0xe3c019c04f80f38d 0xfe3c019c04f80f38

def z165 : W := mkw 0x0004200a844310b8 0x40004200a844310b 0x000c603f80470072 0x0000c603f8047007

def z166 : W := mkw 0x047c2a7adc6f75fb 0x4047c2a7adc6f75f 0xec381e387c7ffffe 0xfec381e387c7ffff

def z167 : W := mkw 0x0000000000000000 0x0000000000000000 0x200001000c00038d 0x2200001000c00038

def z168 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x5f3380007fff0008 0x55f3380007fff000

def z169 : W := mkw 0x004420084c431028 0x0004420084c43102 0xe0cc60384c47307f 0xae0cc60384c47307

def z170 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xa0381e38007ffc76 0x0a0381e38007ffc7

def z171 : W := mkw 0x0fb81fb8102d5463 0x00fb81fb8102d546 0xeff81ff8707ffc7f 0xfeff81ff8707ffc7

def z172 : W := mkw 0x0004000204400090 0x0000400020440009 0x0004002600400072 0x0000400260040007

def z173 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xefcc7fffff80ff8f 0xfefcc7fffff80ff8

def z174 : W := mkw 0x047c2a7adc6f75fb 0x4047c2a7adc6f75f 0xe0fc61ffcc7f33ff 0xae0fc61ffcc7f33f

def z175 : W := mkw 0x2ac004c06a002900 0x02ac004c06a00290 0xccc006c070003c00 0x8ccc006c070003c0

def z176 : W := mkw 0x1004800205d8c2d6 0x81004800205d8c2d 0x200000000ff8c3f8 0x1200000000ff8c3f

def z177 : W := mkw 0x8eaa469100000000 0x08eaa46910000000 0x8cc866d980000000 0x88cc866d98000000

def z178 : W := mkw 0x0040204ac80331b8 0x40040204ac80331b 0xe0c861ffc00733f4 0x8e0c861ffc00733f

def z179 : W := mkw 0x210015c00080ab04 0x0210015c00080ab0 0xa3001fc00f80ff8d 0x7a3001fc00f80ff8

def z180 : W := mkw 0x0100110000808204 0x0010011000080820 0x230019000f80c38d 0x7230019000f80c38

def z181 : W := mkw 0xabc355c56a80ab04 0x0abc355c56a80ab0 0xffc7ffc7ff80ff8d 0xfffc7ffc7ff80ff8

def z182 : W := mkw 0x5ffff9267ffec2de 0x85ffff9267ffec2d 0x7ffff9267fffc3ff 0xf7ffff9267fffc3f

def z183 : W := mkw 0xdfffffb77ffec2de 0x8dfffffb77ffec2d 0xffffffffffffc3ff 0xfffffffffffffc3f

def z184 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0x0fc01fc03f80cf81 0x50fc01fc03f80cf8

def z185 : W := mkw 0x8fff7fffcc4331b8 0x48fff7fffcc4331b 0xffffffffcc4733ff 0xeffffffffcc4733f

def z186 : W := mkw 0x00402048c8033128 0x400402048c803312 0xe0c860f9c047307e 0xae0c860f9c047307

def z187 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x333398000ff8c3f8 0x5333398000ff8c3f

def z188 : W := mkw 0x8fbb5fbd102d5463 0x08fbb5fbd102d546 0x9fffffff807f0077 0xe9fffffff807f007

def z189 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x13ffe1ff80000003 0x013ffe1ff8000000

def z190 : W := mkw 0x0428021810251421 0x0042802181025142 0xec081e187007fc0c 0xfec081e187007fc0

def z191 : W := mkw 0x0eaec00005500000 0x00eaec0000550000 0x1fffe0000ff8000b 0xf1fffe0000ff8000

def z192 : W := mkw 0x0000000000000000 0x0000000000000000 0x80c860d980000000 0x880c860d98000000

def z193 : W := mkw 0x0000004a800131b0 0x40000004a800131b 0xa00001ff800033f4 0x0a00001ff800033f

def z194 : W := mkw 0x0040004048002100 0x0004000404800210 0xe0cc61ffcc00338f 0xae0cc61ffcc00338

def z195 : W := mkw 0x04380a30102c4443 0x004380a30102c444 0x4c381e00707fcc0a 0xf4c381e00707fcc0

def z196 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0001e000000fc04 0x0a0001e000000fc0

def z197 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0x4fc001c07f800389 0xf4fc001c07f80038

def z198 : W := mkw 0x2ac004c06a002900 0x02ac004c06a00290 0xcfc006c07f803c09 0xfcfc006c07f803c0

def z199 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x133799060fb8c381 0x5133799060fb8c38

def z200 : W := mkw 0x843b4a3500000000 0x0843b4a350000000 0x90ffe1ff80000007 0xa90ffe1ff8000000

def z201 : W := mkw 0x0eee60004c420008 0x00eee60004c42000 0x5fffe0004c47000b 0xe5fffe0004c47000

def z202 : W := mkw 0x1015882605d8c2d6 0x81015882605d8c2d 0x303780260ff8c3fa 0x1303780260ff8c3f

def z203 : W := mkw 0x04380a30102c4443 0x004380a30102c444 0xec301e007038fc0c 0xfec301e007038fc0

def z204 : W := mkw 0x8fbb5fb500084042 0x08fbb5fb50008404 0xbfffffff8078c07f 0xfbfffffff8078c07

def z205 : W := mkw 0x153d9b3e15fdd6f7 0x8153d9b3e15fdd6f 0x333f993e0fffc3ff 0x7333f993e0fffc3f

def z206 : W := mkw 0x1111196e8089f3f6 0xc1111196e8089f3f 0xa00019ff8000f3f4 0x0a00019ff8000f3f

def z207 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xcc380638707f3c72 0x8cc380638707f3c7

def z208 : W := mkw 0x00140822044840d2 0x000140822044840d 0x203419260c78c3ff 0x7203419260c78c3f

def z209 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x9ffbfed980000000 0xc9ffbfed98000000

def z210 : W := mkw 0x8eaa469100000000 0x08eaa46910000000 0x0c00060000000000 0x00c0006000000000

def z211 : W := mkw 0x4eaee00037760008 0x04eaee0003776000 0x1f3fe00033ff0002 0x51f3fe00033ff000

def z212 : W := mkw 0x11111b3e0089d6f7 0x811111b3e0089d6f 0xa0001f3e0000fff4 0x0a0001f3e0000fff

def z213 : W := mkw 0x111119260088c2d6 0x8111119260088c2d 0x203019260078c3fe 0x7203019260078c3f

def z214 : W := mkw 0x4efa6a387a2f546b 0x04efa6a387a2f546 0xecf87e38707ffc7e 0xfecf87e38707ffc7

def z215 : W := mkw 0x047c2a7adc6f75fb 0x4047c2a7adc6f75f 0xecfc7ffffc7fffff 0xfecfc7ffffc7ffff

def z216 : W := mkw 0xafbb5fb522808a04 0x0afbb5fb522808a0 0x9fffffffb380cc07 0xf9fffffffb380cc0

def z217 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xc0cc61dfcc073381 0x8c0cc61dfcc07338

def z218 : W := mkw 0x2ac004c06a80ab04 0x02ac004c06a80ab0 0xecc006c07f80ff88 0x9ecc006c07f80ff8

def z219 : W := mkw 0x0111192400808204 0x0011119240080820 0x333799260f80c38f 0x7333799260f80c38

def z220 : W := mkw 0x8b83558500000000 0x08b8355850000000 0x93cfe1ff80000007 0xa93cfe1ff8000000

def z221 : W := mkw 0x00542a7acc4b75fb 0x400542a7acc4b75f 0xe0cc7fffcc47ffff 0xae0cc7fffcc47fff

def z222 : W := mkw 0x4eeee0087f7f546b 0x04eeee0087f7f546 0x7fffe0007ffffc7b 0xf7fffe0007ffffc7

def z223 : W := mkw 0x2bc435c2eec2ab9c 0x42bc435c2eec2ab9 0xefc47fc7ff80ff8d 0xfefc47fc7ff80ff8

def z224 : W := mkw 0x15399b3c11bdd667 0x815399b3c11bdd66 0xff3b9e3873fffc7e 0xfff3b9e3873fffc7

def z225 : W := mkw 0x00442048cc433128 0x400442048cc43312 0xc0cc60d9cc47300b 0xac0cc60d9cc47300

def z226 : W := mkw 0x31159de605d8ebd6 0x831159de605d8ebd 0xb3379fe60ff8ffff 0x7b3379fe60ff8fff

def z227 : W := mkw 0x4feef5807f760008 0x04feef5807f76000 0xdfffffc07fff000f 0xfdfffffc07fff000

def z228 : W := mkw 0x0000000000000000 0x0000000000000000 0x8008003800000006 0xa800800380000000

def z229 : W := mkw 0x2100158000808a04 0x02100158000808a0 0x00001e000000cc00 0x000001e000000cc0

def z230 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x9f3b9e3800000006 0xe9f3b9e380000000

def z231 : W := mkw 0x0040004048002100 0x0004000404800210 0xc0c000c040003000 0x8c0c000c04000300

def z232 : W := mkw 0x004420004c420008 0x0004420004c42000 0xc0cc61ffcc47000f 0xac0cc61ffcc47000

def z233 : W := mkw 0x1145b146cdd2a39c 0xc1145b146cdd2a39 0x13c7e1c78f800381 0x013c7e1c78f80038

def z234 : W := mkw 0x2b80158022808a04 0x02b80158022808a0 0x8fc01fc03380cc05 0xf8fc01fc03380cc0

def z235 : W := mkw 0x00100a3800095463 0x000100a380009546 0xa0301e380078fc7e 0x7a0301e380078fc7

def z236 : W := mkw 0x0b80158000000000 0x00b8015800000000 0x8fcc7fff80000007 0xe8fcc7fff8000000

def z237 : W := mkw 0x0004800205500090 0x0000480020550009 0x333781260ff803ff 0x7333781260ff803f

def z238 : W := mkw 0x0eaa400000000000 0x00eaa40000000000 0x1fffe00000000003 0xe1fffe0000000000

def z239 : W := mkw 0x0000000000084042 0x0000000000008404 0x200000000078c078 0x1200000000078c07

def z240 : W := mkw 0x00000008102d5463 0x000000008102d546 0xec001e00707ffc7c 0xfec001e00707ffc7

def z241 : W := mkw 0x0000800001100000 0x0000080000110000 0x1333800003b80000 0x51333800003b8000

def z242 : W := mkw 0x0a80000022000000 0x00a8000002200000 0x0f00000033800000 0x50f0000003380000

def z243 : W := mkw 0x5bc7f1066fd2829c 0x85bc7f1066fd2829 0x13c7e1060f800381 0x013c7e1060f80038

def z244 : W := mkw 0x05391b3400000000 0x005391b340000000 0x9f3f9f3e00000007 0xe9f3f9f3e0000000

def z245 : W := mkw 0x8ebb4eb500000000 0x08ebb4eb50000000 0x9cffe6ff80000002 0x89cffe6ff8000000

def z246 : W := mkw 0x15399b3411bcc647 0x815399b3411bcc64 0x1f339e0033b8cc00 0x51f339e0033b8cc0

def z247 : W := mkw 0x4eee604afe6731b8 0x44eee604afe6731b 0xeccc61fffc4733ff 0xaeccc61fffc4733f

def z248 : W := mkw 0x8ffb5fb56a000000 0x08ffb5fb56a00000 0xdfffffffff80000f 0xfdfffffffff80000

def z249 : W := mkw 0x0040004048002100 0x0004000404800210 0x00c001c00c000381 0x000c001c00c00038

def z250 : W := mkw 0x8fab579500000000 0x08fab57950000000 0x9fcfe7df80000001 0x89fcfe7df8000000

def z251 : W := mkw 0x5155b9267ffec2de 0x85155b9267ffec2d 0x733799267fffc3ff 0x7733799267fffc3f

def z252 : W := mkw 0x85391fbd102d5463 0x085391fbd102d546 0xec381ffff07ffc7e 0xfec381ffff07ffc7

def z253 : W := mkw 0x0ac000006a000000 0x00ac000006a00000 0x03c000000f800001 0x003c000000f80000

def z254 : W := mkw 0x443eea38157f546b 0x0443eea38157f546 0xfc3ffe38707ffc7e 0xffc3ffe38707ffc7

def z255 : W := mkw 0x2b80158022808a04 0x02b80158022808a0 0xef001e007380fc0c 0xfef001e007380fc0

def z256 : W := mkw 0x9fbbdfb50198c246 0x89fbbdfb50198c24 0x9fffffff83b8c007 0xf9fffffff83b8c00

def z257 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0x0c381e38307fcc72 0x50c381e38307fcc7

def z258 : W := mkw 0x2bc415c26ec0ab94 0x02bc415c26ec0ab9 0xefc41fe67fc0ffff 0xfefc41fe67fc0fff

def z259 : W := mkw 0x0000000000000000 0x0000000000000000 0x80c001c000000005 0xa80c001c00000000

def z260 : W := mkw 0x4ebaca30333c4443 0x04ebaca30333c444 0x1f339e0033b8cc00 0x51f339e0033b8cc0

def z261 : W := mkw 0x0ac000006a000000 0x00ac000006a00000 0xefc01e007f80fc0d 0xfefc01e007f80fc0

def z262 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0x8fc01fc00f800385 0xe8fc01fc00f80038

def z263 : W := mkw 0x9b97dda705d8c2d6 0x89b97dda705d8c2d 0x33f7f9e78ff8c3ff 0x733f7f9e78ff8c3f

def z264 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0x60cc60004c4733fb 0xa60cc60004c4733f

def z265 : W := mkw 0x0000200880031028 0x4000020088003102 0x0008601980070000 0x0000860198007000

def z266 : W := mkw 0x8a82448100000000 0x08a8244810000000 0x00c060c180000000 0x000c060c18000000

def z267 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c00000070000008 0xf4c0000007000000

def z268 : W := mkw 0x0004000204400090 0x0000400020440009 0x200000000c4003f8 0x0200000000c4003f

def z269 : W := mkw 0x9fbfdfb7055840d2 0x89fbfdfb7055840d 0x9fffffff80780077 0xe9fffffff8078007

def z270 : W := mkw 0x0155396ecc4331b8 0x40155396ecc4331b 0xf3fff9ffcc4733ff 0xef3fff9ffcc4733f

def z271 : W := mkw 0x0faa558000000000 0x00faa55800000000 0x9fffffc000000007 0xe9fffffc00000000

def z272 : W := mkw 0x4eaac00033340000 0x04eaac0003334000 0x5f3b800073ff000a 0xf5f3b800073ff000

def z273 : W := mkw 0x0111192400000000 0x0011119240000000 0x93fff9ff80000007 0xe93fff9ff8000000

def z274 : W := mkw 0x0ac000406a002100 0x00ac000406a00210 0xefc001c07f80338d 0xfefc001c07f80338

def z275 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0x23c019c00f80c38d 0x723c019c00f80c38

def z276 : W := mkw 0x004420024c420098 0x0004420024c42009 0x60cc61264c4703ff 0xa60cc61264c4703f

def z277 : W := mkw 0x047c2a7acc4331b8 0x4047c2a7acc4331b 0xecfc7fffcc4733ff 0xeecfc7fffcc4733f

def z278 : W := mkw 0x0b911da400000000 0x00b911da40000000 0x9ff79fe600000007 0xe9ff79fe60000000

def z279 : W := mkw 0x843b4a3d102d5463 0x0843b4a3d102d546 0xfc3ffe3ff07ffc7e 0xffc3ffe3ff07ffc7

def z280 : W := mkw 0x00442042cc422198 0x400442042cc42219 0x00c461c78c000381 0x000c461c78c00038

def z281 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x9ff39fc000000005 0xe9ff39fc00000000

def z282 : W := mkw 0x25381ff810adff67 0x025381ff810adff6 0xec381ff8707ffffe 0xfec381ff8707ffff

def z283 : W := mkw 0x111199240198c246 0x8111199240198c24 0x1333980003b8c000 0x51333980003b8c00

def z284 : W := mkw 0x0100110000808204 0x0010011000080820 0x030018000380c000 0x5030018000380c00

def z285 : W := mkw 0x0428021810251421 0x0042802181025142 0x0008001800070000 0x0000800180007000

def z286 : W := mkw 0x046c204adc6731b8 0x4046c204adc6731b 0xecfc61fffc7f33ff 0xfecfc61fffc7f33f

def z287 : W := mkw 0x0000004000002100 0x0000000400000210 0xa00001c000003384 0x0a00001c00000338

def z288 : W := mkw 0x4044a04aff7731b8 0x44044a04aff7731b 0x600000007fff33f8 0x1600000007fff33f

def z289 : W := mkw 0x2bc435caeec3bbbc 0x42bc435caeec3bbb 0xefc01fc07fc7fffd 0xfefc01fc07fc7fff

def z290 : W := mkw 0x046c225adc6735b9 0x4046c225adc6735b 0xeccc67fffc473fff 0xaeccc67fffc473ff

def z291 : W := mkw 0x6eea64c07a262908 0x06eea64c07a26290 0xccc866c070073c00 0x8ccc866c070073c0

def z292 : W := mkw 0x04380820102c4042 0x004380820102c404 0x6c381820707fc07e 0xf6c381820707fc07

def z293 : W := mkw 0x3bd5bdeeefdbfbfe 0xc3bd5bdeeefdbfbf 0xffffffffffffffff 0xffffffffffffffff

def z294 : W := mkw 0x0004800005500000 0x0000480000550000 0x130780000f800001 0x0130780000f80000

def z295 : W := mkw 0xceeee6917f760008 0x0ceeee6917f76000 0xdfffe6d9ffff000b 0xfdfffe6d9ffff000

def z296 : W := mkw 0x04380a3000000000 0x004380a300000000 0xec381e387000fc0e 0xfec381e387000fc0

def z297 : W := mkw 0x00100a7a800975f3 0x400100a7a800975f 0xa0001fff8000fff4 0x0a0001fff8000fff

def z298 : W := mkw 0x1105910605d08294 0x81105910605d0829 0x330799060f80c38d 0x7330799060f80c38

def z299 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0x03c001c00f800381 0x003c001c00f80038

def z300 : W := mkw 0x85391fb500000000 0x085391fb50000000 0x8c381fff80000006 0xe8c381fff8000000

def z301 : W := mkw 0x8faa579100000000 0x08faa57910000000 0x8fc87fd980000005 0xe8fc87fd98000000

def z302 : W := mkw 0x04380a30102c4443 0x004380a30102c444 0x0030000000380000 0x0003000000038000

def z303 : W := mkw 0x1b959da605d8c2d6 0x81b959da605d8c2d 0xbff79fe60ff8c3ff 0xfbff79fe60ff8c3f

def z304 : W := mkw 0x0000000000000000 0x0000000000000000 0x400800004047000a 0xa400800004047000

def z305 : W := mkw 0x115599664dd8e3d6 0x8115599664dd8e3d 0xf3f799e64ff8f3ff 0xff3f799e64ff8f3f

def z306 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x9f339fff80000004 0x49f339fff8000000

def z307 : W := mkw 0x204000487aadff67 0x0204000487aadff6 0x600000007ffffff8 0x1600000007ffffff

def z308 : W := mkw 0x0ac480006f500000 0x00ac480006f50000 0x5ff780007ff8000b 0xf5ff780007ff8000

def z309 : W := mkw 0x3b959da627d8cad6 0x83b959da627d8cad 0x3f379f263ff8cfff 0x73f379f263ff8cff

def z310 : W := mkw 0x4ac6e0007f760008 0x04ac6e0007f76000 0x53c7e0007fff0009 0x153c7e0007fff000

def z311 : W := mkw 0x4eeee0006f520008 0x04eeee0006f52000 0x1fffe0000f800003 0xe1fffe0000f80000

def z312 : W := mkw 0x0040004848013120 0x0004000484801312 0xe0c801f84c4733ff 0xae0c801f84c4733f

def z313 : W := mkw 0x00402048c8033128 0x400402048c803312 0x4000000040073000 0x0400000004007300

def z314 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c001e003000cc00 0x50c001e003000cc0

def z315 : W := mkw 0x0eaa400000000000 0x00eaa40000000000 0x1f33800000000000 0x41f3380000000000

def z316 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0xb3fff9ff8ff8c3ff 0xfb3fff9ff8ff8c3f

def z317 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xeccc7ffffc47ffff 0xfeccc7ffffc47fff

def z318 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x13ffe0000fff0003 0x013ffe0000fff000

def z319 : W := mkw 0xcfffffb56f520008 0x0cfffffb56f52000 0x9fffffff8f800007 0xe9fffffff8f80000

def z320 : W := mkw 0x8eea66d9c8033128 0x48eea66d9c803312 0xccc866d9c0073000 0x8ccc866d9c007300

def z321 : W := mkw 0x2fe817d87aa5bf25 0x02fe817d87aa5bf2 0xefc81fd87f87ff8d 0xfefc81fd87f87ff8

def z322 : W := mkw 0x0000000800095463 0x0000000080009546 0x200000000000fc70 0x0200000000000fc7

def z323 : W := mkw 0x2b80158022808a04 0x02b80158022808a0 0x0300000003800000 0x0030000000380000

def z324 : W := mkw 0x442ee00015760008 0x0442ee0001576000 0x133fe0000fff000b 0x7133fe0000fff000

def z325 : W := mkw 0x05391b3c102d5463 0x005391b3c102d546 0xff3f9f3e707ffc7f 0xfff3f9f3e707ffc7

def z326 : W := mkw 0x10158826055840d2 0x810158826055840d 0x133780260ff8007b 0x7133780260ff8007

def z327 : W := mkw 0x8eaa469100000000 0x08eaa46910000000 0x8ccc67ff80000007 0xa8ccc67ff8000000

def z328 : W := mkw 0x8fbf7fbf844310b8 0x48fbf7fbf844310b 0x9fffffff80470077 0xe9fffffff8047007

def z329 : W := mkw 0x0000000000000000 0x0000000000000000 0x600000007000fc08 0x1600000007000fc0

def z330 : W := mkw 0x4eea60007a260008 0x04eea60007a26000 0x5fffe00070070003 0xe5fffe0007007000

def z331 : W := mkw 0x111199240198c246 0x8111199240198c24 0x333399000fb8c38d 0x7333399000fb8c38

def z332 : W := mkw 0x1005800605500090 0x8100580060550009 0x1007800600000000 0x0100780060000000

def z333 : W := mkw 0x0bc015806a000000 0x00bc015806a00000 0xcfc01fc07f80000d 0xfcfc01fc07f80000

def z334 : W := mkw 0x0eaa400000000000 0x00eaa40000000000 0x9fffe1ff80000007 0xe9fffe1ff8000000

def z335 : W := mkw 0xcbc7f5856f520008 0x0cbc7f5856f52000 0x13c7e1c78f800001 0x013c7e1c78f80000

def z336 : W := mkw 0xc43fea3515760008 0x0c43fea351576000 0x103fe03f807f0002 0x0103fe03f807f000

def z337 : W := mkw 0xcfffffb57f760008 0x0cfffffb57f76000 0x5ffffe007fff000b 0xf5ffffe007fff000

def z338 : W := mkw 0x0040004ac80131b0 0x40040004ac80131b 0xe0c001ffcc0033fd 0xae0c001ffcc0033f

def z339 : W := mkw 0x0104110204c08294 0x00104110204c0829 0x230419260fc0c3ff 0x7230419260fc0c3f

def z340 : W := mkw 0x0101110400000000 0x0010111040000000 0x1307810600000001 0x0130781060000000

def z341 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0x6c301e00707ffc78 0x56c301e00707ffc7

def z342 : W := mkw 0x9fbfdfb705d8c2d6 0x89fbfdfb705d8c2d 0x3f379f260ff8c3ff 0x73f379f260ff8c3f

def z343 : W := mkw 0x8003400500000000 0x0800340050000000 0x1007e00780000000 0x01007e0078000000

def z344 : W := mkw 0x4eea60007a260008 0x04eea60007a26000 0x4fc860007f870009 0xf4fc860007f87000

def z345 : W := mkw 0xaffb5ff56a80ab04 0x0affb5ff56a80ab0 0x9fffffff8f800387 0xe9fffffff8f80038

def z346 : W := mkw 0x843b4a3d102d5463 0x0843b4a3d102d546 0x103fe03f807f0072 0x0103fe03f807f007

def z347 : W := mkw 0x2fb81fb832adde67 0x02fb81fb832adde6 0xef381e3873fffc7e 0xfef381e3873fffc7

def z348 : W := mkw 0x81553fffcc4331b8 0x481553fffcc4331b 0xe0cc7fffcc4733ff 0xae0cc7fffcc4733f

def z349 : W := mkw 0x4eaa400032240000 0x04eaa40003224000 0x0c00000030000000 0x00c0000003000000

def z350 : W := mkw 0x0115992405500000 0x0011599240550000 0x133799260ff8000f 0x7133799260ff8000

def z351 : W := mkw 0x1011882401184042 0x8101188240118404 0x1033800000380000 0x0103380000038000

def z352 : W := mkw 0x0428000010240000 0x0042800001024000 0xec381e00707ffc0e 0xfec381e00707ffc0

def z353 : W := mkw 0x100080000198c246 0x8100080000198c24 0x0000000003b8c000 0x10000000003b8c00

def z354 : W := mkw 0x0104910005d08204 0x00104910005d0820 0x333799000ff8c38f 0x7333799000ff8c38

def z355 : W := mkw 0xabc355c56a80ab04 0x0abc355c56a80ab0 0x13c7e1c78f800381 0x013c7e1c78f80038

def z356 : W := mkw 0x0428000010240000 0x0042800001024000 0x0c30000030380000 0x50c3000003038000

def z357 : W := mkw 0x4ac4a0007f760008 0x04ac4a0007f76000 0x4fc000007fff0009 0xf4fc000007fff000

def z358 : W := mkw 0x1115992e05d9d2f6 0x81115992e05d9d2f 0xf33f993e4ffff3ff 0xff33f993e4ffff3f

def z359 : W := mkw 0x0000000800011020 0x0000000080001102 0xc008001840073000 0x8c00800184007300

def z360 : W := mkw 0x4ac6e042ef522198 0x44ac6e042ef52219 0x13c7e1c78f800381 0x013c7e1c78f80038

def z361 : W := mkw 0x04380a3000000000 0x004380a300000000 0x8cfc7fff80000007 0xe8cfc7fff8000000

def z362 : W := mkw 0x1115992e15fdd6f7 0x81115992e15fdd6f 0x733799267fffffff 0x7733799267ffffff

def z363 : W := mkw 0x8fbfdfb505500000 0x08fbfdfb50550000 0x9fffffff8ff8000f 0xf9fffffff8ff8000

def z364 : W := mkw 0x6fead5c07bb4ab04 0x06fead5c07bb4ab0 0xfff39fc07fb8ff8d 0xffff39fc07fb8ff8

def z365 : W := mkw 0x04380a3800011020 0x004380a380001102 0xec381e384047307e 0xeec381e384047307

def z366 : W := mkw 0x200000400080ab04 0x0200000400080ab0 0x200000000000ff80 0x0200000000000ff8

def z367 : W := mkw 0x8fff7fb54c420008 0x08fff7fb54c42000 0xdfffffffcc47000f 0xedfffffffcc47000

def z368 : W := mkw 0x1155b96ecddbf3fe 0xc1155b96ecddbf3f 0x733799264ffff3ff 0x7733799264ffff3f

def z369 : W := mkw 0x0054286acc4b71fa 0x40054286acc4b71f 0xe0fc79ffcc7ff3ff 0xfe0fc79ffcc7ff3f

def z370 : W := mkw 0x0428021000000000 0x0042802100000000 0x8c08061800000000 0x88c0806180000000

def z371 : W := mkw 0x04380a3000000000 0x004380a300000000 0x0038003800000002 0x0003800380000000

def z372 : W := mkw 0x2a80048022000800 0x02a8004802200080 0x0c00060030000c00 0x00c00060030000c0

def z373 : W := mkw 0x5ffffb3e7fffd6ff 0x85ffffb3e7fffd6f 0xffffff3e7fffffff 0xfffffff3e7ffffff

def z374 : W := mkw 0x0428021010240401 0x0042802101024040 0x0c00060030000c00 0x00c00060030000c0

def z375 : W := mkw 0x00000000102c4443 0x000000000102c444 0x000000003038cc00 0x1000000003038cc0

def z376 : W := mkw 0x204000406a002900 0x0204000406a00290 0x4000000070003c00 0x04000000070003c0

def z377 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0x6f001e007f80ff88 0x56f001e007f80ff8

def z378 : W := mkw 0x1105910605d8c2d6 0x81105910605d8c2d 0x330781060ff8c3f9 0x1330781060ff8c3f

def z379 : W := mkw 0x1145b14ecdd3b3bc 0xc1145b14ecdd3b3b 0xf3cfe1ffcfc733ff 0xaf3cfe1ffcfc733f

def z380 : W := mkw 0x0044204adc6f75fb 0x40044204adc6f75f 0x600000007c7ffff8 0x1600000007c7ffff

def z381 : W := mkw 0x4eeac0007b340000 0x04eeac0007b34000 0x5ff380007fb80009 0xf5ff380007fb8000

def z382 : W := mkw 0x8fbb5fb5102c4443 0x08fbb5fb5102c444 0x1f339e003038cc00 0x51f339e003038cc0

def z383 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xe00001ffcc4733fc 0x0e00001ffcc4733f

def z384 : W := mkw 0x2bd01de06a88eb46 0x02bd01de06a88eb4 0xeff01fe07ff8ffff 0xfeff01fe07ff8fff

def z385 : W := mkw 0x0000000000000000 0x0000000000000000 0x003000000078000a 0x7003000000078000

def z386 : W := mkw 0x5bd7f9266fdac2de 0x85bd7f9266fdac2d 0x33f7f9260ff8c3ff 0x733f7f9260ff8c3f

def z387 : W := mkw 0x81111fbd00095463 0x081111fbd0009546 0xa0001fff8000fc74 0x0a0001fff8000fc7

def z388 : W := mkw 0x05381b3810add667 0x005381b3810add66 0xef381f387fffffff 0xfef381f387ffffff

def z389 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0x00cc61ff8c4703f3 0x000cc61ff8c4703f

def z390 : W := mkw 0x4efeea387f7f546b 0x04efeea387f7f546 0x5fffe0387fff007b 0xf5fffe0387fff007

def z391 : W := mkw 0x11159b3e05d9d6f7 0x811159b3e05d9d6f 0xb3379f3e0ff8ffff 0x7b3379f3e0ff8fff

def z392 : W := mkw 0x10158826055840d2 0x810158826055840d 0x303781260c7803ff 0x2303781260c7803f

def z393 : W := mkw 0x3b919da42398ca46 0x83b919da42398ca4 0x1f339e0033b8cc00 0x51f339e0033b8cc0

def z394 : W := mkw 0x1155396ecccbf3fe 0xc1155396ecccbf3f 0xe0cc79ffcc47f3ff 0xae0cc79ffcc47f3f

def z395 : W := mkw 0x1155b9264ddac2de 0x81155b9264ddac2d 0x73fff9264fffc3ff 0xf73fff9264fffc3f

def z396 : W := mkw 0x10158826055840d2 0x810158826055840d 0x303798260078c07e 0x7303798260078c07

def z397 : W := mkw 0x0a82400000000000 0x00a8240000000000 0x13c7e00000000001 0x013c7e0000000000

def z398 : W := mkw 0x0000000000000000 0x0000000000000000 0x00cc600000000003 0xa00cc60000000000

def z399 : W := mkw 0x8eba4eb9102d5463 0x08eba4eb9102d546 0xecf87ef9f07ffc7e 0xfecf87ef9f07ffc7

def z400 : W := mkw 0x0a80000000000000 0x00a8000000000000 0x0fc0000000000001 0xe0fc000000000000

def z401 : W := mkw 0xa1111ff50080ab04 0x0a1111ff50080ab0 0xa0001fff8000ff84 0x0a0001fff8000ff8

def z402 : W := mkw 0x4efeea307f7e444b 0x04efeea307f7e444 0x5ffffe007fffcc0b 0xf5ffffe007fffcc0

def z403 : W := mkw 0x04380a30102c4443 0x004380a30102c444 0x2c301e203078cc7e 0x72c301e203078cc7

def z404 : W := mkw 0x04380a3810251421 0x004380a381025142 0xcc381e3870073c06 0xecc381e3870073c0

def z405 : W := mkw 0x81111fb500000000 0x081111fb50000000 0x00001e0000000000 0x000001e000000000

def z406 : W := mkw 0x9fbfdfb705d08294 0x89fbfdfb705d0829 0x9fffffff8f800387 0xe9fffffff8f80038

def z407 : W := mkw 0x447caa387f7f546b 0x0447caa387f7f546 0xec381e387ffffc7e 0xfec381e387ffffc7

def z408 : W := mkw 0x1105910605d08294 0x81105910605d0829 0x133781060ff8038b 0x7133781060ff8038

def z409 : W := mkw 0x0100110000000000 0x0010011000000000 0x0300190000000005 0x6030019000000000

def z410 : W := mkw 0x00100a3000000000 0x000100a300000000 0x80001e3800000004 0x080001e380000000

def z411 : W := mkw 0x6bc6f5c06fd2ab0c 0x06bc6f5c06fd2ab0 0xffc7ffc07f80ff8d 0xfffc7ffc07f80ff8

def z412 : W := mkw 0x2fea55c06a80ab04 0x02fea55c06a80ab0 0xffffffc07f80ff8f 0xfffffffc07f80ff8

def z413 : W := mkw 0x6feef5807ff68a0c 0x06feef5807ff68a0 0x5ffffe007fffcc0b 0xf5ffffe007fffcc0

def z414 : W := mkw 0x04380a7a902d75f3 0x404380a7a902d75f 0xec381ffff07ffffe 0xfec381ffff07ffff

def z415 : W := mkw 0x0010082000000000 0x0001008200000000 0x0030182000000006 0x6003018200000000

def z416 : W := mkw 0x6ffefff87fffff6f 0x06ffefff87fffff6 0xfffffff87fffffff 0xffffffff87ffffff

def z417 : W := mkw 0x8eaa469910251421 0x08eaa46991025142 0xccc866d9f0073c00 0x8ccc866d9f0073c0

def z418 : W := mkw 0x0111192400000000 0x0011119240000000 0x0000192600000004 0x0000019260000000

def z419 : W := mkw 0xaeea46d16a002900 0x0aeea46d16a00290 0xccc866d9f0003c00 0x8ccc866d9f0003c0

def z420 : W := mkw 0x00442042cc422198 0x400442042cc42219 0x20c461e78c4003ff 0x220c461e78c4003f

def z421 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xe0380038407f307e 0xae0380038407f307

def z422 : W := mkw 0x2ac004c06a002900 0x02ac004c06a00290 0x00c000c000000000 0x000c000c00000000

def z423 : W := mkw 0x046c20005c660008 0x0046c20005c66000 0x4cfc60007c7f000b 0xf4cfc60007c7f000

def z424 : W := mkw 0x3bd19de46b98eb46 0x83bd19de46b98eb4 0xfff39fc07fb8ff8d 0xffff39fc07fb8ff8

def z425 : W := mkw 0x00000008102d5463 0x000000008102d546 0xe0080038707ffc7e 0xbe0080038707ffc7

def z426 : W := mkw 0x943fca37055840d2 0x8943fca37055840d 0x103fe03f80780072 0x0103fe03f8078007

def z427 : W := mkw 0x6044a0407ff6ab0c 0x06044a0407ff6ab0 0x600000007fffff88 0x1600000007fffff8

def z428 : W := mkw 0x543fe826157e40da 0x8543fe826157e40d 0x103fe026007f0072 0x0103fe026007f007

def z429 : W := mkw 0x0428000010240000 0x0042800001024000 0x00380000007f0002 0x000380000007f000

def z430 : W := mkw 0x4eea62187a271429 0x04eea62187a27142 0xccc8661870073c00 0x8ccc8661870073c0

def z431 : W := mkw 0x5eeee0027ffec2de 0x85eeee0027ffec2d 0x7fffe0007fffc3fb 0xf7fffe0007fffc3f

def z432 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x1337982603f8c072 0x51337982603f8c07

def z433 : W := mkw 0x2bc435caeec3bbbc 0x42bc435caeec3bbb 0xe3cc61ffcfc733ff 0xae3cc61ffcfc733f

def z434 : W := mkw 0x0428000000000000 0x0042800000000000 0x0c38000000000002 0xe0c3800000000000

def z435 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x8cc87fff80000004 0x88cc87fff8000000

def z436 : W := mkw 0x0100158000000000 0x0010015800000000 0x80001fc000000004 0x080001fc00000000

def z437 : W := mkw 0xcfffffffff7731b8 0x4cfffffffff7731b 0xffffffffffff33ff 0xfffffffffffff33f

def z438 : W := mkw 0x0000021800011421 0x0000002180001142 0x8000061800003c00 0x08000061800003c0

def z439 : W := mkw 0x0ee800007a240000 0x00ee800007a24000 0x4ff800007fff000b 0xf4ff800007fff000

def z440 : W := mkw 0x00100828102d5463 0x000100828102d546 0x60301820707ffc7e 0x760301820707ffc7

def z441 : W := mkw 0x2b8015c00080ab04 0x02b8015c00080ab0 0xafc01fc00000ff85 0xeafc01fc00000ff8

def z442 : W := mkw 0x4006e00005520008 0x04006e0000552000 0x1007e00000000000 0x01007e0000000000

def z443 : W := mkw 0x2ac024c8ea033928 0x42ac024c8ea03392 0xccc866d9f0073c00 0x8ccc866d9f0073c0

def z444 : W := mkw 0x0004200004420008 0x0000420000442000 0x000c600000470002 0x0000c60000047000

def z445 : W := mkw 0x0eea40006a000000 0x00eea40006a00000 0x5fffe0007f80000b 0xf5fffe0007f80000

def z446 : W := mkw 0x2bc015c06a002900 0x02bc015c06a00290 0xcfc01fc070003c05 0xecfc01fc070003c0

def z447 : W := mkw 0x2bc015caea81bbb4 0x42bc015caea81bbb 0xefc01fffff80fffd 0xfefc01fffff80fff

def z448 : W := mkw 0x0100110000808204 0x0010011000080820 0xef001f007f80ff8d 0xfef001f007f80ff8

def z449 : W := mkw 0x31111de60088ebd6 0x831111de60088ebd 0xa0001fe60000fff4 0x0a0001fe60000fff

def z450 : W := mkw 0x1004800a15fdd6f7 0x81004800a15fdd6f 0x600000007ffffff8 0x1600000007ffffff

def z451 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xec081e387007fc74 0x8ec081e387007fc7

def z452 : W := mkw 0x404020007a260008 0x0404020007a26000 0x4000000070070000 0x0400000007007000

def z453 : W := mkw 0x8fbb5fff800131b0 0x48fbb5fff800131b 0xbfffffff800033f7 0xebfffffff800033f

def z454 : W := mkw 0xcfffffbd7f7f546b 0x0cfffffbd7f7f546 0xfffffffffffffc7f 0xffffffffffffffc7

def z455 : W := mkw 0x8bc775cfcc4331b8 0x48bc775cfcc4331b 0xf3cfe1ffcc4733ff 0xaf3cfe1ffcc4733f

def z456 : W := mkw 0x4eea60007a260008 0x04eea60007a26000 0x4cf86000707f000a 0xf4cf86000707f000

def z457 : W := mkw 0x1014882205d8c2d6 0x81014882205d8c2d 0x203018200ff8c3fe 0x7203018200ff8c3f

def z458 : W := mkw 0x3ffd9ffe7ffdfff7 0x83ffd9ffe7ffdfff 0xffff9ffe7fffffff 0xfffff9ffe7ffffff

def z459 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0x20381838007fc07e 0x720381838007fc07

def z460 : W := mkw 0x8b935fb500000000 0x08b935fb50000000 0x93c7ffff80000005 0x093c7ffff8000000

def z461 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xecfc7ffff07ffc7f 0xfecfc7ffff07ffc7

def z462 : W := mkw 0x111199240198c246 0x8111199240198c24 0x1337992603b8c007 0x71337992603b8c00

def z463 : W := mkw 0x1104910205d8c2d6 0x81104910205d8c2d 0x230019000ff8c3fd 0x7230019000ff8c3f

def z464 : W := mkw 0x853b5b3500000000 0x0853b5b350000000 0x133ff93f80000007 0x6133ff93f8000000

def z465 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xecc01fc07000ff84 0x8ecc01fc07000ff8

def z466 : W := mkw 0x0004000204400090 0x0000400020440009 0xa0cc61ff8c4003ff 0xaa0cc61ff8c4003f

def z467 : W := mkw 0x0004200284420098 0x4000420028442009 0x0004600780000000 0x0000460078000000

def z468 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x5fcfe0007f870001 0x85fcfe0007f87000

def z469 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x330799260f80c3f5 0x0330799260f80c3f

def z470 : W := mkw 0x0010082000084042 0x0001008200008404 0xec301e207078fc7e 0xfec301e207078fc7

def z471 : W := mkw 0xafea57d16a80ab04 0x0afea57d16a80ab0 0xefc87fd9ff80ff8d 0xfefc87fd9ff80ff8

def z472 : W := mkw 0x004000006a000000 0x0004000006a00000 0x400000007f800008 0x1400000007f80000

def z473 : W := mkw 0x8fbb5fbd00095463 0x08fbb5fbd0009546 0xbfffffff8000fc77 0xebfffffff8000fc7

def z474 : W := mkw 0x1115996e85d9f3f6 0xc1115996e85d9f3f 0xb33799ff8ff8f3ff 0x7b33799ff8ff8f3f

def z475 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xa0c461ff8c0033f5 0x0a0c461ff8c0033f

def z476 : W := mkw 0x80110a3500000000 0x080110a350000000 0x0000003f80000000 0x00000003f8000000

def z477 : W := mkw 0x4eeee042ff762198 0x44eeee042ff76219 0x5fffe1c7ffff038b 0xf5fffe1c7ffff038

def z478 : W := mkw 0xafbb5ff50080ab04 0x0afbb5ff50080ab0 0xbfffffff8000ff87 0xebfffffff8000ff8

def z479 : W := mkw 0x953fdb3705d8c2d6 0x8953fdb3705d8c2d 0x333ff93f8ff8c3ff 0x7333ff93f8ff8c3f

def z480 : W := mkw 0x4eeee00aff7710b8 0x44eeee00aff7710b 0x5fffe03fffff007b 0xf5fffe03fffff007

def z481 : W := mkw 0x446ee0005d760008 0x0446ee0005d76000 0x50ffe0004c7f000b 0xa50ffe0004c7f000

def z482 : W := mkw 0x0115192604400090 0x0011519260440009 0x333799260c4003ff 0x6333799260c4003f

def z483 : W := mkw 0x8fff7fffdc6f75fb 0x48fff7fffdc6f75f 0xfffffffffc7fffff 0xffffffffffc7ffff

def z484 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x1ffffe0000000003 0xe1ffffe000000000

def z485 : W := mkw 0x304480426fd8ebd6 0x8304480426fd8ebd 0x600000007ff8fff8 0x1600000007ff8fff

def z486 : W := mkw 0xcfbbdfb533340000 0x0cfbbdfb53334000 0x1f339e0033b80000 0x51f339e0033b8000

def z487 : W := mkw 0xceea66917a260008 0x0ceea66917a26000 0xccc866d9f0070000 0x8ccc866d9f007000

def z488 : W := mkw 0x2fb81fb032acce47 0x02fb81fb032acce4 0x0f301e0033b8cc00 0x50f301e0033b8cc0

def z489 : W := mkw 0x0044200acc4310b8 0x40044200acc4310b 0x40cc603fcc47007b 0xa40cc603fcc47007

def z490 : W := mkw 0x042a400000000000 0x0042a40000000000 0x103fe00000000002 0x0103fe0000000000

def z491 : W := mkw 0x210015c00080ab04 0x0210015c00080ab0 0x000001c000000380 0x0000001c00000038

def z492 : W := mkw 0x200004c000002900 0x0200004c00000290 0x800006c000003c00 0x0800006c000003c0

def z493 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0x4c380038707f007a 0xf4c380038707f007

def z494 : W := mkw 0xcfbbdfb533340000 0x0cfbbdfb53334000 0x9fffffffb3b80007 0xf9fffffffb3b8000

def z495 : W := mkw 0x446ee0007f760008 0x0446ee0007f76000 0x503fe0007fff000a 0x1503fe0007fff000

def z496 : W := mkw 0x4efeea7aff7f75fb 0x44efeea7aff7f75f 0xffffffffffffffff 0xffffffffffffffff

def z497 : W := mkw 0x0428021810251421 0x0042802181025142 0xec08063870473c7e 0xaec08063870473c7

def z498 : W := mkw 0x4ac260006a020008 0x04ac260006a02000 0x00c0600000000000 0x000c060000000000

def z499 : W := mkw 0x8b83558500000000 0x08b8355850000000 0x9fc7ffc780000005 0xe9fc7ffc78000000

def z500 : W := mkw 0x0000004880013120 0x4000000488001312 0x800000d980003000 0x0800000d98000300

def z501 : W := mkw 0x81111fb500000000 0x081111fb50000000 0x80cc7fff80000007 0xa80cc7fff8000000

def z502 : W := mkw 0x81111fff800131b0 0x481111fff800131b 0xa0001fff800033f4 0x0a0001fff800033f

def z503 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x1f3ffe3f80000002 0x41f3ffe3f8000000

def z504 : W := mkw 0x4eeee04aff7731b8 0x44eeee04aff7731b 0x7fffe0007fff33fb 0xf7fffe0007fff33f

def z505 : W := mkw 0x1115992605d08294 0x81115992605d0829 0x133799260f800387 0x6133799260f80038

def z506 : W := mkw 0x5044a0027ffec2de 0x85044a0027ffec2d 0x600000007fffc3f8 0x1600000007fffc3f

def z507 : W := mkw 0x00402048c8033128 0x400402048c803312 0xc0cc61ffc0073007 0xac0cc61ffc007300

def z508 : W := mkw 0x004400424c402190 0x0004400424c40219 0xe0c401e64c4033ff 0xae0c401e64c4033f

def z509 : W := mkw 0x8ffb5ff548002100 0x08ffb5ff54800210 0xffffffffcc00338f 0xeffffffffcc00338

def z510 : W := mkw 0x0000000000000000 0x0000000000000000 0x800001ff80000004 0x0800001ff8000000

def z511 : W := mkw 0x0000000800011020 0x0000000080001102 0xec081e387047fc7e 0xfec081e387047fc7

def z512 : W := mkw 0x111199260198c2d6 0x8111199260198c2d 0x3333992603b8c3f4 0x53333992603b8c3f

def z513 : W := mkw 0x00100a3800095463 0x000100a380009546 0x0000003800000070 0x0000000380000007

def z514 : W := mkw 0x0111192400084042 0x0011119240008404 0x333799260078c07f 0x7333799260078c07

def z515 : W := mkw 0x8ffb7ffdc8033128 0x48ffb7ffdc803312 0xdfffffffc0073007 0xedfffffffc007300

def z516 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0x600c603fcc4733fa 0x0600c603fcc4733f

def z517 : W := mkw 0x6eeee0407ff6ab0c 0x06eeee0407ff6ab0 0x7fffe0007fffff8b 0xf7fffe0007fffff8

def z518 : W := mkw 0x8b83558500000000 0x08b8355850000000 0x1303800000000000 0x0130380000000000

def z519 : W := mkw 0x1155b966cddae3de 0xc1155b966cddae3d 0x33f7f9e78ff8c3ff 0x733f7f9e78ff8c3f

def z520 : W := mkw 0x6feef5cafff7bbbc 0x46feef5cafff7bbb 0xffffffffffffffff 0xffffffffffffffff

def z521 : W := mkw 0x210015ca8081bbb4 0x4210015ca8081bbb 0xa0001fff8000fff4 0x0a0001fff8000fff

def z522 : W := mkw 0x143d8a3e157d54f3 0x8143d8a3e157d54f 0x103f803e007f0072 0x0103f803e007f007

def z523 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xcc381e18703ffc00 0xdcc381e18703ffc0

def z524 : W := mkw 0x81111fb500000000 0x081111fb50000000 0x93379fff80000007 0x693379fff8000000

def z525 : W := mkw 0x204000406a80ab04 0x0204000406a80ab0 0xe0c001c07f80ff8d 0xbe0c001c07f80ff8

def z526 : W := mkw 0x2ac004c06a002900 0x02ac004c06a00290 0xecc01ec07000fc0c 0xfecc01ec07000fc0

def z527 : W := mkw 0x2ff81ff07aacef47 0x02ff81ff07aacef4 0xeff01fc07fb8ff8d 0xfeff01fc07fb8ff8

def z528 : W := mkw 0x0004200a844310b8 0x40004200a844310b 0xe00c603fc047307e 0xae00c603fc047307

def z529 : W := mkw 0x0000000000000000 0x0000000000000000 0x1337800000000003 0x6133780000000000

def z530 : W := mkw 0x3bd59de66fd8ebd6 0x83bd59de66fd8ebd 0x33f799e60ff8c3ff 0x733f799e60ff8c3f

def z531 : W := mkw 0x0100110000808204 0x0010011000080820 0x030001000f800381 0x0030001000f80038

def z532 : W := mkw 0x0bc435cacc4331b8 0x40bc435cacc4331b 0xefcc7fffcc4733ff 0xeefcc7fffcc4733f

def z533 : W := mkw 0x2044204aeec3bbbc 0x42044204aeec3bbb 0xe0cc61ffffc7ffff 0xbe0cc61ffffc7fff

def z534 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x1ff7e0003fb80001 0x51ff7e0003fb8000

def z535 : W := mkw 0x0000004a800131b0 0x40000004a800131b 0x20000000000033f0 0x020000000000033f

def z536 : W := mkw 0x0004200a844310b8 0x40004200a844310b 0x200c613f8c4703ff 0x2200c613f8c4703f

def z537 : W := mkw 0x1fbfd92605d8c2d6 0x81fbfd92605d8c2d 0x3ffff9260ff8c3ff 0xf3ffff9260ff8c3f

def z538 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0x60c461c7cc4733f9 0x060c461c7cc4733f

def z539 : W := mkw 0x5effe8267f7e40da 0x85effe8267f7e40d 0x5fffe0267fff007b 0xf5fffe0267fff007

def z540 : W := mkw 0x2bc435c06ec2ab0c 0x02bc435c06ec2ab0 0xefcc7fc07fc7ff8f 0xfefcc7fc07fc7ff8

def z541 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x1ff7ffc780000001 0x41ff7ffc78000000

def z542 : W := mkw 0x111199240198c246 0x8111199240198c24 0x3333982003f8c07e 0x73333982003f8c07

def z543 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xcfc01ec07380fc00 0xdcfc01ec07380fc0

def z544 : W := mkw 0x0000000200000090 0x0000000020000009 0x20000126000003f4 0x020000126000003f

def z545 : W := mkw 0x2bc015806a808a04 0x02bc015806a808a0 0x4fc01e007f80cc09 0xf4fc01e007f80cc0

def z546 : W := mkw 0x1004800205d08294 0x81004800205d0829 0x000000000f800380 0x0000000000f80038

def z547 : W := mkw 0x0eaa400000000000 0x00eaa40000000000 0x0cc8600000000000 0x80cc860000000000

def z548 : W := mkw 0x2ffc3ffafeefffff 0x42ffc3ffafeeffff 0xeffc7fffffffffff 0xfeffc7ffffffffff

def z549 : W := mkw 0x0010082000084042 0x0001008200008404 0x003018000038c000 0x5003018000038c00

def z550 : W := mkw 0x1004800205d8c2d6 0x81004800205d8c2d 0x200401260ff8c3ff 0x3200401260ff8c3f

def z551 : W := mkw 0x0000000000000000 0x0000000000000000 0x200000200040007e 0x2200000200040007

def z552 : W := mkw 0x04380a3000084042 0x004380a300008404 0xac381e380078c07e 0xfac381e380078c07

def z553 : W := mkw 0x0000000000000000 0x0000000000000000 0x200018000000c00c 0x7200018000000c00

def z554 : W := mkw 0x4eeee2187f771429 0x04eeee2187f77142 0xdfffe6187fff3c0b 0xfdfffe6187fff3c0

def z555 : W := mkw 0x446ca0007f760008 0x0446ca0007f76000 0x4c3800007fff000a 0xf4c3800007fff000

def z556 : W := mkw 0x043c8a38157d5463 0x0043c8a38157d546 0xff3f9e387ffffc7f 0xfff3f9e387ffffc7

def z557 : W := mkw 0x0144314accc3b3bc 0x40144314accc3b3b 0xe3cc79ffcfc7f3ff 0xfe3cc79ffcfc7f3f

def z558 : W := mkw 0x100000020088c2d6 0x8100000020088c2d 0x200000000000c3f0 0x0200000000000c3f

def z559 : W := mkw 0x4ebaca38333d5463 0x04ebaca38333d546 0xff3b9e3873fffc7e 0xfff3b9e3873fffc7

def z560 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x1f379f2600000007 0x61f379f260000000

def z561 : W := mkw 0x442ee00015760008 0x0442ee0001576000 0x5c3fe000707f000a 0xf5c3fe000707f000

def z562 : W := mkw 0x842a421100000000 0x0842a42110000000 0x0008601980000000 0x0000860198000000

def z563 : W := mkw 0x8ebb4a3500000000 0x08ebb4a350000000 0x1fffe03f80000003 0xe1fffe03f8000000

def z564 : W := mkw 0x4eaec00037740000 0x04eaec0003774000 0x1f3780003ff8000b 0x71f3780003ff8000

def z565 : W := mkw 0x8101158500000000 0x0810115850000000 0x000001c780000000 0x0000001c78000000

def z566 : W := mkw 0x91111fb70088c2d6 0x891111fb70088c2d 0xa0001fff8000c3f4 0x0a0001fff8000c3f

def z567 : W := mkw 0x4eeee0087f771028 0x04eeee0087f77102 0xffffe0387fff307f 0xfffffe0387fff307

def z568 : W := mkw 0x0004200a844310b8 0x40004200a844310b 0x0000000000470070 0x0000000000047007

def z569 : W := mkw 0x21101ff80089ff67 0x021101ff80089ff6 0xa0001ff80000fff4 0x0a0001ff80000fff

def z570 : W := mkw 0x00000008102d5463 0x000000008102d546 0x00000000007f0070 0x000000000007f007

def z571 : W := mkw 0x7ffffde67ffeebde 0x87ffffde67ffeebd 0xffffffe67fffffff 0xfffffffe67ffffff

def z572 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0x600401264c4733ff 0x2600401264c4733f

def z573 : W := mkw 0x6faad58033b48a04 0x06faad58033b48a0 0x1f339e0033b8cc00 0x51f339e0033b8cc0

def z574 : W := mkw 0x24780a787aadff67 0x024780a787aadff6 0xec381e387ffffffe 0xfec381e387ffffff

def z575 : W := mkw 0x4efee8207f7e404a 0x04efee8207f7e404 0x7ffff8207fffc07f 0xf7ffff8207fffc07

def z576 : W := mkw 0x9b87d58705d08294 0x89b87d58705d0829 0x13c7e1c78f800381 0x013c7e1c78f80038

def z577 : W := mkw 0x5ffff9247ffec24e 0x85ffff9247ffec24 0x5ffff8007fffc00b 0xf5ffff8007fffc00

def z578 : W := mkw 0x047c2a385c6f546b 0x0047c2a385c6f546 0xecfc7e387c7ffc7f 0xfecfc7e387c7ffc7

def z579 : W := mkw 0x8fbb5fbd10251421 0x08fbb5fbd1025142 0xdffffffff0073c07 0xedffffffff0073c0

def z580 : W := mkw 0x0100110000808204 0x0010011000080820 0x200019000000c384 0x0200019000000c38

def z581 : W := mkw 0x4eaee00015760008 0x04eaee0001576000 0x1fffe000007f0003 0xe1fffe000007f000

def z582 : W := mkw 0x0004000204400090 0x0000400020440009 0x000401060c000381 0x0000401060c00038

def z583 : W := mkw 0x1115b92e85dbd2fe 0xc1115b92e85dbd2f 0x333ff93f8fffc3ff 0x7333ff93f8fffc3f

def z584 : W := mkw 0x4eaac00033340000 0x04eaac0003334000 0x1fffe00033b80003 0xf1fffe00033b8000

def z585 : W := mkw 0x0eaa400010240000 0x00eaa40001024000 0x5fffe000707f000b 0xf5fffe000707f000

def z586 : W := mkw 0x0004000004400000 0x0000400000440000 0x000400000c40000b 0x2000400000c40000

def z587 : W := mkw 0x2bc435c2eec2ab9c 0x42bc435c2eec2ab9 0x03c461c78f800381 0x003c461c78f80038

def z588 : W := mkw 0x04380a30102c4443 0x004380a30102c444 0x8c381e383038cc06 0xf8c381e383038cc0

def z589 : W := mkw 0x2044204aeec3bbbc 0x42044204aeec3bbb 0x600000007fc7fff8 0x1600000007fc7fff

def z590 : W := mkw 0x5fbfd92637fcc2d6 0x85fbfd92637fcc2d 0x3f3799263ff8c3ff 0x73f3799263ff8c3f

def z591 : W := mkw 0x2ff81ff06a80ab04 0x02ff81ff06a80ab0 0xeff81ff87f80ff8f 0xfeff81ff87f80ff8

def z592 : W := mkw 0xaffb5ff56a002900 0x0affb5ff56a00290 0xdffffffff0003c07 0xedffffffff0003c0

def z593 : W := mkw 0x00402048c8033128 0x400402048c803312 0xe0c861d9cc07338d 0xae0c861d9cc07338

def z594 : W := mkw 0x2bc495c06fd0ab04 0x02bc495c06fd0ab0 0xfff79fc07ff8ff8f 0xffff79fc07ff8ff8

def z595 : W := mkw 0x0000004280002190 0x4000000428000219 0x000001c780000380 0x0000001c78000038

def z596 : W := mkw 0x111119240088c246 0x8111119240088c24 0x000018000000c000 0x0000018000000c00

def z597 : W := mkw 0xaffb5ff56a80ab04 0x0affb5ff56a80ab0 0xfff39fc07f80ff8d 0xffff39fc07f80ff8

def z598 : W := mkw 0x8eba4eb100000000 0x08eba4eb10000000 0x8cf87ef980000006 0xe8cf87ef98000000

def z599 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xc0cc60ffc0473072 0x8c0cc60ffc047307

def z600 : W := mkw 0x4feef1007ff6820c 0x04feef1007ff6820 0x7ffff9007fffc38f 0xf7ffff9007fffc38

def z601 : W := mkw 0x3bc495c26fd8ebd6 0x83bc495c26fd8ebd 0xefc01fc07ff8fffd 0xfefc01fc07ff8fff

def z602 : W := mkw 0x4044a0006f520008 0x04044a0006f52000 0x000000000f800000 0x0000000000f80000

def z603 : W := mkw 0x00100a38102d5463 0x000100a38102d546 0xe0001e38707ffc7c 0x1e0001e38707ffc7

def z604 : W := mkw 0x6bc4b5c07ff6ab0c 0x06bc4b5c07ff6ab0 0xefc01fc07fffff8d 0xfefc01fc07fffff8

def z605 : W := mkw 0x0111192400000000 0x0011119240000000 0x1333980000000000 0x4133398000000000

def z606 : W := mkw 0x214015c04880ab04 0x0214015c04880ab0 0xe0c01fc04c00ff8d 0xae0c01fc04c00ff8

def z607 : W := mkw 0x210015c00080ab04 0x0210015c00080ab0 0xec001fc07000ff8c 0xfec001fc07000ff8

def z608 : W := mkw 0xcfeff5857f760008 0x0cfeff5857f76000 0x5fffe1c7ffff000b 0xf5fffe1c7ffff000

def z609 : W := mkw 0x0ef80a387a2d5463 0x00ef80a387a2d546 0xeff81e387ffffc7f 0xfeff81e387ffffc7

def z610 : W := mkw 0x0b80158000000000 0x00b8015800000000 0x03c001c000000001 0x003c001c00000000

def z611 : W := mkw 0x6feef5c07ff6ab0c 0x06feef5c07ff6ab0 0x5fffe1c07fff038b 0xf5fffe1c07fff038

def z612 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x5cffe000707f0002 0x85cffe000707f000

def z613 : W := mkw 0x0011082400000000 0x0001108240000000 0x1037802600000002 0x0103780260000000

def z614 : W := mkw 0x0040200048020008 0x0004020004802000 0x40c8600040070000 0x840c860004007000

def z615 : W := mkw 0x442ee00a957710b8 0x4442ee00a957710b 0x103fe03f807f0072 0x0103fe03f807f007

def z616 : W := mkw 0x8bc775c7cc422198 0x48bc775c7cc42219 0x13c7e1c78c000381 0x013c7e1c78c00038

def z617 : W := mkw 0x0bc011006a808204 0x00bc011006a80820 0x6fc019007f80c38d 0xf6fc019007f80c38

def z618 : W := mkw 0x0ac4204aee4331b8 0x40ac4204aee4331b 0xefcc61ffffc733ff 0xfefcc61ffffc733f

def z619 : W := mkw 0x214435caccc3bbbc 0x4214435caccc3bbb 0xe0cc7fffcc47ffff 0xae0cc7fffcc47fff

def z620 : W := mkw 0x0b80158000000000 0x00b8015800000000 0x0f001e0000000000 0x40f001e000000000

def z621 : W := mkw 0x0b80158000000000 0x00b8015800000000 0xefc01fc07000fc0d 0xfefc01fc07000fc0

def z622 : W := mkw 0x004420404c422108 0x0004420404c42210 0xe0cc61c04c47338f 0xae0cc61c04c47338

def z623 : W := mkw 0x0000000800011020 0x0000000080001102 0xa000003800003074 0x0a00000380000307

def z624 : W := mkw 0x8000069100000000 0x0800006910000000 0x800006d980000000 0x0800006d98000000

def z625 : W := mkw 0x11159926055840d2 0x811159926055840d 0x1337992600780077 0x6133799260078007

def z626 : W := mkw 0x8b935da500000000 0x08b935da50000000 0x13f7f9e780000007 0x613f7f9e78000000

def z627 : W := mkw 0x2bd01ff86a89ff67 0x02bd01ff86a89ff6 0xefc01ff87f80fffd 0xfefc01ff87f80fff

def z628 : W := mkw 0x0004200a844310b8 0x40004200a844310b 0x80cc61ff80470077 0xa80cc61ff8047007

def z629 : W := mkw 0x143d8a3e157d54f3 0x8143d8a3e157d54f 0xfc3f9e3e707ffc7e 0xffc3f9e3e707ffc7

def z630 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x4cc860007fff0008 0x94cc860007fff000

def z631 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0x60380038707ffc7a 0x160380038707ffc7

def z632 : W := mkw 0xeffffff57ff6ab0c 0x0effffff57ff6ab0 0xffffffffffffff8f 0xfffffffffffffff8

def z633 : W := mkw 0x0040004048002100 0x0004000404800210 0xecc01fc07c00ff8d 0xfecc01fc07c00ff8

def z634 : W := mkw 0x4044a0007f760008 0x04044a0007f76000 0x40cc60007fff000b 0xb40cc60007fff000

def z635 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x200019260ff8c3fc 0x1200019260ff8c3f

def z636 : W := mkw 0x1115192604c8c2d6 0x81115192604c8c2d 0x200419260c40c3ff 0x2200419260c40c3f

def z637 : W := mkw 0x0004000a044110b0 0x00004000a044110b 0xe00c013e4c4733ff 0xae00c013e4c4733f

def z638 : W := mkw 0x111119260088c2d6 0x8111119260088c2d 0x230019260f80c3fd 0x7230019260f80c3f

def z639 : W := mkw 0x1101910401908204 0x8110191040190820 0x1303800003800000 0x0130380000380000

def z640 : W := mkw 0x204000406a80ab04 0x0204000406a80ab0 0x000000000f800380 0x0000000000f80038

def z641 : W := mkw 0x2ef80ef87a2d7d63 0x02ef80ef87a2d7d6 0xecf81ef8707ffc7e 0xfecf81ef8707ffc7

def z642 : W := mkw 0x04380a3800095463 0x004380a380009546 0xac381e380000fc76 0xeac381e380000fc7

def z643 : W := mkw 0x004420004c420008 0x0004420004c42000 0x400000004c470008 0x0400000004c47000

def z644 : W := mkw 0x00442042cc422198 0x400442042cc42219 0xe0c461c7cc00338d 0xae0c461c7cc00338

def z645 : W := mkw 0x0004204a844331b8 0x40004204a844331b 0xa00c61ff804733f6 0x0a00c61ff804733f

def z646 : W := mkw 0x446ee04add7731b8 0x4446ee04add7731b 0xf0ffe1ffcc7f33ff 0xaf0ffe1ffcc7f33f

def z647 : W := mkw 0x0428000810251020 0x0042800081025102 0xec380038707f307e 0xfec380038707f307

def z648 : W := mkw 0x0000004a800131b0 0x40000004a800131b 0xe00801ffc04733fe 0xae00801ffc04733f

def z649 : W := mkw 0x0ac000006a000000 0x00ac000006a00000 0x4cc0000070000000 0x84cc000007000000

def z650 : W := mkw 0x0000000000000000 0x0000000000000000 0x000c603f80000002 0x0000c603f8000000

def z651 : W := mkw 0x0bc015c048002100 0x00bc015c04800210 0xefc01fc04c00338d 0xeefc01fc04c00338

def z652 : W := mkw 0x9fffffffcddbf3fe 0xc9fffffffcddbf3f 0xffffffffcffff3ff 0xfffffffffcffff3f

def z653 : W := mkw 0x1044a04acddbf3fe 0xc1044a04acddbf3f 0x600000004ffff3f8 0x1600000004ffff3f

def z654 : W := mkw 0xaffb5ffd7aadff67 0x0affb5ffd7aadff6 0xffffffffffffffff 0xffffffffffffffff

def z655 : W := mkw 0x8b911fb500000000 0x08b911fb50000000 0x8fc01fff80000005 0xe8fc01fff8000000

def z656 : W := mkw 0xceffea357f760008 0x0ceffea357f76000 0x5fffe03fffff000b 0xf5fffe03fffff000

def z657 : W := mkw 0x8fbb5fbd00011020 0x08fbb5fbd0001102 0xffffffffc047307f 0xeffffffffc047307

def z658 : W := mkw 0x0000000810251421 0x0000000081025142 0x4000000070073c00 0x04000000070073c0

def z659 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z660 : W := mkw 0x843b4a3500000000 0x0843b4a350000000 0x9c3ffe3f80000006 0xe9c3ffe3f8000000

def z661 : W := mkw 0x4ac6e04aef5331b8 0x44ac6e04aef5331b 0xf3cfe1ffcfc733ff 0xaf3cfe1ffcfc733f

def z662 : W := mkw 0x00442042cc422198 0x400442042cc42219 0x000000000c000380 0x0000000000c00038

def z663 : W := mkw 0x8fab558500000000 0x08fab55850000000 0x1fffe1c780000003 0xe1fffe1c78000000

def z664 : W := mkw 0x3bc595c66fd0ab94 0x83bc595c66fd0ab9 0x13c781c60f800381 0x013c781c60f80038

def z665 : W := mkw 0x0004800005500000 0x0000480000550000 0x1037800000780002 0x0103780000078000

def z666 : W := mkw 0x10048002055840d2 0x810048002055840d 0x0000000000780070 0x0000000000078007

def z667 : W := mkw 0x9fbb5fb70088c2d6 0x89fbb5fb70088c2d 0xbfffffff8000c3f7 0xebfffffff8000c3f

def z668 : W := mkw 0x315599666fd8ebd6 0x8315599666fd8ebd 0x733799267ff8ffff 0x7733799267ff8fff

def z669 : W := mkw 0x847f6a7fcc4331b8 0x4847f6a7fcc4331b 0xf0ffe1ffcc4733ff 0xaf0ffe1ffcc4733f

def z670 : W := mkw 0x4ac6e0006f520008 0x04ac6e0006f52000 0x53cfe0004fc7000b 0xa53cfe0004fc7000

def z671 : W := mkw 0x0044204adc6f75fb 0x40044204adc6f75f 0xe0cc61fffc7fffff 0xbe0cc61fffc7ffff

def z672 : W := mkw 0x10110826000840d2 0x810110826000840d 0x0000002600000070 0x0000000260000007

def z673 : W := mkw 0xafbb5fb522808a04 0x0afbb5fb522808a0 0x1f339e003380cc00 0x51f339e003380cc0

def z674 : W := mkw 0x0fbb592400000000 0x00fbb59240000000 0x1ffff92600000007 0xe1ffff9260000000

def z675 : W := mkw 0xcffb7fb57a260008 0x0cffb7fb57a26000 0xdffffffff0070007 0xedffffffff007000

def z676 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0x8c381e38007f0076 0xe8c381e38007f007

def z677 : W := mkw 0x214015c06a80ab04 0x0214015c06a80ab0 0xe0001fc07f80ff8c 0x1e0001fc07f80ff8

def z678 : W := mkw 0x04780a78582d7563 0x004780a78582d756 0xecf81ff87c7fffff 0xfecf81ff87c7ffff

def z679 : W := mkw 0x0000000000808204 0x0000000000080820 0x200000000f80c388 0x1200000000f80c38

def z680 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xa3c01fc00f80ff85 0x0a3c01fc00f80ff8

def z681 : W := mkw 0x15391b3e10add6f7 0x815391b3e10add6f 0xec381f3e707ffffe 0xfec381f3e707ffff

def z682 : W := mkw 0x143c8a3a15fdd6f7 0x8143c8a3a15fdd6f 0xec381e387ffffffe 0xfec381e387ffffff

def z683 : W := mkw 0x1105910605d08294 0x81105910605d0829 0x330781260fc003ff 0x2330781260fc003f

def z684 : W := mkw 0x2b80158022808a04 0x02b80158022808a0 0x2f001f003f80cf8d 0x72f001f003f80cf8

def z685 : W := mkw 0x2b8015c02280ab04 0x02b8015c02280ab0 0xaf001fc03380ff84 0x5af001fc03380ff8

def z686 : W := mkw 0x0eba4a3000000000 0x00eba4a300000000 0x9ffffe3800000007 0xe9ffffe380000000

def z687 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x303799260078c3f6 0x0303799260078c3f

def z688 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c461c780000001 0x000c461c78000000

def z689 : W := mkw 0x214011406a80ab04 0x0214011406a80ab0 0x630019007f80ff8d 0x7630019007f80ff8

def z690 : W := mkw 0x0eee604acc4331b8 0x40eee604acc4331b 0xffffe1ffcc4733ff 0xeffffe1ffcc4733f

def z691 : W := mkw 0x043c0a3a146d54f3 0x0043c0a3a146d54f 0xec3c1f3e7c7fffff 0xfec3c1f3e7c7ffff

def z692 : W := mkw 0x153d992615fcc2d6 0x8153d992615fcc2d 0x7f3f99267fffc3ff 0xf7f3f99267fffc3f

def z693 : W := mkw 0x111119260088c2d6 0x8111119260088c2d 0x333799260000c3f7 0x6333799260000c3f

def z694 : W := mkw 0x0000000800011020 0x0000000080001102 0x6000000040473078 0x0600000004047307

def z695 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xe3c001c04f80338d 0xae3c001c04f80338

def z696 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xe0c860d9cc4733f8 0x8e0c860d9cc4733f

def z697 : W := mkw 0x553ff92615fec2de 0x8553ff92615fec2d 0x333ff9260fffc3ff 0x7333ff9260fffc3f

def z698 : W := mkw 0x5ffff96efffff3fe 0xc5ffff96efffff3f 0xfffff9fffffff3ff 0xffffff9fffffff3f

def z699 : W := mkw 0x2fe815c07aa4ab04 0x02fe815c07aa4ab0 0xeff81fc07fffff8f 0xfeff81fc07fffff8

def z700 : W := mkw 0x2ac000406a80ab04 0x02ac000406a80ab0 0x6fc000007f80ff89 0xf6fc000007f80ff8

def z701 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc00060070003c00 0x8cc00060070003c0

def z702 : W := mkw 0x04380a3000000000 0x004380a300000000 0x0c301e0000000000 0x40c301e000000000

def z703 : W := mkw 0x0014882005584042 0x0001488200558404 0x333798200ff8c07f 0x7333798200ff8c07

def z704 : W := mkw 0x1015a82e855b50fa 0xc1015a82e855b50f 0x103fe03f807f0072 0x0103fe03f807f007

def z705 : W := mkw 0x6fea75c07aa6ab0c 0x06fea75c07aa6ab0 0xefc87fc07f87ff8d 0xfefc87fc07f87ff8

def z706 : W := mkw 0x04280008102d5463 0x004280008102d546 0x6c380000707ffc7a 0xf6c380000707ffc7

def z707 : W := mkw 0x152d931e15f596b5 0x8152d931e15f596b 0xdf0f871e7f873f81 0x8df0f871e7f873f8

def z708 : W := mkw 0x0000000000000000 0x0000000000000000 0x93ffe1ff80000007 0xe93ffe1ff8000000

def z709 : W := mkw 0xa47b4a756a80ab04 0x0a47b4a756a80ab0 0x703fe03fff80ff8a 0x1703fe03fff80ff8

def z710 : W := mkw 0x2b84358aa6c39abc 0x42b84358aa6c39ab 0x0f0c7e3fb3c7cc72 0x50f0c7e3fb3c7cc7

def z711 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0xdffffe007fff000f 0xfdffffe007fff000

def z712 : W := mkw 0x84390a3d102d5463 0x084390a3d102d546 0xec381e3ff07ffc7e 0xfec381e3ff07ffc7

def z713 : W := mkw 0x31159da605d8cad6 0x831159da605d8cad 0x33379f260ff8cfff 0x733379f260ff8cff

def z714 : W := mkw 0x0004000a044110b0 0x00004000a044110b 0xe0cc61ffcc4733ff 0xae0cc61ffcc4733f

def z715 : W := mkw 0x8fab579500000000 0x08fab57950000000 0x13cfe1df80000001 0x013cfe1df8000000

def z716 : W := mkw 0x0004204a844331b8 0x40004204a844331b 0xa0cc61ff804733f7 0xaa0cc61ff804733f

def z717 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x7ffff8007fffc00f 0xf7ffff8007fffc00

def z718 : W := mkw 0x0000004a800131b0 0x40000004a800131b 0xe0cc61ffc04733ff 0xae0cc61ffc04733f

def z719 : W := mkw 0xc155bfb57f760008 0x0c155bfb57f76000 0xc0001fffffff000c 0x1c0001fffffff000

def z720 : W := mkw 0x2ff81ff87aadff67 0x02ff81ff87aadff6 0x03f801f80fff03f3 0x003f801f80fff03f

def z721 : W := mkw 0x0eea40007a240000 0x00eea40007a24000 0x5fffe0007fff000b 0xf5fffe0007fff000

def z722 : W := mkw 0x8fbb5fb510240401 0x08fbb5fb51024040 0x9fffffffb0000c07 0xe9fffffffb0000c0

def z723 : W := mkw 0xabc115c56a80ab04 0x0abc115c56a80ab0 0xefc01fc7ff80ff8d 0xfefc01fc7ff80ff8

def z724 : W := mkw 0x111199240198c246 0x8111199240198c24 0x333399200ff8c3ff 0x7333399200ff8c3f

def z725 : W := mkw 0x4eaac04ab33531b0 0x44eaac04ab33531b 0xbf3381ffb3b833f4 0x5bf3381ffb3b833f

def z726 : W := mkw 0x0eba4a3000000000 0x00eba4a300000000 0x9fffffff80000007 0xe9fffffff8000000

def z727 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xec3c7e3ff07ffc7e 0xfec3c7e3ff07ffc7

def z728 : W := mkw 0x8ebb4eb500000000 0x08ebb4eb50000000 0x10ffe0ff80000002 0x010ffe0ff8000000

def z729 : W := mkw 0x6eeee4c07f762908 0x06eeee4c07f76290 0x5fffe0c07fff000b 0xf5fffe0c07fff000

def z730 : W := mkw 0x9eaec69305d8c2d6 0x89eaec69305d8c2d 0xacc866d98ff8c3f8 0x9acc866d98ff8c3f

def z731 : W := mkw 0x652ef5c015f6ab0c 0x0652ef5c015f6ab0 0xb03fffc0007fff86 0x0b03fffc0007fff8

def z732 : W := mkw 0x843b4a3d102d5463 0x0843b4a3d102d546 0xfc3b9e38707ffc7e 0xffc3b9e38707ffc7

def z733 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0x60cc61ffcc4733fb 0x060cc61ffcc4733f

def z734 : W := mkw 0x446ee0007f760008 0x0446ee0007f76000 0x533fe0007fff000b 0x7533fe0007fff000

def z735 : W := mkw 0x6eea64c8fa273928 0x46eea64c8fa27392 0xccc866d9f0073c00 0x8ccc866d9f0073c0

def z736 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xe3cc61ffcfc733ff 0xfe3cc61ffcfc733f

def z737 : W := mkw 0x8fff7fffcc4331b8 0x48fff7fffcc4331b 0x7f339e004c4733f8 0x47f339e004c4733f

def z738 : W := mkw 0x5ffb79267aaec2de 0x85ffb79267aaec2d 0x6cc879267007c3f4 0x86cc879267007c3f

def z739 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x333799060ff8c3f9 0x5333799060ff8c3f

def z740 : W := mkw 0x4eeac0007b340000 0x04eeac0007b34000 0x5ffb80007fff000b 0xf5ffb80007fff000

def z741 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x9ffffeff80000002 0xc9ffffeff8000000

def z742 : W := mkw 0x442ee00015760008 0x0442ee0001576000 0x5f3fe0007fff000b 0xf5f3fe0007fff000

def z743 : W := mkw 0x4eeee2107f760008 0x04eeee2107f76000 0xdfffe6187fff000b 0xfdfffe6187fff000

def z744 : W := mkw 0x4ac4a0007f760008 0x04ac4a0007f76000 0x5ff780007fff000b 0xf5ff780007fff000

def z745 : W := mkw 0x8b83579500000000 0x08b8357950000000 0x93c7e7df80000001 0x093c7e7df8000000

def z746 : W := mkw 0x00100a38102d5463 0x000100a38102d546 0xec001e38707ffc7c 0xfec001e38707ffc7

def z747 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x5fffe1267fff000f 0xf5fffe1267fff000

def z748 : W := mkw 0x3ad58ce66f5869d2 0x83ad58ce66f5869d 0xdcf786e670783c72 0x8dcf786e670783c7

def z749 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0xdfffffffc047000f 0xedfffffffc047000

def z750 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xec301e00707ffc7c 0xfec301e00707ffc7

def z751 : W := mkw 0x0044a04acd5331b8 0x40044a04acd5331b 0x600000004fff33f8 0x1600000004fff33f

def z752 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xef001e007f80ff8c 0xfef001e007f80ff8

def z753 : W := mkw 0x214011406a80ab04 0x0214011406a80ab0 0xef001f007f80ff8d 0xfef001f007f80ff8

def z754 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0xffffffffc000300f 0xeffffffffc000300

def z755 : W := mkw 0x4eeee0027f760098 0x04eeee0027f76009 0x5fffe0267fff007b 0xf5fffe0267fff007

def z756 : W := mkw 0x446ee0005d760008 0x0446ee0005d76000 0x53ffe0004fff000b 0xf53ffe0004fff000

def z757 : W := mkw 0x4ad6ea386f5b546b 0x04ad6ea386f5b546 0xb3c7fe380f80fc75 0x0b3c7fe380f80fc7

def z758 : W := mkw 0x0a82400000000000 0x00a8240000000000 0x93cfe1ff80000007 0xa93cfe1ff8000000

def z759 : W := mkw 0x4044a04aff7f75fb 0x44044a04aff7f75f 0x600000007ffffff8 0x1600000007ffffff

def z760 : W := mkw 0x8b935da500000000 0x08b935da50000000 0x93fff9ff80000007 0xe93fff9ff8000000

def z761 : W := mkw 0x4eeee0407f762108 0x04eeee0407f76210 0x5fffe1c07fff038b 0xf5fffe1c07fff038

def z762 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0xdfffe0d9ffff000b 0xfdfffe0d9ffff000

def z763 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x133781260ff803fb 0x7133781260ff803f

def z764 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0xffffe0007fff300f 0xfffffe0007fff300

def z765 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xefc01ec07f80ff88 0xdefc01ec07f80ff8

def z766 : W := mkw 0x0004804a855131b0 0x40004804a855131b 0xb33781ff8ff833ff 0x7b33781ff8ff833f

def z767 : W := mkw 0x4eeee042ff762198 0x44eeee042ff76219 0x7fffe1e7ffff03ff 0xf7fffe1e7ffff03f

def z768 : W := mkw 0xafbb5fb532acce47 0x0afbb5fb532acce4 0x9fffffffb3b8cc07 0xf9fffffffb3b8cc0

def z769 : W := mkw 0x11159b3605d8c2d6 0x811159b3605d8c2d 0xb3379f3e0ff8c3ff 0x7b3379f3e0ff8c3f

def z770 : W := mkw 0x143c8a3a157d54f3 0x8143c8a3a157d54f 0x00380038007f0072 0x000380038007f007

def z771 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0xbfffffff8c00038f 0xebfffffff8c00038

def z772 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x333399000ff8c3fd 0x7333399000ff8c3f

def z773 : W := mkw 0x8fbb5fb5102c4443 0x08fbb5fb5102c444 0xdffffffff07fcc0f 0xfdffffffff07fcc0

def z774 : W := mkw 0xabc255c16a80ab04 0x0abc255c16a80ab0 0xefc07fc1ff80ff8d 0xfefc07fc1ff80ff8

def z775 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xc0cc61ffcc4733f3 0x8c0cc61ffcc4733f

def z776 : W := mkw 0xa1111ffd0089ff67 0x0a1111ffd0089ff6 0xa0001fff8000fff4 0x0a0001fff8000fff

def z777 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x33fff9260ff8c3ff 0xf33fff9260ff8c3f

def z778 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0xbfffffff8000fc07 0xebfffffff8000fc0

def z779 : W := mkw 0x4eeee4807f760008 0x04eeee4807f76000 0xdfffe6c07fff000b 0xfdfffe6c07fff000

def z780 : W := mkw 0x1111192e0089d2f6 0x81111192e0089d2f 0xa000193e0000f3f4 0x0a000193e0000f3f

def z781 : W := mkw 0x1151b96cc99bf36e 0xc1151b96cc99bf36 0xd3fbf8d9c3bff000 0xdd3fbf8d9c3bff00

def z782 : W := mkw 0x8fbb5fb500084042 0x08fbb5fb50008404 0x9fffffff8038c007 0xf9fffffff8038c00

def z783 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0xbfffffff8040007f 0xebfffffff8040007

def z784 : W := mkw 0x111199260198c2d6 0x8111199260198c2d 0x333399260fb8c3fd 0x7333399260fb8c3f

def z785 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xe0cc61fffc47ffff 0xbe0cc61fffc47fff

def z786 : W := mkw 0x4eeae0007b360008 0x04eeae0007b36000 0x5f33800073bf0000 0x55f33800073bf000

def z787 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x9fffffdf80000001 0xc9fffffdf8000000

def z788 : W := mkw 0x4eeee0027f760098 0x04eeee0027f76009 0x5fffe1067fff038b 0xf5fffe1067fff038

def z789 : W := mkw 0x04380820102c4042 0x004380820102c404 0xec381e20707ffc7e 0xfec381e20707ffc7

def z790 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0xbf379f260ff8c3ff 0xfbf379f260ff8c3f

def z791 : W := mkw 0x043a4a38102d5463 0x0043a4a38102d546 0xfc3ffe38707ffc7e 0xffc3ffe38707ffc7

def z792 : W := mkw 0x0ac4a0006f520008 0x00ac4a0006f52000 0x5fffe0007fff000b 0xf5fffe0007fff000

def z793 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x7f3799267ff8c3ff 0xf7f3799267ff8c3f

def z794 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0x40cc61ffcc4703fb 0xa40cc61ffcc4703f

def z795 : W := mkw 0x1014882205d8c2d6 0x81014882205d8c2d 0x333798200ff8c3ff 0x7333798200ff8c3f

def z796 : W := mkw 0x0b80158000808204 0x00b8015800080820 0xefc01fc07f80ff8d 0xfefc01fc07f80ff8

def z797 : W := mkw 0x1111192e0089d6f7 0x81111192e0089d6f 0x200019260000fff4 0x0200019260000fff

def z798 : W := mkw 0x4eeee0427f762198 0x04eeee0427f76219 0xffffe1e67fff33ff 0xfffffe1e67fff33f

def z799 : W := mkw 0x047c2a72dc6e65db 0x4047c2a72dc6e65d 0x0cf47fc7bc38cf81 0x50cf47fc7bc38cf8

def z800 : W := mkw 0x8fbb5fb5102c4443 0x08fbb5fb5102c444 0xbfffffffb078cc7f 0xfbfffffffb078cc7

def z801 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xe0fc61ffcc7f33ff 0xfe0fc61ffcc7f33f

def z802 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xe0cc61ffcc0733f5 0x8e0cc61ffcc0733f

def z803 : W := mkw 0x0044a04acd5331b8 0x40044a04acd5331b 0xf3cfe1ffcfc733ff 0xaf3cfe1ffcfc733f

def z804 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x5ff380007fff0009 0xf5ff380007fff000

def z805 : W := mkw 0x6eeee4807f760808 0x06eeee4807f76080 0x5fffe6007fff0c0b 0xf5fffe6007fff0c0

def z806 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x1fffe0000fff0003 0xe1fffe0000fff000

def z807 : W := mkw 0x2044204aee4339b8 0x42044204aee4339b 0xe0cc61fffc473fff 0xae0cc61fffc473ff

def z808 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x333398200ff8c3fe 0x7333398200ff8c3f

def z809 : W := mkw 0x8fbb5fb500808204 0x08fbb5fb50080820 0xffffffffff80ff8f 0xfffffffffff80ff8

def z810 : W := mkw 0x1044a04acd5b71fa 0xc1044a04acd5b71f 0x600000004c7f33f8 0x0600000004c7f33f

def z811 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0x6fc01e007f80ff89 0xf6fc01e007f80ff8

def z812 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xeff01fc07ff8ff8f 0xfeff01fc07ff8ff8

def z813 : W := mkw 0x04280218102d5463 0x004280218102d546 0xec081e18707ffc7c 0xfec081e18707ffc7

def z814 : W := mkw 0x210015c00080ab04 0x0210015c00080ab0 0xef001fc07f80ff8d 0xfef001fc07f80ff8

def z815 : W := mkw 0x843b4a3500000000 0x0843b4a350000000 0x90ffe0ff80000002 0x890ffe0ff8000000

def z816 : W := mkw 0x1004800205d8c2d6 0x81004800205d8c2d 0x333781260ff8c3ff 0x7333781260ff8c3f

def z817 : W := mkw 0x4044a04aef5331b8 0x44044a04aef5331b 0x600000004fc733f8 0x0600000004fc733f

def z818 : W := mkw 0x4ac6e0007f760008 0x04ac6e0007f76000 0x53f7e0007fff000b 0x753f7e0007fff000

def z819 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xff3f9e38707ffc7f 0xfff3f9e38707ffc7

def z820 : W := mkw 0x0bc011006a808204 0x00bc011006a80820 0xefc01f007f80ff8d 0xfefc01f007f80ff8

def z821 : W := mkw 0x4eaac00033340000 0x04eaac0003334000 0x1f3b800033ff0002 0x51f3b800033ff000

def z822 : W := mkw 0xafbb5fb522000800 0x0afbb5fb52200080 0x9fffffffb0000c07 0xe9fffffffb0000c0

def z823 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0x6c381e38707ffc7a 0x56c381e38707ffc7

def z824 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xec381ffff07ffc7e 0xfec381ffff07ffc7

def z825 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x53ffe0007fff000b 0x153ffe0007fff000

def z826 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xe0c861ffcc4733fc 0x8e0c861ffcc4733f

def z827 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x9ff7ffff80000005 0x49ff7ffff8000000

def z828 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xcc381e38707ffc72 0xdcc381e38707ffc7

def z829 : W := mkw 0xafbb5fb500808a04 0x0afbb5fb500808a0 0x9fffffff8000cc07 0xe9fffffff8000cc0

def z830 : W := mkw 0x042a400000000000 0x0042a40000000000 0x90ffe1ff80000007 0xa90ffe1ff8000000

def z831 : W := mkw 0x843b4a3d102d5463 0x0843b4a3d102d546 0xfcfffffff07ffc7f 0xffcfffffff07ffc7

def z832 : W := mkw 0x442ee00015760008 0x0442ee0001576000 0x133fe00003ff0002 0x5133fe00003ff000

def z833 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xe0cc79ffcc47f3ff 0xfe0cc79ffcc47f3f

def z834 : W := mkw 0x1111192e8089d2f6 0xc1111192e8089d2f 0x2000193f8000c3f4 0x02000193f8000c3f

def z835 : W := mkw 0x046ca0005d760008 0x0046ca0005d76000 0x5fffe0007fff000b 0xf5fffe0007fff000

def z836 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0x6c301e20707ffc7e 0x76c301e20707ffc7

def z837 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0x6c381e00707ffc7a 0xf6c381e00707ffc7

def z838 : W := mkw 0x6eeee4c07f762908 0x06eeee4c07f76290 0xffffe7c07fff3f8f 0xfffffe7c07fff3f8

def z839 : W := mkw 0x0faa558000000000 0x00faa55800000000 0x9fffffff80000007 0xe9fffffff8000000

def z840 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x5ff7e0007fff0009 0x55ff7e0007fff000

def z841 : W := mkw 0xdfbbdfb533bcc246 0x8dfbbdfb533bcc24 0x1f339e0033b8c000 0x51f339e0033b8c00

def z842 : W := mkw 0x4eaac00033340000 0x04eaac0003334000 0x5f3b800073bf0000 0xd5f3b800073bf000

def z843 : W := mkw 0x843a4a39102d5463 0x0843a4a39102d546 0xec387e39f07ffc7e 0xfec387e39f07ffc7

def z844 : W := mkw 0x0040204ac80331b8 0x40040204ac80331b 0xe0c861ffc04733fe 0xae0c861ffc04733f

def z845 : W := mkw 0x31111ffe0089fff7 0x831111ffe0089fff 0xa0001ffe0000fff4 0x0a0001ffe0000fff

def z846 : W := mkw 0x91111fbf0089d6f7 0x891111fbf0089d6f 0xa0001fff8000fff4 0x0a0001fff8000fff

def z847 : W := mkw 0x8b83558d102d5463 0x08b83558d102d546 0x73c7e1c7f07ffc79 0x173c7e1c7f07ffc7

def z848 : W := mkw 0x014011404880a304 0x0014011404880a30 0xefc01fc07f80ff8d 0xfefc01fc07f80ff8

def z849 : W := mkw 0x4eea6258fa273529 0x44eea6258fa27352 0xccc866d9f0073c00 0x8ccc866d9f0073c0

def z850 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xec381e18707ffc78 0xdec381e18707ffc7

def z851 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xec301e38707ffc7c 0x5ec301e38707ffc7

def z852 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0xb33799ff8ff8c3ff 0x7b33799ff8ff8c3f

def z853 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x9fffffff8078000f 0xf9fffffff8078000

def z854 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xec381f387c7fffff 0xfec381f387c7ffff

def z855 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x733799267ff8ffff 0x7733799267ff8fff

def z856 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x9fffffff8f80000f 0xf9fffffff8f80000

def z857 : W := mkw 0x8ebb4eb500000000 0x08ebb4eb50000000 0x9fffe6ff80000003 0xe9fffe6ff8000000

def z858 : W := mkw 0x0044a04acd5331b8 0x40044a04acd5331b 0xf0ffe1ffcc7f33ff 0xaf0ffe1ffcc7f33f

def z859 : W := mkw 0x0044204aee4331b8 0x40044204aee4331b 0xe0cc61ffffc733ff 0xbe0cc61ffffc733f

def z860 : W := mkw 0x4eaec00037740000 0x04eaec0003774000 0x5f3f80007fff000b 0xf5f3f80007fff000

def z861 : W := mkw 0x4eeae0007b360008 0x04eeae0007b36000 0x5ffbe00073ff000a 0xf5ffbe00073ff000

def z862 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xefc01fffff80ff8d 0xfefc01fffff80ff8

def z863 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xefc47fc7ff80ff8d 0xfefc47fc7ff80ff8

def z864 : W := mkw 0xcfbb5fb532240000 0x0cfbb5fb53224000 0x9fffffffb0000007 0xe9fffffffb000000

def z865 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x9cffffff80000006 0x89cffffff8000000

def z866 : W := mkw 0x8fbb5fb5102c4443 0x08fbb5fb5102c444 0x9fffffff80380007 0xe9fffffff8038000

def z867 : W := mkw 0x543fea3e157f54fb 0x8543fea3e157f54f 0x103fe03e007f0072 0x0103fe03e007f007

def z868 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x13fff9ff80000007 0x613fff9ff8000000

def z869 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xefc87fd9ff80ff8d 0xfefc87fd9ff80ff8

def z870 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xecf87ef9f07ffc7e 0xfecf87ef9f07ffc7

def z871 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0xbfffffff8000c00f 0xfbfffffff8000c00

def z872 : W := mkw 0x1004800205d8c2d6 0x81004800205d8c2d 0x333380000ff8c3f8 0x5333380000ff8c3f

def z873 : W := mkw 0x4eaee00037760008 0x04eaee0003776000 0x1f33800033ff0000 0x51f33800033ff000

def z874 : W := mkw 0x2bc035c0ea82ab0c 0x42bc035c0ea82ab0 0xefc07fc1ff80ff8d 0xfefc07fc1ff80ff8

def z875 : W := mkw 0x0eec80007f740000 0x00eec80007f74000 0x5fff80007fff000b 0xf5fff80007fff000

def z876 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x733f99264fffc3ff 0xf733f99264fffc3f

def z877 : W := mkw 0x8fbb5fb522000000 0x08fbb5fb52200000 0x9fffffffb3800007 0xf9fffffffb380000

def z878 : W := mkw 0x8b935fb500000000 0x08b935fb50000000 0x9fc7ffff80000005 0xe9fc7ffff8000000

def z879 : W := mkw 0x8fab579500000000 0x08fab57950000000 0x9fcfe7ff80000007 0xa9fcfe7ff8000000

def z880 : W := mkw 0xceea66d9fa273128 0x4ceea66d9fa27312 0xccc866d9f0073000 0x8ccc866d9f007300

def z881 : W := mkw 0x0010082800095062 0x0001008280009506 0xec381e38707ffc7e 0xfec381e38707ffc7

def z882 : W := mkw 0x10158826055840d2 0x810158826055840d 0x333781260ff803ff 0x7333781260ff803f

def z883 : W := mkw 0x442ee00015760008 0x0442ee0001576000 0x133fe0000fff0003 0x0133fe0000fff000

def z884 : W := mkw 0x6eea66d87a273d29 0x06eea66d87a273d2 0xccc866d870073c00 0x8ccc866d870073c0

def z885 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xcfc01fc07f80ff81 0xdcfc01fc07f80ff8

def z886 : W := mkw 0x0011082400000000 0x0001108240000000 0x90ffe1ff80000007 0xa90ffe1ff8000000

def z887 : W := mkw 0x2bc035c06a82ab0c 0x02bc035c06a82ab0 0xefc87fc07f87ff8d 0xfefc87fc07f87ff8

def z888 : W := mkw 0x8fbb5fb5102c4443 0x08fbb5fb5102c444 0xfffffffff038fc0f 0xffffffffff038fc0

def z889 : W := mkw 0x1105910605d8c2d6 0x81105910605d8c2d 0x333781060ff8c3fb 0x7333781060ff8c3f

def z890 : W := mkw 0x214015c06a80ab04 0x0214015c06a80ab0 0xec001fc07f80ff8c 0xfec001fc07f80ff8

def z891 : W := mkw 0x4eeee2107f760409 0x04eeee2107f76040 0x5fffe6007fff0c0b 0xf5fffe6007fff0c0

def z892 : W := mkw 0x8fbb5fb510240000 0x08fbb5fb51024000 0xdffffffff0070007 0xedffffffff007000

def z893 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xef381e387ffffc7f 0xfef381e387ffffc7

def z894 : W := mkw 0x05391b3400000000 0x005391b340000000 0x9fffffff80000007 0xe9fffffff8000000

def z895 : W := mkw 0x1111196e8089f3f6 0xc1111196e8089f3f 0x200019260000f3f4 0x0200019260000f3f

def z896 : W := mkw 0x8b935fb500000000 0x08b935fb50000000 0x93f7ffff80000007 0x693f7ffff8000000

def z897 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xfff79fc07f80ff8f 0xffff79fc07f80ff8

def z898 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x333798260ff8c3fa 0x5333798260ff8c3f

def z899 : W := mkw 0x8eab469500000000 0x08eab46950000000 0x9ccfe6df80000000 0x89ccfe6df8000000

def z900 : W := mkw 0xceeee2117f760008 0x0ceeee2117f76000 0x5fffe019ffff000b 0xf5fffe019ffff000

def z901 : W := mkw 0xceeee6917f760008 0x0ceeee6917f76000 0x5fffe6007fff000b 0xf5fffe6007fff000

def z902 : W := mkw 0x8fbb5fb500808204 0x08fbb5fb50080820 0x9fffffff8f800387 0xe9fffffff8f80038

def z903 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xefc01fe07fc0ffff 0xfefc01fe07fc0fff

def z904 : W := mkw 0x11159b3605d8c6d7 0x811159b3605d8c6d 0x33379f260ff8cfff 0x733379f260ff8cff

def z905 : W := mkw 0x6bc6f5c2efd2ab9c 0x46bc6f5c2efd2ab9 0x13c7e1c78f800381 0x013c7e1c78f80038

def z906 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x7fffe0207fff007f 0xf7fffe0207fff007

def z907 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xefc81fc07fc7ff8f 0xfefc81fc07fc7ff8

def z908 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x5f3780007fff000b 0x75f3780007fff000

def z909 : W := mkw 0x8fbb5fb500808204 0x08fbb5fb50080820 0xbfffffff8000c387 0xebfffffff8000c38

def z910 : W := mkw 0x81111fb500000000 0x081111fb50000000 0x93ffffff80000007 0xe93ffffff8000000

def z911 : W := mkw 0x4eeee0407f762108 0x04eeee0407f76210 0xdfffe0c07fff300b 0xfdfffe0c07fff300

def z912 : W := mkw 0x853b5fb500000000 0x0853b5fb50000000 0x90ffffff80000007 0xa90ffffff8000000

def z913 : W := mkw 0x0101110400000000 0x0010111040000000 0x93cfe1ff80000007 0xa93cfe1ff8000000

def z914 : W := mkw 0x6044a04afff7bbbc 0x46044a04afff7bbb 0x600000007ffffff8 0x1600000007ffffff

def z915 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xecfc7e38707ffc7f 0xfecfc7e38707ffc7

def z916 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x333799260ff8c3f7 0x0333799260ff8c3f

def z917 : W := mkw 0x004420024c420098 0x0004420024c42009 0xe0cc61ffcc4703ff 0xae0cc61ffcc4703f

def z918 : W := mkw 0x2bc115c46a80ab04 0x02bc115c46a80ab0 0xffc79fc67f80ff8d 0xfffc79fc67f80ff8

def z919 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xec081e38707ffc7c 0x9ec081e38707ffc7

def z920 : W := mkw 0x91159b3705d8c2d6 0x891159b3705d8c2d 0x3337993f8ff8c3ff 0x73337993f8ff8c3f

def z921 : W := mkw 0x91159fb705d8c2d6 0x891159fb705d8c2d 0x33379f260ff8c3ff 0x733379f260ff8c3f

def z922 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x7fffe1007fff038f 0xf7fffe1007fff038

def z923 : W := mkw 0xafbb5fb532acce47 0x0afbb5fb532acce4 0x1f339e0033b8cc00 0x51f339e0033b8cc0

def z924 : W := mkw 0x0ac000406a002100 0x00ac000406a00210 0xefc01fc07f80ff8d 0xfefc01fc07f80ff8

def z925 : W := mkw 0x0040204ac80331b8 0x40040204ac80331b 0xe0cc61ffc00733f7 0xae0cc61ffc00733f

def z926 : W := mkw 0xeeeee6d17f762908 0x0eeeee6d17f76290 0xdfffe6d9ffff3c0b 0xfdfffe6d9ffff3c0

def z927 : W := mkw 0x8b83558500000000 0x08b8355850000000 0x93cfe1df80000001 0x893cfe1df8000000

def z928 : W := mkw 0x204000406a80ab04 0x0204000406a80ab0 0x6c001e007f80ff88 0x56c001e007f80ff8

def z929 : W := mkw 0x8b935fb500000000 0x08b935fb50000000 0x13c7e1ff80000001 0x013c7e1ff8000000

def z930 : W := mkw 0x11111b3c0089d667 0x811111b3c0089d66 0xa0001e380000fc74 0x0a0001e380000fc7

def z931 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xeccc7fffcc4733ff 0xeeccc7fffcc4733f

def z932 : W := mkw 0x4eeae0007b360008 0x04eeae0007b36000 0x5fffe00073bf0003 0xf5fffe00073bf000

def z933 : W := mkw 0x6eeee0407f762908 0x06eeee0407f76290 0x5fffe0007fff3c0b 0xf5fffe0007fff3c0

def z934 : W := mkw 0x0004200a844310b8 0x40004200a844310b 0xa0cc61ff8c4703ff 0xaa0cc61ff8c4703f

def z935 : W := mkw 0x1044a04addfff7ff 0xc1044a04addfff7f 0x600000007ffffff8 0x1600000007ffffff

def z936 : W := mkw 0x1105910605d08294 0x81105910605d0829 0x333781260ff803ff 0x7333781260ff803f

def z937 : W := mkw 0x4eeae0007b360008 0x04eeae0007b36000 0x5ffbe0007fbf0009 0xf5ffbe0007fbf000

def z938 : W := mkw 0x0040004848013120 0x0004000484801312 0xe0cc61ffcc4733ff 0xae0cc61ffcc4733f

def z939 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xefc01fc07f80ff85 0x8efc01fc07f80ff8

def z940 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x3f379f263ff8cfff 0x73f379f263ff8cff

def z941 : W := mkw 0x0428800011340000 0x0042880001134000 0x5f3b800073ff000a 0xf5f3b800073ff000

def z942 : W := mkw 0x943fca3f157d54f3 0x8943fca3f157d54f 0x103fe03f807f0072 0x0103fe03f807f007

def z943 : W := mkw 0x6eeee4c07f762908 0x06eeee4c07f76290 0xfffffec07ffffc0f 0xffffffec07ffffc0

def z944 : W := mkw 0x00148822055840d2 0x000148822055840d 0x333799260ff8c3ff 0x7333799260ff8c3f

def z945 : W := mkw 0xaeea46d97a253d21 0x0aeea46d97a253d2 0xccc866d9f0073c00 0x8ccc866d9f0073c0

def z946 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x5f3fe0007fff000a 0x55f3fe0007fff000

def z947 : W := mkw 0x8fbb5fb5102c4042 0x08fbb5fb5102c404 0xfffffffff07fc07f 0xffffffffff07fc07

def z948 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x5fffe00073ff0002 0xd5fffe00073ff000

def z949 : W := mkw 0x0eeee0004d520008 0x00eeee0004d52000 0x5fffe0004fff000b 0xf5fffe0004fff000

def z950 : W := mkw 0x2ac000406a80ab04 0x02ac000406a80ab0 0xefc01e007f80ff8d 0xfefc01e007f80ff8

def z951 : W := mkw 0x4eea6048fa273128 0x44eea6048fa27312 0x4cc8600070073000 0x84cc860007007300

def z952 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0xdffffffff0003c07 0xedffffffff0003c0

def z953 : W := mkw 0x1115b92685dac2de 0xc1115b92685dac2d 0x3337f9278ff8c3ff 0x73337f9278ff8c3f

def z954 : W := mkw 0x4044a0007f760008 0x04044a0007f76000 0x533380007fff0008 0x5533380007fff000

def z955 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xf3ffe1ffcc4733ff 0xef3ffe1ffcc4733f

def z956 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x5ffbe0007fff0008 0xd5ffbe0007fff000

def z957 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0xb3379f260ff8ffff 0x7b3379f260ff8fff

def z958 : W := mkw 0x8fbb5fb50088c246 0x08fbb5fb50088c24 0xbfffffff8ff8c3ff 0xfbfffffff8ff8c3f

def z959 : W := mkw 0x91111fff8089f3f6 0xc91111fff8089f3f 0xa0001fff8000f3f4 0x0a0001fff8000f3f

def z960 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0xb33f993e0ff8c3ff 0xfb33f993e0ff8c3f

def z961 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x333ff93f8ff8c3ff 0x7333ff93f8ff8c3f

def z962 : W := mkw 0x0044a0004d520008 0x00044a0004d52000 0x533780004fff000b 0x7533780004fff000

def z963 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0xdfffe1c07fff000f 0xfdfffe1c07fff000

def z964 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x1fffffff80000003 0x41fffffff8000000

def z965 : W := mkw 0x4eaee00037760008 0x04eaee0003776000 0x5f3fe00073ff000a 0xf5f3fe00073ff000

def z966 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x9fcfffff80000005 0x89fcfffff8000000

def z967 : W := mkw 0x8ebb4eb500000000 0x08ebb4eb50000000 0x9cffe7ff80000007 0xa9cffe7ff8000000

def z968 : W := mkw 0x8eaa469100000000 0x08eaa46910000000 0x9fffe7ff80000007 0xe9fffe7ff8000000

def z969 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0xb3f799e60ff8c3ff 0xfb3f799e60ff8c3f

def z970 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x5fffe03fffff000b 0xf5fffe03fffff000

def z971 : W := mkw 0xabc355c56a80ab04 0x0abc355c56a80ab0 0xffcfffffff80ff8f 0xfffcfffffff80ff8

def z972 : W := mkw 0x843b4a3500000000 0x0843b4a350000000 0x9cffffff80000007 0xe9cffffff8000000

def z973 : W := mkw 0x1115b92605dac2de 0x81115b92605dac2d 0x333ff9260fffc3ff 0x7333ff9260fffc3f

def z974 : W := mkw 0x8b83558500000000 0x08b8355850000000 0x93c7e1ff80000005 0x093c7e1ff8000000

def z975 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x333798000ff8c3fb 0x7333798000ff8c3f

def z976 : W := mkw 0x3044a04aefdbfbfe 0xc3044a04aefdbfbf 0x600000007ffffff8 0x1600000007ffffff

def z977 : W := mkw 0x0104910205d08294 0x00104910205d0829 0x333799260ff8c3ff 0x7333799260ff8c3f

def z978 : W := mkw 0x0004a00005520008 0x00004a0000552000 0x133fe0000fff000b 0x7133fe0000fff000

def z979 : W := mkw 0x4eeee0407f762108 0x04eeee0407f76210 0xffffffc07fffff8f 0xfffffffc07fffff8

def z980 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0xdfffe6007fff3c0b 0xfdfffe6007fff3c0

def z981 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x93ffffff80000007 0x093ffffff8000000

def z982 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x333781260ff8c3fb 0x1333781260ff8c3f

def z983 : W := mkw 0x0000000000808204 0x0000000000080820 0xec001e007f80ff8c 0xfec001e007f80ff8

def z984 : W := mkw 0x1104910205d8c2d6 0x81104910205d8c2d 0x333799000ff8c3ff 0x7333799000ff8c3f

def z985 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xec3c1f3e707ffc7f 0xfec3c1f3e707ffc7

def z986 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xa0cc61ff8c4733f7 0x0a0cc61ff8c4733f

def z987 : W := mkw 0x4eeee0407f762108 0x04eeee0407f76210 0x7fffe0007fff338b 0xf7fffe0007fff338

def z988 : W := mkw 0x8fbb5fb510240000 0x08fbb5fb51024000 0x9fffffffb0380007 0xf9fffffffb038000

def z989 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x7fffe0007ffffc0b 0xf7fffe0007ffffc0

def z990 : W := mkw 0x11159da605d8c2d6 0x811159da605d8c2d 0xb3379fe60ff8c3ff 0x7b3379fe60ff8c3f

def z991 : W := mkw 0x443eea3a957f54fb 0x4443eea3a957f54f 0x103fe03f807f0072 0x0103fe03f807f007

def z992 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x333799260fb8c3f5 0x5333799260fb8c3f

def z993 : W := mkw 0x4eeee040ff762108 0x44eeee040ff76210 0x5fffe0c1ffff000b 0xf5fffe0c1ffff000

def z994 : W := mkw 0x8fbb5fb500808204 0x08fbb5fb50080820 0x9fffffff8380c007 0xf9fffffff8380c00

def z995 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x1fffe1ff80000003 0xe1fffe1ff8000000

def z996 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xeccc67fffc473fff 0xaeccc67fffc473ff

def z997 : W := mkw 0x8fbb5fb510240000 0x08fbb5fb51024000 0x9fffffff807f0007 0xe9fffffff807f000

def z998 : W := mkw 0x0428000810251020 0x0042800081025102 0xec381e38707ffc7e 0xfec381e38707ffc7

def z999 : W := mkw 0x4eeee042ff762198 0x44eeee042ff76219 0xdfffe1ffffff038f 0xfdfffe1ffffff038

def z1000 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xecf81ff8707ffc7f 0xfecf81ff8707ffc7

def z1001 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x93ffe1ff80000007 0xa93ffe1ff8000000

def z1002 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x5fffe0007fff0003 0x85fffe0007fff000

def z1003 : W := mkw 0x00100828102d5463 0x000100828102d546 0xec301e20707ffc7e 0xfec301e20707ffc7

def z1004 : W := mkw 0x4044a0007f760008 0x04044a0007f76000 0x53ffe0007fff000b 0xf53ffe0007fff000

def z1005 : W := mkw 0x9fbb5fb50088c246 0x89fbb5fb50088c24 0x9fffffff8000c007 0xe9fffffff8000c00

def z1006 : W := mkw 0x4eeee0407f762108 0x04eeee0407f76210 0xffffe1ffffff338f 0xfffffe1ffffff338

def z1007 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0x6fc01fc07f80ff89 0x56fc01fc07f80ff8

def z1008 : W := mkw 0x853b5b3500000000 0x0853b5b350000000 0x93fff9ff80000007 0xe93fff9ff8000000

def z1009 : W := mkw 0x0004800015740000 0x0000480001574000 0x533780007fff000b 0x7533780007fff000

def z1010 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x1fffe0003fff0003 0x51fffe0003fff000

def z1011 : W := mkw 0x4eeee002ff760098 0x44eeee002ff76009 0x5fffe007ffff000b 0xf5fffe007ffff000

def z1012 : W := mkw 0x4eaae00033360008 0x04eaae0003336000 0x1f3be00033bf0000 0x51f3be00033bf000

def z1013 : W := mkw 0xceeee4817f760008 0x0ceeee4817f76000 0x5fffe0c1ffff000b 0xf5fffe0c1ffff000

def z1014 : W := mkw 0x0b911da400000000 0x00b911da40000000 0x9fffffff80000007 0xe9fffffff8000000

def z1015 : W := mkw 0x31111dee8089fbf6 0xc31111dee8089fbf 0xa0001fff8000fff4 0x0a0001fff8000fff

def z1016 : W := mkw 0x8fbb5fb510240000 0x08fbb5fb51024000 0xfffffffff07ffc0f 0xffffffffff07ffc0

def z1017 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x133799260ff8c3f3 0x5133799260ff8c3f

def z1018 : W := mkw 0x0115992605500090 0x0011599260550009 0x333799260ff803ff 0x7333799260ff803f

def z1019 : W := mkw 0x04380a38102d5463 0x004380a38102d546 0xec381e38707ffc76 0x8ec381e38707ffc7

def z1020 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x5f3b80007fff000a 0xf5f3b80007fff000

def z1021 : W := mkw 0x00000008102d5463 0x000000008102d546 0xec081e38707ffc7e 0xfec081e38707ffc7

def z1022 : W := mkw 0x11111b3e0089d6f7 0x811111b3e0089d6f 0x2000193e0000c3f4 0x02000193e0000c3f

def z1023 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xe0cc61ffc04733f6 0x8e0cc61ffc04733f

def z1024 : W := mkw 0x8fbb5fb500084042 0x08fbb5fb50008404 0xfffffffff078fc7f 0xffffffffff078fc7

def z1025 : W := mkw 0x4eaee00037760008 0x04eaee0003776000 0x1f3fe0003fff000b 0x71f3fe0003fff000

def z1026 : W := mkw 0x8fab558500000000 0x08fab55850000000 0x9fffe1ff80000007 0xe9fffe1ff8000000

def z1027 : W := mkw 0x4eaee00037760008 0x04eaee0003776000 0x1fffe00033ff0003 0xf1fffe00033ff000

def z1028 : W := mkw 0x8ebb4eb500000000 0x08ebb4eb50000000 0x9cfffeff80000006 0xe9cfffeff8000000

def z1029 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x53ffe0004fff000b 0xa53ffe0004fff000

def z1030 : W := mkw 0x8b935fb500000000 0x08b935fb50000000 0x93cfffff80000007 0xa93cfffff8000000

def z1031 : W := mkw 0x11111b7e8089f7f7 0xc11111b7e8089f7f 0xa0001fff8000fff4 0x0a0001fff8000fff

def z1032 : W := mkw 0x843b4a3500000000 0x0843b4a350000000 0x10ffe1ff80000003 0x010ffe1ff8000000

def z1033 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0x80cc61ff8c4703f7 0xa80cc61ff8c4703f

def z1034 : W := mkw 0x91159fb705d8c2d6 0x891159fb705d8c2d 0xb3ffffff8ff8c3ff 0xfb3ffffff8ff8c3f

def z1035 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x5fffe0007fbf0001 0xd5fffe0007fbf000

def z1036 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x13ffe0000fff000b 0x713ffe0000fff000

def z1037 : W := mkw 0x0040204ac80331b8 0x40040204ac80331b 0xe0c861ffcc0733fd 0xae0c861ffcc0733f

def z1038 : W := mkw 0x115539264ccac2de 0x8115539264ccac2d 0x60cc79264c47c3ff 0xa60cc79264c47c3f

def z1039 : W := mkw 0x0eaec00015740000 0x00eaec0001574000 0x5fffe0007fff000b 0xf5fffe0007fff000

def z1040 : W := mkw 0x4eeee0027f760098 0x04eeee0027f76009 0x7fffe0007fff03fb 0xf7fffe0007fff03f

def z1041 : W := mkw 0x91159da705d8c2d6 0x891159da705d8c2d 0x333799e78ff8c3ff 0x7333799e78ff8c3f

def z1042 : W := mkw 0x00000008102d5463 0x000000008102d546 0x6c001e00707ffc78 0x56c001e00707ffc7

def z1043 : W := mkw 0x4004a00015760008 0x04004a0001576000 0x133780000fff000b 0x7133780000fff000

def z1044 : W := mkw 0x4eaee00015760008 0x04eaee0001576000 0x1fffe0000fff000b 0xf1fffe0000fff000

def z1045 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0xdffffffff000000f 0xfdffffffff000000

def z1046 : W := mkw 0x4eeee042ff762198 0x44eeee042ff76219 0xffffe1c7ffff338f 0xfffffe1c7ffff338

def z1047 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x5ffffe007fffcc0b 0xf5ffffe007fffcc0

def z1048 : W := mkw 0x8fbb5fb500084443 0x08fbb5fb50008444 0x9fffffff8000cc07 0xe9fffffff8000cc0

def z1049 : W := mkw 0x8b83558500000000 0x08b8355850000000 0x9fcfffff80000007 0xe9fcfffff8000000

def z1050 : W := mkw 0x0004800205500090 0x0000480020550009 0x333780000ff803fb 0x7333780000ff803f

def z1051 : W := mkw 0x1044a04acdd3b3bc 0xc1044a04acdd3b3b 0x600000004fc733f8 0x0600000004fc733f

def z1052 : W := mkw 0xafbb5fb522808a04 0x0afbb5fb522808a0 0x9fffffff83800007 0xe9fffffff8380000

def z1053 : W := mkw 0x0044a04acd5331b8 0x40044a04acd5331b 0xe0cc61ffcfff33ff 0xbe0cc61ffcfff33f

def z1054 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xeccc61fffc4733ff 0xfeccc61fffc4733f

def z1055 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x9fffffffb000cc07 0xf9fffffffb000cc0

def z1056 : W := mkw 0x8ebb4a3500000000 0x08ebb4a350000000 0x9fffe1ff80000007 0xe9fffe1ff8000000

def z1057 : W := mkw 0x4eaac00033340000 0x04eaac0003334000 0x5f33800073ff0008 0x55f33800073ff000

def z1058 : W := mkw 0x143daa3e957f54fb 0xc143daa3e957f54f 0x103fe03f807f0072 0x0103fe03f807f007

def z1059 : W := mkw 0x4eeee0027f760098 0x04eeee0027f76009 0xffffe1ffffff03ff 0xfffffe1ffffff03f

def z1060 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xef001fc07f80ff8c 0x5ef001fc07f80ff8

def z1061 : W := mkw 0x4044a04aef5331b8 0x44044a04aef5331b 0xe0cc61ffcfc733ff 0xae0cc61ffcfc733f

def z1062 : W := mkw 0x2b80158022808a04 0x02b80158022808a0 0xef001f007f80ff8d 0xfef001f007f80ff8

def z1063 : W := mkw 0x0fbb592400000000 0x00fbb59240000000 0x9ffff9ff80000007 0xe9ffff9ff8000000

def z1064 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0xe0cc7fffcc47ffff 0xae0cc7fffcc47fff

def z1065 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x333781260ff803ff 0x2333781260ff803f

def z1066 : W := mkw 0xafbb5fb522808a04 0x0afbb5fb522808a0 0xfffffffff380fc0f 0xffffffffff380fc0

def z1067 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x33f7f9e78ff8c3ff 0x733f7f9e78ff8c3f

def z1068 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xafc01fc03f80ff85 0x5afc01fc03f80ff8

def z1069 : W := mkw 0x204000406a80ab04 0x0204000406a80ab0 0xecc01fc07f80ff8d 0xfecc01fc07f80ff8

def z1070 : W := mkw 0x2ac004c06a80ab04 0x02ac004c06a80ab0 0xecc01ec07f80ff8c 0xfecc01ec07f80ff8

def z1071 : W := mkw 0x4eeee042ff762198 0x44eeee042ff76219 0x5fffe0007fff038b 0xf5fffe0007fff038

def z1072 : W := mkw 0x8fab579500000000 0x08fab57950000000 0x9fcfffdf80000005 0xe9fcfffdf8000000

def z1073 : W := mkw 0x2b8015c02280ab04 0x02b8015c02280ab0 0xaf001fc03f80ff8d 0x7af001fc03f80ff8

def z1074 : W := mkw 0xafbb5fb522808a04 0x0afbb5fb522808a0 0xbfffffffbf80cf8f 0xfbfffffffbf80cf8

def z1075 : W := mkw 0x0114992005d8c246 0x00114992005d8c24 0x333799200ff8c3ff 0x7333799200ff8c3f

def z1076 : W := mkw 0x5044a04afffff3fe 0xc5044a04afffff3f 0x600000007ffff3f8 0x1600000007ffff3f

def z1077 : W := mkw 0x446ca0007f760008 0x0446ca0007f76000 0x5f3f80007fff000b 0xf5f3f80007fff000

def z1078 : W := mkw 0x0004800005500000 0x0000480000550000 0x533f80004fff000b 0xf533f80004fff000

def z1079 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xefc41fe67f80ff8f 0xfefc41fe67f80ff8

def z1080 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xefc81ff87f80ff8f 0xfefc81ff87f80ff8

def z1081 : W := mkw 0x4eaee00037760008 0x04eaee0003776000 0x133fe00003ff0002 0x0133fe00003ff000

def z1082 : W := mkw 0x6bc275c06a82ab0c 0x06bc275c06a82ab0 0xefc07fc07f80ff8d 0xfefc07fc07f80ff8

def z1083 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xefcc7fc07f80ff8f 0xfefcc7fc07f80ff8

def z1084 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x333399260ff8c3fc 0x5333399260ff8c3f

def z1085 : W := mkw 0x042c800015740000 0x0042c80001574000 0x133f80000fff000b 0x7133f80000fff000

def z1086 : W := mkw 0x8fbb5fb500000000 0x08fbb5fb50000000 0x9fffe7ff80000003 0x89fffe7ff8000000

def z1087 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0x6f001f007f80ff8d 0x76f001f007f80ff8

def z1088 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0x5fffe1c7ffff000b 0xf5fffe1c7ffff000

def z1089 : W := mkw 0x2bc255c06a80ab04 0x02bc255c06a80ab0 0xffc7ffc07f80ff8d 0xfffc7ffc07f80ff8

def z1090 : W := mkw 0x4eaac00033340000 0x04eaac0003334000 0x5fffe00073ff000b 0xf5fffe00073ff000

def z1091 : W := mkw 0x8fbb5fb500084042 0x08fbb5fb50008404 0x9fffffff80780077 0xe9fffffff8078007

def z1092 : W := mkw 0x0044204acc4331b8 0x40044204acc4331b 0x20cc61ff8c4703ff 0x220cc61ff8c4703f

def z1093 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0xf33799264ff8f3ff 0xff33799264ff8f3f

def z1094 : W := mkw 0x8b83558500000000 0x08b8355850000000 0x13cfe1ff80000003 0x013cfe1ff8000000

def z1095 : W := mkw 0x8fab579500000000 0x08fab57950000000 0x9fffe7df80000003 0xe9fffe7df8000000

def z1096 : W := mkw 0x7bc7f5c66fd2ab9c 0x87bc7f5c66fd2ab9 0x13c7e1c60f800381 0x013c7e1c60f80038

def z1097 : W := mkw 0x011119240088c246 0x0011119240088c24 0x333799260ff8c3ff 0x7333799260ff8c3f

def z1098 : W := mkw 0x1015882605d8c2d6 0x81015882605d8c2d 0x333780260ff8c3fb 0x7333780260ff8c3f

def z1099 : W := mkw 0x1115992605d8c2d6 0x81115992605d8c2d 0x133799260ff803f7 0x6133799260ff803f

def z1100 : W := mkw 0x8003400500000000 0x0800340050000000 0x90cfe1ff80000007 0xa90cfe1ff8000000

def z1101 : W := mkw 0x3bc5b5c6efd2ab9c 0xc3bc5b5c6efd2ab9 0x13c7e1c78f800381 0x013c7e1c78f80038

def z1102 : W := mkw 0x04390a3c102d5463 0x004390a3c102d546 0xfc3f9e3e707ffc7e 0xffc3f9e3e707ffc7

def z1103 : W := mkw 0x04280008102d5463 0x004280008102d546 0xec381e00707ffc7e 0xfec381e00707ffc7

def z1104 : W := mkw 0xceeee6917f760008 0x0ceeee6917f76000 0xdfffe7ffffff000f 0xfdfffe7ffffff000

def z1105 : W := mkw 0xabc355c56a80ab04 0x0abc355c56a80ab0 0xffc39fc07f80ff8d 0xfffc39fc07f80ff8

def z1106 : W := mkw 0x8fbb5fb500084042 0x08fbb5fb50008404 0xbfffffff8000c077 0xebfffffff8000c07

def z1107 : W := mkw 0x2bc015c06a80ab04 0x02bc015c06a80ab0 0xecc01fc07f80ff8c 0x9ecc01fc07f80ff8

def z1108 : W := mkw 0x9fbbdfb511bcc647 0x89fbbdfb511bcc64 0x1f339e0033b8cc00 0x51f339e0033b8cc0

def z1109 : W := mkw 0x4044a04add7731b8 0x44044a04add7731b 0x600000004c7f33f8 0x0600000004c7f33f

def z1110 : W := mkw 0x4eeee0007f760008 0x04eeee0007f76000 0xdfffe0387fff000f 0xfdfffe0387fff000

def z1111 : W := mkw 0x4ac6e0006f520008 0x04ac6e0006f52000 0x53ffe0004fff000b 0xf53ffe0004fff000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z7,z3,z4,z5,z6]),(0,[z8,z0,z1,z3,z4,z5,z9]),(0,[z0,z1,z3,z10,z4,z5,z6]),(0,[z0,z1,z3,z4,z11,z5,z6]),(0,[z0,z12,z1,z13,z3,z5,z6]),(0,[z14,z0,z1,z3,z4,z15,z6])],[(0,[z16,z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z18,z6])],[(0,[z0,z1,z3,z4,z19,z5,z6]),(0,[z0,z1,z3,z4,z20,z5,z6])],[(0,[z0,z1,z3,z4,z21,z5,z6]),(0,[z22,z0,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z24,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z25])],[(1,[z0,z1,z3,z4,z26,z6]),(0,[z8,z0,z27,z1,z3,z4,z5]),(0,[z0,z12,z1,z3,z28,z5,z6]),(0,[z29,z0,z1,z30,z3,z4,z6]),(0,[z0,z1,z3,z31,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z32,z6])],[(0,[z33,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z34,z4,z5,z6]),(0,[z35,z0,z1,z3,z4,z5,z6]),(0,[z8,z0,z1,z3,z4,z5,z36]),(0,[z0,z3,z4,z37,z5,z18,z6]),(0,[z38,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z39,z6])],[(0,[z40,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z41,z6]),(0,[z0,z42,z1,z3,z4,z43,z6]),(0,[z0,z1,z3,z4,z5,z6,z44]),(0,[z45,z0,z1,z3,z4,z5,z6]),(0,[z0,z46,z1,z3,z4,z5,z6]),(1,[z16,z0,z3,z28,z5,z6])],[(0,[z0,z1,z3,z4,z5,z47,z6]),(0,[z48,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z49,z0,z50,z3,z4,z5,z6]),(0,[z0,z1,z4,z51,z5,z52,z6]),(0,[z0,z1,z3,z4,z53,z5,z6])],[(0,[z54,z1,z3,z4,z5,z52,z6]),(0,[z0,z55,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z56])],[(0,[z0,z1,z3,z4,z5,z57,z6]),(0,[z0,z1,z3,z4,z5,z58,z6]),(0,[z59,z0,z1,z60,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z61,z6]),(0,[z0,z1,z3,z4,z5,z6,z62]),(1,[z0,z1,z3,z4,z63,z6]),(0,[z0,z1,z3,z4,z64,z5,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z0,z65,z1,z3,z4,z5,z6]),(0,[z66,z0,z1,z3,z4,z5,z6]),(0,[z0,z67,z1,z3,z4,z5,z6]),(0,[z0,z1,z68,z3,z4,z5,z6]),(0,[z0,z1,z69,z3,z4,z5,z6]),(0,[z0,z70,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z71,z5,z72,z6])],[(0,[z0,z1,z3,z4,z73,z5,z6]),(0,[z0,z1,z3,z4,z74,z5,z6]),(0,[z75,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z76]),(0,[z0,z1,z77,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z78])],[],[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z79,z4,z80,z5,z6])]],
   [[(0,[z33,z0,z50,z3,z4,z5,z6]),(0,[z0,z1,z3,z81,z4,z5,z6]),(0,[z82,z0,z1,z3,z4,z5,z6])],[(0,[z14,z83,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z84,z4,z5,z6]),(0,[z0,z1,z3,z4,z15,z43,z6]),(0,[z59,z0,z3,z60,z4,z5,z6]),(0,[z16,z0,z1,z3,z4,z85,z6]),(0,[z0,z1,z86,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z87,z6])],[(0,[z16,z0,z1,z13,z3,z5,z6]),(0,[z0,z1,z3,z88,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z89,z6]),(0,[z0,z1,z30,z3,z4,z15,z6]),(0,[z90,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z91])],[(0,[z92,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z93,z5,z6]),(0,[z1,z3,z4,z43,z5,z52,z6]),(0,[z94,z0,z1,z3,z4,z5,z6]),(0,[z0,z42,z1,z30,z3,z4,z6]),(0,[z0,z1,z95,z3,z4,z5,z6])],[(0,[z96,z0,z1,z3,z4,z5,z6]),(0,[z97,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z98,z5,z6]),(0,[z0,z1,z3,z4,z99,z52,z6])],[(1,[z0,z1,z3,z4,z5,z100]),(0,[z101,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z85,z6]),(0,[z16,z0,z1,z3,z28,z5,z6]),(0,[z0,z1,z3,z4,z5,z102,z6]),(0,[z0,z1,z3,z4,z5,z103,z104]),(0,[z0,z27,z1,z3,z4,z5,z105])]],
   [[(0,[z0,z1,z3,z4,z106,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z107]),(0,[z0,z1,z3,z108,z4,z5,z6]),(0,[z109,z0,z1,z3,z4,z5,z6])],[(0,[z110,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z111,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z112]),(0,[z0,z1,z3,z4,z113,z5,z6])],[(0,[z0,z1,z114,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z115,z6]),(0,[z0,z1,z3,z4,z5,z116,z6]),(0,[z0,z1,z117,z3,z5,z6,z36])],[(0,[z118,z1,z3,z119,z4,z5,z6]),(0,[z120,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z121,z5,z6]),(0,[z118,z0,z1,z3,z4,z57,z6]),(0,[z122,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z123,z4,z5,z6]),(0,[z0,z1,z3,z4,z18,z124,z6]),(0,[z0,z1,z3,z4,z5,z125,z6])],[(0,[z0,z1,z3,z4,z5,z6,z126]),(0,[z127,z1,z3,z4,z128,z5,z6]),(0,[z129,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z130,z5,z6])],[(0,[z0,z1,z131,z3,z4,z5,z6]),(0,[z132,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z133,z4,z5,z6]),(0,[z0,z1,z3,z4,z134,z52,z6]),(0,[z0,z135,z1,z3,z4,z5,z6])],[(0,[z0,z1,z136,z3,z4,z5,z6]),(0,[z137,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z138,z4,z5,z6]),(0,[z0,z1,z139,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z140,z6])]],
   [[(0,[z141,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z142]),(0,[z16,z0,z1,z3,z71,z5,z6]),(0,[z0,z1,z3,z4,z143,z5,z6]),(1,[z0,z1,z3,z71,z5,z72])],[(0,[z0,z1,z3,z4,z144,z5,z6]),(1,[z0,z1,z3,z4,z145,z6]),(0,[z14,z146,z1,z3,z4,z5,z6]),(0,[z0,z1,z117,z3,z71,z5,z6])],[(0,[z147,z0,z1,z3,z4,z5,z6]),(0,[z0,z148,z1,z3,z119,z4,z6]),(0,[z0,z1,z149,z3,z4,z5,z6]),(0,[z59,z0,z1,z79,z4,z5,z6]),(0,[z49,z0,z150,z3,z4,z5,z6]),(0,[z151,z0,z1,z3,z4,z5,z6]),(0,[z152,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z153,z4,z5,z6]),(0,[z0,z1,z154,z4,z5,z103,z6])],[(1,[z0,z155,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z104,z36]),(0,[z0,z1,z3,z4,z5,z6,z156])],[(0,[z0,z1,z3,z4,z5,z23,z105]),(0,[z0,z157,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z158,z4,z5,z6]),(0,[z0,z1,z3,z4,z159,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z160]),(0,[z0,z1,z161,z3,z4,z99,z6])],[(0,[z0,z1,z3,z162,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z23,z163])]],
   [[(0,[z118,z14,z0,z1,z4,z5,z6]),(0,[z0,z164,z1,z3,z4,z5,z6]),(1,[z165,z1,z3,z81,z5,z6]),(0,[z0,z1,z166,z3,z4,z5,z6])],[(0,[z167,z0,z1,z3,z4,z5,z6]),(0,[z8,z0,z1,z3,z4,z168,z6]),(0,[z169,z0,z1,z3,z4,z5,z6]),(0,[z0,z170,z1,z3,z4,z5,z6]),(0,[z0,z1,z171,z3,z4,z5,z6])],[(0,[z172,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z173,z5,z6]),(0,[z0,z27,z1,z4,z5,z6,z105]),(0,[z0,z1,z3,z99,z5,z124,z6])],[(0,[z0,z155,z1,z3,z60,z4,z6]),(0,[z0,z1,z174,z3,z4,z5,z6]),(0,[z0,z1,z3,z175,z4,z5,z6]),(0,[z0,z1,z176,z3,z4,z5,z177])],[(0,[z83,z1,z3,z4,z5,z52,z6]),(0,[z178,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z179,z4,z5,z6])],[(0,[z0,z1,z3,z4,z99,z43,z6]),(0,[z0,z180,z12,z1,z3,z5,z6]),(0,[z29,z0,z1,z3,z4,z37,z6]),(0,[z0,z1,z3,z5,z23,z6,z181]),(0,[z0,z1,z30,z3,z4,z182,z6]),(0,[z0,z1,z3,z4,z5,z6,z183])],[(0,[z0,z1,z3,z184,z4,z5,z6]),(0,[z0,z50,z1,z3,z4,z5,z100]),(0,[z8,z0,z1,z3,z4,z5,z185]),(0,[z186,z0,z1,z3,z4,z5,z6]),(0,[z16,z0,z3,z4,z5,z6,z104]),(0,[z0,z1,z3,z4,z80,z5,z6]),(0,[z14,z0,z1,z4,z5,z6,z105]),(0,[z0,z1,z3,z4,z5,z72,z6])],[(1,[z0,z1,z187,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z188])]],
   [[(1,[z0,z1,z3,z4,z5,z189]),(0,[z0,z190,z1,z3,z4,z5,z6]),(0,[z0,z1,z191,z3,z4,z5,z6])],[(0,[z192,z0,z1,z3,z4,z5,z6]),(0,[z193,z1,z3,z4,z43,z5,z6]),(1,[z0,z27,z1,z4,z5,z105]),(0,[z194,z0,z1,z3,z4,z5,z6])],[(0,[z1,z3,z119,z4,z5,z52,z6]),(0,[z0,z195,z1,z3,z4,z5,z6]),(0,[z196,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z28,z5,z6]),(0,[z0,z1,z3,z197,z4,z5,z6]),(0,[z0,z1,z3,z198,z4,z5,z6]),(0,[z0,z1,z161,z3,z158,z5,z6]),(0,[z0,z1,z3,z158,z4,z124,z6]),(1,[z0,z1,z3,z158,z99,z6])],[],[(0,[z0,z1,z199,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z200]),(0,[z0,z1,z201,z3,z4,z5,z6]),(0,[z0,z1,z202,z3,z4,z5,z6])],[(0,[z0,z203,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z200,z6]),(1,[z0,z1,z3,z4,z5,z204]),(0,[z0,z1,z3,z205,z4,z5,z6]),(0,[z0,z1,z154,z3,z4,z5,z6])],[(0,[z0,z1,z206,z3,z119,z4,z6]),(0,[z0,z207,z1,z3,z4,z5,z6]),(0,[z0,z1,z13,z3,z80,z5,z6])],[(0,[z208,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z209,z6]),(0,[z0,z1,z3,z4,z5,z210,z6]),(1,[z0,z1,z3,z4,z211,z6]),(0,[z22,z1,z3,z4,z5,z9,z6]),(1,[z0,z1,z212,z3,z4,z6]),(1,[z0,z1,z30,z4,z134,z6])]],
   [[(0,[z0,z65,z79,z3,z4,z5,z6]),(0,[z0,z1,z213,z3,z4,z5,z6]),(0,[z0,z1,z13,z175,z4,z5,z6]),(0,[z0,z1,z30,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z214,z6])],[(0,[z0,z215,z3,z4,z5,z6,z104]),(0,[z0,z1,z3,z4,z5,z6,z216])],[(0,[z0,z1,z119,z4,z5,z6,z105]),(0,[z217,z0,z1,z3,z4,z5,z6]),(0,[z0,z65,z1,z60,z4,z5,z6]),(0,[z0,z1,z3,z218,z4,z5,z6]),(0,[z0,z219,z1,z3,z4,z5,z6])],[(0,[z0,z50,z1,z3,z4,z5,z220]),(0,[z193,z1,z3,z119,z4,z5,z6]),(0,[z0,z221,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z222,z6])],[(0,[z0,z1,z3,z4,z223,z5,z6]),(0,[z0,z1,z3,z224,z4,z5,z6]),(0,[z0,z1,z3,z4,z168,z5,z6]),(0,[z22,z0,z1,z3,z4,z5,z72]),(0,[z0,z1,z13,z79,z4,z5,z6]),(0,[z225,z0,z1,z3,z4,z5,z6])],[(0,[z22,z0,z1,z3,z4,z5,z104]),(0,[z0,z1,z175,z4,z80,z5,z6]),(0,[z0,z1,z3,z4,z226,z5,z6]),(0,[z0,z1,z3,z4,z5,z227,z6])],[(0,[z228,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z229,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z230,z6]),(0,[z231,z0,z1,z3,z4,z5,z6]),(0,[z127,z0,z1,z3,z128,z5,z6]),(0,[z232,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z233,z4,z5,z6]),(0,[z0,z1,z3,z234,z4,z5,z6]),(0,[z16,z0,z180,z1,z3,z5,z6]),(0,[z49,z0,z1,z3,z4,z5,z6]),(0,[z235,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z26,z5,z6]),(0,[z0,z1,z236,z3,z4,z5,z6]),(1,[z237,z0,z1,z4,z5,z6]),(0,[z8,z0,z1,z238,z3,z4,z5]),(0,[z239,z0,z1,z3,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z6,z163]),(0,[z240,z0,z3,z4,z5,z72,z6])],[(0,[z241,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z242,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z243,z6])],[(0,[z0,z1,z244,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z245,z6])],[(0,[z0,z1,z3,z246,z4,z5,z6]),(0,[z0,z1,z3,z4,z247,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z248])],[(0,[z249,z0,z1,z3,z4,z5,z6]),(0,[z59,z0,z1,z3,z4,z5,z250]),(0,[z0,z3,z4,z5,z23,z6,z104]),(0,[z0,z1,z30,z3,z4,z124,z6]),(0,[z0,z1,z3,z4,z5,z251,z6])],[(0,[z8,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z182,z6]),(0,[z0,z1,z3,z4,z5,z252,z6])],[(0,[z0,z1,z253,z3,z4,z5,z6]),(0,[z49,z0,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z254,z5,z6]),(0,[z0,z1,z3,z71,z4,z5,z36])]],
   [[(0,[z0,z1,z3,z5,z72,z6,z36])],[(0,[z0,z1,z3,z255,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z256]),(0,[z0,z257,z1,z3,z4,z5,z6]),(0,[z0,z12,z1,z3,z5,z6,z36])],[(0,[z0,z1,z3,z4,z258,z5,z6]),(0,[z259,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z161,z3,z124,z6])],[(0,[z127,z0,z1,z3,z4,z145,z6]),(1,[z0,z1,z13,z175,z5,z6])],[(0,[z22,z0,z1,z3,z4,z15,z5]),(0,[z0,z1,z3,z4,z260,z5,z6]),(0,[z0,z1,z261,z3,z4,z5,z6]),(0,[z0,z1,z3,z262,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z263]),(1,[z146,z1,z3,z4,z5,z6]),(0,[z264,z0,z1,z3,z4,z5,z6])],[(0,[z265,z0,z1,z3,z4,z5,z6]),(0,[z8,z0,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z4,z5,z266,z6]),(0,[z267,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z161,z3,z5,z124,z6]),(0,[z0,z1,z117,z3,z4,z5,z6])],[(0,[z268,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z269]),(0,[z0,z270,z1,z3,z4,z5,z6]),(0,[z0,z1,z271,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z272,z5,z6]),(0,[z0,z273,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z71,z128,z5,z6]),(0,[z0,z1,z274,z3,z4,z5,z6]),(1,[z22,z1,z3,z4,z5,z9]),(0,[z0,z1,z3,z275,z4,z5,z6]),(0,[z0,z146,z1,z3,z4,z5,z6]),(0,[z276,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z117,z3,z4,z5,z36])]],
   [[(0,[z1,z3,z4,z5,z9,z6,z185]),(0,[z0,z1,z277,z3,z4,z5,z6]),(0,[z0,z1,z278,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z279,z6])],[(0,[z165,z280,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z281,z6]),(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z0,z12,z1,z3,z71,z5,z6]),(0,[z0,z1,z3,z282,z4,z5,z6])],[(0,[z0,z1,z283,z3,z4,z5,z6]),(0,[z0,z284,z1,z3,z4,z5,z6]),(0,[z0,z285,z1,z3,z4,z5,z6]),(0,[z0,z1,z286,z3,z4,z5,z6])],[(0,[z287,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z288,z5,z52]),(0,[z0,z1,z3,z4,z289,z5,z6]),(0,[z0,z1,z290,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z291,z6])],[(0,[z8,z0,z1,z3,z4,z115,z6]),(0,[z0,z292,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z293,z5,z6]),(0,[z0,z1,z187,z3,z4,z5,z6]),(0,[z294,z0,z1,z3,z4,z5,z6]),(1,[z49,z0,z3,z4,z5,z23]),(0,[z0,z1,z3,z88,z5,z23,z6]),(0,[z0,z1,z3,z4,z177,z6,z295]),(0,[z0,z296,z1,z3,z4,z5,z6])],[(0,[z297,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z298,z3,z4,z5,z6]),(0,[z0,z12,z1,z3,z299,z5,z6]),(0,[z0,z1,z3,z4,z5,z300,z6]),(0,[z0,z1,z3,z4,z5,z301,z6])],[(0,[z0,z302,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z303,z4,z5,z6])]],
   [[(0,[z304,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z305,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z306,z6]),(0,[z0,z1,z3,z307,z4,z5,z6]),(0,[z0,z1,z308,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z309,z5,z6]),(0,[z0,z42,z1,z3,z4,z5,z62]),(0,[z0,z1,z3,z4,z310,z5,z6]),(0,[z0,z1,z3,z4,z311,z5,z6])],[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z312,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z181])],[(1,[z280,z50,z3,z4,z5,z6]),(0,[z118,z0,z1,z3,z4,z26,z6]),(0,[z313,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z212,z3,z4,z5,z6])],[(0,[z314,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z315,z3,z4,z5,z6]),(1,[z0,z1,z316,z4,z5,z6]),(0,[z16,z317,z1,z3,z4,z5,z6]),(0,[z16,z0,z1,z3,z5,z6,z36]),(0,[z14,z0,z1,z3,z4,z134,z6])],[(0,[z0,z1,z3,z4,z5,z6,z185]),(1,[z0,z1,z3,z4,z318,z6]),(0,[z0,z1,z3,z4,z5,z6,z319]),(0,[z0,z1,z3,z4,z5,z104,z163])],[(0,[z280,z0,z215,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z320,z6]),(0,[z0,z1,z3,z4,z5,z105,z36]),(0,[z0,z1,z3,z4,z5,z124,z6])],[(0,[z0,z1,z3,z4,z5,z115,z6]),(1,[z59,z0,z60,z4,z5,z6]),(0,[z0,z1,z3,z4,z321,z5,z6]),(0,[z322,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z238,z3,z4,z5,z103])]],
   [[(0,[z0,z1,z3,z323,z4,z5,z6]),(0,[z0,z273,z1,z3,z119,z4,z5]),(0,[z0,z1,z3,z4,z324,z5,z6]),(0,[z0,z1,z325,z3,z4,z5,z6]),(0,[z0,z1,z326,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z37,z5,z6])],[(0,[z0,z1,z3,z4,z5,z327,z6]),(0,[z0,z1,z3,z4,z5,z6,z328]),(0,[z329,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z330,z5,z6])],[(0,[z118,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z331,z3,z4,z5,z6]),(0,[z0,z1,z332,z3,z4,z5,z6]),(0,[z0,z3,z299,z4,z28,z5,z6]),(0,[z29,z0,z1,z3,z4,z18,z6]),(0,[z0,z180,z1,z13,z4,z5,z6]),(0,[z0,z1,z333,z3,z4,z5,z6])],[(0,[z1,z215,z3,z4,z128,z5,z6]),(0,[z0,z1,z334,z3,z4,z5,z52]),(0,[z8,z0,z1,z3,z173,z5,z6]),(0,[z49,z0,z3,z299,z4,z5,z6]),(0,[z0,z1,z3,z4,z99,z37,z6]),(0,[z0,z1,z3,z4,z5,z6,z335]),(0,[z0,z1,z3,z4,z5,z6,z336])],[(0,[z0,z1,z3,z4,z5,z6,z337]),(0,[z0,z1,z3,z4,z5,z177,z104]),(0,[z0,z1,z3,z158,z99,z5,z6]),(0,[z338,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z220]),(0,[z0,z339,z1,z3,z4,z5,z6]),(0,[z0,z340,z1,z3,z4,z5,z6]),(0,[z0,z180,z1,z3,z80,z5,z6])],[(0,[z0,z1,z3,z4,z5,z145,z6]),(0,[z8,z0,z1,z176,z3,z4,z5]),(1,[z0,z1,z10,z4,z5,z6]),(0,[z16,z0,z3,z4,z28,z5,z6]),(0,[z0,z1,z3,z4,z5,z72,z105]),(0,[z0,z1,z3,z4,z15,z5,z103])]],
   [[(0,[z14,z54,z0,z1,z4,z5,z6]),(0,[z0,z341,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z342]),(0,[z0,z1,z3,z4,z5,z343,z6])],[(0,[z8,z0,z1,z187,z4,z5,z6]),(0,[z16,z0,z1,z3,z299,z5,z6]),(0,[z0,z1,z3,z4,z344,z5,z6])],[(0,[z127,z0,z1,z3,z81,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z345]),(0,[z0,z42,z3,z4,z5,z18,z6])],[(0,[z0,z1,z3,z4,z51,z5,z6]),(0,[z0,z180,z1,z3,z4,z5,z245]),(0,[z0,z180,z1,z4,z80,z5,z6])],[(0,[z0,z1,z3,z4,z5,z346,z6])],[(0,[z0,z1,z3,z4,z347,z5,z6]),(0,[z0,z3,z299,z4,z5,z6,z104]),(0,[z240,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z348,z6])],[(0,[z0,z1,z3,z4,z37,z124,z6])],[(0,[z0,z1,z3,z4,z349,z5,z6]),(0,[z193,z54,z1,z3,z4,z5,z6]),(1,[z83,z1,z3,z4,z52,z6]),(0,[z14,z0,z1,z3,z4,z99,z6]),(0,[z0,z1,z30,z3,z4,z134,z6]),(0,[z0,z350,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z351,z3,z4,z5,z6]),(0,[z0,z352,z1,z3,z4,z5,z6])],[(0,[z0,z1,z353,z3,z4,z5,z6]),(0,[z0,z354,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z355])],[(0,[z0,z356,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z357,z5,z6])],[(0,[z0,z1,z3,z358,z4,z5,z6]),(0,[z359,z0,z1,z3,z4,z5,z6]),(1,[z33,z215,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z360,z5,z6]),(0,[z22,z0,z1,z3,z4,z5,z9]),(0,[z0,z42,z1,z3,z4,z18,z6]),(1,[z0,z150,z3,z4,z5,z104]),(0,[z0,z150,z1,z3,z4,z5,z104])],[(0,[z0,z361,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z362,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z363]),(0,[z0,z1,z176,z3,z4,z5,z6])],[],[(1,[z127,z1,z3,z128,z5,z6]),(0,[z0,z1,z3,z4,z5,z364,z6]),(0,[z0,z365,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z366,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z367]),(0,[z0,z1,z3,z368,z4,z5,z6]),(0,[z0,z369,z1,z3,z4,z5,z6]),(0,[z0,z370,z1,z3,z4,z5,z6]),(1,[z0,z65,z79,z4,z5,z6]),(0,[z0,z371,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z36])]],
   [[(0,[z0,z1,z3,z372,z4,z5,z6]),(0,[z127,z0,z1,z3,z4,z5,z6]),(0,[z22,z0,z1,z3,z4,z5,z36]),(0,[z0,z1,z3,z4,z5,z373,z6]),(0,[z0,z1,z3,z4,z5,z72,z23])],[(0,[z165,z1,z215,z3,z4,z5,z6]),(0,[z0,z374,z1,z3,z4,z5,z6]),(0,[z375,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z376,z4,z5,z6])],[(1,[z54,z1,z283,z4,z5,z6]),(0,[z0,z1,z3,z71,z81,z5,z6]),(0,[z0,z1,z3,z377,z4,z5,z6]),(1,[z0,z42,z3,z4,z18,z6]),(0,[z0,z1,z378,z3,z4,z5,z6]),(1,[z0,z1,z4,z5,z6,z91])],[(0,[z54,z0,z1,z119,z4,z5,z6]),(0,[z0,z1,z334,z3,z4,z5,z6]),(0,[z0,z1,z3,z379,z4,z5,z6])],[(0,[z0,z380,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z381,z5,z6]),(0,[z83,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z52,z6]),(0,[z0,z12,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z382]),(0,[z383,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z128,z5,z6,z36]),(0,[z0,z1,z3,z4,z384,z5,z6]),(0,[z385,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z386,z6]),(0,[z0,z1,z3,z4,z5,z387,z6]),(0,[z0,z1,z388,z3,z4,z5,z6]),(1,[z0,z1,z154,z4,z5,z6])],[(0,[z16,z389,z1,z3,z4,z5,z6]),(1,[z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z299,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z390,z6])],[(0,[z0,z1,z3,z391,z4,z5,z6])]],
   [[(0,[z0,z1,z392,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z393,z5,z6]),(0,[z0,z1,z3,z394,z4,z5,z6])],[(0,[z14,z178,z1,z3,z4,z5,z6])],[(0,[z280,z0,z1,z3,z4,z272,z6]),(0,[z0,z1,z3,z395,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z112]),(0,[z0,z1,z396,z3,z4,z5,z6]),(0,[z0,z1,z397,z3,z4,z5,z6])],[(0,[z193,z0,z1,z3,z4,z5,z6]),(0,[z398,z0,z1,z3,z4,z5,z6]),(1,[z0,z341,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z399,z6]),(0,[z0,z1,z400,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z401]),(1,[z240,z0,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z402,z6]),(0,[z0,z1,z3,z119,z4,z5,z6]),(0,[z0,z403,z1,z3,z4,z5,z6]),(0,[z0,z404,z1,z3,z4,z5,z6]),(0,[z0,z1,z238,z3,z4,z5,z6])],[(0,[z118,z0,z1,z119,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z405,z6]),(0,[z0,z1,z3,z4,z5,z6,z406]),(0,[z0,z180,z1,z3,z4,z5,z107]),(0,[z0,z1,z3,z4,z407,z5,z6])],[(0,[z8,z0,z1,z3,z4,z5,z72]),(0,[z0,z1,z79,z3,z4,z5,z6]),(0,[z0,z1,z408,z3,z4,z5,z6]),(0,[z0,z409,z1,z3,z4,z5,z6]),(0,[z0,z1,z30,z4,z134,z5,z6])],[(0,[z0,z148,z1,z3,z4,z5,z6]),(0,[z165,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z52,z182,z6]),(0,[z410,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z411,z6])]],
   [[(0,[z165,z1,z3,z81,z4,z5,z6]),(0,[z0,z1,z3,z71,z4,z5,z6])],[(1,[z118,z1,z119,z4,z5,z6]),(0,[z0,z1,z3,z4,z412,z5,z6])],[(0,[z16,z0,z12,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z413,z6]),(0,[z0,z1,z414,z3,z4,z5,z6]),(0,[z415,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z416,z6]),(0,[z0,z1,z3,z4,z5,z417,z6]),(0,[z0,z418,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z63,z177,z6]),(0,[z0,z1,z3,z4,z5,z6,z419])],[(0,[z8,z22,z1,z3,z4,z5,z6]),(0,[z420,z0,z1,z3,z4,z5,z6])],[(0,[z0,z421,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z216]),(0,[z0,z1,z3,z4,z5,z9,z6]),(0,[z0,z1,z3,z422,z4,z5,z6]),(0,[z14,z0,z42,z1,z3,z4,z6]),(0,[z0,z1,z4,z134,z5,z182,z6])],[(0,[z0,z1,z423,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z424,z5,z6]),(0,[z425,z0,z1,z3,z4,z5,z6]),(0,[z0,z150,z3,z4,z5,z6,z104]),(0,[z0,z1,z3,z4,z5,z6,z426])],[(0,[z16,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z85,z6]),(0,[z0,z1,z4,z5,z103,z6,z91])]],
   [[(0,[z1,z3,z81,z4,z128,z5,z6]),(0,[z0,z1,z3,z4,z5,z427,z6])],[(0,[z165,z0,z1,z3,z128,z5,z6]),(0,[z0,z1,z3,z81,z4,z5,z216]),(0,[z0,z1,z3,z4,z5,z428,z6])],[(0,[z118,z54,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z211,z5,z6]),(0,[z0,z429,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z430,z5,z6]),(0,[z14,z0,z1,z30,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z431,z6]),(0,[z0,z1,z3,z4,z5,z103,z6])],[(1,[z0,z1,z3,z4,z272,z6]),(0,[z0,z1,z432,z3,z4,z5,z6]),(0,[z8,z1,z3,z4,z5,z6,z185]),(0,[z0,z1,z3,z4,z433,z5,z6]),(0,[z0,z434,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z125,z6]),(0,[z0,z1,z3,z4,z5,z435,z6])],[(1,[z0,z1,z3,z4,z5,z245]),(0,[z0,z27,z1,z3,z4,z5,z177]),(0,[z0,z436,z1,z3,z4,z5,z6])],[(0,[z0,z1,z176,z119,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z437]),(0,[z8,z0,z1,z316,z4,z5,z6]),(0,[z8,z0,z1,z3,z4,z15,z5]),(0,[z0,z65,z1,z79,z4,z5,z6])],[(0,[z438,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z439,z3,z4,z5,z6]),(0,[z0,z1,z30,z3,z4,z6,z163])]],
   [[(0,[z440,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z441,z4,z5,z6])],[(0,[z59,z0,z1,z3,z4,z5,z6]),(0,[z0,z317,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z442,z5,z6]),(0,[z0,z1,z161,z3,z4,z5,z6]),(1,[z0,z1,z117,z3,z5,z36])],[(0,[z0,z1,z206,z3,z4,z5,z6]),(0,[z0,z1,z3,z443,z4,z5,z6]),(0,[z444,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z81,z5,z6,z36]),(0,[z0,z1,z3,z4,z99,z18,z6]),(0,[z0,z1,z3,z4,z5,z103,z23]),(0,[z0,z1,z445,z3,z4,z5,z6])],[(0,[z0,z1,z3,z446,z4,z5,z6])],[(0,[z54,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z447,z5,z6]),(0,[z0,z448,z1,z3,z4,z5,z6]),(0,[z16,z0,z1,z3,z4,z5,z112]),(0,[z0,z1,z3,z4,z449,z5,z6])],[(0,[z0,z1,z450,z3,z4,z5,z6]),(0,[z0,z451,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z452,z5,z6])],[(0,[z0,z1,z283,z4,z5,z6,z105]),(0,[z0,z1,z3,z4,z5,z6,z453]),(0,[z0,z1,z3,z4,z5,z6,z454]),(0,[z0,z1,z3,z4,z5,z104,z105]),(0,[z0,z1,z3,z4,z5,z455,z6]),(0,[z0,z1,z3,z4,z5,z279,z6])],[(0,[z50,z1,z215,z3,z4,z5,z6]),(0,[z280,z1,z3,z4,z128,z5,z6]),(0,[z0,z1,z3,z4,z52,z124,z6]),(0,[z0,z1,z3,z4,z456,z5,z6]),(0,[z0,z1,z457,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z458,z5,z6]),(0,[z0,z12,z3,z299,z4,z5,z6]),(0,[z0,z459,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z177,z36])],[(1,[z193,z1,z3,z4,z43,z6]),(0,[z22,z0,z1,z3,z4,z5,z185]),(0,[z0,z1,z60,z4,z80,z5,z6]),(0,[z0,z42,z1,z3,z4,z5,z460])],[(1,[z0,z1,z206,z3,z4,z6]),(1,[z0,z461,z3,z4,z5,z6]),(0,[z0,z1,z462,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z62]),(0,[z0,z1,z463,z3,z4,z5,z6]),(0,[z0,z1,z238,z3,z4,z15,z6])],[(0,[z127,z0,z1,z3,z4,z211,z6]),(0,[z0,z1,z3,z4,z5,z23,z177]),(0,[z0,z1,z3,z4,z5,z464,z6]),(0,[z0,z1,z3,z465,z4,z5,z6])],[(0,[z49,z0,z215,z3,z4,z5,z6]),(0,[z466,z0,z1,z3,z4,z5,z6])],[(0,[z467,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z193,z14,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z468,z5,z6]),(0,[z0,z1,z469,z3,z4,z5,z6]),(0,[z470,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z471]),(0,[z472,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z473]),(0,[z0,z1,z161,z3,z4,z124,z6])],[(0,[z83,z0,z1,z3,z4,z52,z6]),(0,[z0,z1,z3,z474,z4,z5,z6]),(0,[z0,z155,z1,z3,z4,z5,z6]),(0,[z475,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z476,z6])]],
   [[(0,[z280,z0,z1,z3,z4,z477,z6]),(0,[z0,z1,z4,z5,z177,z6,z105]),(0,[z0,z1,z3,z4,z5,z6,z478]),(0,[z0,z1,z3,z4,z5,z6,z479])],[(0,[z0,z1,z3,z4,z5,z480,z6]),(0,[z0,z1,z3,z4,z481,z5,z6]),(0,[z0,z482,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z483]),(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z484,z6])],[(0,[z0,z1,z3,z4,z485,z5,z6]),(1,[z178,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z486]),(0,[z0,z1,z3,z4,z5,z6,z487])],[(0,[z33,z0,z215,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z488,z5,z6]),(1,[z0,z1,z3,z4,z6,z295]),(0,[z489,z0,z1,z3,z4,z5,z6]),(0,[z0,z490,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z288,z5,z6]),(0,[z0,z1,z3,z491,z4,z5,z6]),(0,[z0,z1,z3,z492,z4,z5,z6]),(0,[z0,z1,z176,z3,z4,z5,z105]),(0,[z0,z493,z1,z3,z4,z5,z6])],[(0,[z193,z0,z1,z3,z4,z52,z6]),(0,[z0,z1,z3,z4,z5,z6,z494]),(0,[z0,z1,z3,z4,z495,z5,z6])],[(0,[z0,z1,z3,z4,z5,z496,z6]),(0,[z0,z497,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z498,z5,z6]),(0,[z0,z1,z3,z4,z5,z499,z6]),(1,[z0,z1,z3,z4,z5,z107])]],
   [[(0,[z500,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z501,z6]),(0,[z0,z1,z3,z4,z5,z502,z6]),(0,[z0,z1,z3,z4,z5,z6,z163])],[(0,[z0,z1,z3,z4,z5,z503,z6]),(0,[z0,z1,z3,z4,z5,z504,z6]),(1,[z29,z0,z3,z4,z37,z6]),(0,[z0,z1,z505,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z506,z6]),(0,[z507,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z43,z182,z6]),(0,[z0,z1,z3,z316,z4,z5,z6]),(1,[z0,z1,z3,z377,z5,z6]),(0,[z0,z1,z3,z4,z318,z5,z6]),(0,[z0,z1,z3,z4,z5,z460,z6]),(0,[z0,z1,z3,z4,z5,z72,z104]),(0,[z0,z1,z13,z3,z4,z5,z6]),(0,[z508,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z158,z4,z99,z6])],[(0,[z0,z1,z176,z283,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z509]),(0,[z510,z0,z1,z3,z4,z5,z6]),(0,[z16,z0,z1,z3,z4,z5,z189]),(0,[z29,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z13,z3,z175,z5,z6]),(0,[z0,z1,z3,z175,z4,z125,z6])],[(0,[z0,z1,z3,z4,z128,z5,z6]),(0,[z511,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z512,z3,z4,z5,z6]),(0,[z513,z0,z1,z3,z4,z5,z6]),(0,[z29,z0,z42,z3,z4,z5,z6]),(0,[z0,z514,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z515]),(0,[z237,z0,z1,z3,z4,z5,z6]),(0,[z516,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z517,z6])],[(0,[z0,z1,z3,z4,z5,z518,z6]),(0,[z0,z1,z3,z519,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z520,z6]),(0,[z0,z1,z3,z521,z4,z5,z6]),(0,[z0,z1,z3,z522,z4,z5,z6])],[(0,[z0,z523,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z524,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z0,z1,z3,z525,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z250])],[(0,[z22,z0,z1,z3,z4,z5,z6]),(0,[z0,z79,z3,z60,z4,z5,z6]),(0,[z0,z1,z3,z526,z4,z5,z6])],[(1,[z0,z1,z3,z4,z477,z6]),(0,[z0,z1,z3,z4,z527,z5,z6]),(0,[z22,z0,z27,z1,z3,z4,z5]),(0,[z528,z0,z1,z3,z4,z5,z6]),(0,[z29,z0,z3,z4,z37,z5,z6]),(0,[z529,z0,z1,z3,z4,z5,z6])],[(0,[z193,z83,z1,z3,z4,z5,z6])],[(0,[z165,z0,z1,z3,z81,z5,z6]),(1,[z0,z1,z3,z4,z288,z5]),(0,[z0,z1,z3,z4,z530,z5,z6]),(1,[z0,z1,z3,z5,z6,z181])],[(0,[z0,z1,z3,z4,z43,z5,z6]),(0,[z8,z0,z341,z3,z4,z5,z6]),(0,[z59,z0,z65,z3,z4,z5,z6])],[(0,[z0,z1,z215,z3,z4,z5,z6]),(0,[z0,z531,z1,z3,z4,z5,z6]),(0,[z0,z1,z532,z3,z4,z5,z6]),(0,[z0,z1,z3,z533,z4,z5,z6])],[(0,[z0,z1,z3,z4,z534,z5,z6]),(0,[z83,z0,z1,z3,z4,z43,z6]),(0,[z0,z1,z238,z3,z4,z5,z163])]],
   [[(0,[z535,z0,z1,z3,z4,z5,z6]),(0,[z536,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z324,z6]),(0,[z0,z1,z3,z537,z4,z5,z6])],[(0,[z538,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z539,z6])],[(0,[z280,z0,z50,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z100]),(0,[z0,z1,z3,z4,z540,z5,z6]),(0,[z59,z0,z1,z3,z4,z5,z204]),(0,[z0,z1,z176,z4,z134,z5,z6])],[(0,[z0,z1,z3,z4,z5,z541,z6]),(0,[z0,z1,z542,z3,z4,z5,z6]),(0,[z0,z50,z3,z4,z5,z6,z104]),(0,[z0,z1,z3,z543,z4,z5,z6]),(0,[z544,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z545,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z250,z6]),(0,[z0,z1,z546,z3,z4,z5,z6]),(0,[z0,z42,z1,z3,z4,z5,z6]),(0,[z0,z1,z547,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z548,z5,z6]),(0,[z549,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z550,z3,z4,z5,z6]),(0,[z49,z0,z1,z3,z4,z5,z104])],[(0,[z551,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z57,z6]),(1,[z0,z1,z3,z522,z5,z6]),(0,[z0,z1,z30,z3,z4,z99,z6]),(0,[z0,z552,z1,z3,z4,z5,z6])],[(0,[z193,z0,z1,z3,z4,z43,z6]),(0,[z553,z0,z1,z3,z4,z5,z6]),(0,[z0,z448,z1,z3,z60,z5,z6]),(0,[z0,z1,z3,z4,z5,z554,z6]),(1,[z14,z0,z1,z4,z182,z6]),(0,[z14,z0,z1,z4,z5,z182,z6])],[(0,[z0,z1,z3,z4,z555,z5,z6]),(0,[z0,z1,z556,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z15,z5,z163])]],
   [[(0,[z0,z1,z3,z4,z173,z5,z6]),(0,[z0,z557,z1,z3,z4,z5,z6]),(0,[z0,z1,z558,z3,z4,z5,z6]),(0,[z0,z1,z3,z71,z4,z5,z72])],[],[(0,[z0,z1,z3,z4,z559,z5,z6]),(0,[z0,z1,z3,z4,z43,z124,z6]),(0,[z8,z0,z1,z3,z4,z5,z104])],[(0,[z0,z1,z3,z4,z5,z560,z6])],[(0,[z280,z50,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z561,z5,z6]),(0,[z0,z1,z3,z4,z5,z562,z6]),(0,[z0,z1,z3,z4,z5,z563,z6])],[(0,[z0,z1,z3,z4,z564,z5,z6]),(0,[z83,z0,z1,z30,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z565,z6]),(0,[z0,z1,z3,z4,z5,z6,z566]),(1,[z0,z1,z238,z3,z4,z163])],[(0,[z0,z1,z3,z4,z5,z567,z6]),(0,[z568,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z569,z4,z5,z6]),(0,[z570,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z571,z6]),(0,[z572,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z573,z6]),(0,[z0,z1,z3,z574,z4,z5,z6]),(0,[z0,z1,z3,z4,z15,z103,z6])],[(0,[z33,z280,z1,z3,z4,z5,z6]),(0,[z237,z0,z1,z4,z5,z52,z6]),(0,[z0,z1,z3,z4,z5,z575,z6]),(0,[z0,z1,z3,z4,z5,z6,z576]),(1,[z0,z1,z176,z4,z5,z177]),(0,[z0,z1,z3,z4,z15,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z577,z6]),(0,[z0,z1,z578,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z579]),(0,[z0,z580,z1,z3,z4,z5,z6]),(0,[z0,z1,z117,z3,z4,z5,z72]),(0,[z0,z1,z3,z4,z581,z5,z6])],[(0,[z582,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z583,z4,z5,z6]),(0,[z16,z49,z0,z3,z4,z5,z6])],[(1,[z0,z1,z4,z51,z5,z6]),(0,[z0,z1,z3,z4,z584,z5,z6]),(0,[z0,z1,z585,z3,z4,z5,z6]),(0,[z49,z0,z3,z4,z5,z23,z6])],[(0,[z586,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z587,z5,z6]),(0,[z0,z588,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z60,z4,z5,z6])],[(0,[z0,z1,z3,z589,z4,z5,z6]),(0,[z193,z0,z1,z30,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z590,z6]),(0,[z0,z1,z3,z4,z591,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z592])],[(0,[z0,z1,z17,z3,z4,z5,z6]),(0,[z593,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z594,z5,z6])],[(0,[z595,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z596,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z597]),(0,[z0,z1,z3,z4,z5,z598,z6]),(0,[z599,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z600,z6]),(0,[z0,z1,z3,z4,z601,z5,z6])],[(0,[z0,z1,z3,z4,z602,z5,z6]),(0,[z14,z0,z1,z3,z4,z182,z6]),(0,[z603,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z604,z6])]],
   [[(0,[z0,z605,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z606,z4,z5,z6])],[(0,[z0,z1,z3,z4,z43,z6,z163]),(1,[z317,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z607,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z608]),(0,[z0,z1,z609,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z103,z6,z163])],[(0,[z22,z0,z1,z176,z3,z4,z5]),(0,[z0,z1,z610,z3,z4,z5,z6])],[(0,[z54,z0,z1,z283,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z611,z6]),(0,[z0,z1,z3,z4,z612,z5,z6]),(0,[z613,z0,z1,z3,z4,z5,z6])],[(1,[z0,z273,z1,z3,z4,z5]),(0,[z614,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z615,z5,z6]),(0,[z8,z0,z461,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z616,z6]),(0,[z389,z0,z1,z3,z4,z5,z6])],[(0,[z1,z283,z3,z119,z4,z5,z6])],[(0,[z29,z0,z1,z3,z4,z52,z6]),(0,[z0,z1,z617,z3,z4,z5,z6]),(0,[z0,z27,z1,z3,z4,z5,z6]),(0,[z0,z1,z618,z3,z4,z5,z6]),(0,[z0,z1,z3,z619,z4,z5,z6])],[(0,[z54,z1,z283,z3,z4,z5,z6]),(0,[z0,z1,z620,z3,z4,z5,z6]),(0,[z0,z1,z212,z3,z60,z4,z6]),(0,[z0,z1,z621,z3,z4,z5,z6]),(0,[z0,z1,z3,z175,z4,z324,z6]),(0,[z622,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z623,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z13,z60,z4,z5,z6]),(0,[z0,z1,z3,z522,z60,z5,z6]),(0,[z16,z0,z1,z3,z4,z318,z6]),(1,[z0,z1,z3,z88,z5,z6]),(0,[z0,z1,z3,z4,z5,z624,z6]),(0,[z0,z1,z625,z3,z4,z5,z6])],[(0,[z0,z50,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z220,z6]),(0,[z0,z1,z3,z4,z5,z6,z204]),(0,[z0,z1,z3,z4,z5,z626,z6]),(1,[z0,z12,z3,z299,z5,z6]),(0,[z0,z1,z3,z4,z627,z5,z6]),(0,[z0,z1,z3,z4,z5,z177,z6]),(0,[z628,z0,z1,z3,z4,z5,z6])],[(0,[z0,z180,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z629,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z630,z5,z6]),(0,[z0,z631,z1,z3,z4,z5,z6])],[(0,[z0,z180,z1,z3,z175,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z632]),(0,[z0,z1,z238,z3,z4,z6,z163])],[(0,[z633,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z634,z5,z6]),(0,[z0,z1,z635,z3,z4,z5,z6])],[(0,[z118,z0,z1,z283,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z72,z177])],[(0,[z0,z1,z636,z3,z4,z5,z6]),(0,[z637,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z638,z3,z4,z5,z6])],[(0,[z0,z1,z639,z3,z4,z5,z6]),(0,[z165,z127,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z640,z4,z5,z6]),(0,[z0,z1,z3,z4,z641,z5,z6])]],
   [[(0,[z0,z3,z4,z5,z72,z279,z6]),(0,[z0,z642,z1,z3,z4,z5,z6])],[(0,[z643,z0,z1,z3,z4,z5,z6])],[(0,[z54,z0,z1,z4,z134,z5,z6]),(0,[z16,z0,z1,z10,z4,z5,z6]),(0,[z644,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z460]),(0,[z0,z27,z1,z176,z4,z5,z6]),(0,[z645,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z99,z5,z6]),(0,[z0,z1,z3,z4,z646,z5,z6])],[(0,[z0,z647,z1,z3,z4,z5,z6]),(0,[z648,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z649,z3,z4,z5,z6])],[(0,[z650,z0,z1,z3,z4,z5,z6]),(0,[z8,z0,z1,z3,z377,z5,z6]),(0,[z0,z1,z651,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z23,z6])],[],[(0,[z0,z1,z3,z4,z5,z6,z652]),(0,[z0,z1,z653,z3,z4,z5,z6]),(0,[z0,z42,z1,z3,z4,z52,z6]),(0,[z0,z1,z3,z4,z5,z6,z654]),(0,[z0,z1,z3,z4,z5,z23,z36]),(0,[z14,z0,z1,z176,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z655,z6]),(0,[z0,z1,z3,z4,z5,z6,z656])],[(0,[z0,z1,z3,z4,z5,z6,z657]),(1,[z0,z1,z3,z4,z168,z6]),(0,[z658,z0,z1,z3,z4,z5,z6]),(0,[z0,z150,z1,z3,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z124,z6])]],
   [[(0,[z659,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z461,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z52,z6,z163]),(0,[z0,z1,z3,z4,z5,z660,z6]),(0,[z0,z1,z3,z4,z661,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z105]),(0,[z0,z1,z3,z4,z5,z6,z295])],[(0,[z662,z0,z1,z3,z4,z5,z6]),(1,[z0,z448,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z663,z6]),(0,[z0,z1,z3,z4,z664,z5,z6]),(0,[z665,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z666,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z667]),(0,[z0,z1,z3,z4,z668,z5,z6]),(0,[z0,z1,z3,z4,z5,z669,z6])],[(0,[z0,z1,z3,z4,z670,z5,z6]),(0,[z0,z671,z1,z3,z4,z5,z6]),(0,[z0,z1,z672,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z134,z5,z6]),(0,[z0,z1,z176,z4,z5,z177,z6]),(0,[z0,z1,z3,z4,z5,z6,z673])],[(0,[z118,z0,z1,z4,z134,z5,z6]),(0,[z0,z1,z3,z4,z43,z134,z6]),(0,[z0,z1,z674,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z675]),(0,[z0,z676,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z677,z4,z5,z6])],[(0,[z0,z1,z678,z3,z4,z5,z6]),(0,[z0,z1,z3,z81,z4,z5,z200]),(1,[z8,z1,z3,z4,z5,z185]),(0,[z0,z1,z3,z4,z5,z189,z6]),(0,[z679,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z134,z5,z6,z105])],[(0,[z29,z0,z1,z3,z4,z43,z6]),(0,[z0,z1,z3,z680,z4,z5,z6]),(0,[z0,z150,z1,z3,z4,z5,z23]),(0,[z0,z1,z3,z681,z4,z5,z6]),(0,[z0,z1,z3,z682,z4,z5,z6])],[(0,[z33,z1,z215,z3,z4,z5,z6]),(0,[z0,z1,z683,z3,z4,z5,z6]),(0,[z0,z1,z3,z684,z4,z5,z6]),(0,[z0,z1,z3,z685,z4,z5,z6]),(0,[z22,z0,z1,z238,z3,z4,z5]),(0,[z0,z1,z686,z3,z4,z5,z6]),(0,[z0,z1,z687,z3,z4,z5,z6])]],
   [[(0,[z688,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z689,z4,z5,z6]),(0,[z0,z1,z690,z3,z4,z5,z6])],[(0,[z0,z1,z691,z3,z4,z5,z6]),(0,[z0,z1,z3,z692,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z104]),(0,[z0,z1,z693,z3,z4,z5,z6])],[(0,[z280,z0,z1,z3,z4,z5,z6]),(0,[z694,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z695,z4,z5,z6]),(0,[z0,z1,z3,z4,z15,z52,z6]),(0,[z0,z42,z1,z3,z4,z37,z6]),(0,[z14,z29,z0,z1,z3,z4,z6]),(0,[z696,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z697,z6])],[(0,[z0,z1,z3,z4,z5,z698,z6]),(1,[z389,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z699,z5,z6]),(1,[z0,z180,z1,z80,z5,z6]),(0,[z0,z1,z3,z4,z63,z5,z6]),(0,[z0,z1,z3,z700,z4,z5,z6])],[(0,[z701,z0,z1,z3,z4,z5,z6])],[(0,[z0,z702,z1,z3,z4,z5,z6])],[(1,[z0,z148,z1,z3,z4,z6]),(0,[z703,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z477,z6]),(0,[z0,z1,z704,z3,z4,z5,z6]),(1,[z0,z1,z653,z3,z4,z5]),(0,[z0,z1,z653,z3,z119,z4,z5]),(1,[z0,z1,z334,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z705,z6]),(0,[z0,z706,z1,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z707,z60,z4,z5,z6]),(0,[z146,z1,z3,z4,z99,z6]),(0,[z708,z0,z1,z3,z4,z5]),(0,[z0,z1,z117,z3,z5,z709])],[(0,[z1,z3,z710,z128,z5,z6]),(0,[z0,z1,z3,z377,z5,z200]),(0,[z8,z1,z3,z4,z5,z669]),(0,[z16,z0,z3,z574,z5,z6])],[],[(0,[z0,z273,z1,z3,z4,z5]),(0,[z389,z1,z3,z4,z5,z189]),(0,[z0,z1,z3,z4,z711,z6]),(0,[z16,z0,z3,z53,z5,z6]),(0,[z0,z3,z4,z5,z712,z6]),(0,[z0,z1,z154,z4,z6,z163])],[(0,[z500,z14,z0,z1,z4,z6]),(0,[z0,z1,z4,z713,z5,z6])],[(0,[z714,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z715]),(0,[z716,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z145,z6]),(0,[z0,z1,z3,z4,z717,z6]),(0,[z718,z1,z3,z4,z5,z6]),(0,[z49,z0,z3,z88,z5,z6]),(0,[z0,z1,z3,z4,z5,z719])],[(0,[z16,z0,z3,z720,z5,z6]),(0,[z0,z1,z721,z3,z4,z6]),(0,[z0,z1,z3,z4,z23,z295]),(0,[z0,z1,z3,z71,z5,z709])]],
   [[(0,[z0,z1,z3,z4,z5,z722]),(0,[z0,z588,z3,z4,z5,z104]),(0,[z0,z155,z1,z3,z4,z6]),(0,[z0,z1,z3,z5,z6,z723]),(0,[z0,z1,z176,z4,z177,z295])],[(0,[z0,z1,z724,z4,z5,z6]),(0,[z0,z461,z3,z4,z5,z72]),(0,[z0,z514,z1,z4,z5,z105])],[(0,[z280,z50,z3,z4,z272,z6]),(0,[z1,z3,z4,z725,z52,z6])],[(0,[z0,z1,z726,z3,z4,z5]),(0,[z0,z727,z3,z4,z5,z6]),(0,[z0,z448,z1,z3,z5,z728]),(0,[z0,z1,z3,z4,z729,z6]),(0,[z0,z3,z4,z5,z660,z104])],[(0,[z165,z1,z3,z81,z5,z6]),(0,[z0,z1,z3,z5,z177,z181]),(1,[z0,z1,z4,z5,z730])],[(0,[z49,z0,z3,z88,z5,z23]),(0,[z0,z1,z3,z99,z731,z6])],[(0,[z0,z3,z4,z5,z732,z6]),(0,[z317,z1,z3,z4,z318,z6]),(0,[z733,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z734,z6])],[(0,[z0,z1,z4,z5,z735,z6]),(0,[z0,z3,z4,z5,z189,z104]),(0,[z736,z1,z3,z4,z5,z6])]],
   [[(0,[z1,z3,z4,z5,z9,z737]),(0,[z0,z1,z30,z4,z738,z6])],[(0,[z0,z1,z739,z4,z5,z6]),(0,[z0,z1,z10,z4,z85,z6]),(0,[z0,z1,z3,z4,z5,z460])],[(0,[z0,z1,z3,z4,z740,z6]),(0,[z0,z1,z3,z4,z5,z741]),(0,[z0,z1,z3,z4,z742,z6])],[(0,[z1,z3,z4,z5,z737,z185]),(0,[z0,z1,z3,z4,z743,z6]),(0,[z0,z180,z1,z10,z5,z6])],[(0,[z0,z1,z3,z4,z744,z6]),(0,[z0,z1,z3,z4,z5,z745]),(0,[z746,z0,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z747,z6]),(0,[z237,z54,z1,z4,z5,z6]),(0,[z0,z1,z274,z3,z124,z6]),(0,[z0,z1,z748,z80,z5,z6]),(0,[z14,z0,z1,z4,z506,z6]),(0,[z0,z27,z1,z4,z5,z105])],[(0,[z0,z1,z3,z4,z5,z749]),(0,[z165,z1,z3,z710,z5,z6]),(0,[z0,z1,z3,z158,z99,z6])],[(0,[z0,z1,z653,z206,z3,z4]),(0,[z0,z750,z3,z4,z5,z6]),(0,[z0,z79,z707,z4,z5,z6]),(0,[z0,z751,z1,z3,z4,z5])]],
   [[(0,[z0,z1,z3,z752,z5,z6]),(0,[z0,z1,z3,z4,z5,z200]),(0,[z0,z1,z3,z606,z99,z6]),(0,[z0,z1,z3,z753,z5,z6])],[(0,[z0,z1,z3,z4,z5,z754]),(0,[z83,z1,z4,z51,z52,z6]),(0,[z0,z448,z1,z3,z5,z6]),(0,[z0,z3,z299,z5,z346,z6])],[(0,[z0,z1,z3,z4,z755,z6]),(0,[z0,z1,z3,z4,z756,z6]),(0,[z237,z0,z1,z4,z182,z6]),(0,[z0,z1,z3,z4,z757,z6]),(0,[z0,z1,z758,z3,z4,z5]),(0,[z14,z276,z0,z1,z4,z6])],[(0,[z0,z1,z3,z4,z759,z5]),(0,[z0,z1,z3,z4,z5,z760]),(0,[z22,z1,z3,z4,z5,z737]),(0,[z0,z1,z30,z4,z134,z6])],[(0,[z0,z1,z3,z4,z761,z6]),(0,[z0,z1,z3,z4,z762,z6]),(0,[z0,z1,z3,z173,z115,z6]),(0,[z0,z1,z763,z4,z5,z6])],[(0,[z0,z1,z3,z4,z764,z6]),(0,[z0,z1,z3,z765,z5,z6]),(0,[z766,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z767,z6]),(0,[z0,z1,z3,z4,z5,z768])],[(0,[z148,z146,z1,z3,z4,z6]),(0,[z146,z42,z1,z3,z4,z6]),(0,[z0,z1,z769,z4,z5,z6]),(0,[z0,z1,z621,z3,z5,z36]),(0,[z0,z1,z3,z770,z5,z6])],[(0,[z75,z215,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z771]),(0,[z0,z1,z772,z4,z5,z6]),(0,[z16,z0,z3,z5,z104,z36])]],
   [[(0,[z118,z1,z206,z119,z4,z6]),(0,[z0,z1,z3,z4,z5,z773]),(0,[z0,z1,z3,z5,z6,z774])],[(0,[z466,z1,z119,z4,z5,z6]),(0,[z775,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z776])],[(0,[z0,z1,z777,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z778]),(0,[z0,z180,z1,z80,z5,z6])],[(0,[z0,z1,z316,z4,z168,z6]),(0,[z0,z180,z1,z748,z5,z6]),(0,[z0,z1,z3,z4,z779,z6]),(0,[z0,z1,z3,z158,z731,z6])],[(0,[z0,z1,z780,z3,z4,z6]),(0,[z511,z215,z3,z4,z5,z6]),(0,[z1,z781,z119,z4,z5,z6]),(1,[z1,z3,z4,z5,z737]),(0,[z59,z0,z212,z60,z4,z6]),(0,[z0,z1,z30,z391,z4,z6]),(0,[z14,z0,z1,z4,z738,z6])],[(0,[z0,z1,z3,z4,z5,z782]),(0,[z237,z0,z1,z4,z5,z6]),(0,[z475,z1,z3,z4,z43,z6])],[(0,[z118,z1,z119,z4,z57,z6]),(1,[z1,z781,z4,z5,z6]),(0,[z0,z1,z653,z3,z4,z5]),(0,[z0,z1,z13,z175,z324,z6])],[(0,[z0,z1,z3,z4,z5,z783]),(0,[z633,z1,z3,z128,z5,z6]),(0,[z0,z273,z1,z4,z5,z105]),(0,[z0,z1,z784,z4,z5,z6]),(0,[z785,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z786,z6])]],
   [[(0,[z237,z83,z0,z1,z4,z6]),(0,[z0,z1,z17,z4,z85,z6])],[(0,[z0,z42,z3,z4,z559,z6]),(0,[z152,z1,z3,z4,z43,z6]),(0,[z0,z1,z316,z377,z5,z6]),(0,[z8,z1,z316,z4,z5,z185]),(0,[z0,z1,z13,z205,z5,z6])],[(0,[z0,z1,z3,z4,z5,z787]),(0,[z0,z1,z3,z4,z788,z6]),(0,[z0,z789,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z719])],[(0,[z0,z1,z790,z4,z5,z6]),(0,[z0,z1,z3,z88,z5,z189]),(0,[z0,z791,z3,z4,z5,z6])],[(0,[z0,z1,z792,z3,z4,z6])],[(0,[z16,z0,z3,z28,z5,z6]),(0,[z0,z1,z793,z4,z5,z6])],[(0,[z794,z1,z3,z4,z5,z6]),(0,[z0,z1,z795,z4,z5,z6]),(0,[z240,z0,z3,z4,z5,z104]),(0,[z0,z3,z4,z5,z279,z177]),(0,[z0,z1,z161,z3,z124,z6])],[(0,[z0,z1,z334,z4,z51,z5]),(0,[z317,z1,z17,z4,z5,z6]),(0,[z0,z1,z176,z4,z5,z730])]],
   [[(0,[z0,z361,z3,z4,z5,z104]),(0,[z280,z50,z3,z4,z477,z6]),(0,[z0,z1,z796,z3,z5,z6]),(0,[z389,z1,z3,z4,z318,z6]),(0,[z29,z0,z3,z681,z4,z6]),(0,[z0,z1,z797,z3,z4,z6]),(0,[z0,z1,z3,z4,z798,z6])],[(0,[z50,z799,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z800]),(0,[z801,z1,z3,z4,z5,z6]),(0,[z802,z1,z3,z4,z5,z6]),(1,[z0,z3,z720,z5,z6])],[(0,[z237,z0,z1,z4,z124,z6]),(0,[z622,z1,z3,z4,z52,z6]),(0,[z803,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z63,z6]),(0,[z0,z1,z3,z4,z5,z709])],[(0,[z0,z1,z3,z4,z804,z6]),(1,[z1,z3,z4,z725,z6]),(0,[z22,z1,z3,z4,z5,z9]),(0,[z8,z1,z3,z4,z5,z455])],[(0,[z193,z148,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z805,z6]),(0,[z165,z1,z3,z81,z5,z200]),(0,[z0,z1,z3,z4,z806,z6]),(0,[z1,z3,z807,z4,z5,z6])],[(0,[z0,z1,z808,z4,z5,z6]),(0,[z54,z146,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z809]),(0,[z0,z1,z810,z3,z4,z5])],[(0,[z0,z1,z3,z811,z5,z6])],[(0,[z0,z1,z236,z3,z5,z36]),(0,[z0,z1,z3,z812,z5,z6]),(0,[z0,z813,z3,z4,z5,z6]),(0,[z0,z1,z3,z689,z5,z72])]],
   [[(0,[z118,z0,z148,z1,z4,z6])],[(0,[z0,z1,z187,z4,z168,z6]),(0,[z0,z1,z3,z814,z5,z6]),(0,[z49,z0,z3,z4,z5,z23])],[(0,[z0,z1,z3,z4,z5,z815]),(0,[z1,z3,z710,z4,z5,z6]),(0,[z0,z1,z3,z5,z200,z36]),(0,[z8,z1,z3,z173,z5,z185]),(0,[z16,z0,z3,z28,z5,z112])],[(0,[z0,z1,z816,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z737]),(0,[z0,z1,z3,z4,z817,z5]),(0,[z0,z3,z88,z5,z6,z104]),(0,[z0,z1,z4,z5,z524,z105])],[(0,[z194,z1,z3,z128,z5,z6]),(0,[z0,z1,z3,z4,z818,z6]),(0,[z0,z819,z3,z4,z5,z6]),(0,[z240,z0,z3,z71,z5,z6])],[(0,[z0,z1,z3,z4,z5,z100]),(0,[z0,z1,z820,z3,z5,z6]),(0,[z0,z1,z3,z4,z821,z6]),(0,[z0,z1,z3,z4,z104,z295])],[(0,[z0,z1,z176,z4,z63,z6])],[(0,[z0,z1,z187,z377,z5,z6]),(0,[z8,z1,z187,z4,z5,z185])]],
   [[(0,[z0,z1,z316,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z822]),(0,[z0,z823,z3,z4,z5,z6]),(0,[z0,z824,z3,z4,z5,z6]),(0,[z317,z1,z3,z4,z85,z6]),(0,[z0,z1,z3,z4,z825,z6]),(0,[z826,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z709])],[(0,[z751,z146,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z827]),(0,[z0,z828,z3,z4,z5,z6]),(0,[z0,z3,z71,z5,z72,z279])],[(0,[z0,z1,z3,z4,z5,z829]),(0,[z29,z0,z3,z4,z360,z6]),(0,[z237,z0,z1,z4,z15,z6]),(0,[z59,z0,z60,z4,z5,z6]),(0,[z0,z830,z1,z3,z4,z5])],[(0,[z0,z3,z4,z5,z831,z6])],[(0,[z0,z1,z3,z4,z832,z6]),(0,[z833,z1,z3,z4,z5,z6]),(0,[z29,z0,z3,z4,z757,z6])],[],[(0,[z0,z1,z834,z3,z4,z6]),(0,[z0,z1,z316,z4,z5,z23]),(0,[z0,z1,z3,z88,z5,z72])]],
   [[(0,[z0,z1,z835,z3,z4,z6]),(0,[z0,z1,z3,z4,z115,z23]),(0,[z0,z448,z1,z10,z5,z6]),(1,[z0,z1,z4,z738,z6]),(0,[z0,z1,z3,z71,z5,z72])],[(0,[z0,z836,z3,z4,z5,z6]),(0,[z0,z837,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z220]),(0,[z0,z1,z3,z4,z838,z6]),(0,[z0,z1,z839,z3,z4,z5]),(0,[z101,z1,z3,z4,z43,z6]),(0,[z0,z341,z3,z4,z168,z6]),(0,[z0,z1,z3,z465,z99,z6])],[(0,[z0,z552,z3,z4,z5,z104])],[(0,[z0,z1,z3,z4,z840,z6]),(0,[z127,z1,z3,z710,z5,z6]),(0,[z83,z1,z334,z3,z4,z52]),(0,[z83,z1,z3,z4,z288,z52]),(0,[z1,z3,z4,z5,z6,z841])],[(0,[z0,z1,z3,z4,z842,z6]),(0,[z0,z12,z3,z720,z5,z6]),(0,[z0,z3,z4,z5,z843,z6])],[(0,[z0,z1,z316,z4,z115,z6]),(0,[z844,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z318,z112]),(0,[z0,z1,z4,z5,z104,z91]),(0,[z146,z1,z3,z4,z15,z6]),(0,[z0,z1,z4,z5,z738,z6])],[(0,[z1,z3,z4,z43,z725,z6]),(0,[z0,z1,z3,z4,z845,z6])]],
   [[(0,[z0,z341,z3,z377,z5,z6]),(0,[z8,z341,z3,z4,z5,z185]),(0,[z59,z0,z522,z60,z5,z6]),(0,[z0,z1,z3,z4,z6,z846]),(0,[z0,z3,z4,z5,z23,z847])],[(0,[z0,z848,z1,z3,z5,z6]),(0,[z0,z1,z4,z849,z5,z6]),(0,[z0,z850,z3,z4,z5,z6]),(0,[z0,z1,z781,z4,z5,z6]),(0,[z0,z1,z3,z173,z5,z6]),(0,[z0,z851,z3,z4,z5,z6]),(0,[z0,z1,z852,z4,z5,z6]),(0,[z389,z1,z17,z4,z5,z6]),(0,[z16,z0,z3,z28,z5,z189])],[(0,[z0,z1,z3,z4,z5,z853]),(0,[z0,z1,z3,z720,z5,z6])],[(0,[z0,z854,z3,z4,z5,z6]),(0,[z83,z1,z3,z4,z52,z6]),(0,[z0,z1,z855,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z856])],[(0,[z22,z1,z3,z4,z159,z5]),(0,[z0,z352,z3,z4,z18,z6]),(0,[z0,z1,z3,z4,z5,z857]),(0,[z858,z1,z3,z4,z5,z6]),(0,[z859,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z860,z6]),(0,[z165,z1,z3,z255,z5,z6])],[(0,[z0,z1,z3,z4,z861,z6]),(0,[z0,z1,z187,z4,z5,z6]),(0,[z0,z1,z3,z862,z5,z6]),(0,[z22,z1,z77,z3,z4,z5]),(0,[z0,z1,z3,z731,z124,z6])],[(0,[z33,z215,z3,z4,z5,z6]),(0,[z0,z448,z1,z80,z5,z6]),(0,[z0,z1,z3,z4,z5,z189]),(0,[z0,z3,z720,z28,z5,z6])]],
   [[(0,[z0,z1,z3,z863,z5,z6]),(0,[z0,z1,z3,z4,z5,z864]),(0,[z0,z1,z3,z173,z5,z23]),(0,[z0,z1,z3,z4,z5,z865]),(0,[z0,z1,z4,z738,z182,z6])],[(0,[z0,z1,z3,z4,z5,z866]),(0,[z0,z1,z3,z5,z867,z6]),(0,[z0,z1,z3,z4,z5,z868]),(0,[z49,z0,z3,z5,z23,z181])],[(0,[z118,z273,z1,z119,z4,z5]),(0,[z0,z1,z3,z869,z5,z6]),(0,[z127,z1,z3,z128,z5,z6]),(1,[z0,z3,z4,z5,z847])],[(0,[z0,z870,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z871]),(0,[z317,z1,z10,z4,z5,z6])],[(0,[z0,z27,z1,z316,z4,z5]),(0,[z0,z1,z3,z377,z5,z72]),(0,[z0,z1,z3,z4,z5,z204]),(0,[z317,z3,z4,z5,z6,z104])],[],[(0,[z54,z1,z283,z4,z5,z6]),(0,[z0,z1,z3,z4,z211,z6]),(0,[z0,z1,z872,z4,z5,z6]),(0,[z0,z1,z316,z173,z5,z6]),(0,[z0,z1,z212,z3,z4,z6]),(0,[z0,z448,z1,z3,z5,z809]),(1,[z0,z1,z748,z5,z6]),(0,[z14,z0,z1,z4,z697,z6]),(0,[z0,z1,z3,z4,z873,z6])],[(0,[z0,z799,z3,z4,z5,z6]),(0,[z0,z1,z3,z874,z5,z6]),(0,[z0,z1,z3,z4,z738,z6]),(0,[z0,z1,z4,z5,z177,z730])]],
   [[(0,[z0,z1,z875,z3,z4,z6])],[(0,[z0,z1,z876,z4,z5,z6]),(0,[z1,z3,z119,z4,z57,z6]),(0,[z0,z1,z3,z4,z5,z877]),(0,[z0,z1,z3,z4,z5,z878]),(1,[z0,z1,z3,z5,z709])],[(0,[z33,z799,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z879]),(0,[z0,z1,z4,z5,z6,z880]),(0,[z0,z1,z17,z4,z5,z6]),(0,[z389,z1,z3,z4,z85,z6])],[(0,[z881,z0,z3,z4,z5,z6]),(0,[z0,z1,z882,z4,z5,z6]),(0,[z0,z1,z3,z4,z883,z6]),(0,[z0,z1,z4,z5,z884,z6])],[(0,[z0,z1,z3,z885,z5,z6]),(0,[z507,z1,z283,z4,z5,z6]),(0,[z0,z1,z187,z4,z115,z6])],[(0,[z118,z1,z119,z4,z26,z6]),(0,[z0,z3,z4,z757,z18,z6]),(0,[z886,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z887,z5,z6]),(0,[z0,z1,z3,z4,z5,z888]),(0,[z0,z1,z636,z4,z134,z6]),(0,[z22,z0,z3,z4,z5,z279]),(0,[z0,z1,z889,z4,z5,z6]),(0,[z0,z1,z3,z890,z5,z6]),(0,[z0,z1,z463,z4,z5,z177])],[(0,[z0,z341,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z891,z6]),(0,[z0,z1,z3,z4,z5,z892]),(0,[z0,z893,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z894,z3,z4,z5]),(0,[z0,z1,z895,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z896]),(0,[z146,z1,z3,z4,z182,z6])],[(0,[z0,z1,z3,z4,z15,z504]),(0,[z0,z1,z13,z526,z5,z6]),(0,[z14,z146,z1,z4,z182,z6]),(0,[z0,z1,z3,z897,z5,z6])],[(0,[z0,z1,z898,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z899]),(0,[z0,z1,z3,z4,z6,z900])],[(0,[z0,z1,z3,z4,z6,z901]),(0,[z0,z1,z3,z4,z5,z902])],[(0,[z59,z0,z60,z4,z5,z204])],[(0,[z0,z1,z3,z903,z5,z6]),(0,[z0,z1,z904,z4,z5,z6]),(0,[z118,z1,z119,z4,z5,z6]),(0,[z0,z3,z4,z5,z905,z6])],[(0,[z14,z0,z1,z4,z57,z6]),(0,[z0,z273,z1,z316,z4,z5]),(0,[z0,z341,z3,z4,z5,z23]),(0,[z0,z190,z79,z4,z5,z6]),(0,[z0,z1,z3,z4,z719,z163])],[(0,[z0,z1,z3,z4,z906,z6]),(0,[z0,z461,z3,z377,z5,z6]),(0,[z0,z1,z17,z4,z5,z112])]],
   [[(0,[z0,z1,z3,z907,z5,z6]),(0,[z127,z1,z3,z128,z145,z6])],[(0,[z0,z1,z334,z3,z4,z115])],[(0,[z0,z1,z3,z4,z908,z6]),(0,[z0,z3,z4,z5,z847,z6]),(0,[z0,z1,z13,z175,z5,z6])],[(0,[z146,z1,z3,z4,z5,z6]),(0,[z8,z0,z1,z3,z5,z181]),(0,[z0,z1,z3,z4,z5,z909])],[(0,[z38,z50,z3,z4,z5,z6]),(0,[z0,z1,z187,z173,z5,z6]),(0,[z0,z1,z3,z198,z124,z6]),(0,[z0,z1,z3,z5,z731,z6])],[(0,[z0,z341,z3,z4,z115,z6]),(0,[z0,z1,z3,z748,z5,z6])],[(0,[z0,z1,z3,z4,z5,z910]),(0,[z0,z3,z299,z720,z5,z6])],[(0,[z0,z1,z3,z4,z911,z6]),(0,[z0,z1,z3,z4,z5,z912]),(0,[z0,z913,z1,z3,z4,z5]),(0,[z0,z3,z4,z5,z279,z6]),(0,[z240,z0,z3,z5,z6,z36])]],
   [[(0,[z0,z1,z3,z4,z272,z6])],[(0,[z0,z1,z3,z4,z5,z914]),(0,[z0,z915,z3,z4,z5,z6]),(0,[z0,z1,z238,z3,z4,z115]),(0,[z0,z1,z916,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z245])],[(0,[z0,z1,z4,z748,z5,z6]),(0,[z917,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z918,z5,z6]),(0,[z0,z919,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z920])],[(0,[z118,z148,z1,z119,z4,z6]),(0,[z0,z1,z4,z5,z6,z921]),(0,[z146,z1,z4,z5,z6,z105])],[(0,[z118,z1,z653,z119,z4,z5]),(0,[z389,z1,z10,z4,z5,z6])],[(1,[z1,z3,z710,z5,z6]),(0,[z16,z0,z3,z28,z318,z6])],[(0,[z0,z1,z3,z4,z922,z6]),(0,[z59,z0,z448,z60,z5,z6]),(0,[z0,z42,z3,z4,z18,z460]),(0,[z146,z1,z176,z4,z5,z6]),(0,[z0,z1,z154,z4,z15,z6])]],
   [[(0,[z54,z1,z781,z4,z5,z6]),(0,[z22,z1,z3,z4,z5,z382]),(0,[z1,z3,z4,z5,z6,z923]),(0,[z146,z1,z3,z4,z124,z6])],[(0,[z0,z1,z924,z3,z5,z6]),(0,[z8,z270,z1,z3,z4,z5])],[(0,[z280,z50,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z115,z104]),(0,[z925,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z6,z926])],[(0,[z0,z1,z3,z4,z5,z927]),(0,[z237,z0,z1,z4,z6,z163]),(0,[z0,z1,z3,z4,z318,z6])],[(0,[z0,z1,z3,z928,z5,z6]),(0,[z127,z1,z3,z128,z211,z6]),(0,[z0,z341,z3,z173,z5,z6]),(0,[z0,z1,z3,z4,z5,z929])],[(0,[z0,z1,z206,z3,z4,z6]),(0,[z0,z1,z930,z3,z4,z6]),(0,[z0,z1,z17,z4,z5,z189]),(0,[z931,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z62])],[(0,[z0,z1,z3,z4,z932,z6]),(1,[z0,z707,z4,z5,z6]),(0,[z0,z1,z3,z5,z105,z181])]],
   [[(0,[z0,z461,z3,z4,z5,z36]),(0,[z16,z0,z10,z28,z5,z6]),(0,[z0,z1,z3,z4,z933,z6])],[(0,[z934,z1,z3,z4,z5,z6])],[(0,[z0,z1,z935,z3,z4,z5]),(0,[z0,z1,z936,z4,z5,z6]),(0,[z0,z1,z3,z4,z937,z6]),(0,[z317,z1,z3,z5,z6,z36]),(0,[z938,z1,z3,z4,z5,z6])],[(0,[z232,z1,z3,z4,z52,z6]),(0,[z0,z1,z3,z939,z5,z6])],[(0,[z280,z50,z3,z4,z5,z100]),(0,[z0,z1,z940,z4,z5,z6]),(0,[z49,z0,z3,z4,z5,z220]),(0,[z0,z941,z1,z3,z4,z6]),(0,[z237,z83,z1,z4,z52,z6]),(0,[z0,z1,z86,z3,z5,z36]),(0,[z0,z1,z238,z3,z4,z719])],[(0,[z0,z1,z3,z5,z6,z942])],[(0,[z0,z1,z10,z4,z5,z6]),(0,[z0,z1,z3,z4,z943,z6])],[(0,[z944,z0,z1,z4,z5,z6]),(0,[z178,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z945]),(0,[z146,z1,z3,z4,z6,z163]),(0,[z0,z1,z4,z5,z730,z105])]],
   [[(0,[z0,z1,z3,z4,z946,z6]),(0,[z193,z1,z3,z394,z4,z6]),(0,[z0,z1,z3,z4,z5,z947]),(0,[z0,z1,z3,z4,z6,z295])],[(0,[z0,z1,z3,z4,z948,z6]),(0,[z0,z1,z949,z3,z4,z6]),(0,[z0,z1,z3,z950,z5,z6]),(0,[z14,z0,z1,z4,z6,z183])],[(0,[z237,z29,z0,z1,z4,z6]),(0,[z0,z1,z3,z4,z5,z737]),(0,[z0,z1,z4,z951,z5,z6]),(0,[z0,z1,z3,z4,z5,z952]),(0,[z317,z1,z3,z71,z5,z6])],[(0,[z0,z1,z953,z4,z5,z6]),(0,[z148,z1,z3,z4,z52,z6]),(0,[z0,z1,z3,z4,z954,z6]),(0,[z0,z1,z3,z4,z5,z107]),(0,[z955,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z956,z6]),(0,[z0,z1,z957,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z958])],[(0,[z0,z1,z3,z4,z6,z959]),(0,[z16,z0,z3,z307,z5,z6]),(0,[z29,z0,z3,z4,z37,z6])],[(0,[z0,z1,z960,z4,z5,z6]),(0,[z0,z1,z961,z4,z5,z6]),(0,[z83,z1,z3,z4,z725,z6]),(0,[z0,z962,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z963,z6]),(0,[z0,z219,z1,z4,z5,z105])]],
   [[(0,[z0,z1,z3,z4,z5,z964]),(0,[z54,z1,z4,z134,z52,z6]),(0,[z0,z1,z3,z377,z5,z36]),(0,[z0,z448,z155,z1,z3,z6]),(0,[z16,z0,z1,z3,z5,z107])],[(0,[z0,z1,z3,z4,z965,z6]),(0,[z0,z1,z3,z4,z5,z966]),(0,[z49,z0,z3,z4,z5,z189]),(0,[z14,z0,z1,z692,z4,z6])],[(0,[z0,z1,z3,z4,z5,z967]),(0,[z0,z1,z3,z4,z5,z968]),(0,[z0,z1,z969,z4,z5,z6]),(0,[z0,z1,z3,z4,z970,z6]),(0,[z0,z150,z3,z4,z5,z104])],[(0,[z0,z1,z3,z5,z6,z971]),(0,[z0,z148,z1,z176,z4,z6]),(0,[z0,z1,z10,z4,z5,z112])],[(0,[z0,z1,z3,z4,z5,z972]),(0,[z0,z1,z973,z4,z5,z6]),(0,[z237,z0,z1,z334,z4,z5]),(0,[z0,z1,z4,z288,z51,z5]),(0,[z0,z1,z3,z4,z5,z974]),(0,[z0,z1,z975,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z250]),(0,[z0,z1,z3,z4,z39,z163])],[(0,[z0,z1,z3,z4,z976,z5])],[(0,[z0,z1,z3,z4,z477,z6]),(0,[z0,z977,z1,z4,z5,z6]),(0,[z978,z0,z1,z3,z4,z6]),(0,[z0,z65,z79,z4,z5,z6])],[(0,[z0,z1,z3,z4,z979,z6]),(0,[z0,z148,z1,z4,z6,z105]),(0,[z237,z0,z1,z4,z134,z6]),(0,[z16,z0,z17,z28,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z288,z5]),(0,[z0,z1,z3,z4,z980,z6]),(0,[z0,z1,z3,z4,z5,z981]),(0,[z0,z1,z982,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z181]),(0,[z983,z0,z1,z3,z5,z6]),(0,[z0,z1,z984,z4,z5,z6])],[(0,[z0,z985,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z725,z6]),(0,[z986,z1,z3,z4,z5,z6]),(0,[z0,z42,z3,z4,z18,z6]),(0,[z0,z150,z3,z4,z5,z847]),(0,[z0,z1,z4,z5,z6,z91])],[(0,[z0,z1,z3,z4,z987,z6]),(0,[z0,z1,z176,z368,z4,z5]),(0,[z59,z0,z155,z60,z4,z6]),(0,[z0,z3,z4,z720,z5,z6])],[(0,[z0,z1,z3,z4,z5,z988]),(0,[z0,z1,z3,z4,z989,z6]),(0,[z0,z1,z990,z4,z5,z6])],[(0,[z0,z1,z3,z991,z5,z6]),(0,[z118,z146,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z324,z6]),(0,[z0,z1,z154,z4,z5,z6])],[],[(0,[z0,z1,z261,z3,z124,z6])],[(0,[z0,z1,z992,z4,z5,z6]),(0,[z0,z1,z3,z4,z993,z6]),(0,[z0,z1,z3,z4,z5,z994]),(0,[z0,z1,z3,z4,z5,z995])]],
   [[(0,[z0,z1,z3,z4,z318,z189])],[(0,[z799,z215,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z57,z6]),(0,[z54,z1,z7,z4,z5,z6]),(0,[z0,z1,z334,z3,z4,z163]),(0,[z0,z1,z3,z522,z5,z6]),(0,[z14,z0,z1,z4,z251,z6])],[(0,[z1,z799,z3,z4,z5,z6]),(0,[z240,z0,z3,z4,z5,z6]),(0,[z146,z1,z3,z4,z134,z6]),(0,[z14,z0,z1,z4,z182,z6])],[(0,[z996,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z997]),(0,[z0,z180,z1,z80,z5,z245])],[(0,[z0,z998,z3,z4,z5,z6]),(0,[z0,z461,z3,z4,z168,z6]),(0,[z0,z1,z3,z4,z999,z6])],[(0,[z0,z1,z4,z134,z738,z6])],[(0,[z0,z1000,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1001]),(0,[z0,z1,z3,z4,z1002,z6]),(0,[z1003,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z709,z36])]],
   [[(0,[z0,z1,z3,z4,z1004,z6]),(0,[z0,z1,z3,z4,z5,z1005]),(0,[z0,z448,z1,z212,z3,z6]),(0,[z16,z0,z3,z28,z85,z6]),(0,[z0,z3,z4,z5,z279,z105]),(0,[z0,z1,z3,z4,z1006,z6])],[(0,[z0,z1,z3,z1007,z5,z6]),(0,[z0,z1,z3,z4,z5,z1008]),(0,[z0,z1,z3,z4,z52,z62]),(0,[z440,z0,z3,z4,z5,z23]),(0,[z240,z0,z3,z4,z5,z23])],[(0,[z237,z0,z1,z4,z99,z6]),(0,[z8,z461,z3,z4,z5,z185]),(0,[z0,z1,z10,z4,z5,z189])],[(0,[z193,z14,z54,z1,z4,z6]),(0,[z0,z1,z176,z4,z5,z327]),(0,[z0,z1,z17,z4,z318,z6])],[(0,[z0,z1,z3,z4,z5,z216]),(0,[z1009,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1010,z6]),(0,[z0,z1,z3,z4,z1011,z6]),(0,[z0,z3,z4,z757,z5,z6]),(0,[z0,z1,z3,z4,z1012,z6]),(0,[z0,z1,z176,z4,z5,z435])],[(0,[z0,z1,z3,z4,z6,z1013]),(0,[z0,z1,z3,z4,z85,z6]),(1,[z0,z3,z4,z757,z6])],[(0,[z0,z1,z1014,z3,z4,z5]),(0,[z0,z341,z316,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z1015,z6]),(0,[z0,z3,z4,z5,z200,z831]),(0,[z22,z0,z1,z3,z5,z181]),(0,[z0,z1,z3,z4,z5,z1016])],[(0,[z0,z1,z1017,z4,z5,z6]),(0,[z0,z1018,z1,z4,z5,z6]),(0,[z0,z1,z585,z3,z4,z163]),(0,[z0,z1019,z3,z4,z5,z6]),(1,[z0,z1,z3,z731,z6])],[(0,[z0,z1,z3,z4,z1020,z6]),(0,[z1021,z0,z3,z4,z5,z6]),(0,[z0,z155,z1,z3,z522,z6]),(0,[z0,z1,z1022,z3,z4,z6]),(0,[z1023,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z134,z6,z566])],[(0,[z0,z148,z1,z653,z3,z4]),(0,[z16,z389,z3,z28,z5,z6]),(0,[z0,z42,z556,z3,z4,z6]),(0,[z0,z1,z3,z4,z125,z6]),(0,[z0,z1,z3,z4,z5,z1024])],[(0,[z0,z273,z1,z176,z4,z5]),(0,[z0,z1,z3,z377,z168,z6]),(0,[z8,z1,z3,z4,z168,z185])],[(0,[z317,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1025,z6]),(0,[z49,z0,z3,z4,z5,z847])],[(0,[z0,z1,z3,z4,z5,z1026]),(0,[z54,z1,z4,z247,z5,z6]),(0,[z0,z1,z3,z4,z1027,z6]),(0,[z0,z1,z334,z3,z4,z15]),(0,[z0,z1,z3,z4,z5,z1028]),(0,[z0,z1,z3,z4,z5,z847])],[(0,[z0,z1,z3,z4,z1029,z6]),(0,[z0,z1,z3,z4,z5,z1030]),(0,[z338,z1,z3,z4,z43,z6]),(0,[z0,z1,z176,z316,z4,z5]),(0,[z708,z146,z1,z3,z4,z5]),(0,[z240,z0,z3,z71,z5,z72])]],
   [[(0,[z0,z1,z1031,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z1032]),(0,[z16,z317,z3,z28,z5,z6]),(0,[z0,z1,z117,z3,z5,z36])],[(0,[z0,z341,z3,z4,z5,z220]),(0,[z1033,z1,z3,z4,z5,z6])],[(0,[z0,z1,z4,z5,z6,z1034]),(0,[z8,z1,z3,z377,z5,z185])],[(0,[z276,z1,z3,z4,z52,z6]),(0,[z0,z1,z316,z4,z5,z72]),(0,[z0,z1,z3,z4,z85,z112])],[(0,[z0,z1,z3,z5,z220,z971]),(0,[z0,z1,z316,z4,z5,z104]),(0,[z0,z1,z3,z88,z5,z6])],[(0,[z0,z1,z3,z4,z1035,z6]),(0,[z0,z1,z3,z4,z1036,z6]),(0,[z49,z317,z3,z4,z5,z6]),(0,[z0,z12,z3,z299,z5,z6]),(0,[z0,z180,z1,z80,z5,z107]),(0,[z1037,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z1038,z4,z6]),(0,[z0,z1,z1039,z3,z4,z6]),(0,[z82,z0,z3,z4,z37,z6]),(0,[z0,z1,z3,z88,z5,z36])],[(0,[z0,z1,z3,z4,z1040,z6]),(0,[z0,z1,z4,z5,z6,z1041]),(0,[z29,z146,z1,z3,z4,z6]),(0,[z0,z706,z3,z4,z5,z23])]],
   [[(0,[z1042,z0,z3,z4,z5,z6]),(0,[z193,z1,z3,z4,z43,z6]),(0,[z0,z1,z3,z4,z1043,z6])],[(0,[z0,z461,z3,z4,z5,z6]),(0,[z54,z0,z148,z1,z4,z6]),(0,[z0,z1,z3,z4,z43,z62]),(0,[z0,z1,z3,z4,z1044,z6])],[(0,[z317,z1,z3,z4,z5,z112]),(0,[z0,z12,z3,z629,z5,z6]),(0,[z0,z1,z457,z4,z5,z177])],[(0,[z0,z1,z3,z4,z5,z1045]),(0,[z0,z1,z3,z4,z1046,z6])],[(0,[z0,z1,z3,z4,z1047,z6]),(0,[z0,z65,z707,z4,z5,z6]),(0,[z0,z27,z1,z4,z5,z730])],[(0,[z0,z1,z3,z4,z5,z1048]),(0,[z0,z341,z187,z4,z5,z6]),(0,[z59,z0,z707,z4,z5,z6]),(0,[z0,z1,z212,z3,z522,z6]),(0,[z0,z1,z3,z4,z731,z6])],[(0,[z0,z1,z3,z4,z5,z1049]),(0,[z0,z1,z3,z4,z15,z115]),(0,[z240,z0,z3,z4,z5,z189])],[(0,[z237,z0,z42,z1,z4,z6]),(0,[z1050,z0,z1,z4,z5,z6]),(0,[z0,z1,z1051,z3,z4,z5])]],
   [[(0,[z0,z1,z3,z4,z5,z1052]),(0,[z193,z1,z3,z4,z564,z6]),(0,[z165,z1,z3,z81,z5,z216]),(0,[z1053,z1,z3,z4,z5,z6])],[(0,[z1,z3,z395,z4,z52,z6])],[(0,[z1054,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z168,z6])],[(0,[z0,z1,z3,z4,z5,z1055]),(0,[z0,z1,z3,z4,z5,z1056]),(0,[z0,z1,z3,z4,z1057,z6])],[(0,[z0,z1,z3,z1058,z5,z6]),(0,[z237,z0,z1,z4,z288,z5]),(0,[z0,z1,z3,z173,z5,z104]),(0,[z0,z1,z4,z5,z23,z91]),(0,[z0,z1,z3,z4,z1059,z6])],[(0,[z0,z1,z3,z1060,z5,z6]),(0,[z193,z237,z0,z1,z4,z6]),(0,[z0,z461,z316,z4,z5,z6]),(0,[z8,z1,z3,z4,z5,z737])],[(0,[z1,z283,z781,z4,z5,z6]),(0,[z0,z461,z3,z4,z115,z6]),(0,[z0,z448,z1,z13,z5,z6]),(0,[z0,z1,z30,z3,z4,z62]),(0,[z1,z3,z4,z1061,z5,z6])]],
   [[(0,[z0,z1,z3,z1062,z5,z6]),(0,[z54,z1,z3,z4,z57,z6]),(0,[z0,z42,z3,z4,z757,z6])],[(0,[z0,z1,z3,z377,z5,z6]),(0,[z14,z0,z1,z395,z4,z6]),(0,[z8,z1,z3,z4,z5,z185])],[(0,[z0,z1,z3,z4,z85,z189])],[(0,[z0,z1,z1063,z3,z4,z5]),(0,[z1064,z1,z3,z4,z5,z6])],[(0,[z280,z50,z3,z4,z5,z220]),(0,[z0,z1,z1065,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1066]),(0,[z0,z1,z1067,z4,z5,z6]),(0,[z8,z1,z690,z3,z4,z5])],[(0,[z0,z1,z3,z1068,z5,z6]),(0,[z237,z0,z1,z4,z57,z6]),(0,[z83,z146,z1,z3,z4,z6]),(0,[z8,z0,z3,z4,z5,z279]),(0,[z0,z12,z1,z3,z5,z107]),(0,[z0,z3,z4,z37,z757,z6])],[(0,[z389,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z1069,z5,z6]),(0,[z0,z1,z3,z928,z5,z220]),(0,[z1,z3,z4,z725,z5,z6]),(0,[z0,z1,z3,z1070,z5,z6]),(0,[z0,z1,z10,z4,z318,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z730])],[(0,[z0,z1,z3,z4,z1071,z6]),(0,[z0,z1,z3,z4,z5,z1072]),(0,[z317,z1,z3,z4,z5,z189])],[(0,[z0,z148,z1,z3,z4,z6]),(0,[z0,z1,z3,z1073,z5,z6]),(0,[z0,z1,z3,z4,z5,z728])],[(0,[z0,z1,z3,z4,z5,z1074]),(0,[z0,z1,z334,z3,z4,z5]),(0,[z0,z1075,z1,z4,z5,z6])],[(0,[z628,z1,z3,z81,z5,z6]),(0,[z237,z146,z1,z4,z5,z6])],[],[(0,[z280,z799,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1076]),(0,[z0,z1,z3,z4,z1077,z6]),(0,[z0,z1,z13,z10,z5,z6]),(0,[z16,z0,z388,z3,z5,z6]),(0,[z0,z1,z30,z4,z291,z6]),(0,[z0,z1,z4,z63,z6,z105])],[(0,[z1078,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z1079,z5,z6]),(0,[z1,z3,z781,z4,z5,z6]),(0,[z0,z461,z3,z173,z5,z6]),(0,[z0,z1,z3,z377,z115,z6]),(0,[z8,z1,z3,z4,z115,z185])]],
   [[(0,[z0,z1,z3,z4,z26,z6]),(0,[z0,z135,z3,z4,z5,z104])],[(0,[z0,z1,z3,z1080,z5,z6]),(0,[z0,z1,z3,z71,z5,z189]),(0,[z16,z0,z3,z5,z6,z654]),(0,[z0,z296,z3,z4,z5,z104])],[(0,[z0,z1,z3,z4,z1081,z6]),(0,[z0,z1,z3,z5,z1082,z6])],[(0,[z0,z1,z3,z1083,z5,z6]),(0,[z0,z341,z3,z4,z5,z104]),(0,[z0,z1,z707,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z62])],[(0,[z0,z1,z3,z710,z5,z6]),(0,[z0,z461,z187,z4,z5,z6]),(0,[z389,z1,z3,z4,z5,z112])],[(0,[z1,z3,z81,z710,z5,z6]),(0,[z0,z1,z3,z71,z5,z200]),(0,[z0,z1,z1084,z4,z5,z6]),(0,[z0,z1085,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z5,z1086])],[(0,[z118,z1,z781,z4,z5,z6]),(0,[z0,z1,z3,z1087,z5,z6]),(0,[z59,z0,z60,z4,z5,z250])]],
   [[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1088,z6]),(0,[z237,z1,z119,z4,z5,z6]),(0,[z1042,z0,z3,z4,z5,z200]),(0,[z0,z1,z3,z1089,z5,z6])],[(1,[z799,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1090,z6]),(0,[z0,z1,z3,z173,z168,z6]),(0,[z0,z1,z3,z4,z5,z1091]),(0,[z1092,z1,z3,z4,z5,z6])],[(0,[z0,z1,z1093,z4,z5,z6]),(0,[z614,z1,z3,z4,z52,z6]),(0,[z0,z1,z3,z4,z5,z1094])],[(0,[z0,z1,z4,z134,z41,z6]),(0,[z137,z1,z3,z4,z52,z6]),(0,[z193,z1,z3,z4,z725,z6]),(0,[z0,z1,z3,z4,z5,z1095]),(0,[z0,z3,z707,z4,z5,z6]),(0,[z0,z3,z4,z5,z1096,z6]),(0,[z0,z1,z4,z5,z6,z730])],[(0,[z280,z203,z3,z4,z5,z6]),(0,[z0,z273,z1,z206,z3,z4]),(0,[z0,z1097,z1,z4,z5,z6]),(0,[z0,z42,z3,z4,z18,z62]),(0,[z0,z1,z1098,z4,z5,z6]),(0,[z0,z1,z238,z3,z4,z163])],[(0,[z0,z1,z1099,z4,z5,z6]),(0,[z0,z12,z3,z5,z6,z355]),(0,[z0,z1,z176,z4,z63,z177])],[(0,[z0,z1,z3,z4,z5,z1100]),(0,[z0,z3,z4,z5,z847,z104]),(0,[z0,z1,z13,z748,z5,z6]),(0,[z0,z1,z176,z4,z5,z177])],[(0,[z0,z1,z4,z134,z57,z6]),(0,[z0,z3,z4,z1101,z5,z6]),(0,[z22,z1,z3,z4,z5,z673]),(0,[z0,z1,z3,z5,z499,z36]),(0,[z0,z1102,z3,z4,z5,z6]),(0,[z14,z0,z1,z4,z431,z6]),(0,[z0,z1103,z3,z4,z5,z6])]],
   [[(0,[z193,z146,z1,z3,z4,z6]),(0,[z0,z1,z3,z607,z99,z6])],[(0,[z0,z148,z273,z1,z3,z4]),(0,[z0,z1,z4,z51,z5,z6]),(0,[z0,z1,z3,z4,z6,z1104]),(0,[z0,z1,z3,z5,z72,z709])],[(0,[z0,z1,z3,z5,z6,z1105]),(0,[z0,z1,z3,z4,z5,z1106]),(0,[z0,z1,z3,z5,z189,z36]),(0,[z0,z1,z13,z175,z125,z6]),(0,[z0,z1,z3,z1107,z5,z6])],[(0,[z0,z3,z4,z5,z220,z104]),(0,[z0,z1,z3,z234,z5,z36]),(0,[z0,z1,z175,z748,z5,z6]),(0,[z0,z1,z30,z4,z6,z487])],[(0,[z0,z1,z30,z474,z4,z6]),(0,[z1,z3,z4,z5,z6,z1108]),(0,[z14,z178,z1,z4,z182,z6])],[(0,[z470,z0,z60,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z112]),(0,[z0,z1,z3,z4,z1109,z5])],[(0,[z0,z1,z3,z4,z1110,z6]),(0,[z0,z1,z3,z4,z1111,z6]),(0,[z0,z1,z3,z4,z115,z6]),(0,[z0,z1,z161,z3,z731,z6])],[(0,[z0,z1,z316,z4,z5,z36])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 542) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 542).take 539) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1081)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [542, 539] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 153).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 153).take 103).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [153, 103] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

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

end PEqualNP.Outside.L_meta_37807

theorem PEqualNP.Outside.L_meta_37807 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074602 * 2 ^ 32 + 4242602112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074602 * 2 ^ 32 + 4242602112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37807.solve
-- Signatures

sig Nickname {}
sig EmailAddr {}
sig Password {}
sig Name {}
sig Surname {}
sig GitHubAccount {}
sig Date {
	value: Int  -- value represents the distance in days from 1-1-1900
} {value >= 0}
sig CodeKata {}
sig BadgeName{}
sig BadgeDescription{}

sig Badge {
	name: BadgeName,
	description: BadgeDescription
} 

abstract sig User {
	nickname: Nickname,
	emailAddr: EmailAddr,
	password: Password,
	name: Name,
	surname: Surname,
	dateOfBirth: Date
}

sig Educator extends User {}

sig Student extends User {
	githubAccount: GitHubAccount,
	badges: set Badge
}

sig SubscribedStudent {
	student: Student,
	var score: Int
} {score >= 0 and score <= 100}

abstract sig TournamentStatus{}
one sig TAvailable, TActive, TEnded extends TournamentStatus{}
abstract sig BattleStatus{}
one sig BNotCreated, BAvailable, BActive, BEnded extends BattleStatus{}

sig Tournament {
	name: Name,
	creator: Educator,
	educators: some Educator,
	badges: set Badge,
	subscribedStudents: set SubscribedStudent,
	registrationDeadline: Date,
	var battles: set Battle,
	var status: TournamentStatus
}

sig Rules {
	minimumNumberOfStudents: Int,
	maximumNumberOfStudents: Int
} {minimumNumberOfStudents > 0}

sig Team {
	students: some Student,
	var score: Int
} {score >= 0 and score <= 100}

sig Battle {
	creator: Educator,
	codeKata: CodeKata,
	registrationDeadline: Date,
	submissionDeadline: Date,
	subscribedStudents: set Student,
	rules: Rules,
	teams: set Team,
	var status: BattleStatus
}

-- Facts

-- Date
fact dateIsUnique {
	no disj d1 , d2 : Date | d1.value = d2.value
}

-- User
fact nicknamesAreUnique {
	no disj u1 , u2 : User | u1.nickname = u2.nickname
}

fact emailsAreUnique {
	no disj u1 , u2 : User | u1.emailAddr = u2.emailAddr
}

fact usernameExistsOnlyWithUser {
	all nn : Nickname | one u : User | nn in u.nickname
}

fact emailAddrExistsOnlyWithUser {
	all email : EmailAddr | one u : User | u.emailAddr in email
}

fact passwordExistsOnlyWithUser {
	all pw : Password | one u : User | u.password in pw
}

fact nameExistsOnlyWithUser {
	all nm : Name | one u : User | u.name in nm
}

fact surnameExistsOnlyWithUser {
	all sm : Surname | one u : User | u.surname in sm
}

fact dateOfBirthExistsOnlyWithUser {
	all dob : Date | one u : User | u.dateOfBirth in dob
}

-- Student

fact githubAccountsAreUnique {
	no disj u1 , u2 : Student | u1.githubAccount = u2.githubAccount
}

fact githubAccountExistsOnlyWithUser {
	all gha: GitHubAccount | one s : Student | s.githubAccount in gha
}

-- Code Kata

fact codeKataExistsOnlyWithBattle {
	all ck: CodeKata | one b : Battle | b.codeKata in ck
}

-- Tournament

fact tournamentNameIsUnique {
	no disj t1, t2: Tournament | t1.name = t2.name
}

fact tournamentBadgeIsUnique {
	all t: Tournament | no disj b1, b2: Badge | b1 in t.badges and b2 in t.badges and b1.name = b2.name and b1.description = b2.description
}

fact tournamentExistsOnlyWithCreator {
	all t: Tournament | one e : Educator | e in t.creator
}

fact badgeExistsOnlyWithTournament {
	all b: Badge | one t: Tournament | b in t.badges
}

fact studentBadgeIsAmongTournamentBadges {
	all s: Student, b: s.badges | one t: Tournament | b in t.badges and s in t.subscribedStudents.student
	and t.status = TEnded
}

fact creatorHasAccessToTournament {
	all t: Tournament | t.creator in t.educators 
}

fact registrationDeadlineIsAfterCreatorDateOfBirth {
	all t: Tournament | t.registrationDeadline.value > t.creator.dateOfBirth.value
}

fact registrationDeadlineIsAfterEducatorsDatesOfBirth {
	all t: Tournament, e: t.educators | t.registrationDeadline.value > e.dateOfBirth.value
}

fact registrationDeadlineIsAfterStudentsDatesOfBirth {
	all t: Tournament, s: t.subscribedStudents.student | t.registrationDeadline.value > s.dateOfBirth.value
}

fact battlesCannotBeRemoved {
	all t: Tournament | always (t.battles in t.battles')
}

fact battlesCannotBeAddedIfTournamentEnded {
	all t: Tournament | always (t.status = TEnded implies t.battles' = t.battles)
}

fact endedTournamentCannotGoBackToAPreviousStatus {
	all t: Tournament | always (t.status = TEnded implies t.status' = TEnded)
}

fact activeTournamentCannotGoBackToAPreviousStatus {
	all t: Tournament | always (t.status = TActive implies (t.status' = TActive or t.status' = TEnded))
}


-- Rules
fact minimumNumberOfStudentsIsLessThanMaximumNumberOfStudents {
	all r: Rules | r.minimumNumberOfStudents <= r.maximumNumberOfStudents
}

fact rulesExistsOnlyWithBattle {
	all r: Rules | one b: Battle | b.rules in r
}

-- Battle
fact creatorHasPermissionToCreateBattle {
	all t: Tournament, b: t.battles | b.creator in t.educators
}

fact battleExistsOnlyWithTournament {
	all b: Battle | one t: Tournament | eventually (b in t.battles)
}

fact battleIsNotCreatedIfItDoesNotBelongToATournamentYet{
	all b: Battle | b.status = BNotCreated implies (all t: Tournament | b not in t.battles)
}

fact registrationDeadlineIsAfterTournamentRegistrationDeadline {
	all t: Tournament, b: t.battles | b.registrationDeadline.value > t.registrationDeadline.value
}

fact submissionDeadlineIsAfterRegistrationDeadline {
	all b: Battle | b.submissionDeadline.value > b.registrationDeadline.value
}

fact subscribedStudentsAreSubscribedToTournament {
	all t: Tournament, b: t.battles, s: b.subscribedStudents | s in t.subscribedStudents.student
}

fact teamExistsOnlyWithBattle {
	all t: Team | one b: Battle | t in b.teams
}

fact teamHasAtLeastMinimumNumberOfStudents {
	all b: Battle, t: b.teams| #t.students >= b.rules.minimumNumberOfStudents
}

fact teamHasAtMostMaximumNumberOfStudents {
	all b: Battle, t: b.teams| #t.students <= b.rules.maximumNumberOfStudents
}

fact teamStudentsAreSubscribedToBattle {
	all b: Battle, t: b.teams, s: t.students | s in b.subscribedStudents
}

fact allSubscribedStudentsAreInATeam {
	all b: Battle | all s: b.subscribedStudents | one t: b.teams | s in t.students
}

fact availableTournamentHasNoBattle {
	all t: Tournament | t.status = TAvailable implies t.battles = none
}

fact endedTournamentHasNoaActiveBattle {
	all t: Tournament | t.status = TEnded implies (all b: t.battles | b.status = BEnded)
}

fact activeBattleImpliesActiveTournament {
	all t: Tournament | (some b: t.battles | b.status = BActive) implies t.status = TActive
}

fact availableBattleImpliesActiveTournament {
	all t: Tournament | (some b: t.battles | b.status = BAvailable) implies t.status = TActive and t.status' = TActive
}

fact activeOrAvailableBattleImpliesNotEndedTournament {
	all t: Tournament | (some b: t.battles | (b.status = BActive or b.status = BAvailable)) implies t.status != TEnded
}

fact endedBattleCannotGoBackToAPreviousStatus {
	all b: Battle | always (b.status = BEnded implies b.status' = BEnded)
}

fact activeBattleCannotGoBackToAPreviousStatus {
	all b: Battle | always (b.status = BActive implies (b.status' = BActive or b.status' = BEnded))
}

fact availableBattleCannotGoBackToAPreviousStatus {
	all b: Battle | always (b.status = BAvailable implies (b.status' = BAvailable or b.status' = BActive))
}


-- Predicates

pred tournamentDeadlineExpires[t: Tournament] {
	t.status = TAvailable
	t.status' = TActive
	all s: t.subscribedStudents | s.score' = 0
}

pred tournamentEnds[t: Tournament] {
	t.status = TActive
	t.status' = TEnded
}

pred battleRegistrationDeadlineExpires[b: Battle] {
	b.status = BAvailable
	b.status' = BActive
	all team: b.teams | team.score' = 0
}

pred battleEnds[b: Battle] {
	b.status = BActive
	b.status' = BEnded
}

pred addABattleToTournament[t: Tournament, b: Battle] {
	t.status = TActive
	b.status = BNotCreated
	t.battles' = t.battles + b
	b.status' = BAvailable
	t.status' = TActive
}

-- Assertions

assert activeTournamentWasOnceAvailable {
	all t: Tournament | tournamentDeadlineExpires[t] implies once t.status = TAvailable
}

assert endedTournamentWasOnceActive {
	all t: Tournament | tournamentEnds[t] implies once t.status = TActive
}

assert activeBattleWasOnceAvailable {
	all b: Battle | battleRegistrationDeadlineExpires[b] implies once b.status = BAvailable
}

assert endedBattleWasOnceActive {
	all b: Battle | battleEnds[b] implies once b.status = BActive
}

assert endedTournamentDoesNotGoBackToPreviousStatus{
	all t: Tournament | always (t.status = TEnded implies t.status' = TEnded)
}

assert activeTournamentDoesNotGoBackToPreviousStatus{
	all t: Tournament | always (t.status = TActive implies (t.status' = TEnded or t.status' = TActive))
}

assert endedBattleDoesNotGoBackToAPreviousStatus {
	all b: Battle | always (b.status = BEnded implies b.status' = BEnded)
}

assert activeBattleDoesNotGoBackToAPreviousStatus {
	all b: Battle | always (b.status = BActive implies (b.status' = BEnded or b.status' = BActive))
}

check activeTournamentWasOnceAvailable
check endedTournamentWasOnceActive
check activeBattleWasOnceAvailable
check endedBattleWasOnceActive
check endedTournamentDoesNotGoBackToPreviousStatus
check activeTournamentDoesNotGoBackToPreviousStatus
check endedBattleDoesNotGoBackToAPreviousStatus
check activeBattleDoesNotGoBackToAPreviousStatus

-- Run

pred example[b: Battle, t: Tournament] {
	t.status = TAvailable
	tournamentDeadlineExpires[t];
	addABattleToTournament[t, b];
	battleRegistrationDeadlineExpires[b]; 
	battleEnds[b]; 
	tournamentEnds[t]
}

pred example1[b, b1: Battle, t: Tournament] {
	t.status = TAvailable
	tournamentDeadlineExpires[t];
	addABattleToTournament[t, b];
	addABattleToTournament[t, b1];
	battleRegistrationDeadlineExpires[b];
	battleEnds[b];
	tournamentEnds[t]
}

run example for 5 but 1 Tournament, 1 Battle
run example1 for 5 but 1 Tournament, 2 Battle

'reach 0.1';

const [ isHand, ROCK, PAPER, SCISSORS ] = makeEnum(3);
const [ isOutcome, B_WINS, DRAW, A_WINS ] = makeEnum(3);

const winner = (handAlice, handBob) =>
    ((handAlice + (4 - handBob)) % 3);

assert(winner(ROCK, PAPER) == B_WINS); // Automatic verification : proof of honest
assert(winner(PAPER, ROCK) == A_WINS); // Automatic verification : proof of honest
assert(winner(ROCK, ROCK) == DRAW); // Automatic verification : proof of honest

forall(UInt, handAlice =>
    forall(UInt, handBob =>
        assert(isOutcome(winner(handAlice, handBob))))); // Automatic verification : proof of honest

forall(UInt, (hand) =>
    assert(winner(hand, hand) == DRAW)); // Automatic verification : proof of honest
    
const Player = {
    ...hasRandom, // <--- new!
    getHand: Fun([], UInt),
    seeOutcome: Fun([UInt], Null),
    informTimeout: Fun([], Null),
};

export const main = Reach.App(() => {
    const Alice = Participant('Alice', { // Specify Alice's interact interface here        
        ...Player,
        wager: UInt, //atomic units of currency
        deadline: UInt, // time delta (blocks/rounds)
    });
    const Bob = Participant('Bob', { // Specify Bob's interact interface here        
        ...Player,
        acceptWager: Fun([UInt], Null),
    });
    init();
    // write your program here 
    const informTimeout = () => {
        each([Alice, Bob], () => {
            interact.informTimeout();
        });
    };

    Alice.only(() => {
        const wager = declassify(interact.wager);
        const deadline = declassify(interact.deadline);
    });
    Alice.publish(wager, deadline)
        .pay(wager);
    commit();

    Bob.only(() => {
        interact.acceptWager(wager);
    });
    Bob.pay(wager)
        .timeout(relativeTime(deadline), () => closeTo(Alice, informTimeout));    

    var outcome = DRAW;
    invariant( balance() == 2 * wager && isOutcome(outcome) );
    while ( outcome == DRAW ) { // Play until we have a winner
        commit();
            
        Alice.only(() => {
            const _handAlice = interact.getHand();
            const [_commitAlice, _saltAlice] = makeCommitment(interact, _handAlice);
            const commitAlice = declassify(_commitAlice);
        });
        Alice.publish(commitAlice)
            .timeout(relativeTime(deadline), () => closeTo(Bob, informTimeout));
        commit();

        unknowable(Bob, Alice(_handAlice, _saltAlice));
        Bob.only(() => {
            const handBob = declassify(interact.getHand());
        });
        Bob.publish(handBob)
            .timeout(relativeTime(deadline), () => closeTo(Alice, informTimeout));
        commit();

        Alice.only(() => {
            const saltAlice = declassify(_saltAlice);
            const handAlice = declassify(_handAlice);
        });
        Alice.publish(saltAlice, handAlice)
            .timeout(relativeTime(deadline), () => closeTo(Bob, informTimeout));
        checkCommitment(commitAlice, saltAlice, handAlice);

        outcome = winner(handAlice, handBob);
        continue;
    }

    assert(outcome == A_WINS || outcome == B_WINS);
    transfer(2 * wager).to(outcome == A_WINS ? Alice : Bob);
    commit();

    each([Alice, Bob], () => {
        interact.seeOutcome(outcome)
    })
});
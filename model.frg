#lang forge/temporal

option max_tracelength 20
option min_tracelength 20
option solver Glucose

sig Tile {
	next: one Tile,
    back: one Tile,
    index: one Int,
    color: one Color
}

abstract sig Color {}

one sig Red extends Color {}
one sig Blue extends Color {}
one sig Green extends Color {}

abstract sig Item {}
one sig Mushroom extends Item {} //sends them forward 3
one sig FireFlower extends Item {} //Sends them back 3
one sig GenieLamp extends Item {} //Sends them to the current location of the star

one sig Star {
    var tile: one Tile,
    var price: one Int
}

abstract sig Player {
    var coins: one Int,
    var position: one Tile,
    var stars: one Int,
    var items: func Item -> Int
}

one sig Mario extends Player {}
one sig Luigi extends Player {}
one sig Toad extends Player {}
one sig Yoshi extends Player {}


sig Board { //Board sig
    board: set Tile,
    var playersMoved: set Player // used to track which players have moved in a given turn; reset once all four have gone in order to repeat
}

-- wellformed predicate that ensures the board is wellformed
pred wellformed[b: Board] {
	-- all nodes are reachable from the root
    all t : Tile { 
        t in b.board
        t.next != t
        t.back != t
        t.index != 0 implies {
            t.index = add[t.back.index, 1]
            t.index > 0
        }
        all disj t1, t2 : Tile | {
            t1.index != t2.index
            t1.next != t2.next
            t1.back != t2.back
            t1.next = t2 implies {{t2.index = add[t1.index, 1]} and {t1.index = subtract[t2.index, 1]}} or t2.index = 0 
        }
    }
    (#{r : b.board | r.color = Red} = 2) // 2
    (#{g : b.board | g.color = Green } = 1) // 1
    (#{bl : b.board | bl.color = Blue } = 5) // 5
    one t : b.board | t.index = 0

    b.playersMoved = none

    Star.price > 0
}

-- init predicate that initializes the game state
pred init {
    all p: Player | p.coins = 5
    all p : Player | {
        p.items[Mushroom] = 0
        p.items[FireFlower] = 0
        p.items[GenieLamp] = 0
    }
    all p: Player | p.stars = 0
    all p: Player | p.position.index = 0
    Star.price = 5

    all b: Board | wellformed[b]
}

-- main predicate that moves the specified player r spaces forward
pred move[p: Player, r: Int] {
    -- moveTo = new position of player, current = current position of player
    one moveTo: Tile, current: Tile | {
        p.position = current
        some t : Tile | one root : Tile | {
            root.index = 0
            -- handle the two cases of moving forward:
            -- 1. if the player is moving forward and not circling back to the beginning
            -- 2. if the player is moving forward and circling back to the beginning
            add[current.index, r] <= subtract[#{Tile}, 1] => {
                moveTo.index = add[current.index, r]
            } else {
                -- if it is looping, get the last index of the board, subtract from the current index, and add to r to get the new index
                moveTo.index = add[subtract[current.index, #{Tile}], r]
            }
        }

        -- handling the blue tile case where player gains a coin and either uses an item or simply moves to the position of that tile
        moveTo.color = Blue => {
            p.coins' = add[p.coins, 1]
            useItem[p, moveTo] or {
                p.items' = p.items
                p.position' = moveTo
            }
        }

        -- handling the red tile case where player loses a coin and either uses an item or simply moves to the position of that tile
        moveTo.color = Red => {
            p.coins' = subtract[p.coins, 1]
            useItem[p, moveTo] or {
                p.items' = p.items
                p.position' = moveTo
            }
        }

        -- handling the green tile case where player gains an item, and cannot use an item
        moveTo.color = Green => {
            p.coins' = p.coins
            one i : Item | all other: Item | {
                i != other => p.items'[other] = p.items[other]
                p.items'[i] = add[p.items[i], 1]
            }
            p.position' = moveTo
        }

        -- check if player passed the star when getting to new position, and add star if they have enough coins + move star on board
        some tilesToStar : Int | {
            { tilesToStar <= r and tilesToStar >= 0 } => {
                add[p.position.index, tilesToStar] = Star.tile.index
                p.coins >= Star.price => {
                    p.stars' = add[p.stars, 1]
                    starMove
                } else {
                    p.stars' = p.stars
                    starStay
                }
            } else {
                p.stars' = p.stars
                starStay
            }
        }
    }
}

-- Helper predicate that handles the use of an item by a player
pred useItem[p: Player, moveTo: Tile] {
    one i : Item | all other : Item | {
        i != other => p.items'[other] = p.items[other]

        -- ensure that player has at least one of the item and then remove one from their inventory
        p.items[i] > 0
        p.items'[i] = subtract[p.items[i], 1]

        -- mushroom moves player forward an additional 3 spaces
        i in Mushroom => {
            one tileAfterItem : Tile | {
                -- now create a new tile that includes the effects of the item
                tileAfterItem.index = moveTo.next.next.next.index

                -- move to that tile instead of the original moveTo
                p.position' = tileAfterItem
            }
        }

        -- genie lamp moves player to the current location of the star
        i in GenieLamp => {
            p.position' = Star.tile
        }

        -- fire flower glues player in place
        i in FireFlower => {
            p.position' = moveTo
        }
    }
}

-- Helper predicate that ensures all other players stay put while one player moves
pred stayPut[p: Player] {
    p.coins' = p.coins
    p.items' = p.items
    p.stars' = p.stars
    p.position' = p.position
}

-- Helper predicate that moves the player anywhere from 1-6 spaces during their turn
pred move_player_turn[p: Player] {
    move[p, 1] or move[p, 2] or move[p, 3] or move[p, 4] or move[p, 5] or move[p, 6]
}

-- Main predicate that handles each player's turn and the minigame that follows
pred game_turn {
    one b: Board | {
        #{b.playersMoved} = 4 => {
            b.playersMoved' = none
            minigame
        } else {
            one p : Player - b.playersMoved | {
                move_player_turn[p]
                all otherP : Player - p | {
                    stayPut[otherP]
                }
                b.playersMoved' = b.playersMoved + p
            }
        }

    }
}

-- Helper predicate that handles the minigame that occurs after all players have moved, giving each player 0-2 coins
pred minigame {
    starStay
    all p: Player | {
        p.items' = p.items
        p.stars' = p.stars
        p.position' = p.position

        p.coins' = add[p.coins, 2] or p.coins' = add[p.coins, 1] or p.coins' = p.coins
    }
}

-- Helper predicates that handle the movement of the star after a player buys it
pred starMove{
    Star.price' >= 0
    Star.price >= 0
    one moveTo: Tile | {
        moveTo != Star.tile
        moveTo = Star.tile'
    }
}

-- Helper predicates that handle the star staying in place when it is not bought
pred starStay{
    Star.price' >= 0
    Star.price >= 0
    Star.tile' = Star.tile
    Star.price' = Star.price
}

pred traces {
    init
    always game_turn
}

pred wellformedall {
    all b: Board | wellformed[b]
}

run { traces } for exactly 1 Board, exactly 8 Tile, 1 Green, 2 Red, 5 Blue, 5 Int
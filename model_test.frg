#lang forge/temporal

open "model.frg"

option max_tracelength 20
option min_tracelength 20
option solver Glucose
//board formation
//tiles on board
//players on board
//4 players
//some star somewhere
//all players start at the same position
//players move in same direction
//players can move back w a fireflower
//players can move extra far w a mushroom 
//players can teleport to star 
//item increment on green tile
//coin decrement on red tile
//coin increment on blue tile
//star moves after purchase
//movement and looping the board
//Once a player has a star, they can't lose it
//All players have moved before a minigame 
//All players can move again after a minigame

test suite for init { //also tests wellformedness
    test expect {
        validInitTest : {
            all t : Tile | all b : Board {
                t in b.board
                t.color = Red or t.color = Green or t.color = Blue
                (#{r : b.board | r.color = Red} = 2) // 2
                (#{g : b.board | g.color = Green } = 1) // 1
                (#{bl : b.board | bl.color = Blue } = 5) // 5
                #{b.board} = 8
                t.next.index = add[t.index, 1] or t.next.index = 0
                t.next.index = 0 => t.index = 7
            }
            all p : Player | all b : Board {
                p.position = 0
                p.coins = 5
                p.stars = 0
                p.items[Mushroom] = 0 
                p.items[FireFlower] = 0
                p.items[GenieLamp] = 0
            }
            init
        } for 5 Int is sat
        badPlayerCoins : {
            all t : Tile | all b : Board | {
                t in b.board
                t.color = Red or t.color = Green or t.color = Blue
                (#{r : b.board | r.color = Red} = 2) // 2
                (#{g : b.board | g.color = Green } = 1) // 1
                (#{bl : b.board | bl.color = Blue } = 5) // 5
                #{b.board} = 8
                t.next.index = add[t.index, 1] or t.next.index = 0
                t.next.index = 0 => t.index = 7
            }
            some p : Player  | {
                p.position = 0
                p.coins = 6
                p.stars = 0
                p.items[Mushroom] = 0 
                p.items[FireFlower] = 0
                p.items[GenieLamp] = 0
            }
            init
        } for 5 Int is unsat
        // badPlayerItems : {
        //     all t : Tile | all b : Board {
        //         t in b.board
        //         t.color = Red or t.color = Green or t.color = Blue
        //         (#{r : b.board | r.color = Red} = 2) // 2
        //         (#{g : b.board | g.color = Green } = 1) // 1
        //         (#{bl : b.board | bl.color = Blue } = 5) // 5
        //         #{b.board} = 8
        //         t.next.index = add[t.index, 1] or t.next.index = 0
        //         t.next.index = 0 => t.index = 7
        //     }
        //     some p : Player {
        //         p.position = 0
        //         p.coins = 5
        //         p.stars = 0
        //         p.items[Mushroom] > 0 or
        //         p.items[FireFlower] > 0 or 
        //         p.items[GenieLamp] > 0
        //     }
        //     init
        // } for 5 Int is unsat
        badPlayerStars : {
            all t : Tile | all b : Board {
                t in b.board
                t.color = Red or t.color = Green or t.color = Blue
                (#{r : b.board | r.color = Red} = 2) // 2
                (#{g : b.board | g.color = Green } = 1) // 1
                (#{bl : b.board | bl.color = Blue } = 5) // 5
                #{b.board} = 8
                t.next.index = add[t.index, 1] or t.next.index = 0
                t.next.index = 0 => t.index = 7
            }
            some p : Player {
                p.position = 0
                p.coins = 5
                p.stars = 1
                p.items[Mushroom] = 0
                p.items[FireFlower] = 0 
                p.items[GenieLamp] = 0
            }
            init
        } for 5 Int is unsat
        noGreen : {
            all t : Tile | all b : Board {
                t in b.board
                t.color = Red or t.color = Green or t.color = Blue
                (#{r : b.board | r.color = Red} = 2) // 2
                (#{g : b.board | g.color = Green } = 0) // 1
                (#{bl : b.board | bl.color = Blue } = 5) // 5
                #{b.board} = 8
                t.next.index = add[t.index, 1] or t.next.index = 0
                t.next.index = 0 => t.index = 7
            }
            some p : Player {
                p.position = 0
                p.coins = 5
                p.stars = 0
                p.items[Mushroom] = 0
                p.items[FireFlower] = 0 
                p.items[GenieLamp] = 0
            }
            init 
        } for 5 Int is unsat
        wrongTileDistribution : {
            all t : Tile | all b : Board {
                t in b.board
                t.color = Red or t.color = Green or t.color = Blue
                (#{r : b.board | r.color = Red} = 1) // 2
                (#{g : b.board | g.color = Green } = 5) // 1
                (#{bl : b.board | bl.color = Blue } = 2) // 5
                #{b.board} = 8
                t.next.index = add[t.index, 1] or t.next.index = 0
                t.next.index = 0 => t.index = 7
            }
            some p : Player {
                p.position = 0
                p.coins = 5
                p.stars = 0
                p.items[Mushroom] = 0
                p.items[FireFlower] = 0 
                p.items[GenieLamp] = 0
            }
            init
        } for 5 Int, 1 Board is unsat
    }
}

test suite for move { //using game_turn pred
    test expect {
        validNormalMove : {
            //NONE OF THE FOLLOWING PREDICATES WORKED WITH THIS TEST EVEN THOUGH THEY SHOULD
            // init
            // wellformedall
            // all b : Board | wellformed[b]
            // all p : Player | p.position.index = 0
            // Mario not in Board.playersMoved
            Mario.position.index = 0
            move[Mario, 1]
            Mario.position'.index = 1
        } for 5 Int, exactly 1 Board is sat
        validWrapMove : {
            wellformedall
            // some b : Board | wellformed[b]
            Mario.position.index = 7
            move[Mario, 3]
            Mario.position'.index = 2
        } for 5 Int, 1 Board is sat
        validMushroomMove: {
            // wellformedall
            some b : Board | wellformed[b]

            Mario.items[Mushroom] = 1
            Mario.position.index = 0
            move[Mario, 1]
            Mario.position'.index = 4
            // Mario.items'[Mushroom] = 0
        } for 5 Int, 1 Board, 8 Tile is sat
        validMushroomWrapMove : {
            wellformedall
            // some b : Board | wellformed[b]
            Mario.items[Mushroom] = 1
            Mario.position.index = 7
            move[Mario, 1]
            Mario.position'.index = 3
            // Mario.items'[Mushroom] = 0
        } for 5 Int, 1 Board is sat
        invalidMushroomMove : {
            // wellformedall
            some b : Board | wellformed[b]
            Mario.items[Mushroom] = 0
            Mario.items[GenieLamp] = 0
            Mario.position.index = 0
            move[Mario, 1]
            Mario.position'.index = 3
        } for 5 Int, 1 Board is unsat
        invalidMushroomWrapMove: {
            some b : Board | wellformed[b]
            // wellformedall
            Mario.items[Mushroom] = 0
            Mario.items[GenieLamp] = 0
            Mario.position.index = 7
            move[Mario, 1]
            Mario.position'.index = 3
        } for 5 Int, 1 Board, 8 Tile is unsat
        validFireFlowerMove : {
            wellformedall
            // some b : Board | wellformed[b]
            Mario.items[FireFlower] = 1
            Mario.position.index = 0
            move[Mario, 1]
            Mario.position'.index = 1
            Mario.items'[FireFlower] = 0
        } for 5 Int, 1 Board is sat
        // validFireFlowerMove : {
        //     // wellformedall 
        //     // // some b : Board | wellformed[b]
        //     // Mario.items[FireFlower] = 1
        //     // Mario.position.index = 0
        //     // move[Mario, 1]
        //     // Mario.position'.index = 1
        //     // // Mario.items'[FireFlower] = 0
        // } for 5 Int, 1 Board is sat
        // inalidFireFlowerMove : { //only can use one item at a time,
        // //WE CANNOT TEST THIS AS IS 
        //     // wellformedall
        //     some b : Board | wellformed[b]
        //     Mario.items[FireFlower] = 0
        //     Mario.position.index = 0
        //     move[Mario, 1]
        //     Mario.position'.index = 2
        //     // Mario.items'[FireFlower] = 0
        // } for 5 Int, 1 Board is sat
        validStarMove : {
            wellformedall
            // some b : Board | wellformed[b]
            some s : Star | s.tile.index = 3
            Mario.items[GenieLamp] = 1
            Mario.position.index = 0
            Mario.position.next.index = 1
            move[Mario, 1]
            Mario.position'.index = 3 // where the star is
            // Mario.items'[GenieLamp] = 0
        } for 5 Int, 1 Board is sat
        invalidStarMove : {
            // wellformedall
            some b : Board | wellformed[b]
            some s : Star | s.tile.index = 3
            Mario.items[GenieLamp] = 0
            Mario.position.index = 0
            Mario.position.next.index = 1
            move[Mario, 1]
            Mario.position'.index = 3 // where the star is
        } for 5 Int, 1 Board is unsat
    }
}

test suite for game_turn {
    test expect { 
        validGameTurnMinigame: {
            one b : Board | #{b.playersMoved} = 4
            Mario.coins = 0
            Luigi.coins = 0
            Yoshi.coins = 0
            Toad.coins = 0
            game_turn
            Mario.coins' = 1
            Luigi.coins' = 1
            Yoshi.coins' = 2
            Toad.coins' = 0
        } for 5 Int, 1 Board is sat
        validGameTurnNoMinigame: {
            all p : Player | p.coins = 5
            one b : Board | Mario not in b.playersMoved
            Mario.position.index = 0
            Luigi.position.index = 3
            Yoshi.position.index = 4
            Toad.position.index = 7
            game_turn
            Mario.position'.index = 3
            Luigi.position'.index = 3
            Yoshi.position'.index = 4
            Toad.position'.index = 7
            Mario.coins' = 6
            Luigi.coins' = 5
            Yoshi.coins' = 5
            Toad.coins' = 5
        } for 5 Int, 1 Board is sat
        noDoubleMove: {
            one b : Board | Mario in b.playersMoved
            Mario.position.index = 0
            Luigi.position.index = 3
            Yoshi.position.index = 4
            Toad.position.index = 7
            game_turn
            Mario.position'.index = 3
            Luigi.position'.index = 3
            Yoshi.position'.index = 4
            Toad.position'.index = 7
        } for 5 Int, 1 Board is unsat
        noMoveOnMinigame : {
            one b : Board | #{b.playersMoved} = 4 and #{b.playersMoved'} = 0
            Mario.position.index = 0
            Luigi.position.index = 3
            Yoshi.position.index = 4
            Toad.position.index = 7
            game_turn
            Mario.position'.index = 0
            Luigi.position'.index = 3
            Yoshi.position'.index = 4
            Toad.position'.index = 7
        } for 5 Int, 1 Board is sat
        nothingReallyChanges : {
            Mario.position.index = 0
            Luigi.position.index = 3
            Yoshi.position.index = 4
            Toad.position.index = 7
            game_turn
            Mario.position'.index = 0
            Luigi.position'.index = 3
            Yoshi.position'.index = 4
            Toad.position'.index = 7
        } for 5 Int, 1 Board is sat
        yoshiGetsToAStar : {
            some s : Star | s.tile.index = 3
            Yoshi.position.index = 0
            Yoshi.position.next.index = 1
            Yoshi.items[GenieLamp] = 1
            game_turn
            Yoshi.position'.index = 3
        } for 5 Int, 1 Board is sat
        yoshiGetsAStar : { //adding wellformedness to the test breaks it
            some s : Star | s.tile.index = 3
            Yoshi.position.index = 0
            Yoshi.stars = 0
            game_turn
            Yoshi.position'.index = 4
            Yoshi.stars' = 1
        } for 5 Int, 1 Board is sat
        }   
}
test suite for stayPut {
    test expect {
        validStayPut : {
            Mario.position.index = 0
            stayPut[Mario]
            Mario.position'.index = 0
            Mario.coins' = Mario.coins
            Mario.items' = Mario.items
            Mario.stars' = Mario.stars
        } for 5 Int, 1 Board is sat
        invalidStayPutIndex : {
            Mario.position.index = 7
            stayPut[Mario]
            Mario.position'.index = 1
        } for 5 Int, 1 Board is unsat
        invalidStayPutCoins : {
            Mario.position.index = 0
            stayPut[Mario]
            Mario.position'.index = 0
            Mario.coins' != Mario.coins
            Mario.items' = Mario.items
            Mario.stars' = Mario.stars
        } for 5 Int, 1 Board is unsat
        invalidStayPutItems : {
            Mario.position.index = 0
            stayPut[Mario]
            Mario.position'.index = 0
            Mario.coins' = Mario.coins
            Mario.items' != Mario.items
            Mario.stars' = Mario.stars
        } for 5 Int, 1 Board is unsat
        invalidStayPutStars: {
            Mario.position.index = 0
            stayPut[Mario]
            Mario.position'.index = 0
            Mario.coins' = Mario.coins
            Mario.items' = Mario.items
            Mario.stars' != Mario.stars
        } for 5 Int, 1 Board is unsat
    }
}

test suite for minigame {
    test expect {
        validMinigame : {
            Mario.coins = 0
            minigame
            Mario.coins' = 1
        } for 5 Int, 1 Board is sat
        validMinigame2 : {
            Mario.coins = 5
            minigame
            Mario.coins' = 6
        } for 5 Int, 1 Board is sat
        invalidMinigame : { //nobody loses coins!
            Mario.coins = 1
            minigame
            Mario.coins' = 0
        } for 5 Int, 1 Board is unsat
    }
}

test suite for starStay {
    test expect {
        validStarStay : {
            some s : Star | s.tile.index = 3 and s.tile'.index = 3
            starStay
        } for 5 Int, 1 Board is sat
        invalidStarStay : {
            some s : Star | s.tile.index = 4 and s.tile'.index = 3
            starStay
        } for 5 Int, 1 Board is unsat
    }
}

test suite for starMove {
    test expect {
        validStarMoveStarMove : {
            some s : Star | s.tile != s.tile'
            starMove
        } for 5 Int, 1 Board is sat
        invalidStarMoveStarMove : {
            some s : Star | s.tile = s.tile'
            starMove
        } for 5 Int, 1 Board is unsat
    }
}

test suite for wellformedall {
    test expect {
        validWellformed : {
            wellformedall
        } for 5 Int, 1 Board is sat
        invalidWellformed : {
            some b : Board | not wellformed[b]
            some b : Board | wellformed[b]
            wellformedall
        } for 5 Int, 2 Board is unsat
    }
}
test suite for final {
    test expect {
        validFinal : {
            Mario.stars = 1
            final
        } for 5 Int, 1 Board is sat
        invalidFinal : {
            Mario.stars = 0
            Luigi.stars = 0
            Yoshi.stars = 0
            Toad.stars = 0
            final
        } for 5 Int, 1 Board is unsat
    }
}

test suite for useItem {
    test expect { //checks item use and decrement
        validUseMushroom : {
            Mario.items[Mushroom] = 1
            useItem[Mario, Mario.position.next]
            Mario.items'[Mushroom] = 0
        } for 5 Int, 1 Board is sat
        invalidUseItem : {
            Mario.items[Mushroom] = 0
            Mario.items[FireFlower] = 0
            Mario.items[GenieLamp] = 0
            useItem[Mario, Mario.position.next]
            Mario.items'[Mushroom] = 0
        } for 5 Int, 1 Board is unsat
         validUseFireFlower : {
            Mario.items[FireFlower] = 1
            useItem[Mario, Mario.position.next]
            Mario.items'[FireFlower] = 0
        } for 5 Int, 1 Board is sat
        validUseGenieLamp : {
            Mario.items[GenieLamp] = 1
            useItem[Mario, Mario.position.next]
            Mario.items'[GenieLamp] = 0
        } for 5 Int, 1 Board is sat
        validUseAny : {
            Mario.items[Mushroom] = 1
            Mario.items[FireFlower] = 1
            Mario.items[GenieLamp] = 1
            useItem[Mario, Mario.position.next]
            Mario.items'[Mushroom] = 0 or Mario.items'[FireFlower] = 0 or Mario.items'[GenieLamp] = 0
        } for 5 Int, 1 Board is sat
        invalidUseAny : {
            Mario.items[Mushroom] = 0
            Mario.items[FireFlower] = 0
            Mario.items[GenieLamp] = 0
            useItem[Mario, Mario.position.next]
            Mario.items'[Mushroom] = 0 or Mario.items'[FireFlower] = 0 or Mario.items'[GenieLamp] = 0
        } for 5 Int, 1 Board is unsat
    }
}

test suite for trace_base { //This is more to see what forge decides to do here than to test the model as we were quite curious!
//it's interesting that forge doesn't exactly fill in the blanks for us unless we explicitly give it all the variables it needs
    test expect {
        validTraceBase : {
            trace_base
        } for exactly 1 Board, exactly 8 Tile, 1 Green, 2 Red, 5 Blue, 5 Int is sat
        validTraceBaseButNot : { //unsat here so it might have to do with our run lines
            trace_base
        } for exactly 1 Board, 5 Int is unsat
        invalidTraceBase : {
            some b : Board | not trace_base
            some b : Board | trace_base
            trace_base
        } for 5 Int, 2 Board is unsat
    }
}







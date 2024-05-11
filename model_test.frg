#lang forge/temporal

open "model.frg"

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
//players can't move more than 7 without a mushroom
//player can only move 0 if they used a fireflower
//player can only move 9 if they used a mushroom
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
        badPlayerItems : {
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
                p.stars = 0
                p.items[Mushroom] > 0 or
                p.items[FireFlower] > 0 or 
                p.items[GenieLamp] > 0
            }
            init
        } for 5 Int is unsat
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
            // init
            // wellformedall
            some b : Board | wellformed[b]
            // all p : Player | p.position.index = 0
            // Mario not in Board.playersMoved
            // Mario.position.index = 0
            // move[Mario, 1]
            // Mario.position'.index = 1
        } for 5 Int, 1 Board is unsat
        validWrapMove : {
            // wellformedall
            some b : Board | wellformed[b]
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
            // wellformedall
            some b : Board | wellformed[b]
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
            // wellformedall
            some b : Board | wellformed[b]
            Mario.items[FireFlower] = 1
            Mario.position.index = 0
            move[Mario, 1]
            Mario.position'.index = 1
            Mario.items'[FireFlower] = 0
        } for 5 Int, 1 Board is sat
        validFireFlowerMove : {
            // wellformedall
            some b : Board | wellformed[b]
            Mario.items[FireFlower] = 1
            Mario.position.index = 0
            move[Mario, 1]
            Mario.position'.index = 1
            Mario.items'[FireFlower] = 0
        } for 5 Int, 1 Board is sat
        inalidFireFlowerMove : { //only can use one item at a time
            // wellformedall
            some b : Board | wellformed[b]
            Mario.items[FireFlower] = 1
            Mario.position.index = 0
            move[Mario, 1]
            Mario.position'.index = 2
            Mario.items'[FireFlower] = 0
        } for 5 Int, 1 Board is sat
    }
}





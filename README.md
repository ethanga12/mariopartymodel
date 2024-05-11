# Logic for Systems Final Project - Mario Party Model
## Language: Forge
## Contributors: Rayhan Meghji (rmeghji), Ethan Asis (ethanga12)

## Introduction

We set out to center our project around modeling the popular Nintendo video game Mario Party, which is effectively a digital board game in which players "roll" virtual dice, collect stars that move around the board in order to win the game, land on different tile types to gain/lose coins or gain items, and play minigames at the end of each round that provide the players with more coins. We wanted to use this model to qualitatively determine the balance of skill vs. luck that contributes to winning/losing the game.

## Design Decisions

Our model's core structure centers around the following main sigs and predicates.

### Sigs:
- Player abstract sig - fields to keep track of each player's coins, stars, and items. Has four one sigs extending it that model different characters that are playable in the game.
- Star one sig - fields to keep track of price and location.
- Tile sig - fields to keep track of next and previous tiles in order to maintain a circularly linked list structure, index on the board, and color.
- Color abstract sig - used in color field of tile to keep track of what each tile should do when landed on. Has three one sigs extending it for Blue (gain one coin), Red (lose one coin), and Green (gain one item) tiles.

### Predicates:
- init - starts the game model with all players at the zero index tile, with five coins and no items, stars, etc.
- wellformed - ensures correct board structure; maintains valid structure for all aspects of game that do not change temporally.
- move - handles logic for players moving forward, and calls helper sigs such as useItem when applicable.
- useItem - helper sig handling logic of each item's use (Mushroom moving player forward three spaces, )
- stayPut, move_player_turn, starMove, starStay - helper predicates that handle the logic of moving a player when it is their turn and keeping them in place when it isn't, and moving the star + changing its price when it is acquired and keeping it at the same tile and price when it isn't.
- minigame - simulates outcome of minigame that occurs between every round (after every player has taken their turn) by giving anywhere from 0-2 coins randomly to each player.
- game_turn - handles the logic of determining which players still need to go using playersMoved set, and running a minigame + simultaneously resetting playersMoved when every player had taken their turn in a given round.

## Limitations
### Simplifications:

We were largely able to successfully model a plausible instance of the game, although there were a few aspects and game mechanics that we had to create more generalized versions of. Some examples of these include:

- The size of the board, which we had to limit to eight tiles in order to run the model in a reasonable timeframe.
- The star buying scheme, which we had to simplify so that a player has to have the amount of coins that the star costs, but those coins are not removed from the player's inventory.
- The star pricing scheme, which we ended up making more randomized within the range of integers as opposed to oscillating from a few set values, in order to account for the limited amount of integers as well as to add an extra layer of randomness to somewhat account for Forge's limitations in randomizing other random elements of gameplay.
- The Fire Flower was initially intended to move a random player three spaces back, but this proved very difficult (potentially impossible) while maintaining a consistent trace structure, so we instead changed it to plant the player in their spot.

### Trace Structure
In addition to this, we had to change from our initial approach regarding the way our traces were structured. Initially, we modeled each turn as one trace - in each trace, every player would move positions, and a simulation of a minigame would give players additional coins. However, we found that this caused several problems such as the star only moving after every player had gone, contradictions within the same traces between the coins that players gained/lost from the tiles with the coins given by minigames, and other similar issues.

We decided to adapt our model so that each trace instead represented each player's individual turn, monitored by a "playersMoved" list that reset once all four players had moved in a round and triggered a minigame. This allowed us to fix the aforementioned contradictions as well as providing a better view of how an actual game of Mario Party flows throughout instead of the very vast overviews we would get previously. However, this did come at the cost of the amount of rounds that were possible to simulate, since we now needed five times the amount of traces to model the same round as before.

## Visualization

We found that the best way to view our project was in the form of Forge's built-in table view, where you can clearly see between each trace the movement of each player, the star, and the items and stars that each player accumulates over the course of the game. We adapted a lot of our initial sig structures in order to make the table view as easy to read as possible, including converting Stars, Items, and Coins to one sigs and tracking player stars with funcs mapping Items to Ints or simply Ints for stars and coins. As such, it is easy to click through each trace and watch player movements and inventories change over the course of the game, as we display in our video.

## Outcome & Reflection

By the end of the project, we found that working through the decisions to structure our model had shifted our goals with the project from determining the randomness factor of winning a game of Mario Party to pushing the bounds of a modeling tool like Forge in modeling a game that is so extensible and often vast. We learned a lot about the mechanics of Forge, such as the bounds of what we could (or should) try to fit in one trace, how to implement "randomness" in a language where actual mathematical randomness seems like less of a concept that is intended to be employed as directly, and balancing a model's structure to make the outcome as readable as possible without compromising the information we wanted to convey.

## Testing

In our testing, we ran into a few limitations with Forge for larger predicates with other predicates being called/referenced within them, so we found smaller unit tests to be more sound ways to test our predicates. We were largely able to account for the implications this had on our testing through our very thorough unit testing, and we utilized extremely extensive hand-testing as we built the model, playing around with it to understand and verify its behaviors. A good example of some of the quirks of Forge that we found ourselves working around lies in its inability to “fill in the blanks” for larger predicates to make things sat or unsat, where when we run a full trace with less specificity in the run statement, but no contradictory information, we get an unsat when the model is very much satisfiable. We also noticed when testing was that if we run a testing file when there is an error in the original file, the testing file will throw a bizarre syntax error without referring to the real issue in the original file. With that being said, we ensured that our testing tests the expected behavior of all predicates very thoroughly, as well as documenting and verifying our larger/initial ideas for how the model behaves.
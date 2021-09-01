'''
Simple example pokerbot, written in Python.
'''
from skeleton.actions import FoldAction, CallAction, CheckAction, RaiseAction, AssignAction
from skeleton.states import GameState, TerminalState, RoundState, BoardState
from skeleton.states import NUM_ROUNDS, STARTING_STACK, BIG_BLIND, SMALL_BLIND, NUM_BOARDS
from skeleton.bot import Bot
from skeleton.runner import parse_args, run_bot
import pickle
import eval7
import random
import pandas as pd
import numpy as np
pd.set_option('display.max_rows', 1500)

class Player(Bot):
    '''
    A pokerbot.
    '''

    def __init__(self):
        '''
        Called when a new game starts. Called exactly once.
        Arguments:
        Nothing.
        Returns:
        Nothing.
        '''
        self.board_allocations = [[], [], []] #keep track of our allocations at round start
        self.hole_strengths = None
        self.our_fold_count = 0
        self.opp_fold_count = 0
        self.opp_fold_streets = {0: 0, 3: 0, 4: 0, 5: 0}
        self.our_fold_streets = {0: 0, 3: 0, 4: 0, 5: 0}
        self.opp_post_flop_raise_count = 0
        self.opp_post_flop_no_raise_count = 0
        self.opp_bets_board = {0: [], 1: [], 2: []}
        self.opp_bets_strength = pd.DataFrame(columns=['bet', 'strength'])
        self.opp_post_flop_call_count = 0

        self.our_post_flop_raise_count = 0

        self.num_showdowns = 0
        self.num_showdown_wins = 0
        self.num_showdown_losses = 0
        self.play_checkfold = False
        with open('hand_strengths.p', 'rb') as fp:
            self.hand_strengths = pickle.load(fp)
        # self.preflop_hand_strength_list = []
        # for key in self.hand_strengths.keys():
        #     print(key, ': ', self.hand_strengths[key]['win_prob'] + .5 * self.hand_strengths[key]['draw_prob'])
        self.card_val_order = ['2', '3', '4', '5', '6', '7', '8', '9', 'T', 'J', 'Q', 'K', 'A']
        self.our_raise_rate = 0
        self.opp_raise_rate = 0
        self.our_fold_rate = 0
        self.opp_fold_rate = 0

        self.opp_bb_raise_count = 0
        self.opp_bb_raise_rate = None
        self.opp_sb_raise_count = 0
        self.opp_sb_raise_rate = None

        self.opp_sb_call_count = 0
        self.opp_sb_call_rate = None

        self.board_folds = [False, False, False]
        self.our_showdown_losses = 0
        self.our_showdown_wins = 0
        self.opp_board_strengths = {0: [], 1: [], 2: []}
        self.opp_board_avg_strength_ranking = None


    def allocate_cards(self, my_cards):
        '''
        Method that allocates our cards at the beginning of a round. Method
        modifies self.board_allocations. The method attempts to make pairs
        by allocating hole cards that share a rank if possible. The exact
        stack these cards are allocated to is not defined.
        Arguments:
        my_cards: a list of the 6 cards given to us at round start
        '''
        possible_card_assignments = [
            [[0, 1], [2, 3], [4, 5]],
            [[0, 1], [2, 4], [3, 5]],
            [[0, 1], [2, 5], [3, 4]],

            [[0, 2], [1, 3], [4, 5]],
            [[0, 2], [1, 4], [3, 5]],
            [[0, 2], [1, 5], [3, 4]],

            [[0, 3], [1, 2], [4, 5]],
            [[0, 3], [1, 4], [2, 5]],
            [[0, 3], [1, 5], [2, 4]],

            [[0, 4], [1, 2], [3, 5]],
            [[0, 4], [1, 3], [2, 5]],
            [[0, 4], [1, 5], [2, 3]],

            [[0, 5], [1, 2], [3, 4]],
            [[0, 5], [1, 3], [2, 4]],
            [[0, 5], [1, 4], [2, 3]],
        ]
        best_allocation = None
        best_allocation_strength = -1
        for possible_allocation in possible_card_assignments:
            allocation_strength_list = []
            #cauclate the weighted hand strnght for each possible paring
            for card_pair_indices in possible_allocation:
                card_pair = [my_cards[card_pair_indices[0]], my_cards[card_pair_indices[1]]]
                card1_value = my_cards[card_pair_indices[0]][0]
                card2_value = my_cards[card_pair_indices[1]][0]
                card1_suit = my_cards[card_pair_indices[0]][1]
                card2_suit = my_cards[card_pair_indices[1]][1]
                if card1_suit == card2_suit:
                    suit_relation = 'same'

                else:
                    suit_relation = 'diff'
                if card1_value == card2_value:
                    card_pair_tup = (card1_value, card2_value)
                else:
                    card1_value_index = [i for i in range(len(self.card_val_order)) if self.card_val_order[i] == card1_value]
                    card2_value_index = [i for i in range(len(self.card_val_order)) if self.card_val_order[i] == card2_value]

                    if card1_value_index > card2_value_index:
                        card_pair_tup = (card2_value, card1_value, suit_relation)
                    else:
                        card_pair_tup = (card1_value, card2_value, suit_relation)

                pair_strength = self.hand_strengths[card_pair_tup]['win_prob'] + .5 * self.hand_strengths[card_pair_tup]['draw_prob']

                allocation_strength_list.append([card_pair, pair_strength])
            allocation_strength_list = sorted(allocation_strength_list, key=lambda x: x[1])
            allocation_weighted_strength = 0
            for i in range(NUM_BOARDS):
                # allocation_weighted_strength += allocation_strength_list[i][1] * (i + 1)
                allocation_weighted_strength += allocation_strength_list[i][1]
            if allocation_weighted_strength > best_allocation_strength:
                best_allocation_strength = allocation_weighted_strength
                best_allocation = allocation_strength_list
        if self.opp_board_avg_strength_ranking is not None:
            count = 0
            for board in self.opp_board_avg_strength_ranking:
                self.board_allocations[board] = best_allocation[(count + 1) % 3][0]
                self.hole_strengths[0][board] = best_allocation[(count + 1) % 3][1]
                count += 1
        else:
            self.board_allocations = [best_allocation[1][0], best_allocation[2][0], best_allocation[0][0]]
            self.hole_strengths[0] = [best_allocation[1][1], best_allocation[2][1], best_allocation[0][1]]
        # for i in range(NUM_BOARDS):
            # self.board_allocations[i] = best_allocation[i][0]
            # self.hole_strengths[0][i] = best_allocation[i][1]
            # self.board_allocations[i] = best_allocation[2-i][0]
            # self.hole_strengths[0][i] = best_allocation[2-i][1]


    def calcualte_strength(self, hole, iters, board_cards, dead_cards, opp_known_cards=None):
        '''
        A Monte Carlo method meant to estimate the win probability of a pair of
        hole cards. Simlulates 'iters' games and determines the win rates of our cards
        Arguments:
        hole: a list of our two hole cards
        iters: a integer that determines how many Monte Carlo samples to take
        '''

        deck = eval7.Deck() #eval7 object!
        hole_cards = [eval7.Card(card) for card in hole] #card objects, used to evaliate hands
        board_cards = [eval7.Card(card) for card in board_cards if card != '']
        dead_cards = [eval7.Card(card) for card in dead_cards]

        for card in hole_cards: #remove cards that we know about! they shouldn't come up in simulations
            deck.cards.remove(card)
        for card in board_cards:
            deck.cards.remove(card)
        for card in dead_cards:
            deck.cards.remove(card)

        score = 0
        if opp_known_cards is not None:
            opp_known_cards = [eval7.Card(card) for card in opp_known_cards]
            our_hand = hole_cards + board_cards
            opp_hand = opp_known_cards + board_cards
            our_hand_value = eval7.evaluate(our_hand) #the ranks of our hands (only useful for comparisons)
            opp_hand_value = eval7.evaluate(opp_hand)
            if our_hand_value > opp_hand_value:
                return 1
            elif our_hand_value < opp_hand_value:
                return 0
            else:
                return .5

        for _ in range(iters): #take 'iters' samples
            deck.shuffle() #make sure our samples are random

            _COMM = 5 - len(board_cards) #the number of cards we need to draw
            _OPP = 2

            draw = deck.peek(_COMM + _OPP)

            opp_hole = draw[: _OPP]
            community = draw[_OPP: ]
            community = community + board_cards

            our_hand = hole_cards + community #the two showdown hands
            opp_hand = opp_hole + community

            our_hand_value = eval7.evaluate(our_hand) #the ranks of our hands (only useful for comparisons)
            opp_hand_value = eval7.evaluate(opp_hand)

            if our_hand_value > opp_hand_value: #we win!
                score += 2

            elif our_hand_value == opp_hand_value: #we tie.
                score += 1

        hand_strength = score / (2 * iters) #this is our win probability!

        return hand_strength

    def handle_new_round(self, game_state, round_state, active):
        '''
        Called when a new round starts. Called NUM_ROUNDS times.
        Arguments:
        game_state: the GameState object.
        round_state: the RoundState object.
        active: your player's index.
        Returns:
        Nothing.
        '''
        self.hole_strengths = {0: [None] * NUM_BOARDS, 3: [None] * NUM_BOARDS, 4: [None] * NUM_BOARDS, 5: [None] * NUM_BOARDS}
        self.opp_bets_board = {0: [], 1: [], 2: []}
        my_bankroll = game_state.bankroll  # the total number of chips you've gained or lost from the beginning of the game to the start of this round
        opp_bankroll = game_state.opp_bankroll # ^but for your opponent
        game_clock = game_state.game_clock  # the total number of seconds your bot has left to play this game
        round_num = game_state.round_num  # the round number from 1 to NUM_ROUNDS
        my_cards = round_state.hands[active]  # your six cards at the start of the round
        big_blind = bool(active)  # True if you are the big blind
        self.allocate_cards(my_cards) #our old allocation strategy

        bankroll_lead = my_bankroll - opp_bankroll
        if round_num % 2 == 1: #even number of rounds left to be played
            checkfold_loss = (500 - round_num + 1) * 21
        else: #odd number of rounds left to be played
            if big_blind:
                checkfold_loss = 24
                checkfold_loss += (500 - round_num) * 21
            else:
                checkfold_loss = 18
                checkfold_loss += (500 - round_num) * 21
        if bankroll_lead > checkfold_loss + 1:
            if self.play_checkfold == False:
                print('Playing checkfold starting at round', round_num)
                print('opp post flop raise rate: ', self.opp_raise_rate)
                print('opp fold rate', self.opp_fold_rate)
                print('our fold rate', self.our_fold_rate)
                print('our showdown wins', self.our_showdown_wins)
                print('our showdown losses', self.our_showdown_losses)
                for i in range(3):
                    print('board #', i, ' opp avg strength:',
                          sum(self.opp_board_strengths[i]) / len(self.opp_board_strengths[i]))

            self.play_checkfold = True
        if round_num >= 29 and round_num % 10 == 0:
            self.opp_raise_rate = self.opp_post_flop_raise_count / (self.opp_post_flop_raise_count + self.opp_post_flop_no_raise_count)
            if self.opp_post_flop_raise_count > 0:
                self.our_fold_rate = self.our_fold_count / (3 * (round_num + 1))
            if self.our_post_flop_raise_count > 0:
                self.opp_fold_rate = self.opp_fold_count / (3 * (round_num + 1))

        if round_num >= 14 and round_num % 10 == 0:
            opp_board_stren_lol = []
            for i in range(3):
                if len(self.opp_board_strengths[i]) > 0:
                    opp_board_stren_lol.append([i, sum(self.opp_board_strengths[i]) / len(self.opp_board_strengths[i])])
                else:
                    opp_board_stren_lol.append([i, .6])

            sorted_opp_board_stren_lol = sorted(opp_board_stren_lol, key=lambda x: x[1])
            self.opp_board_avg_strength_ranking = []
            for pair in sorted_opp_board_stren_lol:
                self.opp_board_avg_strength_ranking.append(pair[0])
            self.opp_bb_raise_rate = self.opp_bb_raise_count / (3 * round_num / 2)
            self.opp_sb_raise_rate = self.opp_sb_raise_count / (3 * round_num / 2)



    def handle_round_over(self, game_state, terminal_state, active):
        '''
        Called when a round ends. Called NUM_ROUNDS times.
        Arguments:
        game_state: the GameState object.
        terminal_state: the TerminalState object.
        active: your player's index.
        Returns:
        Nothing.
        '''
        my_delta = terminal_state.deltas[active]  # your bankroll change from this round
        opp_delta = terminal_state.deltas[1-active] # your opponent's bankroll change from this round
        previous_state = terminal_state.previous_state  # RoundState before payoffs
        street = previous_state.street  # 0, 3, 4, or 5 representing when this round ended  W
        opp_card_lol = []
        for terminal_board_state in previous_state.board_states:
            previous_board_state = terminal_board_state.previous_state
            my_cards = previous_board_state.hands[active]  # your cards
            opp_cards = previous_board_state.hands[1-active]  # opponent's cards or [] if not revealed
            opp_card_lol.append(opp_cards)
            if opp_cards != ['', ''] and opp_cards != []: #there was a showdown
                showdown_res = self.calcualte_strength(my_cards, 1, previous_board_state.deck, [], opp_known_cards = opp_cards)
                self.our_showdown_wins += showdown_res
                self.our_showdown_losses += (1 - showdown_res)





        game_clock = game_state.game_clock #check how much time we have remaining at the end of a game
        round_num = game_state.round_num #Monte Carlo takes a lot of time, we use this to adjust!
        for i in range(3):
            opp_cards = opp_card_lol[i]
            if (opp_cards == ['', ''] or opp_cards == []) and not self.board_folds[i]:
                self.opp_fold_count += 1
            elif self.board_folds[i]:
                self.our_fold_count += 1
            if opp_cards != [] and opp_cards != ['', '']:
                card1_value = opp_cards[0][0]
                card2_value = opp_cards[1][0]
                card1_suit = opp_cards[0][1]
                card2_suit = opp_cards[1][1]
                if card1_suit == card2_suit:
                    suit_relation = 'same'

                else:
                    suit_relation = 'diff'
                if card1_value == card2_value:
                    card_pair_tup = (card1_value, card2_value)
                else:
                    card1_value_index = [i for i in range(len(self.card_val_order)) if
                                         self.card_val_order[i] == card1_value]
                    card2_value_index = [i for i in range(len(self.card_val_order)) if
                                         self.card_val_order[i] == card2_value]

                    if card1_value_index > card2_value_index:
                        card_pair_tup = (card2_value, card1_value, suit_relation)
                    else:
                        card_pair_tup = (card1_value, card2_value, suit_relation)

                pair_strength = self.hand_strengths[card_pair_tup]['win_prob'] + .5 * \
                                self.hand_strengths[card_pair_tup]['draw_prob'] + .015 * i
                self.opp_board_strengths[i].append(pair_strength)

            for bet, board in self.opp_bets_board[i]:
                opp_strength_at_bet = None
                if opp_cards != ['', '']:
                    _ITERS = 200
                    opp_strength_at_bet = self.calcualte_strength(opp_cards, _ITERS, board, [])
                self.opp_bets_strength = self.opp_bets_strength.append({'bet': bet, 'strength': opp_strength_at_bet}, ignore_index=True)

        self.board_allocations = [[], [], []] #reset our variables at the end of every round!
        self.hole_strengths = {0: [None] * NUM_BOARDS, 3: [None] * NUM_BOARDS, 4: [None] * NUM_BOARDS, 5: [None] * NUM_BOARDS}
        self.board_folds = [False, False, False]


        if round_num == NUM_ROUNDS:
            # print(self.opp_bets_strength[self.opp_bets_strength['strength'].notna()].sort_values(by='strength'))
            if not self.play_checkfold:
                print('opp post flop raise rate: ', self.opp_raise_rate)
                print('opp fold rate', self.opp_fold_rate)
                print('our fold rate', self.our_fold_rate)
                print('our showdown wins', self.our_showdown_wins)
                print('our showdown losses', self.our_showdown_losses)
                for i in range(3):
                    print('board #', i, ' opp avg strength:', sum(self.opp_board_strengths[i]) / len(self.opp_board_strengths[i]))
            print(game_clock)







    def get_bet_amount(self, strength, pot_size):
        bet_amount = -106.02197802198144 + 616.7786499215267*strength - 1310.2537938252638 * (strength ** 2) + 1206.0439560439938 * (strength ** 3)  - 405.54683411827534 * (strength ** 4)
        # print('-------')
        # print('assumed pot size: ', pot_size)
        # print('hand_strength: ', strength)
        # print('bet amount as % of pot:', bet_amount)
        bet_amount = min(1.1, bet_amount)
        bet_amount = max(0, bet_amount)
        bet_amount = bet_amount * pot_size
        # print('bet amount: ', bet_amount)
        return bet_amount

    def get_actions(self, game_state, round_state, active):
        '''
        Where the magic happens - your code should implement this function.
        Called any time the engine needs a triplet of actions from your bot.
        Arguments:
        game_state: the GameState object.
        round_state: the RoundState object.
        active: your player's index.
        Returns:
        Your actions.

        TODO: Add a checkfold strategy when we have accumulated enough of a lead that we can still end the game with more chips than the opponent by just giving away the blinds
        '''
        legal_actions = round_state.legal_actions()  # the actions you are allowed to take
        street = round_state.street  # 0, 3, 4, or 5 representing pre-flop, flop, turn, or river respectively
        my_cards = round_state.hands[active]  # your cards across all boards
        board_cards = [board_state.deck if isinstance(board_state, BoardState) else board_state.previous_state.deck for board_state in round_state.board_states] #the board cards
        my_pips = [board_state.pips[active] if isinstance(board_state, BoardState) else 0 for board_state in round_state.board_states] # the number of chips you have contributed to the pot on each board this round of betting
        opp_pips = [board_state.pips[1-active] if isinstance(board_state, BoardState) else 0 for board_state in round_state.board_states] # the number of chips your opponent has contributed to the pot on each board this round of betting
        continue_cost = [opp_pips[i] - my_pips[i] for i in range(NUM_BOARDS)] #the number of chips needed to stay in each board's pot
        my_stack = round_state.stacks[active]  # the number of chips you have remaining
        opp_stack = round_state.stacks[1-active]  # the number of chips your opponent has remaining
        stacks = [my_stack, opp_stack]
        net_upper_raise_bound = round_state.raise_bounds()[1] # max raise across 3 boards
        net_cost = 0 # keep track of the net additional amount you are spending across boards this round
        my_actions = [None] * NUM_BOARDS
        if self.play_checkfold:
            for i in range(NUM_BOARDS):
                if AssignAction in legal_actions[i]:
                    cards = self.board_allocations[i]  # allocate our cards that we made earlier
                    my_actions[i] = AssignAction(cards)  # add to our actions
                elif FoldAction in legal_actions[i]:
                    my_actions[i] = FoldAction()
                    self.board_folds[i] = True
                else:
                    my_actions[i] = CheckAction()
            return my_actions


        for i in range(NUM_BOARDS):
            if AssignAction in legal_actions[i]:
                cards = self.board_allocations[i] #allocate our cards that we made earlier
                my_actions[i] = AssignAction(cards) #add to our actions
            elif isinstance(round_state.board_states[i], TerminalState): #make sure the game isn't over at this board
                my_actions[i] = CheckAction() #check if it is

            else: #do we add more resources?

                # GET OPPONENTS LAST ACTION
                if continue_cost[i] > 0:
                    opp_last_action = 'Raise'
                elif round_state.board_states[i].settled:
                    opp_last_action = 'Call'
                    if game_state.round_num >= 3:
                        self.opp_post_flop_call_count += 1
                else:
                    opp_last_action = 'Check'  # OR FOLD BUT IF THEY FOLD WE WON


                if opp_last_action != 'Raise' and street >= 3:
                    self.opp_post_flop_no_raise_count += 1




                # STATS ABOUT THE BOARD
                board_total = round_state.board_states[i].pot  # amount before we started betting
                board_cont_cost = continue_cost[i]  # we need to pay this to keep playing
                pot_total = my_pips[i] + opp_pips[i] + board_total  # total money in the pot right now
                min_raise, max_raise = round_state.board_states[i].raise_bounds(active, round_state.stacks)

                if street == 0: #preflop
                    if active == 0: #we are small blind
                        if board_cont_cost == 1: #first action
                            if self.hole_strengths[0][i] < .39: # bottom of our range --> LIMP
                                my_actions[i] = FoldAction()
                                continue
                            elif self.hole_strengths[0][i] < .5: # bottom of our range --> LIMP
                                # my_actions[i] = FoldAction()
                                my_actions[i] = CallAction()
                                net_cost += board_cont_cost
                                continue
                            else: #we are going to open
                                if game_state.round_num < 30:
                                    raise_amount = 6
                                else:
                                    raise_amount = 6
                                    # raise_amount = self.get_open_raise_amount()
                                raise_amount = max([min_raise, raise_amount])  # make sure we have a valid raise
                                raise_amount = min([max_raise, raise_amount])
                                my_actions[i] = RaiseAction(raise_amount)
                                net_cost += raise_amount - my_pips[i]
                                # self.our_pre_flop_raise_count += 1
                                continue
                        else: #the opp raised from the big blind
                            self.opp_bb_raise_count += 1
                            pot_odds = board_cont_cost / (pot_total + board_cont_cost)
                            opp_raise_odds_offered = board_cont_cost / pot_total
                            raw_hand_strength = self.hole_strengths[0][i]
                            if self.opp_bb_raise_rate is not None:
                                hand_strength = raw_hand_strength - 2 * ((self.opp_bb_raise_rate) ** 2)
                            else:
                                hand_strength = raw_hand_strength - 2 * ((.2) ** 2)
                            if hand_strength >= pot_odds: # at least call
                                #TODO: Add raise all in (or 3 bet) if vey strong and opp showed aggression
                                if raw_hand_strength > .7: # raise
                                    raise_amount = (pot_total + board_cont_cost) * 2.5
                                    raise_amount = max([min_raise, raise_amount])  # make sure we have a valid raise
                                    raise_amount = min([max_raise, raise_amount])
                                    my_actions[i] = RaiseAction(raise_amount)
                                    net_cost += raise_amount - my_pips[i]
                                elif CallAction in legal_actions[i]: #call
                                    my_actions[i] = CallAction()
                                    net_cost += board_cont_cost
                                else:
                                    my_actions[i] = CheckAction()
                                continue
                            elif CheckAction in legal_actions[i]:
                                my_actions[i] = CheckAction()
                                continue
                            else:
                                my_actions[i] = FoldAction()
                                continue




                    else: # we are big blind
                        if board_cont_cost > 0: # opponent raised
                            self.opp_sb_raise_count += 1
                            pot_odds = board_cont_cost / (pot_total + board_cont_cost)
                            opp_raise_odds_offered = board_cont_cost / pot_total
                            raw_hand_strength = self.hole_strengths[0][i]
                            if self.opp_sb_raise_count is not None:
                                hand_strength = raw_hand_strength - 2 * ((self.opp_sb_raise_count) ** 2)
                            else:
                                hand_strength = raw_hand_strength - 2 * ((.2) ** 2)
                            if hand_strength >= pot_odds: # at least call
                                #TODO: Add raise all in (or 3 bet) if vey strong and opp showed aggression
                                raise_amount = (pot_total + board_cont_cost) * 2.5
                                raise_amount = max([min_raise, raise_amount])  # make sure we have a valid raise
                                raise_amount = min([max_raise, raise_amount])

                                raise_cost = raise_amount - my_pips[i]
                                if RaiseAction in legal_actions[i] and (raise_cost <= my_stack - net_cost) and raw_hand_strength > .7:
                                    my_actions[i] = RaiseAction(raise_amount)
                                    net_cost += raise_cost
                                elif CallAction in legal_actions[i]: #call
                                    my_actions[i] = CallAction()
                                    net_cost += board_cont_cost

                                else:
                                    my_actions[i] = CheckAction()
                                continue

                            else:
                                my_actions[i] = FoldAction()
                                continue


                        else: #opponenet called
                            self.opp_sb_call_count += 1
                            if self.hole_strengths[0][i] > .7:
                                raise_amount = 12
                                my_actions[i] = RaiseAction(raise_amount)
                                net_cost += raise_amount - my_pips[i]
                            elif self.hole_strengths[0][i] > random.random():
                                raise_amount = 12
                                my_actions[i] = RaiseAction(raise_amount)
                                net_cost += raise_amount - my_pips[i]
                            else:
                                my_actions[i] = CheckAction()
                            continue





                #recalculate our hand strength if we have not yet for this board
                if self.hole_strengths[street][i] is None:
                    NUM_ITERS = 100
                    hole_cards = self.board_allocations[i]
                    dead_cards = list(set(my_cards) - set(hole_cards))
                    hand_strength = self.calcualte_strength(hole_cards, NUM_ITERS, board_cards[i], dead_cards)
                    self.hole_strengths[street][i] = hand_strength
                else:
                    hand_strength = self.hole_strengths[street][i]

                raise_amount = int(pot_total * (1 + self.hole_strengths[street][i]))
                raise_amount = max([min_raise, raise_amount]) #make sure we have a valid raise
                raise_amount = min([max_raise, raise_amount])

                raise_cost = raise_amount - my_pips[i] #how much it costs to make that raise

                if RaiseAction in legal_actions[i] and (raise_cost <= my_stack - net_cost): #raise if we can and if we can afford it
                    commit_action = RaiseAction(raise_amount)
                    commit_cost = raise_cost

                elif CallAction in legal_actions[i]:
                    commit_action = CallAction()
                    commit_cost = board_cont_cost #the cost to call is board_cont_cost

                else: #checking is our only valid move here
                    commit_action = CheckAction()
                    commit_cost = 0


                if board_cont_cost > 0: #our opp raised!!! we must respond




                    pot_odds = board_cont_cost / (pot_total + board_cont_cost)
                    opp_raise_odds_offered = board_cont_cost / pot_total
                    if street >= 3:
                        self.opp_post_flop_raise_count += 1
                        self.opp_bets_board[i].append([opp_raise_odds_offered, board_cards[i]])
                    if street >= 3:
                        if game_state.round_num < 30:
                            if opp_last_action == 'Raise':
                                _INTIMIDATION = 0.2
                            elif opp_last_action == 'Call':
                                _INTIMIDATION = 0.07
                            else:
                                _INTIMIDATION = 0
                            previous_raise_agg_factor = (len(self.opp_bets_board[i]) - 1) * (
                                        .5 * np.exp(-10 * self.opp_raise_rate))
                            hand_strength = max([0, hand_strength - _INTIMIDATION - previous_raise_agg_factor])
                        else:
                            num_entries = min(55, len(self.opp_bets_strength))
                            raise_strength_series = self.opp_bets_strength.iloc[(self.opp_bets_strength['bet'] - opp_raise_odds_offered).abs().argsort()[:num_entries]]['strength']
                            median_raise_strength = raise_strength_series.median()
                            avg_raise_strength = raise_strength_series.mean()
                            previous_raise_agg_factor = (len(self.opp_bets_board[i]) - 1) * (.5 * np.exp(-10 * self.opp_raise_rate))
                            hand_strength = 1 - ((1 - hand_strength) ** ((2+(self.opp_raise_rate - .25))*(1- (avg_raise_strength + previous_raise_agg_factor))))


                    if hand_strength >= pot_odds: #Positive Expected Value!! at least call!!

                        if hand_strength > 0.5 and random.random() < hand_strength: #raise sometimes, more likely if our hand is strong
                            my_actions[i] = commit_action
                            net_cost += commit_cost
                            self.our_post_flop_raise_count += 1
                            continue

                        else: # at least call if we don't raise
                            my_actions[i] = CallAction()
                            net_cost += board_cont_cost
                            continue

                    else: #Negatice Expected Value!!! FOLD!!!
                        my_actions[i] = FoldAction()
                        self.board_folds[i] = True
                        net_cost += 0
                        continue

                else: #board_cont_cost == 0, we control the action
                    if self.opp_fold_rate > 0:
                        adj_stren = hand_strength + .5 * self.opp_fold_rate
                    else:
                        adj_stren = hand_strength
                    if random.random() < adj_stren: #raise sometimes, more likely if our hand is strong and if oppenent overfolds
                        my_actions[i] = commit_action
                        net_cost += commit_cost
                        self.our_post_flop_raise_count += 1

                    else: #just check otherwise
                        my_actions[i] = CheckAction()
                        net_cost += 0



        return my_actions


if __name__ == '__main__':
    run_bot(Player(), parse_args())
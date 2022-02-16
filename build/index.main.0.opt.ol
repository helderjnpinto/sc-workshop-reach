#lang ll
parts {
  "Alice" = interact {
    deadline = IT_Val UInt,
    getHand = IT_Fun [] UInt,
    informTimeout = IT_Fun [] Null,
    random = IT_Fun [] UInt,
    seeOutcome = IT_Fun [UInt] Null,
    wager = IT_Val UInt},
  "Bob" = interact {
    acceptWager = IT_Fun [UInt] Null,
    getHand = IT_Fun [] UInt,
    informTimeout = IT_Fun [] Null,
    random = IT_Fun [] UInt,
    seeOutcome = IT_Fun [UInt] Null}};

// maps
{
  }
// initialization

{
  }
{
  }
{
  }
{
  }
const v284* = {
  i = 0,
  sign = true};
const v286* = impossible(Cannot inspect value from `forall`);
const v287* = impossible(Cannot inspect value from `forall`);
const v288* = 4 - v287;
const v289* = v286 + v288;
const v290* = v289 % 3;
const v291* = 0 <= v290;
const v292* = v290 < 3;
const v293* = (v291 ? v292 : false);
claim(CT_Assert)(v293, Nothing);
const v294* = impossible(Cannot inspect value from `forall`);
const v295* = 4 - v294;
const v296* = v294 + v295;
const v297* = v296 % 3;
const v298* = v297 == 1;
claim(CT_Assert)(v298, Nothing);
only(Left "Alice") {
  const v299* = "Alice".interact.deadline;
  const v300* = "Alice".interact.wager;
   };
only(Left "Alice") {
  const v301* = selfAddress("Alice", False, 46 )();
  const v302* = null;
   };
publish(@0)
  .case("Alice").send({
    isClass = False,
    msg = [v300, v299],
    pay = [v300, ],
    when = true})
  .recv({
    didSend = v56,
    from = v303,
    msg = [v304, v305],
    secs = v307,
    time = v306}){
    timeOrder((Nothing, thisConsensusTime/306 ), (Nothing, thisConsensusSecs/307 ) );
    const v308* = 0;
    const v309* = wager/304;
    checkPay(wager/304, Nothing);
    const v310* = thisConsensusTime/306;
    const v311* = thisConsensusTime/306;
    const v312* = UInt.max - thisConsensusTime/306;
    const v313* = v312 - deadline/305;
    const v314* = v313 >= 0;
    const v315* = null;
    const v316* = thisConsensusTime/306 + deadline/305;
    const v317* = <Left v316>;
    commit();
    only(Left "Bob") {
      const v318* = selfAddress("Bob", False, 57 )();
      protect<Null>("Bob".interact.acceptWager(wager/304 ));
      const v319* = null;
       };
    publish(@thisConsensusTime/306)
      .timeout(Left v316, {
        publish(@thisConsensusTime/306)
          .case("Alice").send({
            isClass = False,
            msg = [],
            pay = [0, ],
            when = true})
          .case("Bob").send({
            isClass = False,
            msg = [],
            pay = [0, ],
            when = true})
          .recv({
            didSend = v260,
            from = v473,
            msg = [],
            secs = v475,
            time = v474}){
            timeOrder((Just thisConsensusTime/306, thisConsensusTime/474 ), (Just thisConsensusSecs/307, thisConsensusSecs/475 ) );
            const v476* = wager/304;
            checkPay(0, Nothing);
            const v477* = wager/304;
            const v478* = wager/304;
            const v479* = wager/304 <= wager/304;
            claim(CT_Assert)(v479, Just "balance sufficient for transfer");
            const v480* = wager/304;
            const v481* = wager/304 - wager/304;
            transfer.(wager/304, Nothing).to(v303);
            const v483* = v481;
            const v484* = 0 == v481;
            claim(CT_Assert)(v484, Just "balance zero at application exit");
            commit();
            only(Left "Alice") {
              const v485* = selfAddress("Alice", False, 267 )();
              protect<Null>("Alice".interact.informTimeout());
              const v486* = null;
               };
            only(Left "Bob") {
              const v487* = selfAddress("Bob", False, 270 )();
              protect<Null>("Bob".interact.informTimeout());
              const v488* = null;
               };
            const v482* = null;
            exit(); }
           } )
      .case("Bob").send({
        isClass = False,
        msg = [],
        pay = [wager/304, ],
        when = true})
      .recv({
        didSend = v65,
        from = v320,
        msg = [],
        secs = v322,
        time = v321}){
        timeOrder((Just thisConsensusTime/306, thisConsensusTime/321 ), (Just thisConsensusSecs/307, thisConsensusSecs/322 ) );
        const v323* = wager/304;
        const v324* = wager/304 + wager/304;
        checkPay(wager/304, Nothing);
        loopvar {
          v325 = 1,
          v326 = thisConsensusTime/321,
          v327 = thisConsensusTime/306,
          v328 = v316,
          v329 = thisConsensusSecs/322,
          v330 = thisConsensusSecs/307,
          v331 = thisConsensusSecs/307,
          v332 = v324};
        invariant{
          const v333* = balance(0)/332;
          const v334* = 2 * wager/304;
          const v335* = balance(0)/332 == v334;
          const v336* = 0 <= outcome/325;
          const v337* = outcome/325 < 3;
          const v338* = (v336 ? v337 : false);
          const v339* = (v335 ? v338 : false);
          
          return v339; }
        while{
          const v340* = outcome/325 == 1;
          
          return v340; }
        {
          const v341* = thisConsensusTime/326;
          const v342* = thisConsensusTime/326;
          const v343* = UInt.max - thisConsensusTime/326;
          const v344* = v343 - deadline/305;
          const v345* = v344 >= 0;
          const v346* = null;
          const v347* = thisConsensusTime/326 + deadline/305;
          const v348* = <Left v347>;
          commit();
          only(Left "Alice") {
            const v349* = selfAddress("Alice", False, 78 )();
            const v351* = protect<UInt>("Alice".interact.getHand());
            const v352* = protect<UInt>("Alice".interact.random());
            const v353* = digest(v352, v351 );
            const v354* = [v353, v352 ];
            const v350* = null;
             };
          publish(@thisConsensusTime/326)
            .timeout(Left v347, {
              publish(@thisConsensusTime/326)
                .case("Alice").send({
                  isClass = False,
                  msg = [],
                  pay = [0, ],
                  when = true})
                .case("Bob").send({
                  isClass = False,
                  msg = [],
                  pay = [0, ],
                  when = true})
                .recv({
                  didSend = v212,
                  from = v438,
                  msg = [],
                  secs = v440,
                  time = v439}){
                  timeOrder((Just thisConsensusTime/326, thisConsensusTime/439 ), (Just thisConsensusSecs/329, thisConsensusSecs/440 ) );
                  const v441* = balance(0)/332;
                  checkPay(0, Nothing);
                  const v442* = v303 == v438;
                  const v443* = v320 == v438;
                  const v444* = (v442 ? true : v443);
                  claim(CT_Require)(v444, Just "sender correct");
                  const v445* = balance(0)/332;
                  const v446* = balance(0)/332;
                  const v447* = balance(0)/332 <= balance(0)/332;
                  claim(CT_Assert)(v447, Just "balance sufficient for transfer");
                  const v448* = balance(0)/332;
                  const v449* = balance(0)/332 - balance(0)/332;
                  transfer.(balance(0)/332, Nothing).to(v320);
                  const v451* = v449;
                  const v452* = 0 == v449;
                  claim(CT_Assert)(v452, Just "balance zero at application exit");
                  commit();
                  only(Left "Alice") {
                    const v453* = selfAddress("Alice", False, 219 )();
                    protect<Null>("Alice".interact.informTimeout());
                    const v454* = null;
                     };
                  only(Left "Bob") {
                    const v455* = selfAddress("Bob", False, 222 )();
                    protect<Null>("Bob".interact.informTimeout());
                    const v456* = null;
                     };
                  const v450* = null;
                  exit(); }
                 } )
            .case("Alice").send({
              isClass = False,
              msg = [v353],
              pay = [0, ],
              when = true})
            .recv({
              didSend = v92,
              from = v355,
              msg = [v356],
              secs = v358,
              time = v357}){
              timeOrder((Just thisConsensusTime/326, thisConsensusTime/357 ), (Just thisConsensusSecs/329, thisConsensusSecs/358 ) );
              const v359* = balance(0)/332;
              checkPay(0, Nothing);
              const v360* = v303 == v355;
              claim(CT_Require)(v360, Just "sender correct");
              claim(CT_Unknowable "Bob" [DLA_Var v351,DLA_Var v352])(false, Nothing);
              const v361* = thisConsensusTime/357;
              const v362* = thisConsensusTime/357;
              const v363* = UInt.max - thisConsensusTime/357;
              const v364* = v363 - deadline/305;
              const v365* = v364 >= 0;
              const v366* = null;
              const v367* = thisConsensusTime/357 + deadline/305;
              const v368* = <Left v367>;
              commit();
              only(Left "Bob") {
                const v369* = selfAddress("Bob", False, 93 )();
                const v371* = protect<UInt>("Bob".interact.getHand());
                const v370* = null;
                 };
              publish(@thisConsensusTime/357)
                .timeout(Left v367, {
                  publish(@thisConsensusTime/357)
                    .case("Alice").send({
                      isClass = False,
                      msg = [],
                      pay = [0, ],
                      when = true})
                    .case("Bob").send({
                      isClass = False,
                      msg = [],
                      pay = [0, ],
                      when = true})
                    .recv({
                      didSend = v177,
                      from = v419,
                      msg = [],
                      secs = v421,
                      time = v420}){
                      timeOrder((Just thisConsensusTime/357, thisConsensusTime/420 ), (Just thisConsensusSecs/358, thisConsensusSecs/421 ) );
                      const v422* = balance(0)/332;
                      checkPay(0, Nothing);
                      const v423* = v303 == v419;
                      const v424* = v320 == v419;
                      const v425* = (v423 ? true : v424);
                      claim(CT_Require)(v425, Just "sender correct");
                      const v426* = balance(0)/332;
                      const v427* = balance(0)/332;
                      const v428* = balance(0)/332 <= balance(0)/332;
                      claim(CT_Assert)(v428, Just "balance sufficient for transfer");
                      const v429* = balance(0)/332;
                      const v430* = balance(0)/332 - balance(0)/332;
                      transfer.(balance(0)/332, Nothing).to(v303);
                      const v432* = v430;
                      const v433* = 0 == v430;
                      claim(CT_Assert)(v433, Just "balance zero at application exit");
                      commit();
                      only(Left "Alice") {
                        const v434* = selfAddress("Alice", False, 184 )();
                        protect<Null>("Alice".interact.informTimeout());
                        const v435* = null;
                         };
                      only(Left "Bob") {
                        const v436* = selfAddress("Bob", False, 187 )();
                        protect<Null>("Bob".interact.informTimeout());
                        const v437* = null;
                         };
                      const v431* = null;
                      exit(); }
                     } )
                .case("Bob").send({
                  isClass = False,
                  msg = [v371],
                  pay = [0, ],
                  when = true})
                .recv({
                  didSend = v103,
                  from = v372,
                  msg = [v373],
                  secs = v375,
                  time = v374}){
                  timeOrder((Just thisConsensusTime/357, thisConsensusTime/374 ), (Just thisConsensusSecs/358, thisConsensusSecs/375 ) );
                  const v376* = balance(0)/332;
                  checkPay(0, Nothing);
                  const v377* = v320 == v372;
                  claim(CT_Require)(v377, Just "sender correct");
                  const v378* = thisConsensusTime/374;
                  const v379* = thisConsensusTime/374;
                  const v380* = UInt.max - thisConsensusTime/374;
                  const v381* = v380 - deadline/305;
                  const v382* = v381 >= 0;
                  const v383* = null;
                  const v384* = thisConsensusTime/374 + deadline/305;
                  const v385* = <Left v384>;
                  commit();
                  only(Left "Alice") {
                    const v386* = selfAddress("Alice", False, 104 )();
                    const v387* = null;
                     };
                  publish(@thisConsensusTime/374)
                    .timeout(Left v384, {
                      publish(@thisConsensusTime/374)
                        .case("Alice").send({
                          isClass = False,
                          msg = [],
                          pay = [0, ],
                          when = true})
                        .case("Bob").send({
                          isClass = False,
                          msg = [],
                          pay = [0, ],
                          when = true})
                        .recv({
                          didSend = v142,
                          from = v400,
                          msg = [],
                          secs = v402,
                          time = v401}){
                          timeOrder((Just thisConsensusTime/374, thisConsensusTime/401 ), (Just thisConsensusSecs/375, thisConsensusSecs/402 ) );
                          const v403* = balance(0)/332;
                          checkPay(0, Nothing);
                          const v404* = v303 == v400;
                          const v405* = v320 == v400;
                          const v406* = (v404 ? true : v405);
                          claim(CT_Require)(v406, Just "sender correct");
                          const v407* = balance(0)/332;
                          const v408* = balance(0)/332;
                          const v409* = balance(0)/332 <= balance(0)/332;
                          claim(CT_Assert)(v409, Just "balance sufficient for transfer");
                          const v410* = balance(0)/332;
                          const v411* = balance(0)/332 - balance(0)/332;
                          transfer.(balance(0)/332, Nothing).to(v320);
                          const v413* = v411;
                          const v414* = 0 == v411;
                          claim(CT_Assert)(v414, Just "balance zero at application exit");
                          commit();
                          only(Left "Alice") {
                            const v415* = selfAddress("Alice", False, 149 )();
                            protect<Null>("Alice".interact.informTimeout());
                            const v416* = null;
                             };
                          only(Left "Bob") {
                            const v417* = selfAddress("Bob", False, 152 )();
                            protect<Null>("Bob".interact.informTimeout());
                            const v418* = null;
                             };
                          const v412* = null;
                          exit(); }
                         } )
                    .case("Alice").send({
                      isClass = False,
                      msg = [v352, v351],
                      pay = [0, ],
                      when = true})
                    .recv({
                      didSend = v114,
                      from = v388,
                      msg = [v389, v390],
                      secs = v392,
                      time = v391}){
                      timeOrder((Just thisConsensusTime/374, thisConsensusTime/391 ), (Just thisConsensusSecs/375, thisConsensusSecs/392 ) );
                      const v393* = balance(0)/332;
                      checkPay(0, Nothing);
                      const v394* = v303 == v388;
                      claim(CT_Require)(v394, Just "sender correct");
                      const v395* = digest(saltAlice/389, handAlice/390 );
                      const v396* = commitAlice/356 == v395;
                      claim(CT_Require)(v396, Nothing);
                      const v397* = 4 - handBob/373;
                      const v398* = handAlice/390 + v397;
                      const v399* = v398 % 3;
                      {
                        v325 = v399,
                        v326 = thisConsensusTime/391,
                        v327 = thisConsensusTime/374,
                        v328 = v384,
                        v329 = thisConsensusSecs/392,
                        v330 = thisConsensusSecs/375,
                        v331 = thisConsensusSecs/375,
                        v332 = balance(0)/332}
                      continue; }
                     }
                 }
             }
        const v457* = outcome/325 == 2;
        const v458* = outcome/325 == 0;
        const v459* = (v457 ? true : v458);
        claim(CT_Assert)(v459, Nothing);
        const v460* = 2 * wager/304;
        const v462* = (v457 ? v303 : v320);
        const v463* = balance(0)/332;
        const v464* = v460 <= balance(0)/332;
        claim(CT_Assert)(v464, Just "balance sufficient for transfer");
        const v465* = balance(0)/332;
        const v466* = balance(0)/332 - v460;
        transfer.(v460, Nothing).to(v462);
        const v467* = v466;
        const v468* = 0 == v466;
        claim(CT_Assert)(v468, Just "balance zero at application exit");
        commit();
        only(Left "Alice") {
          const v469* = selfAddress("Alice", False, 237 )();
          protect<Null>("Alice".interact.seeOutcome(outcome/325 ));
          const v470* = null;
           };
        only(Left "Bob") {
          const v471* = selfAddress("Bob", False, 240 )();
          protect<Null>("Bob".interact.seeOutcome(outcome/325 ));
          const v472* = null;
           };
        exit(); }
       }
  
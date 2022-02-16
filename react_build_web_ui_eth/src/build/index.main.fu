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
const v285* = {
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
only(Left "Bob") {
   };
only(Left "Alice") {
  const v301* = selfAddress("Alice", False, 46 )();
  let v302;
  v302 = null;
   };
only(Left "Alice") {
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
    timeOrder((None, thisConsensusTime/306 ), (None, thisConsensusSecs/307 ) );
    const v308* = 0;
    const v309* = balance(0)/308 + wager/304;
    checkPay(wager/304, None);
    const v310* = thisConsensusTime/306;
    const v311* = thisConsensusTime/306;
    const v312* = UInt.max - baseWaitTime/311;
    const v313* = v312 - deadline/305;
    const v314* = v313 >= 0;
    let v315;
    v315 = null;
    const v316* = baseWaitTime/310 + deadline/305;
    const v317* = <Left v316>;
    commit();
    only(Left "Bob") {
      const v318* = selfAddress("Bob", False, 57 )();
      let v319;
      protect<Null>("Bob".interact.acceptWager(wager/304 ));
      v319 = null;
       };
    only(Left "Bob") {
       };
    publish(@thisConsensusTime/306)
      .timeout(Left v316, {
        only(Left "Alice") {
           };
        only(Left "Bob") {
           };
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
            timeOrder((Some thisConsensusTime/306, thisConsensusTime/474 ), (Some thisConsensusSecs/307, thisConsensusSecs/475 ) );
            const v476* = v309;
            checkPay(0, None);
            const v477* = balance(0)/476;
            const v478* = balance(0)/476;
            const v479* = balance(0)/477 <= balance(0)/478;
            claim(CT_Assert)(v479, Just "balance sufficient for transfer");
            const v480* = balance(0)/476;
            const v481* = balance(0)/480 - balance(0)/477;
            transfer.(balance(0)/477, None).to(v303);
            let v482;
            const v483* = v481;
            const v484* = 0 == balance(0)/483;
            claim(CT_Assert)(v484, Just "balance zero at application exit");
            commit();
            only(Left "Alice") {
              const v485* = selfAddress("Alice", False, 267 )();
              let v486;
              protect<Null>("Alice".interact.informTimeout());
              v486 = null;
               };
            only(Left "Bob") {
              const v487* = selfAddress("Bob", False, 270 )();
              let v488;
              protect<Null>("Bob".interact.informTimeout());
              v488 = null;
               };
            v482 = null;
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
        timeOrder((Some thisConsensusTime/306, thisConsensusTime/321 ), (Some thisConsensusSecs/307, thisConsensusSecs/322 ) );
        const v323* = v309;
        const v324* = balance(0)/323 + wager/304;
        checkPay(wager/304, None);
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
          const v335* = balance(0)/333 == v334;
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
          const v343* = UInt.max - baseWaitTime/342;
          const v344* = v343 - deadline/305;
          const v345* = v344 >= 0;
          let v346;
          v346 = null;
          const v347* = baseWaitTime/341 + deadline/305;
          const v348* = <Left v347>;
          commit();
          only(Left "Alice") {
            const v349* = selfAddress("Alice", False, 78 )();
            let v350;
            const v351* = protect<UInt>("Alice".interact.getHand());
            const v352* = protect<UInt>("Alice".interact.random());
            const v353* = digest(v352, v351 );
            const v354* = [v353, v352 ];
            v350 = null;
             };
          only(Left "Alice") {
             };
          publish(@thisConsensusTime/326)
            .timeout(Left v347, {
              only(Left "Alice") {
                 };
              only(Left "Bob") {
                 };
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
                  timeOrder((Some thisConsensusTime/326, thisConsensusTime/439 ), (Some thisConsensusSecs/329, thisConsensusSecs/440 ) );
                  const v441* = balance(0)/332;
                  checkPay(0, None);
                  const v442* = v303 == v438;
                  const v443* = v320 == v438;
                  const v444* = (v442 ? true : v443);
                  claim(CT_Require)(v444, Just "sender correct");
                  const v445* = balance(0)/441;
                  const v446* = balance(0)/441;
                  const v447* = balance(0)/445 <= balance(0)/446;
                  claim(CT_Assert)(v447, Just "balance sufficient for transfer");
                  const v448* = balance(0)/441;
                  const v449* = balance(0)/448 - balance(0)/445;
                  transfer.(balance(0)/445, None).to(v320);
                  let v450;
                  const v451* = v449;
                  const v452* = 0 == balance(0)/451;
                  claim(CT_Assert)(v452, Just "balance zero at application exit");
                  commit();
                  only(Left "Alice") {
                    const v453* = selfAddress("Alice", False, 219 )();
                    let v454;
                    protect<Null>("Alice".interact.informTimeout());
                    v454 = null;
                     };
                  only(Left "Bob") {
                    const v455* = selfAddress("Bob", False, 222 )();
                    let v456;
                    protect<Null>("Bob".interact.informTimeout());
                    v456 = null;
                     };
                  v450 = null;
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
              timeOrder((Some thisConsensusTime/326, thisConsensusTime/357 ), (Some thisConsensusSecs/329, thisConsensusSecs/358 ) );
              const v359* = balance(0)/332;
              checkPay(0, None);
              const v360* = v303 == v355;
              claim(CT_Require)(v360, Just "sender correct");
              claim(CT_Unknowable "Bob" [DLA_Var v351,DLA_Var v352])(false, Nothing);
              const v361* = thisConsensusTime/357;
              const v362* = thisConsensusTime/357;
              const v363* = UInt.max - baseWaitTime/362;
              const v364* = v363 - deadline/305;
              const v365* = v364 >= 0;
              let v366;
              v366 = null;
              const v367* = baseWaitTime/361 + deadline/305;
              const v368* = <Left v367>;
              commit();
              only(Left "Bob") {
                const v369* = selfAddress("Bob", False, 93 )();
                let v370;
                const v371* = protect<UInt>("Bob".interact.getHand());
                v370 = null;
                 };
              only(Left "Bob") {
                 };
              publish(@thisConsensusTime/357)
                .timeout(Left v367, {
                  only(Left "Alice") {
                     };
                  only(Left "Bob") {
                     };
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
                      timeOrder((Some thisConsensusTime/357, thisConsensusTime/420 ), (Some thisConsensusSecs/358, thisConsensusSecs/421 ) );
                      const v422* = balance(0)/359;
                      checkPay(0, None);
                      const v423* = v303 == v419;
                      const v424* = v320 == v419;
                      const v425* = (v423 ? true : v424);
                      claim(CT_Require)(v425, Just "sender correct");
                      const v426* = balance(0)/422;
                      const v427* = balance(0)/422;
                      const v428* = balance(0)/426 <= balance(0)/427;
                      claim(CT_Assert)(v428, Just "balance sufficient for transfer");
                      const v429* = balance(0)/422;
                      const v430* = balance(0)/429 - balance(0)/426;
                      transfer.(balance(0)/426, None).to(v303);
                      let v431;
                      const v432* = v430;
                      const v433* = 0 == balance(0)/432;
                      claim(CT_Assert)(v433, Just "balance zero at application exit");
                      commit();
                      only(Left "Alice") {
                        const v434* = selfAddress("Alice", False, 184 )();
                        let v435;
                        protect<Null>("Alice".interact.informTimeout());
                        v435 = null;
                         };
                      only(Left "Bob") {
                        const v436* = selfAddress("Bob", False, 187 )();
                        let v437;
                        protect<Null>("Bob".interact.informTimeout());
                        v437 = null;
                         };
                      v431 = null;
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
                  timeOrder((Some thisConsensusTime/357, thisConsensusTime/374 ), (Some thisConsensusSecs/358, thisConsensusSecs/375 ) );
                  const v376* = balance(0)/359;
                  checkPay(0, None);
                  const v377* = v320 == v372;
                  claim(CT_Require)(v377, Just "sender correct");
                  const v378* = thisConsensusTime/374;
                  const v379* = thisConsensusTime/374;
                  const v380* = UInt.max - baseWaitTime/379;
                  const v381* = v380 - deadline/305;
                  const v382* = v381 >= 0;
                  let v383;
                  v383 = null;
                  const v384* = baseWaitTime/378 + deadline/305;
                  const v385* = <Left v384>;
                  commit();
                  only(Left "Alice") {
                    const v386* = selfAddress("Alice", False, 104 )();
                    let v387;
                    v387 = null;
                     };
                  only(Left "Alice") {
                     };
                  publish(@thisConsensusTime/374)
                    .timeout(Left v384, {
                      only(Left "Alice") {
                         };
                      only(Left "Bob") {
                         };
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
                          timeOrder((Some thisConsensusTime/374, thisConsensusTime/401 ), (Some thisConsensusSecs/375, thisConsensusSecs/402 ) );
                          const v403* = balance(0)/376;
                          checkPay(0, None);
                          const v404* = v303 == v400;
                          const v405* = v320 == v400;
                          const v406* = (v404 ? true : v405);
                          claim(CT_Require)(v406, Just "sender correct");
                          const v407* = balance(0)/403;
                          const v408* = balance(0)/403;
                          const v409* = balance(0)/407 <= balance(0)/408;
                          claim(CT_Assert)(v409, Just "balance sufficient for transfer");
                          const v410* = balance(0)/403;
                          const v411* = balance(0)/410 - balance(0)/407;
                          transfer.(balance(0)/407, None).to(v320);
                          let v412;
                          const v413* = v411;
                          const v414* = 0 == balance(0)/413;
                          claim(CT_Assert)(v414, Just "balance zero at application exit");
                          commit();
                          only(Left "Alice") {
                            const v415* = selfAddress("Alice", False, 149 )();
                            let v416;
                            protect<Null>("Alice".interact.informTimeout());
                            v416 = null;
                             };
                          only(Left "Bob") {
                            const v417* = selfAddress("Bob", False, 152 )();
                            let v418;
                            protect<Null>("Bob".interact.informTimeout());
                            v418 = null;
                             };
                          v412 = null;
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
                      timeOrder((Some thisConsensusTime/374, thisConsensusTime/391 ), (Some thisConsensusSecs/375, thisConsensusSecs/392 ) );
                      const v393* = balance(0)/376;
                      checkPay(0, None);
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
                        v332 = balance(0)/393}
                      continue; }
                     }
                 }
             }
        const v457* = outcome/325 == 2;
        const v458* = outcome/325 == 0;
        const v459* = (v457 ? true : v458);
        claim(CT_Assert)(v459, Nothing);
        const v460* = 2 * wager/304;
        const v461* = outcome/325 == 2;
        const v462* = (v461 ? v303 : v320);
        const v463* = balance(0)/332;
        const v464* = v460 <= balance(0)/463;
        claim(CT_Assert)(v464, Just "balance sufficient for transfer");
        const v465* = balance(0)/332;
        const v466* = balance(0)/465 - v460;
        transfer.(v460, None).to(v462);
        const v467* = v466;
        const v468* = 0 == balance(0)/467;
        claim(CT_Assert)(v468, Just "balance zero at application exit");
        commit();
        only(Left "Alice") {
          const v469* = selfAddress("Alice", False, 237 )();
          let v470;
          protect<Null>("Alice".interact.seeOutcome(outcome/325 ));
          v470 = null;
           };
        only(Left "Bob") {
          const v471* = selfAddress("Bob", False, 240 )();
          let v472;
          protect<Null>("Bob".interact.seeOutcome(outcome/325 ));
          v472 = null;
           };
        exit(); }
       }
  
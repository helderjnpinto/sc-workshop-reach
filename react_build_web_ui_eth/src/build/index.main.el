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
only(Left "Alice") {
  const v299! = "Alice".interact.deadline;
  const v300* = "Alice".interact.wager;
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
    checkPay(wager/304, None);
    const v316* = thisConsensusTime/306 + deadline/305;
    commit();
    only(Left "Bob") {
      protect<Null>("Bob".interact.acceptWager(wager/304 ));
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
            checkPay(0, None);
            transfer.(wager/304, None).to(v303);
            commit();
            only(Left "Alice") {
              protect<Null>("Alice".interact.informTimeout());
               };
            only(Left "Bob") {
              protect<Null>("Bob".interact.informTimeout());
               };
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
        const v324! = wager/304 + wager/304;
        checkPay(wager/304, None);
        loopvar {
          v325 = 1,
          v326 = thisConsensusTime/321,
          v332 = v324};
        invariant{
          
          return null; }
        while{
          const v340! = outcome/325 == 1;
          
          return v340; }
        {
          const v347! = thisConsensusTime/326 + deadline/305;
          commit();
          only(Left "Alice") {
            const v351* = protect<UInt>("Alice".interact.getHand());
            const v352* = protect<UInt>("Alice".interact.random());
            const v353! = digest(v352, v351 );
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
                  checkPay(0, None);
                  const v442! = v303 == v438;
                  const v443! = v320 == v438;
                  const v444! = (v442 ? true : v443);
                  claim(CT_Require)(v444, Just "sender correct");
                  transfer.(balance(0)/332, None).to(v320);
                  commit();
                  only(Left "Alice") {
                    protect<Null>("Alice".interact.informTimeout());
                     };
                  only(Left "Bob") {
                    protect<Null>("Bob".interact.informTimeout());
                     };
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
              checkPay(0, None);
              const v360! = v303 == v355;
              claim(CT_Require)(v360, Just "sender correct");
              const v367! = thisConsensusTime/357 + deadline/305;
              commit();
              only(Left "Bob") {
                const v371* = protect<UInt>("Bob".interact.getHand());
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
                      checkPay(0, None);
                      const v423! = v303 == v419;
                      const v424! = v320 == v419;
                      const v425! = (v423 ? true : v424);
                      claim(CT_Require)(v425, Just "sender correct");
                      transfer.(balance(0)/332, None).to(v303);
                      commit();
                      only(Left "Alice") {
                        protect<Null>("Alice".interact.informTimeout());
                         };
                      only(Left "Bob") {
                        protect<Null>("Bob".interact.informTimeout());
                         };
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
                  checkPay(0, None);
                  const v377! = v320 == v372;
                  claim(CT_Require)(v377, Just "sender correct");
                  const v384* = thisConsensusTime/374 + deadline/305;
                  commit();
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
                          checkPay(0, None);
                          const v404! = v303 == v400;
                          const v405! = v320 == v400;
                          const v406! = (v404 ? true : v405);
                          claim(CT_Require)(v406, Just "sender correct");
                          transfer.(balance(0)/332, None).to(v320);
                          commit();
                          only(Left "Alice") {
                            protect<Null>("Alice".interact.informTimeout());
                             };
                          only(Left "Bob") {
                            protect<Null>("Bob".interact.informTimeout());
                             };
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
                      checkPay(0, None);
                      const v394! = v303 == v388;
                      claim(CT_Require)(v394, Just "sender correct");
                      const v395! = digest(saltAlice/389, handAlice/390 );
                      const v396! = commitAlice/356 == v395;
                      claim(CT_Require)(v396, Nothing);
                      const v397! = 4 - handBob/373;
                      const v398! = handAlice/390 + v397;
                      const v399! = v398 % 3;
                      {
                        v325 = v399,
                        v326 = thisConsensusTime/391,
                        v332 = balance(0)/332}
                      continue; }
                     }
                 }
             }
        const v457* = outcome/325 == 2;
        const v460* = 2 * wager/304;
        const v462! = (v457 ? v303 : v320);
        transfer.(v460, None).to(v462);
        commit();
        only(Left "Alice") {
          protect<Null>("Alice".interact.seeOutcome(outcome/325 ));
           };
        only(Left "Bob") {
          protect<Null>("Bob".interact.seeOutcome(outcome/325 ));
           };
        exit(); }
       }
  
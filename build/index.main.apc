#lang pl
{
  }
// maps
{
  }
// initialization

APIs:{
  }
{
  "Alice" = interact {
    deadline = IT_Val UInt,
    getHand = IT_Fun [] UInt,
    informTimeout = IT_Fun [] Null,
    random = IT_Fun [] UInt,
    seeOutcome = IT_Fun [UInt] Null,
    wager = IT_Val UInt};
  only(Right False) {
    const v299! = "Alice".interact.deadline;
    const v300* = "Alice".interact.wager;
     };
  send({
    amt = [v300, ],
    as = (v300, v299 ),
    saved = (),
    soloSend = True,
    when = true,
    which = 0})
  recv({
    didSendv = v56,
    from = v303,
    lct = Just 0,
    msg = (v304, v305 ),
    out = (),
    prev = 0,
    secsv = v307,
    timev = v306,
    which = 0})
  {
    checkPay(wager/304, Nothing);
    const v316! = thisConsensusTime/306 + deadline/305;
    fromConsensus 1 (continue [(v303, v303), (v304, wager/304), (v305, deadline/305), (v316, v316)]) ;
    recv({
      didSendv = v65,
      from = v320,
      lct = Just thisConsensusTime/306,
      msg = (),
      out = (),
      prev = 1,
      secsv = v322,
      timev = v321,
      which = 1})
    timeout(Just Left v316, {
      send({
        amt = [0, ],
        as = (),
        saved = (v303, v304, v305, v316 ),
        soloSend = False,
        when = true,
        which = 2})
      recv({
        didSendv = v260,
        from = v473,
        lct = Just thisConsensusTime/306,
        msg = (),
        out = (),
        prev = 1,
        secsv = v475,
        timev = v474,
        which = 2})
      {
        checkPay(0, Nothing);
        transfer.(wager/304, Nothing).to(v303);
        fromConsensus 2 (halt []) ;
        only(Right False) {
          protect<Null>("Alice".interact.informTimeout());
           };
         } } )
    {
      const v324! = wager/304 + wager/304;
      checkPay(wager/304, Nothing);
      loopvar {
        v325 = 1,
        v326 = thisConsensusTime/321,
        v332 = v324};
      invariant{
        () }
      while{
        const v340! = outcome/325 == 1;
        
        return v340; }
      {
        const v347! = thisConsensusTime/326 + deadline/305;
        fromConsensus 5 (continue [(v303, v303), (v304, wager/304), (v305, deadline/305), (v320, v320), (v332, balance(0)/332), (v347, v347)]) ;
        only(Right False) {
          const v351* = protect<UInt>("Alice".interact.getHand());
          const v352* = protect<UInt>("Alice".interact.random());
          const v353! = digest(v352, v351 );
           };
        send({
          amt = [0, ],
          as = (v353 ),
          saved = (v303, v304, v305, v320, v332, v347 ),
          soloSend = True,
          when = true,
          which = 4})
        recv({
          didSendv = v92,
          from = v355,
          lct = Just thisConsensusTime/326,
          msg = (v356 ),
          out = (),
          prev = 5,
          secsv = v358,
          timev = v357,
          which = 4})
        timeout(Just Left v347, {
          send({
            amt = [0, ],
            as = (),
            saved = (v303, v304, v305, v320, v332, v347 ),
            soloSend = False,
            when = true,
            which = 5})
          recv({
            didSendv = v212,
            from = v438,
            lct = Just thisConsensusTime/326,
            msg = (),
            out = (),
            prev = 5,
            secsv = v440,
            timev = v439,
            which = 5})
          {
            checkPay(0, Nothing);
            const v442! = v303 == v438;
            const v443! = v320 == v438;
            const v444! = (v442 ? true : v443);
            claim(CT_Require)(v444, Just "sender correct");
            transfer.(balance(0)/332, Nothing).to(v320);
            fromConsensus 6 (halt []) ;
            only(Right False) {
              protect<Null>("Alice".interact.informTimeout());
               };
             } } )
        {
          checkPay(0, Nothing);
          const v360! = v303 == v355;
          claim(CT_Require)(v360, Just "sender correct");
          const v367! = thisConsensusTime/357 + deadline/305;
          fromConsensus 7 (continue [(v303, v303), (v304, wager/304), (v305, deadline/305), (v320, v320), (v332, balance(0)/332), (v356, commitAlice/356), (v367, v367)]) ;
          recv({
            didSendv = v103,
            from = v372,
            lct = Just thisConsensusTime/357,
            msg = (v373 ),
            out = (),
            prev = 7,
            secsv = v375,
            timev = v374,
            which = 6})
          timeout(Just Left v367, {
            send({
              amt = [0, ],
              as = (),
              saved = (v303, v304, v305, v320, v332, v356, v367 ),
              soloSend = False,
              when = true,
              which = 7})
            recv({
              didSendv = v177,
              from = v419,
              lct = Just thisConsensusTime/357,
              msg = (),
              out = (),
              prev = 7,
              secsv = v421,
              timev = v420,
              which = 7})
            {
              checkPay(0, Nothing);
              const v423! = v303 == v419;
              const v424! = v320 == v419;
              const v425! = (v423 ? true : v424);
              claim(CT_Require)(v425, Just "sender correct");
              transfer.(balance(0)/332, Nothing).to(v303);
              fromConsensus 8 (halt []) ;
              only(Right False) {
                protect<Null>("Alice".interact.informTimeout());
                 };
               } } )
          {
            checkPay(0, Nothing);
            const v377! = v320 == v372;
            claim(CT_Require)(v377, Just "sender correct");
            const v384! = thisConsensusTime/374 + deadline/305;
            fromConsensus 9 (continue [(v303, v303), (v304, wager/304), (v305, deadline/305), (v320, v320), (v332, balance(0)/332), (v356, commitAlice/356), (v373, handBob/373), (v384, v384)]) ;
            send({
              amt = [0, ],
              as = (v352, v351 ),
              saved = (v303, v304, v305, v320, v332, v356, v373, v384 ),
              soloSend = True,
              when = true,
              which = 8})
            recv({
              didSendv = v114,
              from = v388,
              lct = Just thisConsensusTime/374,
              msg = (v389, v390 ),
              out = (),
              prev = 9,
              secsv = v392,
              timev = v391,
              which = 8})
            timeout(Just Left v384, {
              send({
                amt = [0, ],
                as = (),
                saved = (v303, v304, v305, v320, v332, v356, v373, v384 ),
                soloSend = False,
                when = true,
                which = 9})
              recv({
                didSendv = v142,
                from = v400,
                lct = Just thisConsensusTime/374,
                msg = (),
                out = (),
                prev = 9,
                secsv = v402,
                timev = v401,
                which = 9})
              {
                checkPay(0, Nothing);
                const v404! = v303 == v400;
                const v405! = v320 == v400;
                const v406! = (v404 ? true : v405);
                claim(CT_Require)(v406, Just "sender correct");
                transfer.(balance(0)/332, Nothing).to(v320);
                fromConsensus 10 (halt []) ;
                only(Right False) {
                  protect<Null>("Alice".interact.informTimeout());
                   };
                 } } )
            {
              checkPay(0, Nothing);
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
              continue; } } } }
      const v457! = outcome/325 == 2;
      const v460! = 2 * wager/304;
      const v462! = (v457 ? v303 : v320);
      transfer.(v460, Nothing).to(v462);
      fromConsensus 4 (halt []) ;
      only(Right False) {
        protect<Null>("Alice".interact.seeOutcome(outcome/325 ));
         };
       } },
  "Bob" = interact {
    acceptWager = IT_Fun [UInt] Null,
    getHand = IT_Fun [] UInt,
    informTimeout = IT_Fun [] Null,
    random = IT_Fun [] UInt,
    seeOutcome = IT_Fun [UInt] Null};
  recv({
    didSendv = v56,
    from = v303,
    lct = Just 0,
    msg = (v304, v305 ),
    out = (),
    prev = 0,
    secsv = v307,
    timev = v306,
    which = 0})
  {
    checkPay(wager/304, Nothing);
    const v316! = thisConsensusTime/306 + deadline/305;
    fromConsensus 1 (continue [(v303, v303), (v304, wager/304), (v305, deadline/305), (v316, v316)]) ;
    only(Right False) {
      protect<Null>("Bob".interact.acceptWager(wager/304 ));
       };
    send({
      amt = [wager/304, ],
      as = (),
      saved = (v303, v304, v305, v316 ),
      soloSend = True,
      when = true,
      which = 1})
    recv({
      didSendv = v65,
      from = v320,
      lct = Just thisConsensusTime/306,
      msg = (),
      out = (),
      prev = 1,
      secsv = v322,
      timev = v321,
      which = 1})
    timeout(Just Left v316, {
      send({
        amt = [0, ],
        as = (),
        saved = (v303, v304, v305, v316 ),
        soloSend = False,
        when = true,
        which = 2})
      recv({
        didSendv = v260,
        from = v473,
        lct = Just thisConsensusTime/306,
        msg = (),
        out = (),
        prev = 1,
        secsv = v475,
        timev = v474,
        which = 2})
      {
        checkPay(0, Nothing);
        transfer.(wager/304, Nothing).to(v303);
        fromConsensus 2 (halt []) ;
        only(Right False) {
          protect<Null>("Bob".interact.informTimeout());
           };
         } } )
    {
      const v324! = wager/304 + wager/304;
      checkPay(wager/304, Nothing);
      loopvar {
        v325 = 1,
        v326 = thisConsensusTime/321,
        v332 = v324};
      invariant{
        () }
      while{
        const v340! = outcome/325 == 1;
        
        return v340; }
      {
        const v347! = thisConsensusTime/326 + deadline/305;
        fromConsensus 5 (continue [(v303, v303), (v304, wager/304), (v305, deadline/305), (v320, v320), (v332, balance(0)/332), (v347, v347)]) ;
        recv({
          didSendv = v92,
          from = v355,
          lct = Just thisConsensusTime/326,
          msg = (v356 ),
          out = (),
          prev = 5,
          secsv = v358,
          timev = v357,
          which = 4})
        timeout(Just Left v347, {
          send({
            amt = [0, ],
            as = (),
            saved = (v303, v304, v305, v320, v332, v347 ),
            soloSend = False,
            when = true,
            which = 5})
          recv({
            didSendv = v212,
            from = v438,
            lct = Just thisConsensusTime/326,
            msg = (),
            out = (),
            prev = 5,
            secsv = v440,
            timev = v439,
            which = 5})
          {
            checkPay(0, Nothing);
            const v442! = v303 == v438;
            const v443! = v320 == v438;
            const v444! = (v442 ? true : v443);
            claim(CT_Require)(v444, Just "sender correct");
            transfer.(balance(0)/332, Nothing).to(v320);
            fromConsensus 6 (halt []) ;
            only(Right False) {
              protect<Null>("Bob".interact.informTimeout());
               };
             } } )
        {
          checkPay(0, Nothing);
          const v360! = v303 == v355;
          claim(CT_Require)(v360, Just "sender correct");
          const v367! = thisConsensusTime/357 + deadline/305;
          fromConsensus 7 (continue [(v303, v303), (v304, wager/304), (v305, deadline/305), (v320, v320), (v332, balance(0)/332), (v356, commitAlice/356), (v367, v367)]) ;
          only(Right False) {
            const v371* = protect<UInt>("Bob".interact.getHand());
             };
          send({
            amt = [0, ],
            as = (v371 ),
            saved = (v303, v304, v305, v320, v332, v356, v367 ),
            soloSend = True,
            when = true,
            which = 6})
          recv({
            didSendv = v103,
            from = v372,
            lct = Just thisConsensusTime/357,
            msg = (v373 ),
            out = (),
            prev = 7,
            secsv = v375,
            timev = v374,
            which = 6})
          timeout(Just Left v367, {
            send({
              amt = [0, ],
              as = (),
              saved = (v303, v304, v305, v320, v332, v356, v367 ),
              soloSend = False,
              when = true,
              which = 7})
            recv({
              didSendv = v177,
              from = v419,
              lct = Just thisConsensusTime/357,
              msg = (),
              out = (),
              prev = 7,
              secsv = v421,
              timev = v420,
              which = 7})
            {
              checkPay(0, Nothing);
              const v423! = v303 == v419;
              const v424! = v320 == v419;
              const v425! = (v423 ? true : v424);
              claim(CT_Require)(v425, Just "sender correct");
              transfer.(balance(0)/332, Nothing).to(v303);
              fromConsensus 8 (halt []) ;
              only(Right False) {
                protect<Null>("Bob".interact.informTimeout());
                 };
               } } )
          {
            checkPay(0, Nothing);
            const v377! = v320 == v372;
            claim(CT_Require)(v377, Just "sender correct");
            const v384! = thisConsensusTime/374 + deadline/305;
            fromConsensus 9 (continue [(v303, v303), (v304, wager/304), (v305, deadline/305), (v320, v320), (v332, balance(0)/332), (v356, commitAlice/356), (v373, handBob/373), (v384, v384)]) ;
            recv({
              didSendv = v114,
              from = v388,
              lct = Just thisConsensusTime/374,
              msg = (v389, v390 ),
              out = (),
              prev = 9,
              secsv = v392,
              timev = v391,
              which = 8})
            timeout(Just Left v384, {
              send({
                amt = [0, ],
                as = (),
                saved = (v303, v304, v305, v320, v332, v356, v373, v384 ),
                soloSend = False,
                when = true,
                which = 9})
              recv({
                didSendv = v142,
                from = v400,
                lct = Just thisConsensusTime/374,
                msg = (),
                out = (),
                prev = 9,
                secsv = v402,
                timev = v401,
                which = 9})
              {
                checkPay(0, Nothing);
                const v404! = v303 == v400;
                const v405! = v320 == v400;
                const v406! = (v404 ? true : v405);
                claim(CT_Require)(v406, Just "sender correct");
                transfer.(balance(0)/332, Nothing).to(v320);
                fromConsensus 10 (halt []) ;
                only(Right False) {
                  protect<Null>("Bob".interact.informTimeout());
                   };
                 } } )
            {
              checkPay(0, Nothing);
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
              continue; } } } }
      const v457! = outcome/325 == 2;
      const v460! = 2 * wager/304;
      const v462! = (v457 ? v303 : v320);
      transfer.(v460, Nothing).to(v462);
      fromConsensus 4 (halt []) ;
      only(Right False) {
        protect<Null>("Bob".interact.seeOutcome(outcome/325 ));
         };
       } }}


views: ({
  }, {
  1 = (view [v303, v304, v305, v316] {
    }),
  5 = (view [v303, v304, v305, v320, v332, v347] {
    }),
  7 = (view [v303, v304, v305, v320, v332, v356, v367] {
    }),
  9 = (view [v303, v304, v305, v320, v332, v356, v373, v384] {
    })})
apiInfo: {
  }
events: {
  }
{
  0 = {
    v303,
    (between [Nothing] [Nothing]),
    last = 0,
    [],
    [],
    [v304, v305],
    [UInt, UInt],
    timev = v306,
    secsv = v307,
    {
      checkPay(wager/304, Nothing);
      const v316! = thisConsensusTime/306 + deadline/305;
      (from 1, (continue [(v303, v303), (v304, wager/304), (v305, deadline/305), (v316, v316)])) }
     },
  1 = {
    v320,
    (between [Nothing] [Just Left v316]),
    last = 1,
    [v303, v304, v305, v316],
    [Address, UInt, UInt, UInt],
    [],
    [],
    timev = v321,
    secsv = v322,
    {
      const v324! = wager/304 + wager/304;
      checkPay(wager/304, Nothing);
      (jump! 3 [v303, v304, v305, v320] {
        v325 = 1,
        v326 = thisConsensusTime/321,
        v332 = v324}) }
     },
  2 = {
    v473,
    (between [Just Left v316] [Nothing]),
    last = 1,
    [v303, v304, v305, v316],
    [Address, UInt, UInt, UInt],
    [],
    [],
    timev = v474,
    secsv = v475,
    {
      checkPay(0, Nothing);
      transfer.(wager/304, Nothing).to(v303);
      (from 2, (halt [])) }
     },
  3 = {
    loop!,
    [v303, v304, v305, v320],
    [v325, v326, v332],
    {
      const v340! = outcome/325 == 1;
      if v340 then {
        const v347! = thisConsensusTime/326 + deadline/305;
        (from 5, (continue [(v303, v303), (v304, wager/304), (v305, deadline/305), (v320, v320), (v332, balance(0)/332), (v347, v347)])) }
      else {
        const v457! = outcome/325 == 2;
        const v460! = 2 * wager/304;
        const v462! = (v457 ? v303 : v320);
        transfer.(v460, Nothing).to(v462);
        (from 4, (halt [])) }; }
     },
  4 = {
    v355,
    (between [Nothing] [Just Left v347]),
    last = 5,
    [v303, v304, v305, v320, v332, v347],
    [Address, UInt, UInt, Address, UInt, UInt],
    [v356],
    [Digest],
    timev = v357,
    secsv = v358,
    {
      checkPay(0, Nothing);
      const v360! = v303 == v355;
      claim(CT_Require)(v360, Just "sender correct");
      const v367! = thisConsensusTime/357 + deadline/305;
      (from 7, (continue [(v303, v303), (v304, wager/304), (v305, deadline/305), (v320, v320), (v332, balance(0)/332), (v356, commitAlice/356), (v367, v367)])) }
     },
  5 = {
    v438,
    (between [Just Left v347] [Nothing]),
    last = 5,
    [v303, v304, v305, v320, v332, v347],
    [Address, UInt, UInt, Address, UInt, UInt],
    [],
    [],
    timev = v439,
    secsv = v440,
    {
      checkPay(0, Nothing);
      const v442! = v303 == v438;
      const v443! = v320 == v438;
      const v444! = (v442 ? true : v443);
      claim(CT_Require)(v444, Just "sender correct");
      transfer.(balance(0)/332, Nothing).to(v320);
      (from 6, (halt [])) }
     },
  6 = {
    v372,
    (between [Nothing] [Just Left v367]),
    last = 7,
    [v303, v304, v305, v320, v332, v356, v367],
    [Address, UInt, UInt, Address, UInt, Digest, UInt],
    [v373],
    [UInt],
    timev = v374,
    secsv = v375,
    {
      checkPay(0, Nothing);
      const v377! = v320 == v372;
      claim(CT_Require)(v377, Just "sender correct");
      const v384! = thisConsensusTime/374 + deadline/305;
      (from 9, (continue [(v303, v303), (v304, wager/304), (v305, deadline/305), (v320, v320), (v332, balance(0)/332), (v356, commitAlice/356), (v373, handBob/373), (v384, v384)])) }
     },
  7 = {
    v419,
    (between [Just Left v367] [Nothing]),
    last = 7,
    [v303, v304, v305, v320, v332, v356, v367],
    [Address, UInt, UInt, Address, UInt, Digest, UInt],
    [],
    [],
    timev = v420,
    secsv = v421,
    {
      checkPay(0, Nothing);
      const v423! = v303 == v419;
      const v424! = v320 == v419;
      const v425! = (v423 ? true : v424);
      claim(CT_Require)(v425, Just "sender correct");
      transfer.(balance(0)/332, Nothing).to(v303);
      (from 8, (halt [])) }
     },
  8 = {
    v388,
    (between [Nothing] [Just Left v384]),
    last = 9,
    [v303, v304, v305, v320, v332, v356, v373, v384],
    [Address, UInt, UInt, Address, UInt, Digest, UInt, UInt],
    [v389, v390],
    [UInt, UInt],
    timev = v391,
    secsv = v392,
    {
      checkPay(0, Nothing);
      const v394! = v303 == v388;
      claim(CT_Require)(v394, Just "sender correct");
      const v395! = digest(saltAlice/389, handAlice/390 );
      const v396! = commitAlice/356 == v395;
      claim(CT_Require)(v396, Nothing);
      const v397! = 4 - handBob/373;
      const v398! = handAlice/390 + v397;
      const v399! = v398 % 3;
      (jump! 3 [v303, v304, v305, v320] {
        v325 = v399,
        v326 = thisConsensusTime/391,
        v332 = balance(0)/332}) }
     },
  9 = {
    v400,
    (between [Just Left v384] [Nothing]),
    last = 9,
    [v303, v304, v305, v320, v332, v356, v373, v384],
    [Address, UInt, UInt, Address, UInt, Digest, UInt, UInt],
    [],
    [],
    timev = v401,
    secsv = v402,
    {
      checkPay(0, Nothing);
      const v404! = v303 == v400;
      const v405! = v320 == v400;
      const v406! = (v404 ? true : v405);
      claim(CT_Require)(v406, Just "sender correct");
      transfer.(balance(0)/332, Nothing).to(v320);
      (from 10, (halt [])) }
     }}
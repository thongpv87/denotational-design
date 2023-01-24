Dear Conal,

> I think you are trying to argue that the existence of a raw monoid homomorphism from a (law-abiding) monoid does not imply that the homomorphism’s target obeys the monoid laws. Am I accurately understanding the nature of your claim?

Yes, that's exactly what I was trying to prove.

> I think the shape of your argument here (leading to the third bullet point above) is that if P ⇒ Q then ¬ P ⇒ ¬ Q, which you probably realize is not generally valid. (Not all sufficient conditions are necessary conditions.)

Thank you for pointed that out. Now I see the error with my proof.

> Is your claim above somehow related to a purpose you see being served by including the Monoid constraints in the MonoidH class (and similarly for CommMonoidH)?

>> In your CommMonoidH class, what purpose is served by the P-comm, comm-monoidₘ and comm-monoidₙ fields? In other words, what value would be lost if you eliminated them? Likewise, in your MonoidH class, what purpose is served by the third and fourth fields (monoidₘ and monoidₙ)?

Because you asked *"what value would be lost if you eliminated them?"*, I want to show that without `Monoid` constraints in `MonoidH` or similarly with `CommMonoidH`, the homomorphisms would *not* be the morphisms that preserve (monoid/communicative monoid) structure. That's why I need to include it in the definition of those homomorphisms.

I apologize if there was any confusion caused by my misunderstanding of your request or if my English is not clear. As a non-native speaker, I sometimes or struggle to express myself clearly in writing. 

Sincerely,

Thong

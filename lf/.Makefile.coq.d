Preface.vo Preface.glob Preface.v.beautified Preface.required_vo: Preface.v 
Preface.vos Preface.vok Preface.required_vos: Preface.v 
Basics.vo Basics.glob Basics.v.beautified Basics.required_vo: Basics.v 
Basics.vos Basics.vok Basics.required_vos: Basics.v 
Induction.vo Induction.glob Induction.v.beautified Induction.required_vo: Induction.v Basics.vo
Induction.vos Induction.vok Induction.required_vos: Induction.v Basics.vos
Lists.vo Lists.glob Lists.v.beautified Lists.required_vo: Lists.v Induction.vo
Lists.vos Lists.vok Lists.required_vos: Lists.v Induction.vos
Poly.vo Poly.glob Poly.v.beautified Poly.required_vo: Poly.v Lists.vo
Poly.vos Poly.vok Poly.required_vos: Poly.v Lists.vos
Tactics.vo Tactics.glob Tactics.v.beautified Tactics.required_vo: Tactics.v Poly.vo
Tactics.vos Tactics.vok Tactics.required_vos: Tactics.v Poly.vos
Logic.vo Logic.glob Logic.v.beautified Logic.required_vo: Logic.v Tactics.vo
Logic.vos Logic.vok Logic.required_vos: Logic.v Tactics.vos
IndProp.vo IndProp.glob IndProp.v.beautified IndProp.required_vo: IndProp.v Logic.vo
IndProp.vos IndProp.vok IndProp.required_vos: IndProp.v Logic.vos
Maps.vo Maps.glob Maps.v.beautified Maps.required_vo: Maps.v 
Maps.vos Maps.vok Maps.required_vos: Maps.v 
ProofObjects.vo ProofObjects.glob ProofObjects.v.beautified ProofObjects.required_vo: ProofObjects.v IndProp.vo
ProofObjects.vos ProofObjects.vok ProofObjects.required_vos: ProofObjects.v IndProp.vos
IndPrinciples.vo IndPrinciples.glob IndPrinciples.v.beautified IndPrinciples.required_vo: IndPrinciples.v ProofObjects.vo
IndPrinciples.vos IndPrinciples.vok IndPrinciples.required_vos: IndPrinciples.v ProofObjects.vos
Rel.vo Rel.glob Rel.v.beautified Rel.required_vo: Rel.v IndProp.vo
Rel.vos Rel.vok Rel.required_vos: Rel.v IndProp.vos
Imp.vo Imp.glob Imp.v.beautified Imp.required_vo: Imp.v Maps.vo
Imp.vos Imp.vok Imp.required_vos: Imp.v Maps.vos
ImpParser.vo ImpParser.glob ImpParser.v.beautified ImpParser.required_vo: ImpParser.v Maps.vo Imp.vo
ImpParser.vos ImpParser.vok ImpParser.required_vos: ImpParser.v Maps.vos Imp.vos
ImpCEvalFun.vo ImpCEvalFun.glob ImpCEvalFun.v.beautified ImpCEvalFun.required_vo: ImpCEvalFun.v Imp.vo Maps.vo
ImpCEvalFun.vos ImpCEvalFun.vok ImpCEvalFun.required_vos: ImpCEvalFun.v Imp.vos Maps.vos
Extraction.vo Extraction.glob Extraction.v.beautified Extraction.required_vo: Extraction.v ImpCEvalFun.vo Imp.vo ImpParser.vo Maps.vo
Extraction.vos Extraction.vok Extraction.required_vos: Extraction.v ImpCEvalFun.vos Imp.vos ImpParser.vos Maps.vos
Auto.vo Auto.glob Auto.v.beautified Auto.required_vo: Auto.v Maps.vo Imp.vo
Auto.vos Auto.vok Auto.required_vos: Auto.v Maps.vos Imp.vos
AltAuto.vo AltAuto.glob AltAuto.v.beautified AltAuto.required_vo: AltAuto.v IndProp.vo
AltAuto.vos AltAuto.vok AltAuto.required_vos: AltAuto.v IndProp.vos
Postscript.vo Postscript.glob Postscript.v.beautified Postscript.required_vo: Postscript.v 
Postscript.vos Postscript.vok Postscript.required_vos: Postscript.v 
Bib.vo Bib.glob Bib.v.beautified Bib.required_vo: Bib.v 
Bib.vos Bib.vok Bib.required_vos: Bib.v 
PrefaceTest.vo PrefaceTest.glob PrefaceTest.v.beautified PrefaceTest.required_vo: PrefaceTest.v Preface.vo
PrefaceTest.vos PrefaceTest.vok PrefaceTest.required_vos: PrefaceTest.v Preface.vos
BasicsTest.vo BasicsTest.glob BasicsTest.v.beautified BasicsTest.required_vo: BasicsTest.v Basics.vo
BasicsTest.vos BasicsTest.vok BasicsTest.required_vos: BasicsTest.v Basics.vos
InductionTest.vo InductionTest.glob InductionTest.v.beautified InductionTest.required_vo: InductionTest.v Induction.vo
InductionTest.vos InductionTest.vok InductionTest.required_vos: InductionTest.v Induction.vos
ListsTest.vo ListsTest.glob ListsTest.v.beautified ListsTest.required_vo: ListsTest.v Lists.vo
ListsTest.vos ListsTest.vok ListsTest.required_vos: ListsTest.v Lists.vos
PolyTest.vo PolyTest.glob PolyTest.v.beautified PolyTest.required_vo: PolyTest.v Poly.vo
PolyTest.vos PolyTest.vok PolyTest.required_vos: PolyTest.v Poly.vos
TacticsTest.vo TacticsTest.glob TacticsTest.v.beautified TacticsTest.required_vo: TacticsTest.v Tactics.vo
TacticsTest.vos TacticsTest.vok TacticsTest.required_vos: TacticsTest.v Tactics.vos
LogicTest.vo LogicTest.glob LogicTest.v.beautified LogicTest.required_vo: LogicTest.v Logic.vo
LogicTest.vos LogicTest.vok LogicTest.required_vos: LogicTest.v Logic.vos
IndPropTest.vo IndPropTest.glob IndPropTest.v.beautified IndPropTest.required_vo: IndPropTest.v IndProp.vo
IndPropTest.vos IndPropTest.vok IndPropTest.required_vos: IndPropTest.v IndProp.vos
MapsTest.vo MapsTest.glob MapsTest.v.beautified MapsTest.required_vo: MapsTest.v Maps.vo
MapsTest.vos MapsTest.vok MapsTest.required_vos: MapsTest.v Maps.vos
ProofObjectsTest.vo ProofObjectsTest.glob ProofObjectsTest.v.beautified ProofObjectsTest.required_vo: ProofObjectsTest.v ProofObjects.vo
ProofObjectsTest.vos ProofObjectsTest.vok ProofObjectsTest.required_vos: ProofObjectsTest.v ProofObjects.vos
IndPrinciplesTest.vo IndPrinciplesTest.glob IndPrinciplesTest.v.beautified IndPrinciplesTest.required_vo: IndPrinciplesTest.v IndPrinciples.vo
IndPrinciplesTest.vos IndPrinciplesTest.vok IndPrinciplesTest.required_vos: IndPrinciplesTest.v IndPrinciples.vos
RelTest.vo RelTest.glob RelTest.v.beautified RelTest.required_vo: RelTest.v Rel.vo
RelTest.vos RelTest.vok RelTest.required_vos: RelTest.v Rel.vos
ImpTest.vo ImpTest.glob ImpTest.v.beautified ImpTest.required_vo: ImpTest.v Imp.vo
ImpTest.vos ImpTest.vok ImpTest.required_vos: ImpTest.v Imp.vos
ImpParserTest.vo ImpParserTest.glob ImpParserTest.v.beautified ImpParserTest.required_vo: ImpParserTest.v ImpParser.vo
ImpParserTest.vos ImpParserTest.vok ImpParserTest.required_vos: ImpParserTest.v ImpParser.vos
ImpCEvalFunTest.vo ImpCEvalFunTest.glob ImpCEvalFunTest.v.beautified ImpCEvalFunTest.required_vo: ImpCEvalFunTest.v ImpCEvalFun.vo
ImpCEvalFunTest.vos ImpCEvalFunTest.vok ImpCEvalFunTest.required_vos: ImpCEvalFunTest.v ImpCEvalFun.vos
ExtractionTest.vo ExtractionTest.glob ExtractionTest.v.beautified ExtractionTest.required_vo: ExtractionTest.v Extraction.vo
ExtractionTest.vos ExtractionTest.vok ExtractionTest.required_vos: ExtractionTest.v Extraction.vos
AutoTest.vo AutoTest.glob AutoTest.v.beautified AutoTest.required_vo: AutoTest.v Auto.vo
AutoTest.vos AutoTest.vok AutoTest.required_vos: AutoTest.v Auto.vos
AltAutoTest.vo AltAutoTest.glob AltAutoTest.v.beautified AltAutoTest.required_vo: AltAutoTest.v AltAuto.vo
AltAutoTest.vos AltAutoTest.vok AltAutoTest.required_vos: AltAutoTest.v AltAuto.vos
PostscriptTest.vo PostscriptTest.glob PostscriptTest.v.beautified PostscriptTest.required_vo: PostscriptTest.v Postscript.vo
PostscriptTest.vos PostscriptTest.vok PostscriptTest.required_vos: PostscriptTest.v Postscript.vos
BibTest.vo BibTest.glob BibTest.v.beautified BibTest.required_vo: BibTest.v Bib.vo
BibTest.vos BibTest.vok BibTest.required_vos: BibTest.v Bib.vos

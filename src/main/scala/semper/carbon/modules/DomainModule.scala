package semper.carbon.modules

import semper.sil.{ast => sil}
import semper.carbon.boogie.{Type, Decl, Exp}

/**
 * A module for translating SIL domains.
 *
 * @author Stefan Heule
 */
trait DomainModule extends Module {
  def translateDomain(exp: sil.Domain): Seq[Decl]
  def translateDomainFuncApp(fa: sil.DomainFuncApp): Exp
  def translateDomainTyp(typ: sil.DomainType): Type
}
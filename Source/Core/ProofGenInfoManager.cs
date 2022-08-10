using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.IO;
using System.Linq;
using System.Runtime.Serialization.Formatters.Binary;

namespace Microsoft.Boogie
{
  public static class ProofGenInfoManager
  {
    private static IDictionary<Implementation, ProofGenInfo> mapFromImplementationToProofGenInfo;
    private static ProofGenInfo currentProofGenInfo;

    public static IDictionary<Implementation, ProofGenInfo> GetMapFromImplementationToProofGenInfo()
    {
      /*
      if (mapFromImplementationToProofGenInfo == null)
      {
        mapFromImplementationToProofGenInfo = new Dictionary<Implementation, ProofGenInfo>();
      }

      return mapFromImplementationToProofGenInfo;
      */
      
      return mapFromImplementationToProofGenInfo ??= new Dictionary<Implementation, ProofGenInfo>();
    }
    
    public static ProofGenInfo GetCurrentProofGenInfo()
    {
      return currentProofGenInfo ??= new ProofGenInfo();
    }
    
    public static void SetCurrentProofGenInfo(ProofGenInfo proofGenInfo)
    {
      currentProofGenInfo = proofGenInfo;
    }
  }
}
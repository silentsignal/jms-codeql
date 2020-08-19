/**
 * @name IBM MQ JMS Insecure Deserialization
 * @description Alerts when object deserialization happens during the handling of 'JMSMessage' objects
 * @problem.severity warning
 * @kind path-problem
 * @id silentsignal/java/ibm-mq-jms-deserialization
 * @tags security
 */

import java
import semmle.code.java.dataflow.DataFlow
import DataFlow::PathGraph 

predicate isJMSGetBody(Expr arg) {
  exists(MethodAccess call, Method getbody |
    call.getMethod() = getbody and
    getbody.hasName("getBody") and
    getbody.getDeclaringType().getAnAncestor().hasQualifiedName("javax.jms", "Message") and
    arg = call.getQualifier()
  )
}

predicate isJMSGetObject(Expr arg) {
  exists(MethodAccess call, Method getobject |
    call.getMethod() = getobject and
    (getobject.hasName("getObject") or getobject.hasName("getObjectInternal")) and
    getobject.getDeclaringType().getAnAncestor().hasQualifiedName("javax.jms", "Message") and
    arg = call.getQualifier()
  )
}

/*
Example source for Spring
*/
class ReceiveMessageMethod extends Method {
  ReceiveMessageMethod() {
    this.getAnAnnotation().toString().matches("JmsListener")
  }
}

class IBMJMSDeserConfig extends DataFlow::Configuration{
  IBMJMSDeserConfig(){
    this = "IBMJMSDeserConfig"
  }

  /**
   * Holds if `source` is a relevant data flow source.
   */
  override predicate isSource(DataFlow::Node source){
      exists( ReceiveMessageMethod rcvmsg |
        source.asParameter() = rcvmsg.getParameter(0)
      )
  }

  /**
   * Holds if `sink` is a relevant data flow sink.
   */
  override predicate isSink(DataFlow::Node sink){
      exists (
          Expr arg | 
          (isJMSGetBody(arg) or isJMSGetObject(arg)) and 
          sink.asExpr() = arg
      )
  }
  
}

from IBMJMSDeserConfig config, DataFlow::PathNode source, DataFlow::PathNode sink
where config.hasFlowPath(source, sink)
select sink,source,sink,"JMSMessage deserialization"

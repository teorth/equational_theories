var toolTipLib = { 
	xCord : 0,
	yCord : 0,
	obj : null,
	tipElements : ['a','abbr','acronym'],
	attachToolTipBehavior: function() {
		if ( !document.getElementById ||
			!document.createElement ||
			!document.getElementsByTagName ) {
			return;
		}
		var i,j;
		addEvent(document,'mousemove',toolTipLib.updateXY,false);
		if ( document.captureEvents ) {
				document.captureEvents(Event.MOUSEMOVE);
		}
		for ( i=0;i<toolTipLib.tipElements.length;i++ ) {
			var current = document.getElementsByTagName(toolTipLib.tipElements[i]);
			for ( j=0;j<current.length;j++ ) {
				addEvent(current[j],'mouseover',toolTipLib.tipOver,false);
				addEvent(current[j],'mouseout',toolTipLib.tipOut,false);
				current[j].setAttribute('tip',current[j].title);
				current[j].removeAttribute('title');
			}
		}
	},
	updateXY : function(e) {
		if ( document.captureEvents ) {
			toolTipLib.xCord = e.pageX;
			toolTipLib.yCord = e.pageY;
		} else if ( window.event.clientX ) {
			toolTipLib.xCord = window.event.clientX+document.documentElement.scrollLeft;
			toolTipLib.yCord = window.event.clientY+document.documentElement.scrollTop;
		}
	},
	tipOut: function(e) {
		if ( window.tID ) {
			clearTimeout(tID);
		}
		if ( window.opacityID ) {
			clearTimeout(opacityID);
		}
		var l = getEventSrc(e);
		var div = document.getElementById('toolTip');
		if ( div ) {
			div.parentNode.removeChild(div);
		}
	},
	checkNode : function(obj) {
		var trueObj = obj;
		if ( trueObj.nodeName.toLowerCase() == 'a' || trueObj.nodeName.toLowerCase() == 'acronym' || trueObj.nodeName.toLowerCase() == 'abbr' ) {
			return trueObj;
		} else {
			return trueObj.parentNode;
		}
	},
	tipOver : function(e) {
		toolTipLib.obj = getEventSrc(e);
		tID = setTimeout("toolTipLib.tipShow()",500)
	},
	tipShow : function() {
		var newDiv = document.createElement('div');
		var scrX = Number(toolTipLib.xCord);
		var scrY = Number(toolTipLib.yCord);
		var tp = parseInt(scrY+15);
		var lt = parseInt(scrX+10);
		var anch = toolTipLib.checkNode(toolTipLib.obj);
		var addy = '';
		var access = '';
		if ( anch.nodeName.toLowerCase() == 'a' ) {
			addy = (anch.href.length > 25 ? anch.href.toString().substring(0,25)+"..." : anch.href);
			var access = ( anch.accessKey ? ' <span>['+anch.accessKey+']</span> ' : '' );
		} else {
			addy = anch.firstChild.nodeValue;
		}
		newDiv.id = 'toolTip';
		document.getElementsByTagName('body')[0].appendChild(newDiv);
		newDiv.style.opacity = '.1';
		newDiv.innerHTML = "<p>"+anch.getAttribute('tip')+"<em>"+access+addy+"</em></p>";
		if ( parseInt(document.documentElement.clientWidth+document.documentElement.scrollLeft) < parseInt(newDiv.offsetWidth+lt) ) {
			newDiv.style.left = parseInt(lt-(newDiv.offsetWidth+10))+'px';
		} else {
			newDiv.style.left = lt+'px';
		}
		if ( parseInt(document.documentElement.clientHeight+document.documentElement.scrollTop) < parseInt(newDiv.offsetHeight+tp) ) {
			newDiv.style.top = parseInt(tp-(newDiv.offsetHeight+10))+'px';
		} else {
			newDiv.style.top = tp+'px';
		}
		toolTipLib.tipFade('toolTip',10);
	},
	tipFade: function(div,opac) {
		var obj = document.getElementById(div);
		var passed = parseInt(opac);
		var newOpac = parseInt(passed+10);
		if ( newOpac < 80 ) {
			obj.style.opacity = '.'+newOpac;
			obj.style.filter = "alpha(opacity:"+newOpac+")";
			opacityID = setTimeout("toolTipLib.tipFade('toolTip','"+newOpac+"')",20);
		}
		else { 
			obj.style.opacity = '.80';
			obj.style.filter = "alpha(opacity:80)";
		}
	}
};
addEvent(window,'load',toolTipLib.attachToolTipBehavior,false);
$(document).ready(function() {
     var icon = function($icon, $class, $id) {
         if ($id) {
             $id = ' id="'+$id+'"';
         } else {
             $id = '';
         }

         return '<svg'+ $id + ' class="icon icon-' + $icon + ' ' + $class +'"><use xlink:href="symbol-defs.svg#icon-'+$icon+'"></use></svg>'
     };

     $("#toc-toggle").click(function() {
         $("nav.toc").toggle()
     });

    $("nav.toc").on("click", "span.expand-toc",
            function() {
                $(this).siblings("ul").slideToggle('fast');

                if ($(this).html() == "▼") {
                  $(this).html("▶");
                } else {
                  $(this).html("▼");
                };

            })


    $("div.proof_content p:last").append('<span class="qed">□</span>')

    $("div.proof_heading").click(
           function() {
               var expand_span = $(this).children('span.expand-proof');
                if ($(expand_span).html() == "▼") {
                  $(expand_span).html("▶");
                } else {
                  $(expand_span).html("▼");
                };

               $(this).siblings("div.proof_content").slideToggle()
           })

    $("a.proof").click(
            function() {
                var ref= $(this).attr('href').split('#')[1];
                var proof = $('#'+ref)
                proof.show()
                proof.children('.proof_content').each(
                    function() { 
                        var proof_content = $(this)
                        proof_content.show().addClass('hilite')
                        setTimeout(function(){
                            proof_content.removeClass('hilite')
                            }, 1000);
                    })
                var expand_icon = proof.find('svg.expand-proof');
                expand_icon.replaceWith(icon('cross', 'expand-proof'));
            })


    $("button.modal").click(
        function() {
          $(this).next("div.modal-container").css('display', 'flex');
        })
    $("button.closebtn").click(
        function() {
          $(this).parent().parent().parent().hide();
        })
});
